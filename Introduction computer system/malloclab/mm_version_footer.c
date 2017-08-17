/*
 ******************************************************************************
 *                               mm.c                                         *
 *           64-bit struct-based implicit free list memory allocator          *
 *                  15-213: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *              this file create one simple memory allocator. :)              *
 *              Name: Shu Liu   AndrewID: Shul2                               *
 *  ************************************************************************  *
 *  ** ADVICE FOR STUDENTS. **                                                *
 *  Step 0: Please read the writeup!                                          *
 *  Step 1: Write your heap checker. Write. Heap. checker.                    *
 *  Step 2: Place your contracts / debugging assert statements.               *
 *  Good luck, and have fun!                                                  *
 *                                                                            *
 ******************************************************************************
 */

/* Do not change the following! */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
// #define DEBUG // uncomment this line to enable debugging

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*wsize;          // double word size (bytes)
static const size_t min_block_size = 2*dsize; // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t prev_alloc_mask = 0x2;   // to remove the footer
static const word_t size_mask = ~(word_t)0xF;

typedef struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    /*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
    char payload[0];
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
} block_t;

/* Global variables */
/* Pointer to first block */
static block_t *heap_start = NULL;
static char *root = NULL;  // head of the freed block

bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool prev_alloc, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool prev_alloc, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);\

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);


/*
 * costom functions
 */
static bool prologue_check(block_t *phead);
static bool epilogue_check(block_t *phead);
static void debug_message(int line);

static void write_prev_pointer(block_t *block, block_t *prev_block);
static void write_next_pointer(block_t *block, block_t *next_block);
static void write_head_pointer(block_t *pointer);
static void write_tail_pointer(block_t *pointer);
static block_t *get_head_pointer();
static block_t *get_tail_pointer();
static bool get_prev_alloc(block_t *block);
static block_t *find_next_free_block(block_t *block);
static block_t *find_prev_free_block(block_t *block);

static void freeblock_insert(block_t *block, block_t *freeblock_next);
static void freeblock_remove(block_t *block);
static block_t *freeblock_coalesce(block_t *block);
static void split_freeblock(block_t *block, block_t *block_next);

static bool next_add_check(block_t *block);
static bool prev_add_check(block_t *block);
static bool address_check();
static void checker(block_t *block);

static void set_alloc_bit(block_t *block);
static void off_alloc_bit(block_t *block);

static void debug_break(block_t *block);
/*
 *  mm_init is used for Initialize the memory system
 */
bool mm_init(void)
{

    // Create head and tail node for the freed block list
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1)
    {
        return false;
    }
    root = (char *)start;

    write_head_pointer(NULL);
    write_tail_pointer(NULL);

    // Create the initial empty heap
    start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1)
    {
        return false;
    }

    start[0] = pack(0, true, true); // Prologue footer
    start[1] = pack(0, true, true); // Epilogue header
    // Heap starts with first "block header", currently the epilogue footer
    heap_start = (block_t *) &(start[1]);
    //root = NULL;

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    return true;
}

/*
 * malloc is used for allocting a bunch of memory
 */
void *malloc(size_t size)
{
    dbg_requires(mm_checkheap(__LINE__));
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_start == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }
dbg_printf("********  Malloc start ********\n");
    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + dsize, dsize);
dbg_printf("in malloc, the asize after round_up is %zu\n", asize);

    // Search the free list for first available fit
    block = find_fit(asize);
dbg_printf("in malloc, the block after find_fit is %p\n", block);

    if (block == NULL)
    {
        extendsize = max(asize, chunksize);
        dbg_printf("in malloc, the size after max is %zu\n", extendsize);
        block = extend_heap(extendsize);
        dbg_printf("block address is %p and size is %zu\n", block, asize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }
    }
    dbg_requires(mm_checkheap(__LINE__));

dbg_printf("in malloc, the block before place is %p\n", block);
    place(block, asize);
dbg_printf("in malloc, the block after place is %p\n", block);
    bp = header_to_payload(block);
dbg_printf("block address is %p and size is %zu\n", block, asize);
    dbg_ensures(mm_checkheap(__LINE__));
dbg_printf("********  Malloc end ********\n");
    return bp;
}

/*
 * free is used for releasing a bunch of memory
 */
void free(void *bp)
{
    if (bp == NULL)
    {
        return;
    }
dbg_printf("********  Free start ********\n");
    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    debug_break(block);
dbg_printf("in free, the block add before write header is %p\n", block);
dbg_printf("in free, the size before write header is %lx\n", size);

    write_header(block, size, get_prev_alloc(block), false);
    write_footer(block, size, false);

dbg_printf("in free, the block add after write footer is %p\n", block);

    block_t *next_block = find_next(block);
    off_alloc_bit(next_block);

    freeblock_coalesce(block);
dbg_printf("in free, the block add after coalesce is %p\n", block);
dbg_printf("********  Free end ********\n");
}

/*
 *  realloc is used for reallocing the memory system
 */
void *realloc(void *ptr, size_t size)
{
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (newptr == NULL)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/*
 * calloc is a strong version of malloc
 */
void *calloc(size_t elements, size_t size)
{
    void *bp;
    size_t asize = elements * size;

    if (asize/elements != size)
    // Multiplication overflowed
    return NULL;

    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * extend_heap is used for applying more memory
 */
static block_t *extend_heap(size_t size)
{
    void *bp;
    dbg_requires(mm_checkheap(__LINE__));
    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
dbg_printf("in extend_heap, before Initialize, the size is %zu\n", size);

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);

    bool prev_alloc_flag = get_prev_alloc(block);
    write_header(block, size, prev_alloc_flag, false);
    write_footer(block, size, false);
dbg_printf("in extend_heap, after Initialize, the block add is %p\n", block);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, false, true);
dbg_printf("in extend_heap, after create, the block next add is %p\n", block_next);

    return freeblock_coalesce(block);
}

/*
 * place is used for allocting memory for payload
 */
 static void place(block_t *block, size_t asize)
 {
     size_t csize = get_size(block);

     if ((csize - asize) >= min_block_size)
     {

         block_t *block_next;
         write_header(block, asize, true, true);
         //write_footer(block, asize, true);
 dbg_printf("in place, before split, the block add is %20p\n", block);

         block_next = find_next(block);
         write_header(block_next, csize-asize, true, false);
         write_footer(block_next, csize-asize, false);
 dbg_printf("in place, after split, the block next add is %20p\n", block_next);

         split_freeblock(block, block_next);
 dbg_printf("in place, after split_freeblock, block next add is %20p\n", block_next);

     }

     else
     {
 dbg_printf("in place, no split, the block add is %20p\n", block);
         write_header(block, csize, true, true);
         // write_footer(block, csize, true);

         block_t *next_block = find_next(block);
         set_alloc_bit(next_block);

         // remove the free node
         freeblock_remove(block);
     }
}

/*
 * <what does find_fit do?>
 */
static block_t *find_fit(size_t asize)
{
    block_t *block;
    block_t *firstblock;
    block_t *secondblock;
    bool flag1 = false;
    bool flag2 = false;

    for (block = get_tail_pointer(); block != NULL
             && get_size(block) > 0; block = find_prev_free_block(block))
    {

      dbg_printf("in find_fit, the head is %p\n", get_head_pointer());
      dbg_printf("in find_fit, the current block is %p\n", block);
      dbg_printf("in find_fit, the asize is %zu\n", asize);
      dbg_printf("in find_fit, the available size is %zu\n", get_size(block));

      if (asize <= get_size(block))
      {
          if (!flag1 && !flag2) {
              firstblock = block;
              flag1 = !flag1;
          } else if (!flag2){
              secondblock = block;
              flag2 = !flag2;
              break;
          }
      }
    }
    if (flag1 && flag2) {
        return get_size(firstblock) > get_size(secondblock)
                  ? secondblock : firstblock;
    } else if (flag1) {
        return firstblock;
    }

    return NULL; // no fit found
}

/*
 *
 */
static bool footer_header_consis_check(block_t *block)
{
    word_t header = block->header;

    word_t* footer = (word_t*)((block->payload) + get_size(block) - dsize);

    dbg_printf("debug head %zu, footer %zu\n", header, *footer);
    return header == (*footer);
}

/*
 * <what does consistency_check do?>
 */
static bool consistency_check()
{
    block_t *block;

    for (block = heap_start; get_size(block) > 0;
                             block = find_next(block))
    {

        if (!footer_header_consis_check(block))
        {
            return false;
        }
    }
    return true; // no bug found
}

/*
 * <what does consecutive_check do?>
 */
static bool consecutive_check()
{
    block_t *block;
    bool freeflag = false;
    for (block = heap_start; get_size(block) > 0;
                             block = find_next(block))
    {

        if (!get_alloc(block))   // found free block
        {
            if (!freeflag) // no consecutive block
            {
                freeflag = true;
            }
            else {         // have consecutive block
dbg_printf("the block add is %p, the prev block add is %p",
                    block, find_prev(block));
                return false;
            }
        }
        else {
            freeflag = false;
        }
    }
    return true; // no consecutive free block found
}


/*
 * address_check is
 */
static bool address_check()
{
    block_t *block;

    for (block = heap_start; get_size(block) > 0;
                             block = find_next(block))
    {

        if (!get_alloc(block))
        {
            if (!next_add_check(block) || !prev_add_check(block)) {
dbg_printf("the problem block is %p, head is %p\n", block, get_head_pointer());
                return false;
            }
        }
    }
    return true; // no bug found
}



/*
 * freeblock_insert: insert the free block into the head of free linked list.
 */
static void freeblock_insert(block_t *block, block_t *freeblock_next)
{
    //if (root == NULL) {
    if (get_head_pointer() == NULL) { // case 1: free list is empty
        // root = block;
        write_head_pointer(block);
        write_tail_pointer(block);
        write_next_pointer(block, NULL);
        write_prev_pointer(block, NULL);
    }
    else {   // case 2: free list is not empty
        if (get_head_pointer() == block) {
            // 2.1 root is block itself
            dbg_printf("the head points to that block!\n");
            write_next_pointer(block, freeblock_next);
            write_prev_pointer(block, NULL);
            if (freeblock_next != NULL) {
                write_prev_pointer(freeblock_next, block);
            }

        } else {
            // 2.2 root is other block
            dbg_printf("the head points to other block!\n");
            block_t *next_free_pointer = get_head_pointer();
            write_prev_pointer(next_free_pointer, block);
            write_next_pointer(block, next_free_pointer);  // bug recode
            write_prev_pointer(block, NULL);

            // root = block;
            write_head_pointer(block);
        }
    }
}

/*
 * freeblock_remove
 */
static void freeblock_remove(block_t *block)
{
    block_t *block_next_predecessor = find_prev_free_block(block);
    block_t *block_next_successor = find_next_free_block(block);

dbg_printf("in freeblock_remove, block next pred is %p\n", block_next_predecessor);
dbg_printf("in freeblock_remove, block next succ is %p\n", block_next_successor);

    if (!block_next_predecessor && !block_next_successor) {

        // root = NULL;
        write_head_pointer(NULL);
        write_tail_pointer(NULL);
    }
    else if (!block_next_predecessor) { // head of the list
        // root = block_next_successor;
        write_head_pointer(block_next_successor);
        write_prev_pointer(block_next_successor, NULL);
dbg_printf("in freeblock_remove, head, the head is %p\n", get_head_pointer());
dbg_printf("in freeblock_remove, head, successor is %p\n", block_next_successor);
    }
    else if (!block_next_successor) { // end of the list
        write_tail_pointer(block_next_predecessor);
        write_next_pointer(block_next_predecessor, NULL);
dbg_printf("in freeblock_remove, end, the head is %p\n", get_head_pointer());
    }
    else { // in the middle
        write_next_pointer(block_next_predecessor, block_next_successor);
        write_prev_pointer(block_next_successor, block_next_predecessor);
dbg_printf("in freeblock_remove, middle, the head is %p\n", get_head_pointer());
    }
    write_next_pointer(block, NULL);
    write_prev_pointer(block, NULL);
}

/*
 * split_freeblock
 */
static void split_freeblock(block_t *block, block_t *block_next)
{
    block_t *next_free_pointer = find_next_free_block(block);
    block_t *prev_free_pointer = find_prev_free_block(block);
    // split the free block
    // if (root == block) {   // the first free block
    if (get_head_pointer() == block) {   // the first free block
        // root = block_next;
        write_head_pointer(block_next);

dbg_printf("in split_freeblock, first, the head add is %p\n", get_head_pointer());
dbg_printf("in split_freeblock, next_free_pointer add is %p\n", next_free_pointer);
dbg_printf("in split_freeblock, prev_free_pointer add is %p\n", prev_free_pointer);

        if (next_free_pointer) {
dbg_printf("in split_freeblock, block_next add is %p\n", block_next);
            write_next_pointer(block_next, next_free_pointer);
            write_prev_pointer(block_next, NULL);
            write_prev_pointer(next_free_pointer, block_next);
        } else {
            write_next_pointer(block_next, NULL);
            write_prev_pointer(block_next, NULL);

            write_tail_pointer(block_next);
        }
    }
    else if (!next_free_pointer) { //  the last free block

dbg_printf("in split_freeblock, last, the head add is %p\n", get_head_pointer());
        write_next_pointer(prev_free_pointer, block_next);
        write_prev_pointer(block_next, prev_free_pointer);
        write_next_pointer(block_next, NULL);

        write_tail_pointer(block_next);
    }
    else {     //  the middle free block

dbg_printf("in split_freeblock, middle, the head add is %p\n", get_head_pointer());
        write_next_pointer(prev_free_pointer, block_next);
        write_prev_pointer(block_next, prev_free_pointer);
        write_next_pointer(block_next, next_free_pointer);

        write_prev_pointer(next_free_pointer, block_next);  // bug record
    }
}


/*
 * freeblock_coalesce
 */
static block_t *freeblock_coalesce(block_t *block)
{

dbg_printf("in freeblock_coalesce, the block is %p\n", block);

        block_t *block_next = find_next(block);

        // get the prev
        //block_t *block_prev = find_prev(block);

        bool prev_alloc = get_prev_alloc(block);
        bool next_alloc = get_alloc(block_next);

        size_t size = get_size(block);
        block_t *freeblock_next = NULL;

        if (prev_alloc && next_alloc)              // Case 1  only middle free
        {
            freeblock_insert(block, freeblock_next);
dbg_printf("in freeblock_coalesce, 1, block next is %p\n", block_next);
            off_alloc_bit(block_next);
        }

        else if (prev_alloc && !next_alloc)        // Case 2  mid & next free
        {
            freeblock_next = find_next_free_block(block_next);
dbg_printf("in freeblock_coalesce, 2, next free block add is %p\n", freeblock_next);

            size += get_size(block_next);
            write_header(block, size, true, false);   // bug record
            write_footer(block, size, false);
dbg_printf("in freeblock_coalesce, 2, the block_next add is %p\n", block_next);

            freeblock_remove(block_next);
            freeblock_insert(block, freeblock_next);
        }

        else if (!prev_alloc && next_alloc)        // Case 3  mid & prev free
        {
            block_t *block_prev = find_prev(block);
dbg_printf("in freeblock_coalesce, 3, block prev is %p\n", block_prev);
            freeblock_next = find_next_free_block(block_prev);
dbg_printf("in freeblock_coalesce, 3, next free block add is %p\n", freeblock_next);

            size += get_size(block_prev);
            write_header(block_prev, size, true, false);
            write_footer(block_prev, size, false);

            off_alloc_bit(block_next);

dbg_printf("in freeblock_coalesce, 3, the block add is %p\n", block_next);

            block = block_prev;
            freeblock_remove(block_prev);
            freeblock_insert(block, freeblock_next);
        }

        else                                        // Case 4  both free
        {
            block_t *block_prev = find_prev(block);

            freeblock_next = find_next_free_block(block_prev);
dbg_printf("in freeblock_coalesce, 4, next free block add is %p\n", freeblock_next);

            size += get_size(block_next) + get_size(block_prev);

            write_header(block_prev, size, true, false);
            write_footer(block_prev, size, false);

dbg_printf("in freeblock_coalesce, 4, the block_next add is %p\n", block_next);
            block = block_prev;
            freeblock_remove(block_prev);
dbg_printf("in freeblock_coalesce, 4, the block_prev add is %p\n", block_prev);
            freeblock_remove(block_next);
dbg_printf("in freeblock_coalesce, 4, the block add is %p\n", block);
            freeblock_insert(block, freeblock_next);
        }

    return block;
}


/*
 * <what does your heap checker do?>
 * Please keep modularity in mind when you're writing the heap checker!
 */
bool mm_checkheap(int line)
{
    //  printf("Successful until line %d \n", line);
    // Check heap start pointer
    if (heap_start == NULL) {
      debug_message(line);
      dbg_ensures(heap_start != NULL);
    }

    // Check epilogue and prologue blocks
    if (!epilogue_check(heap_start)) {
      debug_message(line);
      dbg_ensures(epilogue_check(heap_start));
    }

    //Check each block’s header and footer
    // if (!consistency_check()) {
    //   debug_message(line);
    //   dbg_ensures(consistency_check());
    // }

    // Check coalescing: no two consecutive free blocks in the heap
    if (!consecutive_check()) {
      debug_message(line);
      dbg_ensures(consecutive_check());
    }

    // Check coalescing: no two consecutive free blocks in the heap
    if (!address_check()) {
      debug_message(line);
      dbg_ensures(address_check());
    }

    return true;

}


/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details within your header comments for the functions above!     *
 *                                                                           *
 *                                                                           *
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a de ad be ef 0a 0a 0a               *
 *                                                                           *
 *****************************************************************************
 */

 static bool next_add_check(block_t *block)
 {
     word_t* next_add = (word_t*)((block->payload));
     if (*next_add == 0) {
       return true;
     }
     else {
       uint32_t* checker = (uint32_t*)((block->payload) + sizeof(uint32_t));
       return (*checker) == 0x8;
     }
 }

 static bool prev_add_check(block_t *block)
 {
     word_t* prev_add = (word_t*)((block->payload) + wsize);
     if (*prev_add == 0) {
       return true;
     }
     else {
       uint32_t* checker = (uint32_t*)((block->payload) + wsize + sizeof(uint32_t));
       return (*checker) == 0x8;
     }
 }

/*
 *
 */

static void debug_message(int line)
{
    dbg_printf("mm_checkheap with line: %d encountered problem!\n", line);
}

/*
 * epilogue_check
 */
static bool epilogue_check(block_t *phead)
{
    return get_alloc(phead - 1);
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}

/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    if (size <= 40) {
        return 32;
    }
    else {
        dbg_printf("before, the size is %zu\n", size);
        size_t result = (n * ((size + (n-1)) / n));
        dbg_printf("after, the size is %zu\n", result);
        return result;
    }
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool prev_alloc, bool alloc)
{
    word_t set_alloc = alloc ? (size | alloc_mask) : size;

    return prev_alloc ? (set_alloc | prev_alloc_mask) : set_alloc;
}

/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - wsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * extract_prev_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_prev_alloc(word_t word)
{
    return (bool)(word & prev_alloc_mask);
}

static void set_alloc_bit(block_t *block)
{
    // word_t header = *(word_t)block;
dbg_printf("the header before off is %p\n", block);
    (*(word_t *)block) |= prev_alloc_mask;
}

static void off_alloc_bit(block_t *block)
{
    //word_t header = (word_t)block;
dbg_printf("the header before off is %p\n", block);
    (*(word_t *)block) &= (~(word_t)prev_alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * get_prev_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_prev_alloc(block_t *block)
{
    return extract_prev_alloc(block->header);
}


/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size, bool prev_alloc, bool alloc)
{
    block->header = pack(size, prev_alloc, alloc);
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
dbg_printf("the cur block is %p, size is %lx\n", block, size);
    word_t *footerp = (word_t *)((block->payload) + get_size(block) - dsize);
    *footerp = pack(size, get_prev_alloc(block), alloc);
}


/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    dbg_requires(block != NULL);
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));

    dbg_ensures(block_next != NULL);
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload);
}


// customized wrapper functions
/*
 *
 */
static void debug_break(block_t *block)
{
   dbg_printf("the block add is %p\n", block);
}



/*
 *
 */
static block_t *get_pointer(char *pointer)
{
    if (((word_t *)pointer)[0] == 0) {
        return NULL;
    } else{
        return (block_t *)(((word_t *)pointer)[0]);
    }
}

/*
 * find_prev_free_block, given the current pointer, returns the prev free
 * block pointer, null if cannot find
 */
static block_t *find_prev_free_block(block_t *block)
{
    char *pointer = (char *)block + dsize;

    return get_pointer(pointer);
}

/*
 * find_next_free_block, given the current pointer, returns the next free
 * block pointer, null if cannot find
 */
static block_t *find_next_free_block(block_t *block)
{
    char *pointer = (char *)block + wsize;

    return get_pointer(pointer);
}

/*
 * write_next_pointer
 */
static void write_next_pointer(block_t *block, block_t *next_block)
{

    word_t *next_pointer = (word_t *)(block->payload);
    next_pointer[0] = (word_t)next_block;
}

/*
 * write_prev_pointer
 */
static void write_prev_pointer(block_t *block, block_t *prev_block)
{

    word_t *prev_pointer = (word_t *)(block->payload) + 1;
    prev_pointer[0] = (word_t)prev_block;
}

static void write_head_pointer(block_t *pointer)
{
    ((word_t *)root)[0] = (word_t)pointer;
}

static void write_tail_pointer(block_t *pointer)
{
    ((word_t *)root)[1] = (word_t)pointer;
}

static block_t *get_head_pointer()
{
    return get_pointer(root);
}

static block_t *get_tail_pointer()
{
    char *pointer = (char *)root + wsize;
    return get_pointer(pointer);
}
