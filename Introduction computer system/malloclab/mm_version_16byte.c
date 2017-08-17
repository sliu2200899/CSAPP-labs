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
static const size_t small_block_size = dsize; // 16 bytes of block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t prev_alloc_mask = 0x2;   // to remove the footer
static const word_t small_block_mask = 0x4;  //  indicate it is a small block
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
static char *root[8];  // head of the freed block

bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(char *size_class_pointer, block_t *block, size_t asize);
static block_t *find_fit(char *size_class_pointer, size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool prev_small, bool prev_alloc, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool prev_small_block,
                      bool prev_alloc, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

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
static void write_head_pointer(char *size_class_pointer, block_t *pointer);
static void write_tail_pointer(char *size_class_pointer, block_t *pointer);
static block_t *get_head_pointer(char *size_class_pointer);
static block_t *get_tail_pointer(char *size_class_pointer);
static bool get_prev_alloc(block_t *block);   // ????? add size_class_pointer,
static block_t *find_next_free_block(block_t *block);
static block_t *find_prev_free_block(block_t *block);

static void freeblock_insert(char *size_class_pointer, block_t *block, block_t *freeblock_next);
static void freeblock_remove(char *size_class_pointer, block_t *block,
             block_t *successor, block_t *predece);
static block_t *freeblock_coalesce(block_t *block);
static void split_freeblock(char *size_class_pointer,
        char *leftspace_pointer, block_t *block, block_t *block_next);

static bool next_add_check(block_t *block);
static bool prev_add_check(block_t *block);
static bool address_check();
static void checker(block_t *block);

static void set_alloc_bit(block_t *block);
static void off_alloc_bit(block_t *block);

static char *find_proper_freelist(size_t size);
static block_t *find_proper_block(char *size_class_pointer, size_t asize);
static void add_small_block_list(block_t *block_next);
static void remove_small_block_list(block_t *block);
static bool get_prev_small_block(block_t *block);
static block_t *find_small_prev(block_t *block);
static void set_smallblock_bit(block_t *block);
static void off_smallblock_bit(block_t *block);
static void debug_break1();
static void debug_break2();
/*
 *  mm_init is used for Initialize the memory system
 */
bool mm_init(void)
{

    int i = 0;

    // Create head and tail node for the freed block list
    word_t *start = (word_t *)(mem_sbrk(2*8*wsize));

    if (start == (void *)-1)
    {
        return false;
    }

    for (i = 0; i < 8; i++) {
        root[i] = (char *)start + i * 2 * 8;
        write_head_pointer(root[i], NULL);
        write_tail_pointer(root[i], NULL);
    }

    // Create the initial empty heap
    start = (word_t *)(mem_sbrk(2*wsize));

    if (start == (void *)-1)
    {
        return false;
    }

    start[0] = pack(0, false, true, true); // Prologue footer
    start[1] = pack(0, false, true, true); // Epilogue header
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
    char *size_class_freelist = NULL;
    size_t latersize = 0;

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

    // find the proper free list
    size_class_freelist = find_proper_freelist(asize);

    // Search the free list for first available fit
    block = find_fit(size_class_freelist, asize);
dbg_printf("in malloc, the block after find_fit is %p\n", block);

    if (block == NULL)
    {
        extendsize = asize;   // implement it temparily

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
    latersize = get_size(block);
    size_class_freelist = find_proper_freelist(latersize);
    place(size_class_freelist, block, asize);
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

dbg_printf("in free, the block add before write header is %p\n", block);
dbg_printf("in free, the size before write header is %zu\n", size);

    if (size == small_block_size) {
        write_header(block, size, get_prev_small_block(block),
                    get_prev_alloc(block), false);
    }

    else {
      write_header(block, size, get_prev_small_block(block),
                    get_prev_alloc(block), false);
      write_footer(block, size, false);
    }

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

    if (size == small_block_size) {
        write_header(block, size, get_prev_small_block(block),
                    prev_alloc_flag, false);
        // Create new epilogue header
        block_t *block_next = find_next(block);
        write_header(block_next, 0, true, false, true);
dbg_printf("in extend_heap, small block, the block add is %p\n", block);
dbg_printf("in extend_heap, small block, the block next is %p\n", block_next);
    } else {
        write_header(block, size, get_prev_small_block(block),
                    prev_alloc_flag, false);
        write_footer(block, size, false);
        // Create new epilogue header
        block_t *block_next = find_next(block);
        write_header(block_next, 0, false, false, true);
dbg_printf("in extend_heap, large block, the block add is %p\n", block);
dbg_printf("in extend_heap, large block, the block next is %p\n", block_next);
    }

    return freeblock_coalesce(block);
}

/*
 * place is used for allocting memory for payload
 */
 static void place(char *size_class_freelist, block_t *block, size_t asize)
 {
     size_t csize = get_size(block);
     char *leftspace_freelist = NULL;
     block_t *block_predecessor = NULL;
     block_t *block_successor = NULL;

    //  block_predecessor = find_prev_free_block(block);
    //  block_successor = find_next_free_block(block);

     if (csize == small_block_size) {
          // if the allocated block is 16 bytes
dbg_printf("only 16 bytes available\n");
          write_header(block, csize, get_prev_small_block(block), true, true);

          block_t *next_block = find_next(block);
          set_alloc_bit(next_block);
          set_smallblock_bit(next_block);

          // remove the free node
          remove_small_block_list(block);
     }

     else if (csize - asize == small_block_size){
          // if the block size is 16 bytes
          block_predecessor = find_prev_free_block(block);
          block_successor = find_next_free_block(block);

          block_t *block_next;
          write_header(block, asize, get_prev_small_block(block), true, true);

dbg_printf("in place, 16 bytes left, the block is %20p\n", block);

          block_next = find_next(block);
          if (asize == small_block_size) {
            write_header(block_next, csize-asize, true, true, false); // bug
          } else {
            write_header(block_next, csize-asize, false, true, false);
          }

dbg_printf("in place, 16 byte left, the block next is %20p\n", block_next);

          freeblock_remove(size_class_freelist, block, block_successor,
                      block_predecessor);
          add_small_block_list(block_next);
dbg_printf("in place, 16 byte left, after add, block next add is %20p\n", block_next);
          block_t *block_next_next = find_next(block_next);
          set_smallblock_bit(block_next_next);
     }

     else if ((csize - asize) >= min_block_size)
     {
         block_predecessor = find_prev_free_block(block);
         block_successor = find_next_free_block(block);

         block_t *block_next;
         write_header(block, asize, get_prev_small_block(block), true, true);
         //write_footer(block, asize, true);
 dbg_printf("in place, normal, the block add is %20p\n", block);

         block_next = find_next(block);
         if (asize == small_block_size) {
            write_header(block_next, csize-asize, true, true, false); // bug
         } else {
            write_header(block_next, csize-asize, false, true, false);
         }

         write_footer(block_next, csize-asize, false);
 dbg_printf("in place, normal, the block next add is %20p\n", block_next);

         size_t left_space = csize - asize;
         leftspace_freelist = find_proper_freelist(left_space);
         freeblock_remove(size_class_freelist, block, block_successor,
                                block_predecessor);
         freeblock_insert(leftspace_freelist, block_next, NULL);
dbg_printf("in place, normal, block next add is %20p\n", block_next);

     }

     else {
         block_predecessor = find_prev_free_block(block);
         block_successor = find_next_free_block(block);

dbg_printf("in place, other, the block add is %20p\n", block);
         write_header(block, csize, get_prev_small_block(block),
                          true, true);
         // write_footer(block, csize, true);

         block_t *next_block = find_next(block);
         set_alloc_bit(next_block);

        //  if (asize == small_block_size) {
        //     set_smallblock_bit(next_block);
        //  }

         // remove the free node
         freeblock_remove(size_class_freelist, block, block_successor,
                                block_predecessor);
     }
}

/*
 * <what does find_fit do?>
 */
static block_t *find_fit(char *size_class_pointer, size_t asize)
{
    block_t *block = NULL;
    int i = 0;
    bool flag = false;

    if (asize == small_block_size) {
        // when it is the 16 bytes block list
        for (block = get_head_pointer(size_class_pointer); block != NULL
                 && get_size(block) > 0; block = find_next_free_block(block))
        {
            return block;
        }

        if (block == NULL) {
            for (i = 1; i < 8; i++) {
                block = find_proper_block(root[i], asize);
dbg_printf("in find_fit, not 16, after find proper block, block is %p\n", block);
                if (block == NULL) {
                    continue;
                } else {
                    return block;
                }
            }
        }

    }

    else {
        for (i = 1; i < 8; i++) {

            if (!flag) {
                if (root[i] != size_class_pointer) {
                    continue;
                } else {
                    flag = true;
                    block = find_proper_block(root[i], asize);
dbg_printf("in find_fit, other block, block is %p\n", block);
                    if (block == NULL) {
                        continue;
                    } else {
                        return block;
                    }
                }
            } else {
                block = find_proper_block(root[i], asize);
dbg_printf("in find_fit, other block, block is %p\n", block);
                if (block == NULL) {
                    continue;
                } else {
                    return block;
                }
            }
        }
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
dbg_printf("the problem block is %p, head is %p\n", block, get_head_pointer(root[1]));
                return false;
            }
        }
    }
    return true; // no bug found
      // return true;
}



/*
 * freeblock_insert: insert the free block into the head of free linked list.
 */
static void freeblock_insert(char *size_class_freelist,
                      block_t *block, block_t *freeblock_next)
{
    //if (root == NULL) {
    if (get_head_pointer(size_class_freelist) == NULL) { // case 1: free list is empty
        // root = block;
        dbg_printf("free list is empty!\n");
        write_head_pointer(size_class_freelist, block);
        write_tail_pointer(size_class_freelist, block);
        write_next_pointer(block, NULL);
        write_prev_pointer(block, NULL);
    }
    else {   // case 2: free list is not empty
        if (get_head_pointer(size_class_freelist) == block) {
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
            block_t *next_free_pointer = get_head_pointer(size_class_freelist);
            write_prev_pointer(next_free_pointer, block);
            write_next_pointer(block, next_free_pointer);  // bug recode
            write_prev_pointer(block, NULL);

            // root = block;
            write_head_pointer(size_class_freelist, block);
        }
    }
}

/*
 * freeblock_remove
 */
static void freeblock_remove(char *size_class_freelist, block_t *block,
                block_t *successor, block_t *predecessor)
{
    block_t *block_next_predecessor = predecessor;
    block_t *block_next_successor = successor;

dbg_printf("in freeblock_remove, block next pred is %p\n", block_next_predecessor);
dbg_printf("in freeblock_remove, block next succ is %p\n", block_next_successor);

    if (!block_next_predecessor && !block_next_successor) {

        // root = NULL;
        write_head_pointer(size_class_freelist, NULL);
        write_tail_pointer(size_class_freelist, NULL);
    }
    else if (!block_next_predecessor) { // head of the list
        // root = block_next_successor;
        write_head_pointer(size_class_freelist, block_next_successor);
        write_prev_pointer(block_next_successor, NULL);
dbg_printf("in freeblock_remove, head, the head is %p\n", get_head_pointer(size_class_freelist));
dbg_printf("in freeblock_remove, head, successor is %p\n", block_next_successor);
    }
    else if (!block_next_successor) { // end of the list
        write_tail_pointer(size_class_freelist, block_next_predecessor);
        write_next_pointer(block_next_predecessor, NULL);
dbg_printf("in freeblock_remove, end, the head is %p\n", get_head_pointer(size_class_freelist));
    }
    else { // in the middle
        write_next_pointer(block_next_predecessor, block_next_successor);
        write_prev_pointer(block_next_successor, block_next_predecessor);
dbg_printf("in freeblock_remove, middle, the head is %p\n", get_head_pointer(size_class_freelist));
    }

    if (get_size(block) == small_block_size) {   // bug record
        write_next_pointer(block, NULL);
    } else {
        write_next_pointer(block, NULL);
        write_prev_pointer(block, NULL);
    }

}

/*
 *
 */
static void add_small_block_list(block_t *block)
{
    //char *size_class_pointer = find_proper_freelist(16);

    if (root[0] == NULL) {
        write_head_pointer(root[0], block);
        write_next_pointer(block, NULL);
    } else {
        block_t *header = get_head_pointer(root[0]);
        write_head_pointer(root[0], block);
        write_next_pointer(block, header);
    }
}

static void remove_small_block_list(block_t *block)
{
    //char *size_class_pointer = find_proper_freelist(16);
    block_t *parent = NULL;
    block_t *cur = NULL;

    if (get_head_pointer(root[0]) == block) {
        cur = find_next_free_block(block);
        if (cur == NULL) {
            write_head_pointer(root[0], NULL);
            write_tail_pointer(root[0], NULL);
        } else {
            write_head_pointer(root[0], cur);
        }

    } else {
        cur = get_head_pointer(root[0]);
        while (cur != NULL) {
            if (cur == block) {
                if (get_tail_pointer(root[0]) == block) {
                    write_tail_pointer(root[0], parent);
                } else {
                    write_next_pointer(parent, find_next_free_block(cur));
                }
            }
            parent = cur;
            cur = find_next_free_block(cur);
        }
    }
}


/*
 * freeblock_coalesce
 */
static block_t *freeblock_coalesce(block_t *block)
{

dbg_printf("in freeblock_coalesce, the block is %p\n", block);

        block_t *block_next = find_next(block);

        bool prev_alloc = get_prev_alloc(block);
        bool next_alloc = get_alloc(block_next);
        bool prev_small_block = get_prev_small_block(block);

        size_t size = get_size(block);
        block_t *freeblock_next = NULL;
        char *size_class_pointer = NULL;
        char *size_class_newpointer = NULL;
        size_t size_next = 0;
        size_t size_prev = 0;

        block_t *block_predecessor = NULL;
        block_t *block_successor = NULL;

        if (prev_alloc && next_alloc)              // Case 1  only middle free
        {
            size_class_pointer = find_proper_freelist(size);
            if (size == small_block_size) {
                add_small_block_list(block);
                set_smallblock_bit(block_next);   //
            }

            else {
                freeblock_insert(size_class_pointer, block, freeblock_next);
            }

dbg_printf("in freeblock_coalesce, 1, block next is %p\n", block_next);
            off_alloc_bit(block_next);
        }

        else if (prev_alloc && !next_alloc)        // Case 2  mid & next free
        {
            size_next = get_size(block_next);
            freeblock_next = find_next_free_block(block_next);
dbg_printf("in freeblock_coalesce, 2, next free block add is %p\n", freeblock_next);

            if (size_next == small_block_size) {
              remove_small_block_list(block_next);
              block_t *block_next_next = find_next(block_next);
              off_smallblock_bit(block_next_next);
            }
            else {
              block_predecessor = find_prev_free_block(block_next);
              size_class_pointer = find_proper_freelist(size_next);
              freeblock_remove(size_class_pointer, block_next, freeblock_next,
                            block_predecessor);
            }

            size += size_next;
            write_header(block, size, get_prev_small_block(block),
                                true, false);   // bug record
            write_footer(block, size, false);
dbg_printf("in freeblock_coalesce, 2, the block_next add is %p\n", block_next);

            size_class_newpointer = find_proper_freelist(size);
            freeblock_insert(size_class_newpointer, block, freeblock_next);
        }

        else if (!prev_alloc && next_alloc)        // Case 3  mid & prev free
        {
            if (size == small_block_size) {
                off_smallblock_bit(block_next);
            }
            block_t *block_prev = NULL;
            if (prev_small_block) {
                block_prev = find_small_prev(block);
            } else {
                block_prev = find_prev(block);
            }

dbg_printf("in freeblock_coalesce, 3, block prev is %p\n", block_prev);
            freeblock_next = find_next_free_block(block_prev);
dbg_printf("in freeblock_coalesce, 3, next free block add is %p\n", freeblock_next);
            size_prev = get_size(block_prev);

            if (size_prev == small_block_size) {
              remove_small_block_list(block_prev);
            }
            else {
              block_predecessor = find_prev_free_block(block_prev);
              size_class_pointer = find_proper_freelist(size_prev);
              freeblock_remove(size_class_pointer, block_prev, freeblock_next,
                          block_predecessor);
            }

            size += size_prev;
            write_header(block_prev, size, get_prev_small_block(block_prev),
                                  true, false);
            write_footer(block_prev, size, false);

            off_alloc_bit(block_next);

dbg_printf("in freeblock_coalesce, 3, the block add is %p\n", block_next);

            block = block_prev;

            size_class_newpointer = find_proper_freelist(size);
dbg_printf("in freeblock_coalesce, 3*, the block add is %zu\n", size);
dbg_printf("in freeblock_coalesce, 3*, the block add is %p\n", size_class_newpointer);
            freeblock_insert(size_class_newpointer, block, freeblock_next);

        }

        else                                        // Case 4  both free
        {
            block_t *block_prev = NULL;
            if (prev_small_block) {
                block_prev = find_small_prev(block);
dbg_printf("in freeblock_coalesce, 4, prev is small block!\n");
            } else {
                block_prev = find_prev(block);
dbg_printf("in freeblock_coalesce, 4, prev is not small!\n");
            }

            freeblock_next = find_next_free_block(block_prev);
dbg_printf("in freeblock_coalesce, 4, next free block add is %p\n", freeblock_next);

            size_next = get_size(block_next);
dbg_printf("in freeblock_coalesce, 4, size_next is %zu!\n", size_next);
            size_prev = get_size(block_prev);
dbg_printf("in freeblock_coalesce, 4, size_prev is %zu!\n", size_prev);

            if (size_prev == small_block_size) {
                remove_small_block_list(block_prev);
            } else {
                block_successor = freeblock_next;
                block_predecessor = find_prev_free_block(block_prev);
                size_class_pointer = find_proper_freelist(size_prev);
                freeblock_remove(size_class_pointer, block_prev,
                      block_successor, block_predecessor);
            }

            if (size_next == small_block_size) {
                remove_small_block_list(block_next);
                block_t *block_next_next = find_next(block_next);
                off_smallblock_bit(block_next_next);
            } else {
                block_successor = find_next_free_block(block_next);
                block_predecessor = find_prev_free_block(block_next);
                size_class_pointer = find_proper_freelist(size_next);
                freeblock_remove(size_class_pointer, block_next,
                      block_successor, block_predecessor);
            }

            size += (size_next + size_prev);

            write_header(block_prev, size, get_prev_small_block(block_prev),
                              true, false);
            write_footer(block_prev, size, false);

dbg_printf("in freeblock_coalesce, 4, the block_next add is %p\n", block_next);
            block = block_prev;

            size_class_newpointer = find_proper_freelist(size);
            freeblock_insert(size_class_newpointer, block, freeblock_next);
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

    // Check coalescing: no two consecutive free blocks in the heap
    if (!consecutive_check()) {
      debug_message(line);
      dbg_ensures(consecutive_check());
    }

    block_t *cur = get_tail_pointer(root[0]);
    if ((word_t)cur != 0) {
      dbg_printf("the cur block is %p\n", cur);
      dbg_ensures((word_t)cur == 0);
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
    if (size <= 24) {
        return 16;
    }
    else if (size <= 40) {
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
static word_t pack(size_t size, bool prev_small, bool prev_alloc, bool alloc)
{
    word_t set_alloc = alloc ? (size | alloc_mask) : size;

    word_t set_prev_alloc = prev_alloc ? (set_alloc | prev_alloc_mask) : set_alloc;

    return prev_small ? (set_prev_alloc | small_block_mask) : set_prev_alloc;
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

static void set_smallblock_bit(block_t *block)
{
    // word_t header = *(word_t)block;
dbg_printf("the header before off is %p\n", block);
    (*(word_t *)block) |= small_block_mask;
}

static void off_smallblock_bit(block_t *block)
{
    //word_t header = (word_t)block;
dbg_printf("the header before off is %p\n", block);
    (*(word_t *)block) &= (~(word_t)small_block_mask);
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

static bool get_small(word_t word)
{
    return (bool)(word & small_block_mask);
}

static bool get_prev_small_block(block_t *block)
{
    return get_small(block->header);
}


/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header.
 */
static void write_header(block_t *block, size_t size,
          bool prev_small_block, bool prev_alloc, bool alloc)
{
    block->header = pack(size, prev_small_block, prev_alloc, alloc);
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
    *footerp = pack(size, get_prev_small_block(block), get_prev_alloc(block), alloc);
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

static block_t *find_small_prev(block_t *block)
{
    return (block_t *)((char *)block - small_block_size);
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
static char *find_proper_freelist(size_t size)
 {
     if (size <= 16) {
         return root[0];
     } else if (size <= 64) {
         return root[1];
     } else if (size <= 128) {
         return root[2];
     } else if (size <= 512) {
         return root[3];
     } else if (size <= 1024) {
         return root[4];
     } else if (size <= 4096) {
         return root[5];
     } else if (size <= 16384) {
         return root[6];
     } else {
         return root[7];
     }
 }


static block_t *find_proper_block(char *size_class_pointer, size_t asize)
{
     block_t *block;
     block_t *firstblock;
     block_t *secondblock;
     bool flag1 = false;
     bool flag2 = false;

     // other circumstance
     for (block = get_tail_pointer(size_class_pointer); block != NULL
              && get_size(block) > 0; block = find_prev_free_block(block))
     {

dbg_printf("in find_fit, the head is %p\n", get_head_pointer(size_class_pointer));
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
     return NULL;
}

static void debug_break1()
{
   dbg_printf("the program stops here in malloc 16!\n");
}

static void debug_break2()
{
    dbg_printf("the program stops here in free 16!\n");
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

static void write_head_pointer(char *size_class_freelist, block_t *pointer)
{
    ((word_t *)size_class_freelist)[0] = (word_t)pointer;
}

static void write_tail_pointer(char *size_class_freelist, block_t *pointer)
{
    ((word_t *)size_class_freelist)[1] = (word_t)pointer;
}

static block_t *get_head_pointer(char *size_class_freelist)
{
    return get_pointer(size_class_freelist);
}

static block_t *get_tail_pointer(char *size_class_freelist)
{
    char *pointer = size_class_freelist + wsize;
    return get_pointer(pointer);
}
