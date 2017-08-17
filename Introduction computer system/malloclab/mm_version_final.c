/*
 ******************************************************************************
 *                               mm.c                                         *
 *           64-bit struct-based implicit free list memory allocator          *
 *                  15-213: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *              this file create one simple memory allocator. :)              *
 *              Name: Shu Liu   AndrewID: Shul2                               *
 *  our memory system is constructured as a segregated list which has a single*
 *  free list for 16 bytes free list block and doubly linked list for other   *
 *  free list. In addition, we remove the footer in each allocated block,     *
 *  enhancing the utilization of memory.                                      *
 *                                                                            *
 *                                                                            *
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

#define block_size_32      32
#define block_size_48      48
#define block_size_64      64
#define block_size_96      96
#define block_size_128     128
#define block_size_256     256
#define block_size_512     512
#define block_size_1024    1024
#define block_size_2048    2048
#define block_size_4096    4096


/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*wsize;          // double word size (bytes)
static const size_t min_block_size = 2*dsize; // Minimum block size
static const size_t small_block_size = dsize; // 16 bytes of block size
static const size_t size_class_number = 12; // the number of the size class
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
static char *root[size_class_number];  // head of the freed block

bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void normal_block_place(block_t *block, size_t asize,
              size_t csize, char *size_class_freelist);
static void place(char *size_class_pointer, block_t *block, size_t asize);
static block_t *find_fit_small_block(char *size_class_pointer, size_t asize);
static block_t *find_fit_normal_block(char *size_class_pointer, size_t asize);
static block_t *find_fit(char *size_class_pointer, size_t asize);
static void freeblock_insert(char *size_class_pointer,
                      block_t *block, block_t *freeblock_next);
static void freeblock_remove(char *size_class_pointer, block_t *block,
                      block_t *successor, block_t *predece);
static void only_middle_coalesce(block_t *block, block_t *block_next,
                        size_t size, bool prev_small_block);
static void mid_next_coalesce(block_t *block, block_t *block_next,
                        size_t size, bool prev_small_block);
static void mid_next_prev_coalesce(block_t *block, block_t *block_next,
                        size_t size, bool prev_small_block);
static block_t *freeblock_coalesce(block_t *block, block_t *block_next,
                        size_t size);
static void remove_small_block_list(block_t *block);


/*
 * costomize wrapper functions
 */
static void add_small_block_list(block_t *block_next);
static bool small_block_tail_check();
static bool consistency_check();
static bool consecutive_check();
static bool address_check();
static block_t *find_proper_block(char *size_class_pointer, size_t asize);
static bool next_add_check(block_t *block);
static bool prev_add_check(block_t *block);
static bool prologue_check(block_t *phead);
static bool epilogue_check(block_t *phead);
static void debug_message(int line);
static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool prev_small, bool prev_alloc, bool alloc);
static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);
static bool extract_alloc(word_t header);
static bool extract_prev_alloc(word_t word);
static void set_alloc_bit(block_t *block);
static void off_alloc_bit(block_t *block);
static void set_smallblock_bit(block_t *block);
static void off_smallblock_bit(block_t *block);
static bool get_alloc(block_t *block);
static bool get_prev_alloc(block_t *block);
static bool get_small(word_t word);
static bool get_prev_small_block(block_t *block);
static void write_header(block_t *block, size_t size, bool prev_small_block,
                      bool prev_alloc, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);
static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);
static block_t *find_small_prev(block_t *block);
static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);
static char *find_proper_freelist(size_t size);
static block_t *get_pointer(char *pointer);
static block_t *find_prev_free_block(block_t *block);
static block_t *find_next_free_block(block_t *block);
static void write_prev_pointer(block_t *block, block_t *prev_block);
static void write_next_pointer(block_t *block, block_t *next_block);
static void write_head_pointer(char *size_class_pointer, block_t *pointer);
static void write_tail_pointer(char *size_class_pointer, block_t *pointer);
static block_t *get_head_pointer(char *size_class_pointer);
static block_t *get_tail_pointer(char *size_class_pointer);
static bool footer_header_consis_check(block_t *block);
static void insert_block(block_t *block, size_t size, block_t *freeblock_next);
static void small_block_place(block_t *block, size_t csize);
static void insert_empty_list(char *size_class_freelist, block_t *block);
static void insert_block_itself(block_t *block, block_t * freeblock_next);
static void normal_insert_block(char *size_class_freelist, block_t *block);
static void empty_block_update(char *size_class_freelist);
static void head_block_update(char *size_class_freelist,
                  block_t *block_next_successor);
static void end_block_update(char *ssize_class_freelist,
                  block_t *block_next_predecessor);
static void middle_block_update(block_t *block_next_predecessor,
                  block_t *block_next_successor);
static void next_pointer_update(block_t *block);
static void update_next_header(block_t *block_next, size_t asize, size_t csize);


/*
 *  mm_init is used for Initialize the memory system, including allocating
 *  memory for each size class pointer and extend for a certain size memory
 */
bool mm_init(void)
{

    size_t i = 0;

    // Create head and tail node for the freed block list
    word_t *start = (word_t *)(mem_sbrk(2 * size_class_number * wsize));

    if (start == (void *)-1)
    {
        return false;
    }

    for (i = 0; i < size_class_number; i++) {
        root[i] = (char *)start + i * 2 * wsize;
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
 * malloc is used for allocting a bunch of memory, including finding the proper
 * free block list and allocating the memory using place function
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
    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + dsize, dsize);

    // find the proper free list
    size_class_freelist = find_proper_freelist(asize);

    // Search the free list for first available fit
    block = find_fit(size_class_freelist, asize);

    if (block == NULL)
    {
        extendsize = asize;   // implement it temparily

        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }
    }
    dbg_requires(mm_checkheap(__LINE__));

    latersize = get_size(block);
    size_class_freelist = find_proper_freelist(latersize);
    place(size_class_freelist, block, asize);
    bp = header_to_payload(block);

    return bp;
}

/*
 * free is used for releasing a bunch of memory, including update header infor
 * and also start coalesce neighboring free memory
 */
void free(void *bp)
{
    if (bp == NULL)
    {
        return;
    }
    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    if (size == small_block_size) {
        write_header(block, size, get_prev_small_block(block),
                    get_prev_alloc(block), false);
    }
    else {
      write_header(block, size, get_prev_small_block(block),
                    get_prev_alloc(block), false);
      write_footer(block, size, false);
    }

    block_t *next_block = find_next(block);
    off_alloc_bit(next_block);

    freeblock_coalesce(block, next_block, size);
}

/*
 *  realloc is used for reallocing the memory system, which include allocating
 *  new memory and copy old data to new place
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

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    block_t *block_next = NULL;

    bool prev_alloc_flag = get_prev_alloc(block);

    if (size == small_block_size) {
        write_header(block, size, get_prev_small_block(block),
                    prev_alloc_flag, false);

        // Create new epilogue header
        block_next = find_next(block);
        write_header(block_next, 0, true, false, true);

    } else {
        write_header(block, size, get_prev_small_block(block),
                    prev_alloc_flag, false);
        write_footer(block, size, false);

        // Create new epilogue header
        block_next = find_next(block);
        write_header(block_next, 0, false, false, true);
    }

    return freeblock_coalesce(block, block_next, size);
}

/*
 * normal_block_place is used for place normal block
 */
static void normal_block_place(block_t *block, size_t asize,
              size_t csize, char *size_class_freelist)
{
    block_t *block_predecessor = NULL;
    block_t *block_successor = NULL;
    char *leftspace_freelist = NULL;

    block_predecessor = find_prev_free_block(block);
    block_successor = find_next_free_block(block);

    if (csize - asize == small_block_size){
         // if the block size is 16 bytes
         block_t *block_next;
         write_header(block, asize, get_prev_small_block(block), true, true);

         block_next = find_next(block);
         update_next_header(block_next, asize, csize);

         freeblock_remove(size_class_freelist, block, block_successor,
                     block_predecessor);
         add_small_block_list(block_next);
         block_t *block_next_next = find_next(block_next);
         set_smallblock_bit(block_next_next);
    }

    else if ((csize - asize) >= min_block_size)
    {

        block_t *block_next;
        write_header(block, asize, get_prev_small_block(block), true, true);

        block_next = find_next(block);
        update_next_header(block_next, asize, csize);

        write_footer(block_next, csize-asize, false);

        size_t left_space = csize - asize;
        leftspace_freelist = find_proper_freelist(left_space);
        freeblock_remove(size_class_freelist, block, block_successor,
                               block_predecessor);
        freeblock_insert(leftspace_freelist, block_next, NULL);

    }
    else {

        write_header(block, csize, get_prev_small_block(block),
                         true, true);
        block_t *block_next = find_next(block);
        set_alloc_bit(block_next);

        // remove the free node
        freeblock_remove(size_class_freelist, block, block_successor,
                               block_predecessor);
    }
}

/*
 * place is used for allocting memory for payload in general
 */
 static void place(char *size_class_freelist, block_t *block, size_t asize)
 {
     size_t csize = get_size(block);

     if (csize == small_block_size) {
          // block size equals to 16 bytes
          small_block_place(block, csize);
     }
     else {
          // other situation
          normal_block_place(block, asize, csize, size_class_freelist);
     }
}

/*
 * find_fit_small_block : find small fit block
 */
static block_t *find_fit_small_block(char *size_class_pointer, size_t asize)
{
    block_t *block = NULL;
    size_t i = 0;

    for (block = get_head_pointer(size_class_pointer); block != NULL
             && get_size(block) > 0; block = find_next_free_block(block))
    {
        return block;
    }

    if (block == NULL) {
        for (i = 1; i < size_class_number; i++) {
            block = find_proper_block(root[i], asize);
            if (block != NULL) {
                return block;
            }
        }
    }
    return NULL;
}

/*
 * find_fit_normal_block is used for find normal fit free block
 */
static block_t *find_fit_normal_block(char *size_class_pointer, size_t asize)
{
    block_t *block = NULL;
    size_t i = 0;
    bool flag = false;

    for (i = 1; i < size_class_number; i++) {

        if (!flag) {
            if (root[i] != size_class_pointer) {
                continue;
            } else {
                flag = true;
                block = find_proper_block(root[i], asize);
                if (block != NULL) {
                    return block;
                }
            }
        } else {
            block = find_proper_block(root[i], asize);
            if (block != NULL) {
                return block;
            }
        }
    }
    return NULL;
}

/*
 * find fit block for the given size.
 */
static block_t *find_fit(char *size_class_pointer, size_t asize)
{
    if (asize == small_block_size) {
        // when it is the 16 bytes block list
        return find_fit_small_block(size_class_pointer, asize);
    }
    else {
        // when it is the normal block
        return find_fit_normal_block(size_class_pointer, asize);
    }
    return NULL; // no fit found
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
        insert_empty_list(size_class_freelist, block);
    }
    else {   // case 2: free list is not empty
        if (get_head_pointer(size_class_freelist) == block) {
            // 2.1 root is block itself
            insert_block_itself(block, freeblock_next);

        } else {
            // 2.2 root is other block
            normal_insert_block(size_class_freelist, block);
        }
    }
}

/*
 * freeblock_remove, deal with removing normal free block from the list
 */
static void freeblock_remove(char *size_class_freelist, block_t *block,
                block_t *successor, block_t *predecessor)
{
    block_t *block_next_predecessor = predecessor;
    block_t *block_next_successor = successor;

    if (!block_next_predecessor && !block_next_successor) {
        // root = NULL;
        empty_block_update(size_class_freelist);
    }
    else if (!block_next_predecessor) { // head of the list
        // root = block_next_successor;
        head_block_update(size_class_freelist, block_next_successor);
    }
    else if (!block_next_successor) { // end of the list
        end_block_update(size_class_freelist, block_next_predecessor);
    }
    else { // in the middle
        middle_block_update(block_next_predecessor, block_next_successor);
    }

    next_pointer_update(block);
}

/*
 * only_middle_coalesce is used for coalesce process of only middle block free
 */
static void only_middle_coalesce(block_t *block, block_t *block_next,
                        size_t size, bool prev_small_block)
{
    char *size_class_pointer = find_proper_freelist(size);
    block_t *freeblock_next = NULL;

    if (size == small_block_size) {
        add_small_block_list(block);
        set_smallblock_bit(block_next);   //
    }
    else {
        freeblock_insert(size_class_pointer, block, freeblock_next);
    }

    off_alloc_bit(block_next);
}

/*
 * mid_next_coalesce is used for coalesce process of free middle and next block
 */
static void mid_next_coalesce(block_t *block, block_t *block_next,
                        size_t size, bool prev_small_block)
{
    size_t size_next = get_size(block_next);
    block_t *block_predecessor = NULL;
    char *size_class_pointer = NULL;
    block_t *freeblock_next = NULL;

    freeblock_next = find_next_free_block(block_next);

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
    write_header(block, size, get_prev_small_block(block), true, false);
    write_footer(block, size, false);

    insert_block(block, size, freeblock_next);
}

/*
 * mid_next_prev_coalesce is used for coalesce process of prev, middle and next
 * block
 */
static void mid_next_prev_coalesce(block_t *block, block_t *block_next,
                        size_t size, bool prev_small_block)
{
    block_t *block_prev = NULL;
    block_t *freeblock_next = NULL;
    block_t *block_predecessor = NULL;
    block_t *block_successor = NULL;
    char *size_class_pointer = NULL;
    size_t size_next = 0;
    size_t size_prev = 0;

    if (prev_small_block) {
        block_prev = find_small_prev(block);
    } else {
        block_prev = find_prev(block);
    }

    freeblock_next = find_next_free_block(block_prev);

    size_next = get_size(block_next);
    size_prev = get_size(block_prev);

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

    block = block_prev;
    insert_block(block, size, freeblock_next);
}
/*
 * freeblock_coalesce: general function distributing task for each situation
 */
static block_t *freeblock_coalesce(block_t *block, block_t *block_next,
                          size_t size)
{
        bool prev_alloc = get_prev_alloc(block);
        bool next_alloc = get_alloc(block_next);
        bool prev_small_block = get_prev_small_block(block);

        block_t *freeblock_next = NULL;
        char *size_class_pointer = NULL;
        size_t size_prev = 0;

        block_t *block_predecessor = NULL;

        if (prev_alloc && next_alloc)              // Case 1  only middle free
        {
            only_middle_coalesce(block, block_next, size, prev_small_block);
        }
        else if (prev_alloc && !next_alloc)        // Case 2  mid & next free
        {
            mid_next_coalesce(block, block_next, size, prev_small_block);
        }
        else if (!prev_alloc && next_alloc)        // Case 3  mid & prev free
        {
            // most difficult part and is likely to incur bugs
            if (size == small_block_size) {
                off_smallblock_bit(block_next);
            }
            // find the prev free block
            block_t *block_prev = NULL;
            if (prev_small_block) {
                block_prev = find_small_prev(block);
            } else {
                block_prev = find_prev(block);
            }

            freeblock_next = find_next_free_block(block_prev);
            size_prev = get_size(block_prev);

            // remove the prev block from its free list
            if (size_prev == small_block_size) {
              remove_small_block_list(block_prev);
            }
            else {
              block_predecessor = find_prev_free_block(block_prev);
              size_class_pointer = find_proper_freelist(size_prev);
              freeblock_remove(size_class_pointer, block_prev, freeblock_next,
                          block_predecessor);
            }

            // find the proper free list
            size += size_prev;
            write_header(block_prev, size, get_prev_small_block(block_prev),
                                  true, false);
            write_footer(block_prev, size, false);
            off_alloc_bit(block_next);
            // dbg_printf("the prev block is %p\n", block_prev);
            // dbg_printf("the new block size is %zu\n", size);

            // insert it
            block = block_prev;
            insert_block(block, size, freeblock_next);
        }

        else // Case 4  both free
        {
            mid_next_prev_coalesce(block, block_next, size, prev_small_block);
        }

    return block;
}

/*
 * remove_small_block_list is used for remove small block from its list
 */
static void remove_small_block_list(block_t *block)
{
   block_t *parent = NULL;
   block_t *cur = NULL;
   block_t *pointerSmall = get_head_pointer(root[0]);

   if (pointerSmall == block) {
       cur = find_next_free_block(block);
       if (cur == NULL) {
           write_head_pointer(root[0], NULL);
           write_tail_pointer(root[0], NULL);
       } else {
           write_head_pointer(root[0], cur);
       }

   } else {
       cur = pointerSmall;
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

    // check the small block list tail pointer
    if (!small_block_tail_check()) {
       debug_message(line);
       dbg_ensures(small_block_tail_check());
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
 /*
  * add_small_block_list is used for add small block list
  */
static void add_small_block_list(block_t *block)
{
   if (root[0] == NULL) {
       write_head_pointer(root[0], block);
       write_next_pointer(block, NULL);
   } else {
       block_t *header = get_head_pointer(root[0]);
       write_head_pointer(root[0], block);
       write_next_pointer(block, header);
   }
}

/*
 * address_check is used for checking small block tail value
 */
static bool small_block_tail_check()
{
    block_t *cur = get_tail_pointer(root[0]);
    if ((word_t)cur != 0) {
        return false;
    }
    return true;
}

/*
 * consistency_check is used for checking consistency of footer and header
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
 * consecutive_check is used for checking no consecutive block
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
            else
            {   // have consecutive block
                printf("teh consecutive block is %p\n", block);
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
* address_check is used for checking whether next and prev address are valid
* address or not.
*/
static bool address_check()
{
  block_t *block;

  for (block = heap_start; get_size(block) > 0; block = find_next(block))
  {
      if (!get_alloc(block))
      {
          if (!next_add_check(block) || !prev_add_check(block)) {

              return false;
          }
      }
  }
  return true; // no bug found
}

/*
 * find_proper_block is used for find proper block with given size
 */
static block_t *find_proper_block(char *size_class_pointer, size_t asize)
{
    block_t *block;
    size_t cur = 0;

    for (block = get_tail_pointer(size_class_pointer); block != NULL
             && (cur = get_size(block)) > 0; block = find_prev_free_block(block))
    {
        if (asize <= cur)
        {
           return block;
        }
    }

    return NULL;
}

/*
 * next_add_check: used for checking the next address
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

/*
 * prev_add_check: used for checking the prev address
 */
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
 * output the debug message
 */
static void debug_message(int line)
{
    //dbg_printf("mm_checkheap with line: %d encountered problem!\n", line);
}

/*
 * epilogue_check: check the epilogue
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
        size_t result = (n * ((size + (n-1)) / n));
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
    word_t set_prev_alloc =
              prev_alloc ? (set_alloc | prev_alloc_mask) : set_alloc;

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

/*
 * set_alloc_bit: set alloc bit for this block
 */
static void set_alloc_bit(block_t *block)
{
    (*(word_t *)block) |= prev_alloc_mask;
}

/*
 * off_alloc_bit: set off the alloc bit for this block
 */
static void off_alloc_bit(block_t *block)
{
    (*(word_t *)block) &= (~(word_t)prev_alloc_mask);
}

/*
 * set_smallblock_bit: set 16 bytes bit for this block
 */
static void set_smallblock_bit(block_t *block)
{
    (*(word_t *)block) |= small_block_mask;
}

/*
 * off_smallblock_bit: set off 16 bytes bit for this block
 */
static void off_smallblock_bit(block_t *block)
{
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

/*
 * get_small: get small block bit of this word
 */
static bool get_small(word_t word)
{
    return (bool)(word & small_block_mask);
}

/*
 * get_prev_small_block: get the small bit of this block
 */
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
/*
 * find_small_prev: returns the previous block position by calculating the
 * start of the previous block based on its size.
 */
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

/*
 * find the proper freelist for give size
 */
static char *find_proper_freelist(size_t size)
 {
     if (size <= small_block_size) {
         return root[0];
     } else if (size <= block_size_32) {
         return root[1];
     } else if (size <= block_size_48) {
         return root[2];
     } else if (size <= block_size_64) {
         return root[3];
     } else if (size <= block_size_96) {
         return root[4];
     } else if (size <= block_size_128) {
         return root[5];
     } else if (size <= block_size_256) {
         return root[6];
     } else if (size <= block_size_512) {
         return root[7];
     } else if (size <= block_size_1024) {
         return root[8];
     } else if (size <= block_size_2048) {
         return root[9];
     } else if (size <= block_size_4096) {
         return root[10];
     } else {
         return root[11];
     }
 }

/*
 * get_pointer: get the address of this pointer
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
 * write_next_pointer: write next_block to next pointer
 */
static void write_next_pointer(block_t *block, block_t *next_block)
{

    word_t *next_pointer = (word_t *)(block->payload);
    next_pointer[0] = (word_t)next_block;
}

/*
 * write_prev_pointer: write prev_block pointer to prev pointer
 */
static void write_prev_pointer(block_t *block, block_t *prev_block)
{

    word_t *prev_pointer = (word_t *)(block->payload) + 1;
    prev_pointer[0] = (word_t)prev_block;
}

/*
 * write_head_pointer: write pointer to this size class head pointer
 */
static void write_head_pointer(char *size_class_freelist, block_t *pointer)
{
    ((word_t *)size_class_freelist)[0] = (word_t)pointer;
}

/*
 * write_tail_pointer: write pointer to this size class tail pointer
 */
static void write_tail_pointer(char *size_class_freelist, block_t *pointer)
{
    ((word_t *)size_class_freelist)[1] = (word_t)pointer;
}

/*
 * get_head_pointer: get pointer to this size class head pointer
 */
static block_t *get_head_pointer(char *size_class_freelist)
{
    return get_pointer(size_class_freelist);
}

/*
 * get_tail_pointer: get pointer to this size class tail pointer
 */
static block_t *get_tail_pointer(char *size_class_freelist)
{
    char *pointer = size_class_freelist + wsize;
    return get_pointer(pointer);
}

/*
 * footer_header_consis_check is used for check the footer and header
 */
static bool footer_header_consis_check(block_t *block)
{
    word_t header = block->header;
    word_t* footer = (word_t*)((block->payload) + get_size(block) - dsize);

    return header == (*footer);
}

/*
 * insert_block: is the wrapper function of insert free block
 */
static void insert_block(block_t *block, size_t size, block_t *freeblock_next)
{
  char *size_class_newpointer = find_proper_freelist(size);
  freeblock_insert(size_class_newpointer, block, freeblock_next);
}

/*
 * small_block_place is used for place those small block
 */
static void small_block_place(block_t *block, size_t csize)
{
    block_t *next_block = NULL;
    // if the allocated block is 16 bytes
    write_header(block, csize, get_prev_small_block(block), true, true);

    next_block = find_next(block);
    set_alloc_bit(next_block);
    set_smallblock_bit(next_block);

    // remove the free node
    remove_small_block_list(block);
}

/*
 * insert_empty_list is used for insert block in empty list
 */
static void insert_empty_list(char *size_class_freelist, block_t *block)
{
    write_head_pointer(size_class_freelist, block);
    write_tail_pointer(size_class_freelist, block);
    write_next_pointer(block, NULL);
    write_prev_pointer(block, NULL);
}

/*
 * insert_block_itself is used for insert block which is root header
 */
static void insert_block_itself(block_t *block, block_t * freeblock_next)
{
    write_next_pointer(block, freeblock_next);
    write_prev_pointer(block, NULL);
    if (freeblock_next != NULL) {
        write_prev_pointer(freeblock_next, block);
    }
}

/*
 * normal_insert_block is used for insert block in a list
 */
static void normal_insert_block(char *size_class_freelist, block_t *block)
{
    block_t *next_free_pointer = get_head_pointer(size_class_freelist);
    write_prev_pointer(next_free_pointer, block);
    write_next_pointer(block, next_free_pointer);  // bug recode
    write_prev_pointer(block, NULL);

    // root = block;
    write_head_pointer(size_class_freelist, block);
}

/*
 * normal_insert_block is used for update a emptylist block
 */
static void empty_block_update(char *size_class_freelist)
{
    write_head_pointer(size_class_freelist, NULL);
    write_tail_pointer(size_class_freelist, NULL);
}

/*
 * normal_insert_block is used for update a head placed block
 */
static void head_block_update(char *size_class_freelist,
                  block_t *block_next_successor)
{
    write_head_pointer(size_class_freelist, block_next_successor);
    write_prev_pointer(block_next_successor, NULL);
}

/*
 * normal_insert_block is used for update an end placed block
 */
static void end_block_update(char *size_class_freelist,
                  block_t *block_next_predecessor)
{
    write_tail_pointer(size_class_freelist, block_next_predecessor);
    write_next_pointer(block_next_predecessor, NULL);
}

/*
 * middle_block_update is used for update a middle placed block
 */
static void middle_block_update(block_t *block_next_predecessor,
                  block_t *block_next_successor)
{
    write_next_pointer(block_next_predecessor, block_next_successor);
    write_prev_pointer(block_next_successor, block_next_predecessor);
}

/*
 * next_pointer_update is used for update next block
 */
static void next_pointer_update(block_t *block)
{
    // finally, need to deal with the next pointer bit
    if (get_size(block) == small_block_size) {   // bug record
        write_next_pointer(block, NULL);
    } else {
        write_next_pointer(block, NULL);
        write_prev_pointer(block, NULL);
    }
}

/*
 * update_next_header is used for update next block header
 */
static void update_next_header(block_t *block_next, size_t asize, size_t csize)
{
    if (asize == small_block_size) {
       write_header(block_next, csize-asize, true, true, false); // bug
    } else {
       write_header(block_next, csize-asize, false, true, false);
    }
}
