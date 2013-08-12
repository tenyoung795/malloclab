/*
 * mm-single.c - A 32-bit malloc implementation based on doubly-linked segregated free lists
 * on a singly-linked heap.
 * The lists are not sorted, though appending new blocks
 * tends to approximate order by address.
 * 
 * A unit is 64 bits.
 * An n-block consists of 1 block for the header + n blocks for the payload.
 * If the block is free then the first payload block contains data
 * as a node in a doubly-linked list.
 * The heap itself is an implicit singly linked list.
 * 
 * There are 10 classes by payload size:
 * + Small (1 unit, 2, 3, ..., 7)
 * + Medium (8-15, 16-31, 32-63)
 * + Large (>=64)
 */
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <limits.h>

#include "mm.h"
#include "memlib.h"

#define DEBUG
#ifdef DEBUG
#include <assert.h>
#else
#define assert(cond) ((void)0)
#endif


/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
  /* Team name */
  "ateam",
  /* First member's full name */
  "Harry Bovik",
  /* First member's email address */
  "bovik@cs.cmu.edu",
  /* Second member's full name (leave blank if none) */
  "",
  /* Second member's email address (leave blank if none) */
  ""
};

enum {
  NUM_SMALL_CLASSES = 7,
  NUM_MEDIUM_CLASSES = 3,
  NUM_CLASSES = NUM_SMALL_CLASSES
  + NUM_MEDIUM_CLASSES + 1,
  
  UNIT_BYTES = 8
};

typedef struct header {
  size_t size: 29; // 1 less than the payload size in units
  unsigned padding: 2; // unused
  unsigned alloc: 1;
  int i; // class index
  struct header *prev;
  struct header *next;
} header_t;

typedef struct {
  char data[UNIT_BYTES];
} unit_t;


static struct {
  header_t *head;
  header_t *last;
} classes[NUM_CLASSES];
static unit_t *next;

static size_t bytes_to_units(size_t);
static int get_class_index(size_t);
static size_t get_total_units(header_t *);
static header_t *get_header(void *);
static unit_t *get_payload(header_t *);
static header_t *get_next_in_heap(header_t *);
static void free_block(header_t *);
static unit_t *allocate(size_t);
static unit_t *allocate_from_larger(int, size_t);
static unit_t *allocate_largish(int, size_t);
static unit_t *allocate_block(header_t *);
static unit_t *split_block(header_t *, size_t);
static unit_t *allocate_next(size_t);
static int grow_heap(size_t);


/*
 * bytes_to_units - converts bytes to units - 1 by taking the ceiling of bytes / UNIT_BYTES - 1
 */
inline static size_t bytes_to_units(const size_t bytes) {
  assert(bytes);
  return bytes / UNIT_BYTES - (bytes % UNIT_BYTES == 0);
}

/*
 * get_class_index - gets the index of the class that corresponds to units of payload - 1
 */
inline static int get_class_index(const size_t units) {
  switch (units) {
  case 0 ... 6:
    return units;
  case 7 ... 14:
    return 7;
  case 15 ... 30:
    return 8;
  case 31 ... 62:
    return 9;
  default:
    return 10;
  }
}

/*
 * get_total_units - gets the block's total number of units, including header
 */
inline static size_t get_total_units(header_t *const block) {
  return 2 + block->size;
}

/*
 * get_next_in_heap - get the block immediately after a given block in the heap, NOT the free list
 */
inline static header_t *get_next_in_heap(header_t *const block) {
  return (header_t *)((unit_t *)block + get_total_units(block));
}

/*
 * get_header - gets a payload's header
 */
inline static header_t *get_header(void *const payload) {
  header_t *const header = (header_t *)((unit_t *)payload - 1);
  if (!header->alloc) {
    fprintf(stderr, "%p is the payload of an already freed block\n"
	    "\tpayload size (in %d-byte units): %u\n"
	    "\tprevious block: %p\n"
	    "\tnext block: %p\n",
	    payload,
	    UNIT_BYTES, header->size + 1,
	    header->prev,
	    header->next);
    abort();
  }
  return header;
}

/*
 * get_payload - gets a block's payload
 */
inline static unit_t *get_payload(header_t *const block) {
  return (unit_t *)block + 1;
}

/*
 * free_block - frees a block and adds it to its free list.
 */
inline static void free_block(header_t *const block) {
  assert(block != NULL); 
  assert(block->alloc);
  block->alloc = 0; 
  block->i = get_class_index(block->size); 
  if (classes[block->i].head == NULL) { 
    classes[block->i].head = block;
    block->prev = NULL; 
  } else {
    classes[block->i].last->next = block;
    block->prev = classes[block->i].last;
  }
  block->next = NULL;
  classes[block->i].last = block;
}

/*
 * allocate - allocates a block of a payload size in units
 */
inline static unit_t *allocate(const size_t units) {
  const int i = get_class_index(units);

  if (classes[i].head != NULL) {
    // for a small class, go straight to allocating the head
    if (i < NUM_SMALL_CLASSES)
      return allocate_block(classes[i].head);

    // for a medium or large class, find a free block that fits, then split it   
    return allocate_largish(i, units);
  }
  // if the list is empty, try to find a larger existing block to split up
  return allocate_from_larger(i, units);
}

/*
 * allocate_from_larger - allocate from a larger class size than the one specified.
  *  returns the payload or NULL on heap failure.
 */
static unit_t *allocate_from_larger(const int i, const size_t units) {
  assert(i == get_class_index(units));

  int j;
  for (j = i + 1; j < NUM_CLASSES && classes[j].head == NULL; j++);

  // if none of the classes have any free blocks, try to grab from the end of the heap
  if (j == NUM_CLASSES)
    return allocate_next(units);
  // otherwise, use its head
  return split_block(classes[j].head, units);
}

/*
 * allocate_largish - allocate a "largish" (medium or large) block.
 */
static unit_t *allocate_largish(const int i, const size_t units) {
  assert(i == get_class_index(units));
  assert(classes[i].head != NULL);

  header_t *block;
  for (block = classes[i].head; block != NULL && block->size < units; block = block->next);

  // if no fitting block exists, allocate from larger sources
  if (block == NULL)
    return allocate_from_larger(i, units);
  // allocate/split the block that fits
  return split_block(block, units);
}


/*
 * allocate_block - allocates a block and removes it from its free list
 */
static unit_t *allocate_block(header_t *const block) {
  assert(block != NULL);
  assert(!block->alloc);
  assert(block->i == get_class_index(block->size));
  assert((block->prev == NULL) == (classes[block->i].head == block));
  assert((block->next == NULL) == (classes[block->i].last == block));

  block->alloc = 1;

  const int isHead = block->prev == NULL;//classes[i].head == block;
  const int isLast = block->next == NULL;//classes[i].last == block;

  // special casing
  if (isHead && isLast) {
    classes[block->i].head = classes[block->i].last = NULL;
  } else if (isHead) {
    classes[block->i].head = block->next;
    block->next->prev = NULL;
  } else if (isLast) {
    classes[block->i].last = block->prev;
    block->prev->next = NULL;
  } else {
    block->prev->next = block->next;
    block->next->prev = block->prev;
  }

  return get_payload(block);
}

/*
 * split_block - splits a block that is not the head.
 */
inline static unit_t *split_block(header_t *const left, const size_t left_size) {
  assert(left != NULL);
  assert(left->i == get_class_index(left->size));
  assert(!left->alloc);
  assert(left_size <= left->size);

  const size_t prev_size = left->size;
  unit_t *const payload = allocate_block(left);

  // remaining includes the header
  // do NOT split if there is not enough space for a right block
  const size_t remaining = prev_size - left_size;
  if (remaining < 2)
    return payload;

  // change the size accordingly
  left->size = left_size;
  
  header_t *const right = get_next_in_heap(left);
  // -1 for the header, -1 for how units is defined
  right->size = remaining - 2;
  right->alloc = 1;
  free_block(right);

  return payload;
}

/*
 * allocate_next - attempts to allocate the next block in the entire heap.
 *  returns NULL if the heap needs to grow but cannot.
 */
static unit_t *allocate_next(const size_t units) {
  header_t *const block = (header_t *)next;

  // +1 for header, +1 for first payload unit
  if (grow_heap(2 + units) < 0)
    return NULL;
 
  block->size = units;
  block->alloc = 1;

  return get_payload(block);
}

/*
 * grow_heap - grows the heap in units
 *  returns 0 on success, -1 on failure
 */
static int grow_heap(const size_t units) {
  assert(units);
  
  const size_t prev_heapsize = mem_heapsize();
  int64_t bytes;
  for (bytes = units * (int64_t)sizeof(unit_t); bytes >= INT_MAX; bytes -= INT_MAX)
    if (mem_sbrk(INT_MAX) == (void *)-1)
      goto heapfail;
  if (bytes && mem_sbrk(bytes) == (void *)-1)
    goto heapfail;

  next += units;
  
  return 0;

 heapfail:
  mem_reset_brk();
  mem_sbrk(prev_heapsize);
  return -1;
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
  int i;
  for (i = 0; i < NUM_CLASSES; i++)
    classes[i].head = classes[i].last = NULL;

  next = mem_heap_lo();

  return 0;
}

/* 
 * mm_malloc - Allocate a block.
 *  If size == 0, returns NULL as a "success."
 *  If size > 0, returns non-NULL on success, NULL on failure to grow the heap.
 */
void *mm_malloc(const size_t size) {
  if (size == 0)
    return NULL;
  return allocate(bytes_to_units(size));
}

/*
 * mm_free - Frees a block.
 *  will abort program if ptr is certainly not an allocated block.
 */
void mm_free(void *const ptr) {
  if (ptr != NULL)
    free_block(get_header(ptr));
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free.
 *  A NULL return is a success if bytes == 0, a failure otherwise.
 *  will abort program if ptr is certainly not an allocated block.
 */
void *mm_realloc(void *const ptr, const size_t bytes) {
  if (ptr == NULL)
    return mm_malloc(bytes);
  
  if (bytes == 0) {
    mm_free(ptr);
    return NULL;
  }

  header_t *const block = get_header(ptr);
  const size_t prev_size = block->size;
  const size_t size = bytes_to_units(bytes);

  if (size == prev_size) {
    return ptr;
  }

  // if smaller size, attempt to split the block
  if (size < prev_size) {
    const size_t remaining = prev_size - size;
    if (remaining < 2)
      return ptr;
    
    block->size = size;
    
    header_t *const right = get_next_in_heap(block);
    right->size = remaining - 2;
    right->alloc = 1;
    free_block(right);

    return ptr;
  }

  header_t *const right = get_next_in_heap(block);

  const size_t needed = size - prev_size;

  // see if we can coalesce
  header_t *iter;
  size_t total;
  for (iter = right, total = 0;
       (unit_t *)iter < next && !iter->alloc && total < needed;
       iter = get_next_in_heap(iter))
    total += get_total_units(iter);

  // colaesce then possibly split the last block
  if (total >= needed) {
    header_t *const stop = iter;
    iter = right;
    while (1) {
      header_t *const inext = get_next_in_heap(iter);
      if (inext < stop) {
	allocate_block(iter);
	iter = inext;
      }
      else
	break;
    }
    
    const size_t extra = total - needed;

    // if the block isn't big enough to be split,
    // coalesce the whole thing.
    if (extra < 2) {
      allocate_block(iter);
      block->size = total; // including the extra
    }
    // even if the header would be enough
    // you can't have 0-blocks
    else if (extra == iter->size + 1) {
      split_block(iter, 0); // 0 for a 1-block
      block->size = size + 1;
    }
    else {
      split_block(iter, iter->size - extra);
      block->size = size;
    }

    return ptr;
  }

  // coalesce then grow heap
  if ((unit_t *)iter == next) {
    unit_t *const stop = next;
    if (grow_heap(needed - total) < 0)
      return NULL;

    for (iter = right; (unit_t *)iter < stop; iter = get_next_in_heap(iter))
      allocate_block(iter);
    
    block->size = size;
    return ptr;
  }


  // if we go here, that means the for loop terminated
  // because we found an allocated block, meaning we can't coalesce.
  unit_t *const newPtr = allocate(size);
  if (newPtr == NULL)
    return NULL;
  memcpy(newPtr, ptr, (prev_size + 1) * sizeof(*newPtr));
  free_block(block);
  
  return newPtr;
}
