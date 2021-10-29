/*
 * mm.c
 *
 * Name: Evan Kunkel
 *
 * This code implements the memory allocation function, malloc(), memory freeing fucntion, free(), and the memory re-allocation function, realloc().
 * 
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
// #define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#endif /* DEBUG */

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* DRIVER */

/* What is the correct alignment? */
#define ALIGNMENT 16
#define SEGLISTNUM 32 //MAX 59
#define MINBLOCKSIZE 32

/* Free block node used in linked list */
typedef struct free_blk{
    struct free_blk *next;
    struct free_blk *prev;
} free_blk_t;

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}
/*Finds appropriate class to put *header to for the segregrated free list*/
int int_log2(size_t x){
  int i = ((sizeof(size_t)*8-1)^__builtin_clzl(x)) - 5; //Since the minimum number of bytes is 32 or 2^5, we subtract 5 to get to 0th place on the segregrated free list.
  if(i > SEGLISTNUM - 1)
    i = SEGLISTNUM - 1;
  return i;
}

void setCurrAlloc(size_t *hf){
  *hf |= 1;
  return;
}

void setPrevAlloc(size_t *hf){
  *hf |= 2;
  return;
}

void resetCurrAlloc(size_t *hf){
  *hf &= -2;
  return;
}

void resetPrevAlloc(size_t *hf){
  *hf &= -3;
  return;
}

void* getHeaderFromFB(void *fb){
  return (size_t *)(fb) - 1;
}

void* getFBFromHeader(void *header){
  return (size_t *)(header) + 1;
}

void* getPrevFooterFromHeader(size_t *currHeader){
  return currHeader - 1;
}

void* getPrevHeaderFromHeader(size_t *currHeader){
  size_t *prevFooter = getPrevFooterFromHeader(currHeader);
  return prevFooter - (*prevFooter/sizeof(size_t)) + 1;
}

void* getNextHeaderFromHeader(size_t *currHeader){
  return currHeader + (*currHeader/sizeof(size_t));
}

void* getFooterFromHeader(size_t *currHeader){
  return (size_t *)getNextHeaderFromHeader(currHeader) - 1;
}

void* getNextFooterFromHeader(size_t *currHeader){
  return getFooterFromHeader(getNextHeaderFromHeader(currHeader));
}

/* Remove a free block from the list */
void removeFreeBlock(free_blk_t *fb){
  /* Move pointers from fb to the next or previous. Set fb pointers to NULL. */
  if(fb->next)
    fb->next->prev = fb->prev; 
  if(fb->prev)
    fb->prev->next = fb->next; 
  fb->next = NULL;
  fb->prev = NULL;
}

/* Attempted to coalesce the current block forward */
void* coalesceForward(free_blk_t *currfb){
  size_t *currHeader, *currFooter, *nextHeader, *nextFooter;
  free_blk_t *nextfb; 

  /* Get the header that goes with the free block, as well as the next header. */
  currHeader = getHeaderFromFB(currfb);
  nextHeader = getNextHeaderFromHeader(currHeader); 

  /* If the next header is not the fake header at the end and it is free, coalesce. */
  if(!(*nextHeader & 1)){
    currFooter = getFooterFromHeader(currHeader); 
    nextFooter = getFooterFromHeader(nextHeader); 

    *currHeader += *nextHeader; 
    *nextFooter += *currFooter;

    *currFooter = 0;
    *nextHeader = 0;
    
    nextfb = getFBFromHeader(nextHeader);
    removeFreeBlock(nextfb);
  }
  return currfb;
}

/* Attempt to coalesce the current block backwards */
void* coalesceBackward(free_blk_t *currfb){
  size_t *prevHeader, *prevFooter, *currHeader, *currFooter;
  free_blk_t *prevfb; 

  /* Get the header that goes with the free block */
  currHeader = getHeaderFromFB(currfb);

  /* If the header lies within the heap and is not the first header and the prev alloc bit is 0, coalesce. */
  if(!(*currHeader & 2)){
    prevFooter = getPrevFooterFromHeader(currHeader);
    prevHeader = getPrevHeaderFromHeader(currHeader); 
    currFooter = getFooterFromHeader(currHeader); 

    *prevHeader += *currHeader;
    *currFooter += *prevFooter;

    *prevFooter = 0;
    *currHeader = 0;
    
    prevfb = getFBFromHeader(prevHeader);
    removeFreeBlock(prevfb);
    return prevfb;
  }
  return currfb;
}



/* Add a free block to the list */
void addFreeBlock(free_blk_t *currfb){
  size_t *currHeader, *nextHeader;
  free_blk_t *prevfb, *end;
  int log;

  currHeader = getHeaderFromFB(currfb);
  log = int_log2(*currHeader & -3);
  
  prevfb = mem_heap_lo();
  end = prevfb + SEGLISTNUM;

  /* Attempt to coalece before adding to free block list. */
  currfb = coalesceForward(currfb);
  currfb = coalesceBackward(currfb);
  
  prevfb += log;

  nextHeader = getHeaderFromFB(prevfb->next);

  /* If prevfb exists and its next is outside of the seglist part of the heap and its smaller than the currfb */
  while(prevfb && prevfb->next > end && (*currHeader & -3) > (*nextHeader & -3)){ //
    prevfb = prevfb->next;
    nextHeader = getHeaderFromFB(prevfb);
  }

  /* Linked list insertion. */
  currfb->next = prevfb->next;
  prevfb->next = currfb;
  currfb->prev = prevfb;
  if(currfb->next)
    currfb->next->prev = currfb;
}

/* Find a free block that is size or bigger */
void *findFreeBlock(size_t size){
  size_t *header;
  free_blk_t *fb, *end;
  int log;

  log = int_log2(size);
  fb = mem_heap_lo(); 
  end = fb + SEGLISTNUM; // 
  
  fb += log;
  fb = fb->next;

  /* Iterate through the rest of the free blocks, seeing they are real (not part of seglist) and big enough */
  while(fb){
    if(fb > end){
      header = getHeaderFromFB(fb);
      if(*header >= size){ // The statement that checks if there is a free block available that can fit size_t size 
	      removeFreeBlock(fb);
	      return header;
      }
    }
    fb = fb->next;
  }
  return NULL;
}

/*
 * Initialize: returns false on error, true on success.
 */

bool mm_init(void)
{
    /* IMPLEMENT THIS */
  free_blk_t *fbp = mem_sbrk(2*sizeof(size_t) + SEGLISTNUM*sizeof(free_blk_t));
  size_t *fakehf;
  int i = 0;
  
  if(fbp){
    /* Create the seglist at the start of the heap. */
    fbp->next = fbp + 1;
    fbp->prev = NULL;
    fbp += 1;
    for(i = 1; i < SEGLISTNUM - 1; i += 1){ //Creates the linked lists for segregrated linked lists
      fbp->next = fbp + 1;
      fbp->prev = fbp - 1;
      fbp += 1;
    }
    fbp->next = NULL;
    fbp->prev = fbp - 1;

    /* Create the fake header and footer. */
    fakehf = (size_t *)(fbp + 1);
    *fakehf = 1;
    fakehf += 1;
    *fakehf = 3;
    return true;
  }
  else
    return false;
}

/*
 * malloc
 */
void* malloc(size_t size)
{
  /* Base case */
  if(size==0){
    return NULL;
  }

  size_t block_size = align(size + sizeof(size_t));
  if(block_size < MINBLOCKSIZE) // Makes sure the block_size is indeed the minimum bytes in order to function, 32 bytes.
    block_size = MINBLOCKSIZE;
  size_t *currHeader = findFreeBlock(block_size), *currFooter, *nextHeader, *nextFooter;
  size_t temp; 
  free_blk_t *fb;

  /* Allocate more memory to heap. Add it as a free block and find it again in case it can be coalesced with memory at end of heap */
  if(!currHeader){
    currHeader = mem_sbrk(block_size);
    if(!currHeader)
      return NULL;
    
    currHeader -= 1;
    resetCurrAlloc(currHeader);

    //currFooter = getFooterFromHeader(currHeader);
    //nextHeader = getNextHeaderFromHeader(currHeader);
    
    *currHeader |= block_size;
    currFooter = getFooterFromHeader(currHeader);
    *currFooter = block_size;
    nextHeader = getNextHeaderFromHeader(currHeader);
    *nextHeader = 1;

    fb = getFBFromHeader(currHeader);
    addFreeBlock(fb);

    currHeader = findFreeBlock(block_size);
  }

  /* Block returned is bigger than needed. Split it into two blocks, setting the unneeded bytes as free. */
  if(*currHeader >= block_size + MINBLOCKSIZE){
    temp = *currHeader & -3;
    *currHeader -= temp;
    *currHeader += block_size;

    nextHeader = getNextHeaderFromHeader(currHeader);
    *nextHeader = (temp - block_size) | 2;
    nextFooter = getNextFooterFromHeader(currHeader);
    *nextFooter = temp - block_size;

    currFooter = getFooterFromHeader(currHeader);
    setCurrAlloc(currHeader);
    *currFooter = block_size | 1;

    fb = getFBFromHeader(nextHeader);
    addFreeBlock(fb);
  }else{
    /* Set alloc bits for header, footer, and next header */
    currFooter = getFooterFromHeader(currHeader);
    nextHeader = getNextHeaderFromHeader(currHeader);

    setCurrAlloc(currHeader);
    setCurrAlloc(currFooter);
    setPrevAlloc(nextHeader);
  }
  return currHeader + 1;
}

/*
 * free
 */
void free(void* ptr)
{
  /* Go to header, make sure it has a value and that it is allocated. Then reset alloc bit */  
  free_blk_t *fb = ptr;
  size_t *currHeader = getHeaderFromFB(ptr), *currFooter, *nextHeader;
  
  if(currHeader == NULL) return;
  if(!(*currHeader&1)) return;

  resetCurrAlloc(currHeader); //Resets alloc bit for currHeader

  nextHeader = getNextHeaderFromHeader(currHeader);
  resetPrevAlloc(nextHeader); //Resets prev alloc bit for nextHeader
	
  /* Go to footer and reset it */
  currFooter = getFooterFromHeader(currHeader);
  *currFooter = *currHeader;
  resetPrevAlloc(currFooter); //Resets alloc bits for currFooter
	
  /* Create a free block at the current address. Add it to the list */
  addFreeBlock(fb);  
  return;
}

/*
 * realloc
 */
void* realloc(void* oldptr, size_t size)
{
  if(!oldptr) return malloc(size);
  if(size == 0) free(oldptr);

  uint8_t *old = oldptr;
  size_t *header = getHeaderFromFB(oldptr);

  size_t oldsize = *header & -4;
  size_t copynum = oldsize < size ? oldsize : size;

  uint8_t *new = malloc(size);

  /* Copy the bytes from the old block to the new block. */
  memcpy(new, old, copynum);
  free(oldptr);
  
  return new;
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno)
{
#ifdef DEBUG
    /* Write code to check heap invariants here */
    /*Checks if heap exists for heap block ptr to be valid*/
  if(mem_heap_lo() >= mem_heap_hi())
    return false;
  if(mem_heapsize() <= 0)
    return false;
	
  size_t *prevHeader, *prevFooter, *currHeader, *currFooter, *heapend;
  free_blk_t *endseglist, *fb = mem_heap_lo();
  endseglist = fb + SEGLISTNUM;

  heapend = mem_heap_hi();
  heapend -= 1;

  /* Iterate through list of free blocks */
  while(fb){
    if(fb > endseglist){
      if(!(fb->prev))
	return false;
      currHeader = (size_t *)fb;
      currHeader -= 1;
      currFooter = currHeader + (*currHeader/sizeof(size_t)) - 1;
      if(*currHeader & 1 || *currFooter & 1) //Checks if fb is allocated, which would be false
        return false;
    }
    fb = fb->next;
  }
  currHeader = (size_t *)endseglist;
  currHeader += 1;
  
  currFooter = currHeader + (*currHeader/sizeof(size_t)) - 1;
  
  prevHeader = NULL;
  prevFooter = NULL;
	
  /* Implicitly iterate through blocks in heap, excluding the seglist */
  while(currHeader < heapend){
    /* Alloc and PrevAlloc bit both set to 0. Should not happen (free blocks would be coalesced). */
    if(!(*currHeader & 1) && !(*currHeader & 2)) 
      return false;
    
    if(prevHeader && prevFooter){
      /*Previous and current header both have alloc bits set to 0. Should not happen (free blocks would be coalesced)*/
      if(!(*currHeader & 1) && !(*prevHeader & 1)) //Both previous and current block are free, ergo false
	return false;
      /* Current header has PrevAlloc bit set to 1 when the previous block is free */
      if((*currHeader & 2) && !(*prevHeader & 1))
	return false;
      /* Current header has PrevAlloc bit set to 0 when the previous block is alloc */
      if(!(*currHeader & 2) && (*prevHeader & 1))
	return false;
      /* If previous footer exists, make sure it has the same size as previous header */
      if(!(*currHeader & 2))
	if(*prevFooter != (*prevHeader & -3))
	  return false;
    }
    
    prevHeader = currHeader;
    prevFooter = currFooter;
    currHeader = currFooter + 1;
    currFooter += (*currHeader/sizeof(size_t));
  }
  return true;
  
#endif /* DEBUG */
    return true;
}
