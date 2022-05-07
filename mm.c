/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include "mm.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"

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
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4              // 워드 = 헤더 = 풋터 사이즈(bytes)
#define DSIZE 8              // 더블워드 사이즈(bytes)
#define CHUNKSIZE (1 << 12)  // heap을 이정도 늘린다(bytes)
// #define LISTLIMIT 20 //list의 limit 값을 설정해준다. CHUNKSIZE에 비해 충분히
// 큰 값을 준 것 같다(정확한 이유 모르겠음)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

// size와 할당 여부를 하나로 합친다
#define PACK(size, alloc) ((size) | (alloc))

// Read and wirte a word at address p
// p는 (void*)포인터이며, 이것은 직접 역참조할 수 없다.
#define GET(p) (*(unsigned int *)(p))  // p가 가리키는 놈의 값을 가져온다
#define PUT(p, val) \
  (*(unsigned int *)(p) = (val))  // p가 가리키는 포인터에 val을 넣는다
// Read the size and allocated fields from address p
#define GET_SIZE(p) \
  (GET(p) & ~0x7)  //포인터 p가 가르키는 곳의 값에서 하위 3비트를 제거하여 블럭
                   //사이즈를 반환(헤더+푸터+페이로드+패딩)
#define GET_ALLOC(p) \
  (GET(p) & 0x1)  //포인터 p가 가르키는 곳의 값에서 맨 아래 비트를 반환하여
                  //할당상태 판별

// Given block ptr bp, compute address of its header and footer
//블럭포인터를 통해 헤더 포인터,푸터 포인터 계산
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// Given block ptr bp, compute address of next and previous blocks
// 현재 bp에서 WSIZE를 빼서 header를 가리키게 하고, header에서 get size를 한다.
// 그럼 현재 블록 크기를 return하고(헤더+데이터+풋터), 그걸 현재 bp에 더하면
// next_bp나옴
//가용 블럭 리스트에서 next 와 prev의 포인터를 반환
#define NEXT_PTR(ptr) ((char *)(ptr))
#define PREV_PTR(ptr) ((char *)(ptr) + WSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

char *heap_listp = 0;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
/*
 * mm_init - initialize the malloc package.
 */
// 최초가용 블럭으로 힙 생성하기
int mm_init(void) {
  int list;

  if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) return -1;
  PUT(heap_listp, 0);                            /* Alignment padding */
  PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
  PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
  PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
  heap_listp = heap_listp + (2 * WSIZE);  // 다른사람들은 이 줄을 없앴네

  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extend_heap(CHUNKSIZE / WSIZE) == NULL)  // 90점
    // if (extend_heap(CHUNKSIZE/WSIZE) == NULL) : 88점
    return -1;
  return 0;
}

static void *extend_heap(size_t words) {
  char *bp;
  size_t size;

  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if ((long)(bp = mem_sbrk(size)) == -1) return NULL;

  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New Epilogue Block */

  return coalesce(bp);
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp) {
  size_t size = GET_SIZE(HDRP(bp));
  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  coalesce(bp);
}

static void *coalesce(void *bp) {
  size_t prev_alloc =
      GET_ALLOC(FTRP(PREV_BLKP(bp)));  // 이전 블럭 free인지 check
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));  // 다음 ~
  size_t size = GET_SIZE(HDRP(bp));                    // 현재 블럭의 size

  /* case 1 */  // 이전 블럭, 다음 블럭 최하위 bit 둘 다 1 할당이면, 블럭 병합
                // 없이 bp return
  if (prev_alloc && next_alloc) {
    return bp;
  } else if (prev_alloc && !next_alloc) {
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  } else if (!prev_alloc && next_alloc) {
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }

  /* case 4 */  // 이전 블럭 최하위 bit 0(비할당), 다음 블럭 최하위 bit
                // 0(비할당)이면
  else {
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  return bp;
}

void *mm_malloc(size_t size) {
  size_t asize;
  size_t extendsize;
  char *bp;

  if (size == 0) return NULL;

  if (size <= DSIZE)
    asize = 2 * DSIZE;
  else
    asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }

  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL) return NULL;
  place(bp, asize);
  return bp;
}

static void *find_fit(size_t asize) {
  void *bp;
  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
      return bp;
    }
  }
  return NULL;
}

static void place(void *bp, size_t asize) {
  size_t csize = GET_SIZE(HDRP(bp));
  if ((csize - asize) >= (2 * DSIZE)) {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));
  } else {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
  void *oldptr = ptr;
  void *newptr;
  size_t copySize;

  newptr = mm_malloc(size);
  if (newptr == NULL) return NULL;
  copySize = GET_SIZE(HDRP(oldptr));
  if (size < copySize) copySize = size;
  // memcpy - 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리
  // 영역으로 복사해주는 함수(oldptr로부터 copySize만큼의 문자를 newptr로
  // 복사해라)
  memcpy(newptr, oldptr, copySize);
  mm_free(oldptr);
  return newptr;
}