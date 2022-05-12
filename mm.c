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
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team 8",
    /* First member's full name */
    "Heo Wonyoung",
    /* First member's email address */
    "dnjsdud2257@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

// 기본 상수와 메크로
#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8 
#define MINIMUM     16
#define CHUNKSIZE (1<<12)

#define MAX(x,y) ((x) > (y) ? (x): (y))

// 헤더와 푸터에 저장할 수 있는 값 리턴
#define PACK(size, alloc) ((size) | (alloc))

/* 크기와 할당 비트를 통합해서 헤더와 푸터에 저장할 수 있는 값을 리턴*/
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 주소 p의 헤더 또는 푸터의 SIZE와 할당 비트를 리턴한다.*/
#define GET_SIZE(p)   (GET(p) & ~0x7) // 뒤에 3비트를 제외하고 읽어옴
#define GET_ALLOC(p)  (GET(p) & 0x1) // 할당 가용 확인

/* 각각 블록 헤더와 풋터를 가리키는 포인터를 리턴한다.*/
#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp))- DSIZE)

/* 다음과 이전 블록 포인터를 각각 리턴한다.*/
#define NEXT_BLKP(bp)   (((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)   (((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE)))

// bp의 기본형은 (void *) 담고 있는 값은 prec 블록의 주소 임
// bp를 역참조해서 값을 가져와 다음 블록을 확인해야하지만 (void*)는 역참조 불가
// bp를 역참조하기 위해서 (void**) 후 역참조 시행함
// 
#define PREC_FREEP(bp) (*(void**)(bp))
#define SUCC_FREEP(bp) (*(void**)(bp + WSIZE))

// global variable & functions
static char* heap_listp = NULL;
static char* free_listp = NULL;

static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void* find_fit(size_t asize);
static void place(void* bp, size_t newsize);

int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void * bp);
void *mm_realloc(void *ptr, size_t size);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{   
    // mem_sbrk: 힙 영역을 incr(0이 아닌 양수) bytes 만큼 확장하고, 새로 할당된 힙 영역의 첫번째 byte를 가리키는 제네릭 포인터를 리턴함
    // padding, prologue(header, footer), PREC, SUCC, epliogue_header 총 6word로 빈 가용리스트 초기화
    if((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1){
        return -1;
    };

    PUT(heap_listp, 0);														// padding
    PUT(heap_listp + (1*WSIZE), PACK(MINIMUM, 1)); // prologue header
    PUT(heap_listp + (2*WSIZE), NULL);						// PREC
    PUT(heap_listp + (3*WSIZE), NULL);						// SUCC
    PUT(heap_listp + (4*WSIZE), PACK(MINIMUM, 1)); // prologue footer
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));			// epliogue_header
    
    free_listp = heap_listp + 2*WSIZE; // free_listp를 탐색의 시작점으로 둔다. 

    // CHUNKSIZE 만큼이 가용블록을 생성함
    if(extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

static void *extend_heap(size_t words)
{
    // 요청한 크기를 인접 2워드의 배수(8바이트)로 반올림하여, 그 후에 추가적인 힙 공간 요청
    char *bp;
    size_t size;
    // 요청한 크기를 2워드의 배수로 반올림하고 추가 힙 공간을 요청함
    size = (words %2) ? (words+1)*WSIZE : (words) * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;


    PUT(HDRP(bp), PACK(size, 0));  //free 블록의 header
    PUT(FTRP(bp), PACK(size, 0));  //free 블록의 footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // new epilogue header

		// 만약 이전 블록이 가용 블록이라면 연결하기 위해 coalesce 함수 호출
    return coalesce(bp);
};

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0){
        return NULL;
    }

    asize = ALIGN(size + SIZE_T_SIZE);  
    // 가용 블록을 가용리스트에서 검색하고 할당기는 요청한 블록을 배치한다.
    if((bp = find_fit(asize)) !=NULL){
        place(bp, asize);
        return bp;
    }

    //맞는 블록을 찾기 못한다면 새로운 가용 블록으로 확장하고 배치한다.
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);

    return bp;
}

// 할당된 블록을 합칠 수 있는 경우 4가지에 따라 메모리 연결
static void *coalesce(void *bp)
{		
    // 직전 블록의 footer, 직후 블록의 header를 보고 가용 여부를 확인.
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));	// 직전 블록의 가용 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));	// 직후 블록의 가용 여부
    size_t size = GET_SIZE(HDRP(bp));

    // case 1 : 직전, 직후 블록 모두 할당 -> 해당 블록만 free 시킴

    // case 2: 직전 블록 할당, 직후 블록 가용
    if(prev_alloc && !next_alloc){
        removeBlock(NEXT_BLKP(bp)); // free 상태인 직후 블록 free list에서 제거한다.
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case 3: 직전 블록 가용, 직후 블록 할당
    else if(!prev_alloc && next_alloc){
        removeBlock(PREV_BLKP(bp)); // 직전 블록을 free list에서 제거한다.
        size+= GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp); 
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
    }
    //case 4: 직전, 직후 모두 가용 블록
    else if(!prev_alloc && !next_alloc){
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))+ GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp); 
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // 연결된 새 가용 블록을 free list에 추가
    putFreeBlock(bp);
    return bp;
}

static void *find_fit(size_t asize){
    // 적절한 가용 블록을 검색하고 가용블록의 주소를 반환한다
    //first fit 검색을 수행한다. -> 리스트 처음부터 탐색하여 가용블록 찾기
    void *bp;
    //헤더의 사이즈가 0보다 크다. -> 에필로그까지 탐색한다.
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp)){
        if(asize <= GET_SIZE(HDRP(bp))){
            return bp;
        }
    }
    return NULL;
}

// 새로 반환되거나 생성된 가용 블록을 free list의 첫 부분에 넣는다.
void putFreeBlock(void* bp){
	SUCC_FREEP(bp) = free_listp;
	PREC_FREEP(bp) = NULL;
	PREC_FREEP(free_listp) = bp;
	free_listp = bp;
}

//할당되거나 연결되는 가용 블록을 free list에서 없앤다.
void removeBlock(void *bp){
	// free list의 첫번째 블록을 없앨 때
	if (bp == free_listp){
		PREC_FREEP(SUCC_FREEP(bp)) = NULL;
		free_listp = SUCC_FREEP(bp);
	}
	// free list 안에서 없앨 때
	else{
		SUCC_FREEP(PREC_FREEP(bp)) = SUCC_FREEP(bp);
		PREC_FREEP(SUCC_FREEP(bp)) = PREC_FREEP(bp);
	}
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    // 해당 블록의 size를 알아내 header와 footer의 정보를 수정함
    size_t size = GET_SIZE(HDRP(ptr));

    // header와 footer를 설정
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    //앞뒤의 블록이 가용 상태라면 연결
    coalesce(ptr);
}

// 
static void place(void *bp, size_t asize){
    // 현재 할당할 수 있는 후보 가용 블록의 주소
    size_t csize = GET_SIZE(HDRP(bp));
    
    // 할당될 블록이므로 free list에서 없애준다.
    removeBlock(bp);

    // 분할이 가능한 경우
    if((csize - asize) >= (2*DSIZE)){
        // 앞의 블록은 할당 블록으로
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // 뒤의 블록은 가용 블록으로 분할
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));

        //free list 첫번째에 분할된 블록을 넣는다.
        putFreeBlock(bp);
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    void *old_bp = bp;  // 크기를 조절하고 싶은 힙의 시작 포인터
    void *new_bp;       // 크기 조절 뒤의 새 힙의 시작 포인터
    size_t copySize;    // 복사할 힙의 크기
    
    new_bp = mm_malloc(size);
    if (new_bp == NULL)
      return NULL;

    copySize = GET_SIZE(HDRP(old_bp));

    // 원래 메모리 크기보다 적은 크기를 realloc하면 크기에 맞는 메모리만 할당되고 나머지는 안됨
    if (size < copySize)
      copySize = size;
    memcpy(new_bp, old_bp, copySize);  // 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수(old_bp로부터 copySize만큼의 문자를 new_bp로 복사해라)
    mm_free(old_bp); // 기존의 힙을 반환한다.
    return new_bp;
}
