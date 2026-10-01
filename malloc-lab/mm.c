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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/***********************************************************
 * simple - naive malloc 구현
 * 최초 작성 코드의 문제 및 필요한 기능
 * 0. mm_init이 아무 동작도 하지 않음
 * 1. header에 alloc/free 여부를 확인할 수 있는 flag의 부재
 * 2. free 함수가 아무런 기능을 하지 않고 void 반환
 * 3. 이로 인해 realloc 함수도 기존 메모리 주소를 free 하지 않고 계속 alloc만 함
 * -> utilization 성능 저하
 * 4. mm_malloc()함수가 mem_sbrk(newsize)를 먼저 호출하는데, 그 전에 가용 블록이
 * 있는지 확인 필요 (free, next, best fit 중 배치 정책 선택) ->find_fit()
 * 5. 기존 free block 탐색 -> place()
 * 6. 찾은 블록에 배치하고 필요하면 split, 적당한 블록이 없으면 extend_heap
 * 7. mm_free()에 coalescing도 고려해야 함 -> footer가 필요
 * -> NEXT_BLKP(bp) / PREV_BLKP(bp)가 필요
************************************************************/

/* single word (4) or double word (8) alignment*/
#define ALIGNMENT 8
#define WSIZE 4 // header와 footer를 만들기 위한 단위 크기 정의
#define DSIZE 8 // 정렬 단위와 같은 크기

/* rounds up to the nearest multiple of ALIGNMENT
 * 8 바이트 단위로 정렬하기 위한 올림 과정
 **********************************************************************************
 * 주소 정렬을 하는 이유: CPU는 정렬된 주소에서 데이터를 접근하는 것이
 * 효율적이거나 특정 아키텍쳐는 이를 요구함
 * malloc은 사용자가 요구하는 어떤 데이터 타입이든 관계 없이 메모리를 할당하는 것이 기능상 목적
 * 따라서 malloc은 반환한 메모리를 사용자가 다양한 데이터 타입에 안전하고 효율적으로 사용할
 * 수 있도록 적절한 alignment를 보장하기 위해서 내부적으로 정렬을 함
 **********************************************************************************
 * (size) + (ALIGNMENT - 1) = (size) + 7
 * & ~0x7은 이진법으로 끝 세자리 111을 000으로 만드는 동작
*/
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define PACK(size, alloc) ((size) | (alloc)) // | <- 비트 or 연산자. || 와 구분해야 함

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// header와 footer에 저장할 정보를 쓰고 다시 읽는 역할의 매크로 GET과 PUT
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // -> p를 unsigned int*로 형변환하고, 그 주소를 역참조해서 val을 대입한다.
#define GET(p) (*(unsigned int *)(p))

// 헤더에서 사이즈 값과 alloc 여부 값을 각각 분리하는 매크로
#define GET_SIZE(p) (GET(p) & ~0x7) //payload 사이즈가 아닌 블록 전체의 사이즈
#define GET_ALLOC(p) (GET(p) & 0x1)

// header와 footer의 주소 계산 및 가리키는 포인터 생성
#define HDRP(bp) (((char *)(bp)) - WSIZE) // char *로 변환하여 주소를 byte 단위로 계산
#define FTRP(bp) (((char *)(bp)) + GET_SIZE(HDRP(bp)) - DSIZE) // bp를 기준으로 계산한 것
/* HDRP를 기준으로 FTRP를 구할 수도 있다!
 * #define FTRP(bp) ((HDRP(bp)) + GET_SIZE(HDRP(bp)) - WSIZE)
*/

// 다음 블록과 이전 블록의 주소 구하기
#define NEXT_BLKP(bp) (((char *)(bp)) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) (((char *)(bp)) - GET_SIZE(((char *)(bp)) - DSIZE))
/*
 * mm_init - initialize the malloc package.
 * free block, padding, prologue block, epilogue block 전부 고려
 * prologue / epilogue가 필요한 이유:
 * free를 하는데 해당 블록이 처음/마지막 블록일 경우 prev. next.가 없음
 * 그 경우 coalescing 하면서 조건문으로 검사를 해야 함 -> 효율성 저하
 * 이를 방지하기 위해 init 시점에서 쓰지 않을 prologue / epilogue 블록을 만듦
 * 경계 처리를 단순하게 만드는 sentinel의 역할
 */

static char *heap_listp = NULL; // 힙의 블록 순회의 시작 주소를 기억하기 위한 포인터

int mm_init(void)
{
    /*
     * 초기 메모리 설정하기
     * 패딩 4 - 프롤로그 헤더 4 - 프롤로그 푸터 4 - 에필로그 헤더 4
     */
    heap_listp = mem_sbrk(4 * WSIZE);
    if (heap_listp == (void *)-1){
        return -1;
    }

    PUT(heap_listp, 0); // 패딩 설정
    PUT(heap_listp + WSIZE, PACK(DSIZE, 1)); // 프롤로그 헤더 설정
    PUT(heap_listp + DSIZE, PACK(DSIZE, 1)); // 프롤로그 풋터 설정
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); // 에필로그 헤더 설정

    heap_listp += DSIZE; // bp로 포인터 이동

    /* 여기까지의 흐름으로 초기 골격은 만들었지만, 할당할 free block은 없다.
     * 고로 extend_heap을 써서 free block을 만들어야 한다.
    */
   

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
        return NULL;
    else
    {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}