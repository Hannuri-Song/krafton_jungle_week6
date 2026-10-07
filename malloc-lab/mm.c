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
    "Team 5",
    /* First member's full name */
    "Antonio",
    /* First member's email address */
    "Antonio@jungle.edu",
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
#define CHUNKSIZE (1 << 10) //할당기가 힙을 확장하는데 사용하는 기본 크기 단위 설정 (2^12 = 4096바이트)


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
 * & ~0x7은 이진법으로 끝 세자리 111을 000으로 만드는 동작 */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define PACK(size, alloc) ((size) | (alloc)) // | <- 비트 or 연산자. || 와 구분해야 함

// #define SIZE_T_SIZE (ALIGN(sizeof(size_t))) naive allocator에서 size 값을 저장할 공간의 크기를 alignment에 맞춰 계산하기 위해서

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
 * #define FTRP(bp) ((HDRP(bp)) + GET_SIZE(HDRP(bp)) - WSIZE) */

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
 * 경계 처리를 단순하게 만드는 sentinel의 역할 */

static char *heap_listp = NULL; // 힙의 블록 순회의 시작 주소를 기억하기 위한 포인터
static char *next_freep = NULL; // find_fit()을 next_fit 방식으로 구현하기 위해 마지막 탐색 위치 기억할 포인터

static void *extend_heap(size_t words); // words = CHUNKSIZE / WSIZE = WORD의 개수만큼 확장한다는 의미
static void *coalesce(void *bp);
static void *find_fit(size_t size);
static void place(char *bp, size_t size);

int mm_init(void)
{
    /*
     * 초기 메모리 설정하기
     * 패딩 4 - 프롤로그 헤더 4 - 프롤로그 푸터 4 - 에필로그 헤더 4 */
    heap_listp = mem_sbrk(4 * WSIZE);
    if (heap_listp == (void *)-1){ // 초기 할당할 메모리가 없을 경우
        return -1;
    }

    PUT(heap_listp, 0); // 패딩 설정
    PUT(heap_listp + WSIZE, PACK(DSIZE, 1)); // 프롤로그 헤더 설정
    PUT(heap_listp + DSIZE, PACK(DSIZE, 1)); // 프롤로그 풋터 설정
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); // 에필로그 헤더 설정

    heap_listp += (DSIZE); // bp로 포인터 이동

    /* 여기까지의 흐름으로 초기 골격은 만들었지만, 할당할 free block은 없다.
     * 고로 extend_heap을 써서 free block을 만들어야 한다.
     * extend_heap을 하기 위해서는 얼마만큼 heap 영역을 확장할건지에 대한 크기 설정도 필요하다
     * 이를 위해서 CHUNKSIZE를 정의하는 것 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL){
        return -1;
    }
    next_freep = NEXT_BLKP(heap_listp);
    // 힙 영역 확장 후 최초의 free block으로 이동

    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* 블록 크기가 정렬 조건을 만족하도록 words가 홀수인 경우 처리하기
     * 8-byte 정렬 조건
     * 어차피 CHUNKSIZE / WSIZE는 짝수잖아?
     * 하지만 mm_init 외에도 mm_malloc에서도 호출될 수 있고 이 경우 항상 짝수를
     * 보장하기 어려움. 따라서 어떤 words를 받더라도 정렬 규칙을 지키도록 하는 것 */
    if (words % 2 != 0){
        size = (words + 1) * WSIZE;
    }
    else {
    size = words * WSIZE;
    }

    bp = mem_sbrk(size);
    if (bp == (void *) -1){
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0)); // 새로 확장한 영역의 헤더
    PUT(FTRP(bp), PACK(size, 0)); // 새로 확장한 영역의 풋터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새로 확장한 영역의 에필로그 헤더

    /* 여기까지의 흐름으로는 힙 영역 확장은 했음. 다만 기존에 있는 free block의
     * coalescing이 필요함 이 밑으로 그 부분의 코드를 작성 할 것임.
     * coalescing이 필요한 순간은 "새로운 free block이 생기는 순간"
     * 그래서 이 때도, free() 함수 때도 고려해야 하는 것
     * 지금은 우측은 어차피 epi.header니까 좌측만 고려하면 됨
     * 어차피 free()때도 써야만 한다면 coalesce()함수로 별도 생성하는 것도 방법
     */
    
    /* extend_heap 전용 coalesce 코드 이걸 범용 coalesce() 함수로 대체
     if (GET_ALLOC(HDRP(PREV_BLKP(bp))) == 0){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));        
    }
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    bp = PREV_BLKP(bp);

    return bp;
    */
    bp = coalesce(bp);
    return bp;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // 기존 naive allocator 코드
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
    //     return NULL;
    // else
    // {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
    if (size == 0){
        return NULL;
    }

    size_t newsize = ALIGN(size + DSIZE); // DSIZE(헤더, 풋터 크기)를 포함한 전체 블록 크기
    

    void *p = find_fit(newsize);
    if (p != NULL){
        place(p, newsize);
        return p;
    }

    size_t extend_size;
    if (newsize < CHUNKSIZE){
        extend_size = CHUNKSIZE;
    }
    else{
        extend_size = newsize;
    }

    p = extend_heap(extend_size / WSIZE);
    if (p == NULL){
        return NULL;
    }

    place(p, newsize);
    return p;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    if (bp == NULL){
        return;
    }
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    coalesce(bp);
}

 /*
  * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
  * 기본 realloc()의 문제점: 기존의 free block을 사용할 수 있는 상황에서도 무조건
  * 새 블록을 만들어서 할당한다.
  * 순서 상 새 block을 만들고 기존 block을 free 하기 때문에 util이 안좋음
  * 궁극적인 목표는 "기존 block을 쓸 수 있으면 그거부터 쓰자"
  */
void *mm_realloc(void *bp, size_t size)
{
    // void *oldbp = bp; // 기존의 bp를 저장하는 변수
    void *newbp; // 새로 할당받은 bp
    size_t new_size;
    size_t cur_size;
    size_t copy_size;


    // case 0. 특수 예외처리 bp가 NULL이거나 size가 0인 경우
    if (bp == NULL){
        return mm_malloc(size);
    }
    if (size == 0){
        mm_free(bp);
        return NULL;
    }


    new_size = ALIGN(size + DSIZE); //헤더 풋터 포함 8배수 정렬
    cur_size = GET_SIZE(HDRP(bp));

    // case 1. 현재 블록을 그대로 쓸 수 있는 경우
    if (cur_size >= new_size){
        // 스플릿 과정. 헤더+풋터+페이로드 해서 16바이트 이상 남으면 자른다.
        if ((cur_size - new_size) >= (2 * DSIZE)){
            PUT(HDRP(bp), PACK(new_size, 1));
            PUT(FTRP(bp), PACK(new_size, 1));
            PUT(HDRP(NEXT_BLKP(bp)), PACK((cur_size - new_size), 0));
            PUT(FTRP(NEXT_BLKP(bp)), PACK((cur_size - new_size), 0));

            // 기존의 다음 블록이 free면 지금 split한 블록이랑 병합
            coalesce(NEXT_BLKP(bp));
        }

        else{
            PUT(HDRP(bp), PACK(cur_size, 1));
            PUT(FTRP(bp), PACK(cur_size, 1));
        }

    return bp;
    }

    // case 2. next_block이 free block인 경우
    if (GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0){
        size_t sum_size;

        sum_size = cur_size + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        // 현재 블록과 다음 블록을 합친 크기가 요구 크기보다 큰지 검사
        if (sum_size >= new_size){
            int next_was_freep = (next_freep == NEXT_BLKP(bp));
            // next-fit을 위한 변수. free block인 다음 블록을 합치는 과정에서
            // next_freep의 위치도 바꿔줘야 하기 때문
            if ((sum_size - new_size) >= (2 * DSIZE)){
                PUT(HDRP(bp), PACK(new_size, 1));
                PUT(FTRP(bp), PACK(new_size, 1));

                PUT(HDRP(NEXT_BLKP(bp)), PACK((sum_size - new_size), 0));
                PUT(FTRP(NEXT_BLKP(bp)), PACK((sum_size - new_size), 0));

                // 스플릿 이후 새롭게 생긴 free block과 그 다음 block도 free block인
                // 케이스를 고려해서 coalescing 함
                coalesce(NEXT_BLKP(bp));
                
                // 스플릿 했으면 새롭게 생긴 블록 다음 블록이 다시 free block이므로
                // 다음 블록으로 next_freep를 옮겨 준다.
                if (next_was_freep){
                    next_freep = NEXT_BLKP(bp);
                }

            }
            else {
            PUT(HDRP(bp), PACK(sum_size, 1));
            PUT(FTRP(bp), PACK(sum_size, 1));
            
                if (next_was_freep){
                    next_freep = NEXT_BLKP(bp);
                }

            }
            return bp;
        }
    }

    // case 3. 현재 블록이 heap의 마지막 블록인가?
    if (GET_SIZE(HDRP(NEXT_BLKP(bp))) == 0){
        newbp = extend_heap((new_size - cur_size) / WSIZE);

        // 힙 확장에 성공했을 경우에만 진행
        if (newbp !=NULL){

            // next fit 동작시키기 위한 변수
            // newbp가 bp와 합쳐진 후 next_freep가 allocated block 내부에 남지 않도록
            int next_was_freep = (next_freep == newbp);
            new_size = cur_size + GET_SIZE(HDRP(newbp));

            PUT(HDRP(bp), PACK(new_size, 1));
            PUT(FTRP(bp), PACK(new_size, 1));

            if (next_was_freep){
                next_freep = NEXT_BLKP(bp);
            }
            return bp;
        }
    }   

    // // case NULL. prev_block, next_block이 free block인 경우
    // if (GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0 && GET_ALLOC(HDRP(PREV_BLKP(bp))) == 0){
    //     size_t sum_size;
    //     size_t prev_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
    //     size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
    //     void *old_prevp;
    //     void *old_nextp;

    //     sum_size = prev_size + cur_size + next_size;

    //     if (sum_size >= new_size && (cur_size + prev_size) < new_size){
    //         old_prevp = PREV_BLKP(bp);
    //         old_nextp = NEXT_BLKP(bp);
    //         copy_size = cur_size - DSIZE;

    //         int prev_was_freep = (next_freep == old_prevp);
    //         int next_was_freep = (next_freep == old_nextp);

    //         memmove(old_prevp, bp, copy_size);

    //         if ((sum_size - new_size) >= (2 * DSIZE)){
    //             PUT(HDRP(old_prevp), PACK(new_size, 1));
    //             PUT(FTRP(old_prevp), PACK(new_size, 1));

    //             PUT(HDRP(NEXT_BLKP(old_prevp)), PACK((sum_size - new_size), 0));
    //             PUT(FTRP(NEXT_BLKP(old_prevp)), PACK((sum_size - new_size), 0));

    //             coalesce(NEXT_BLKP(old_prevp));

    //             if (prev_was_freep || next_was_freep){
    //                 next_freep = NEXT_BLKP(old_prevp);
    //             }
    //         }

    //         else{
    //             PUT(HDRP(old_prevp), PACK(sum_size, 1));
    //             PUT(FTRP(old_prevp), PACK(sum_size, 1));

    //             if (prev_was_freep || next_was_freep){
    //                 next_freep = NEXT_BLKP(old_prevp);
    //             }
    //         }

    //         return old_prevp;
    //     }
    // } 

    // case 4. prev_block이 free block인 경우
    if (GET_ALLOC(HDRP(PREV_BLKP(bp))) == 0){
        size_t sum_size;
        void *old_prevp;
        sum_size = cur_size + GET_SIZE(HDRP(PREV_BLKP(bp)));

        if (sum_size >= new_size){
            old_prevp = PREV_BLKP(bp);
            copy_size = cur_size - DSIZE;

            int prev_was_freep = (next_freep == old_prevp);

            memmove(old_prevp, bp, copy_size);

            if ((sum_size - new_size) >= (2 * DSIZE)){
                PUT(HDRP(old_prevp), PACK(new_size, 1));
                PUT(FTRP(old_prevp), PACK(new_size, 1));

                PUT(HDRP(NEXT_BLKP(old_prevp)), PACK((sum_size - new_size), 0));
                PUT(FTRP(NEXT_BLKP(old_prevp)), PACK((sum_size - new_size), 0));

                coalesce(NEXT_BLKP(old_prevp));

                if (prev_was_freep){
                    next_freep = NEXT_BLKP(old_prevp);
                }
            }

            else{
                PUT(HDRP(old_prevp), PACK(sum_size, 1));
                PUT(FTRP(old_prevp), PACK(sum_size, 1));
            
                if (prev_was_freep){
                    next_freep = NEXT_BLKP(old_prevp);
                }
            }

            return old_prevp;
        }
    }

    // case 5. 현재 블록 재활용 불가. 새 블록 할당 후 데이터 복사
    newbp = mm_malloc(size);
    if (newbp == NULL)
        return NULL;
    copy_size = GET_SIZE(HDRP(bp)) - DSIZE;
    if (size < copy_size)
        copy_size = size;
    memcpy(newbp, bp, copy_size);
    mm_free(bp);
    return newbp;
}

static void *coalesce(void *bp) // 인접한 free block들 병합하기
{
    int prev_alloc;
    int next_alloc;
    size_t size;

    prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    size = GET_SIZE(HDRP(bp)); 

    if (prev_alloc == 1 && next_alloc == 1){
        return bp;
    }
    else if (prev_alloc == 1 && next_alloc == 0){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        
        // 병합 후 next_frep의 위치를 bp로 옮기는 역할
        if (bp <= next_freep && next_freep < NEXT_BLKP(bp)) {
            next_freep = bp;
        }

        return bp;
    }
    else if (prev_alloc == 0 && next_alloc == 1){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);

        if (bp <= next_freep && next_freep < NEXT_BLKP(bp)){
            next_freep = bp;
        }

        return bp;
    }
    else{
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

        if (bp <= next_freep && next_freep < NEXT_BLKP(bp)){
            next_freep = bp;
        }
        return bp;
    }
}

// static void *find_fit(size_t size) // first_fit 방식
// {
//     char *bp;
//     bp = NEXT_BLKP(heap_listp);

//     while (GET_SIZE(HDRP(bp)) != 0){
//         if (GET_ALLOC(HDRP(bp)) == 0 && GET_SIZE(HDRP(bp)) >= size){
//             return bp;
//         }
//         bp = NEXT_BLKP(bp);
//     }
//     return NULL;
// }

// static void *find_fit(size_t size) // next_fit 방식
// {
//     char *bp;
//     char *last_searchp;

//     last_searchp = next_freep;
//     /*마지막으로 탐색한 위치 기억하기 위해서,
//      * 에필로그까지 탐색하고 처음부터 이 위치까지 다 탐색하려고*/

//     bp = next_freep;
//     // next_freep = NEXT_BLKP(heap_listp)고 이게 프롤로그 블록 이후 첫번째 실제 block

//     // 에필로그 헤더의 크기는 0이니까 에필로그 헤더 전까지 순회
//     while (GET_SIZE(HDRP(bp)) != 0){
//         if (GET_ALLOC(HDRP(bp)) == 0 && GET_SIZE(HDRP(bp)) >= size){
//             return bp;
//         }
//         bp = NEXT_BLKP(bp);
//     }

//     // 끝까지 다 돌고 처음부터 last_searchp까지 순회
//     bp = NEXT_BLKP(heap_listp);
//     while (bp != last_searchp){ 
//         if (GET_ALLOC(HDRP(bp)) == 0 && GET_SIZE(HDRP(bp)) >= size){
//             return bp;
//         }
//         bp = NEXT_BLKP(bp);
//     }
    
//     return NULL;

// }

// static void *find_fit(size_t size) // best_fit 방식
// {
//     char *bp;
//     char *best_bp;
//     size_t cur_size;
//     int fit_count = 0; // bounded_best-fit

//     bp = NEXT_BLKP(heap_listp);
//     // 첫 번째 가용 블록의 bp

//     best_bp = NULL;

//     // 에필로그 헤더의 크기는 0이니까 에필로그 헤더 전까지 순회
//     while (GET_SIZE(HDRP(bp)) != 0){
//         cur_size = GET_SIZE(HDRP(bp));
//         if (GET_ALLOC(HDRP(bp)) == 0 && cur_size >= size){
//             fit_count++;

//             if (best_bp == NULL){
//                 best_bp = bp;
//             }

//             else if (cur_size < GET_SIZE(HDRP(best_bp))){
//                 best_bp = bp;
//             }

//             if (cur_size == size){ //맞는 블록을 찾으면 전부 순회하지 말고 바로 반환
//                 return bp;
//             }

//             if (fit_count == 1){ // 이게 1이면 사실상 first-fit과 다를게 없음
//                 return best_bp;
//             }
//         }
//         bp = NEXT_BLKP(bp);
//     }

//     return best_bp;
// }

static void *find_fit(size_t size) // hybrid_fit (next_fit + first_fit)
{
    char *bp;
    char *last_searchp;
    char *first_unchecked; // first_fit에서 순회가 끝난 다음 블록
    size_t cur_size;
    int block_count = 0; // first_fit에서 순회할 블록의 갯수

    bp = NEXT_BLKP(heap_listp); // 첫 번째 가용 블록의 bp

    // 에필로그 헤더의 크기는 0이니까 에필로그 헤더 전까지 순회
    while (GET_SIZE(HDRP(bp)) != 0){ 
        cur_size = GET_SIZE(HDRP(bp));
        if (GET_ALLOC(HDRP(bp)) == 0 && cur_size >= size){
            return bp;
        }
        block_count ++;

        if (block_count == 3){
            first_unchecked = NEXT_BLKP(bp);
            break;
        }

        bp = NEXT_BLKP(bp);
    }

    if (block_count < 3){
        return NULL;
    }

    last_searchp = next_freep;
    bp = next_freep;

    while (GET_SIZE(HDRP(bp)) != 0){
        if (GET_ALLOC(HDRP(bp)) == 0 && GET_SIZE(HDRP(bp)) >= size){
            return bp;
        }
        bp = NEXT_BLKP(bp);
    }
    if (next_freep < first_unchecked){
        return NULL;
    }

    bp = first_unchecked;
    
    while (bp != last_searchp){
        if (GET_ALLOC(HDRP(bp)) == 0 && GET_SIZE(HDRP(bp)) >= size){
            return bp;
        }
        bp = NEXT_BLKP(bp);
    }
    return NULL;
}

static void place(char *bp, size_t size)
{
    size_t cur_size;
    cur_size = GET_SIZE(HDRP(bp));

    /* free block을 쪼갠 뒤 남는 공간이 최소의 크기를 갖는지 검사하는 조건
     * 헤더 4바이트, 풋터 4바이트를 제외하면 payload는 최소 8바이트를 가져야
     * 8의 배수인 16을 만족한다. 4바이트면 총 12바이트라 8의 배수로 정렬이 안됨
     */
    if ((cur_size - size) >= (2 * DSIZE)){
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
        PUT(HDRP(NEXT_BLKP(bp)), PACK((cur_size - size), 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK((cur_size - size), 0));
    }
    else{
        PUT(HDRP(bp), PACK(cur_size, 1));
        PUT(FTRP(bp), PACK(cur_size, 1));
    }

    /* 이 과정이 find_fit에 있었을 경우, place()하면서 split하면서
     * find_fit 시점의 bp와 place() 이후의 bp 위치가 달라질 수 있다.
     * 그렇기 때문에 place가 split을 한 후 next_freep의 위치를 옮겨준다.
     */
    next_freep = NEXT_BLKP(bp);
}