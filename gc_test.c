//frama-c-gui -wp -wp-rte -wp-prover -wp-no-simpl script,alt-ergo,cvc4,cvc4-ce,z3 test.c
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#define CLEAN               (-1)
#define INVALID             (-2)
#define N_PHY_BLOCKS        150
#define N_LOG_BLOCKS        100
#define N_PAGE              100
#define LRU_SIZE            100
#define MAX_WEAR_CNT        1000
#define DATA_MIGRATION_FREQ 100

int tau = 20;
bool clean[N_PHY_BLOCKS] = {true};
bool is_valid_page[N_PHY_BLOCKS][N_PAGE];

int erase_count_index[MAX_WEAR_CNT] = {N_PHY_BLOCKS};
int index_2_physical[N_PHY_BLOCKS];
int spare_area[N_PHY_BLOCKS][N_PAGE];
int disk[N_PHY_BLOCKS][N_PAGE];
int l_to_p[N_LOG_BLOCKS][N_PAGE];

int l_act_block_index_p, h_act_block_index_p;
int l_act_page_p, h_act_page_p;
int clean_counter;

int chance_index_p = 0;
int cache[LRU_SIZE] = {-1};
bool chance_arr[LRU_SIZE] = {false};
/*@
    // F:A->B is a "bijection" if and only if F is
    //  1. injective(one-to-one): F(x) == F(y) ==> x == y, and
    //  2. surjective(onto): forall b belongs to B, there is some a belongs to A such that F(a) = b
    predicate bijection{L}(int i2p[N_PHY_BLOCKS]) =
        (\forall integer x, y; i2p[x] == i2p[y] ==> x == y) &&
        (\forall integer b; 0 <= b < N_PHY_BLOCKS ==> (\exists integer a; 0 <= a < N_PHY_BLOCKS ==> i2p[a] == b));
    
    logic integer count_clean(integer i) = 
        i <= 0 ? 0 :
            (clean[i-1] == true ? count_clean(i-1) + 1 : count_clean(i-1));
    
    logic integer count_efficiency(integer block, integer page) = 
        page<=0 ? 0 :
            (is_valid_page[block][page-1] == false ? count_efficiency(block, page-1) + 1 : count_efficiency(block, page-1));
    
    predicate monotone_decreasing{L}(int eci[MAX_WEAR_CNT]) = 
        (\forall integer i, j; 0 <= i < j < MAX_WEAR_CNT ==> 0 <= eci[i] <= eci[j] <= N_PHY_BLOCKS);
    
    logic integer count_max_wear(integer size, integer max) = 
        size <= 0 ? max :
            (erase_count_index[size-1] == N_PHY_BLOCKS ? count_max_wear(size-1, size-1) : count_max_wear(size-1, max));
    
    //lemma calc_wear{L}: \forall integer i; 0 < i <= MAX_WEAR_CNT ==> -1 <= count_max_wear(i, -1) < i;
*/
/*
    lemma same_count{L1,L2}:
        \forall integer size; 0<= size < N_PHY_BLOCKS ==>
            (\forall integer i; 0 <= i < size ==> \at(clean[i],L1) == \at(clean[i],L2)) ==>
                count_clean{L1}(size) == count_clean{L2}(size);
    
    lemma same_but_one{L1,L2}:
        \forall integer size; 0 <= size < N_PHY_BLOCKS ==>
            \forall integer i_diff; 0 <= i_diff < size ==>
                (\forall integer i; 0 <= i < size && i != i_diff ==> \at(clean[i],L1) == \at(clean[i],L2)) && \at(clean[i_diff],L1) == false && \at(clean[i_diff],L2) == true ==>
                    count_clean{L1}(size) + 1 == count_clean{L2}(size);
*/

/*
    // Correctness: 1. data of l_to_p won't be changed
    //              2. 0 <= max_wear - min_wear <= tau
    
    Correctness: 0 <= max_wear - min_wear <= tau
        1. 保證erase_count_index[ 0 .. (MAX_WEAR_CNT - 1) ]為單調遞減的陣列
        2. 用logic integer找出max wear & min wear
*/


/*@
    
    requires 0 <= tau <= MAX_WEAR_CNT;
    requires bijection(index_2_physical);
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    requires 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS && l_act_block_index_p != h_act_block_index_p;
    requires clean[index_2_physical[l_act_block_index_p]] == false && clean[index_2_physical[h_act_block_index_p]] == false;
    requires clean_counter == count_clean(N_PHY_BLOCKS);
    requires 1 <= clean_counter <= N_PHY_BLOCKS - 2;
    
    assigns tau;
    assigns clean[0 .. (N_PHY_BLOCKS - 1)];
    assigns is_valid_page[0 .. (N_PHY_BLOCKS - 1)][0 .. (N_PAGE - 1)];
    assigns erase_count_index[0 .. (MAX_WEAR_CNT - 1)];
    assigns index_2_physical[0 .. (N_PHY_BLOCKS - 1)];
    assigns spare_area[0 .. (N_PHY_BLOCKS - 1)][0 .. (N_PAGE - 1)];
    assigns disk[0 .. (N_PHY_BLOCKS - 1)][0 .. (N_PAGE - 1)];
    assigns l_to_p[0 .. (N_LOG_BLOCKS - 1)][0 .. (N_PAGE - 1)];
    assigns l_act_block_index_p, h_act_block_index_p;
    assigns l_act_page_p, h_act_page_p;
    assigns clean_counter;
    
*/
void write(int d, int lb, int lp){
    /* ghost
        int count = 0;
        
        /@
            loop invariant 0 <= i <= N_PHY_BLOCKS;
            loop invariant 0 <= count <= i;
            loop invariant count + count_clean(i) == i;
            loop assigns count, i;
            loop variant N_PHY_BLOCKS - i;
        @/
        for(int i=0; i < N_PHY_BLOCKS; i++){
            if (clean[i]==false) {
                count++;
            }
        }
        /@ assert count + count_clean(N_PHY_BLOCKS) == N_PHY_BLOCKS; @/
        */
    write_helper(d, lb, lp);
    
    update_lru(lb, lp);
    
    if (clean_counter < 2) {
        //@ assert clean_counter == count_clean(N_PHY_BLOCKS) == 1;
        gc();
    }
}

/*@
    requires 0 <= tau <= MAX_WEAR_CNT;
    requires bijection(index_2_physical);
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    requires 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS && l_act_block_index_p != h_act_block_index_p;
    requires clean[index_2_physical[l_act_block_index_p]] == false && clean[index_2_physical[h_act_block_index_p]] == false;
    requires clean_counter == count_clean(N_PHY_BLOCKS);
    requires 1 <= clean_counter < 2;
    
    assigns tau;
    assigns clean[0 .. (N_PHY_BLOCKS - 1)];
    assigns is_valid_page[0 .. (N_PHY_BLOCKS - 1)][0 .. (N_PAGE - 1)];
    assigns erase_count_index[0 .. (MAX_WEAR_CNT - 1)];
    assigns index_2_physical[0 .. (N_PHY_BLOCKS - 1)];
    assigns spare_area[0 .. (N_PHY_BLOCKS - 1)][0 .. (N_PAGE - 1)];
    assigns disk[0 .. (N_PHY_BLOCKS - 1)][0 .. (N_PAGE - 1)];
    assigns l_to_p[0 .. (N_LOG_BLOCKS - 1)][0 .. (N_PAGE - 1)];
    assigns l_act_block_index_p, h_act_block_index_p;
    assigns l_act_page_p, h_act_page_p;
    assigns clean_counter;
    
    ensures 0 <= tau <= MAX_WEAR_CNT;
    ensures bijection(index_2_physical);
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    ensures \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    ensures 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS && l_act_block_index_p != h_act_block_index_p;
    ensures clean[index_2_physical[l_act_block_index_p]] == false && clean[index_2_physical[h_act_block_index_p]] == false;
    ensures clean_counter == count_clean(N_PHY_BLOCKS);
    ensures 2 <= clean_counter <= N_PHY_BLOCKS - 2;
*/
void gc(void){
    /*@
        loop invariant 0 <= tau <= MAX_WEAR_CNT;
        loop invariant bijection(index_2_physical);
        loop invariant \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
        loop invariant \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
        loop invariant 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS && l_act_block_index_p != h_act_block_index_p;
        loop invariant clean[index_2_physical[l_act_block_index_p]] == false && clean[index_2_physical[h_act_block_index_p]] == false;
        loop invariant clean_counter == count_clean(N_PHY_BLOCKS);
        loop invariant 1 <= clean_counter <= N_PHY_BLOCKS - 2;
        
        loop assigns tau;
        loop assigns clean[0 .. (N_PHY_BLOCKS - 1)];
        loop assigns is_valid_page[0 .. (N_PHY_BLOCKS - 1)][0 .. (N_PAGE - 1)];
        loop assigns erase_count_index[0 .. (MAX_WEAR_CNT - 1)];
        loop assigns index_2_physical[0 .. (N_PHY_BLOCKS - 1)];
        loop assigns spare_area[0 .. (N_PHY_BLOCKS - 1)][0 .. (N_PAGE - 1)];
        loop assigns disk[0 .. (N_PHY_BLOCKS - 1)][0 .. (N_PAGE - 1)];
        loop assigns l_to_p[0 .. (N_LOG_BLOCKS - 1)][0 .. (N_PAGE - 1)];
        loop assigns l_act_block_index_p, h_act_block_index_p;
        loop assigns l_act_page_p, h_act_page_p;
        loop assigns clean_counter;
    */
    while(clean_counter < 2){
        /* 
         * 1. clean_counter < N_PHY_BLOCKS - 2  <==> 存在clean為false的block (非active pointer)
         * 
         * cnt1 : # of dirty blocks without high & low active block index pointer
         * cnt2 : # of all dirty blocks, which means that cnt2 + clean_counter == N_PHY_BLOCKS
         * 
         * ==> if cnt1 > 0, then there must exist at least one dirty block, which is not high or low active block index pointer
         * cnt1 > 0
         * \exists integer i; 0 <= i < N_PHY_BLOCKS && i != index_2_physical[l_act_block_index_p] && i != index_2_physical[h_act_block_index_p] && clean[i] == false
         * 
         * 
         * 2. index_2_physical與clean為false的block之間的關聯
         * \exists integer i; 0 <= i < N_PHY_BLOCKS && i != index_2_physical[l_act_block_index_p] && i != index_2_physical[h_act_block_index_p] && clean[i] == false
         * \exists integer i; 0 <= i < N_PHY_BLOCKS && i != l_act_block_index_p                   && i!= h_act_block_index_p                    && clean[index_2_physical[i]] == false
         * 
         */
        
        /*@ ghost int cnt1 = 0; */ 
        /*@ ghost int cnt2 = 0; */
        /*@ ghost
        /@
            loop invariant 0 <= i <= N_PHY_BLOCKS;
            loop invariant bijection(index_2_physical);
            loop invariant 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS && l_act_block_index_p != h_act_block_index_p;
            loop invariant clean[index_2_physical[l_act_block_index_p]] == false && clean[index_2_physical[h_act_block_index_p]] == false;
            loop invariant l_act_block_index_p == \at(l_act_block_index_p, LoopEntry) && h_act_block_index_p == \at(h_act_block_index_p, LoopEntry);
            loop invariant \forall integer i; 0 <= i < N_PHY_BLOCKS ==> index_2_physical[i] == \at(index_2_physical[i], LoopEntry);
            
            loop invariant i <= index_2_physical[l_act_block_index_p] && i <= index_2_physical[h_act_block_index_p] ==> 0 <= cnt1 == cnt2 <= i;
            loop invariant (i <= index_2_physical[l_act_block_index_p] && i > index_2_physical[h_act_block_index_p]) || 
                           (i > index_2_physical[l_act_block_index_p] && i <= index_2_physical[h_act_block_index_p]) ==> 0 <= cnt1 + 1 == cnt2 <= i;
            loop invariant i > index_2_physical[l_act_block_index_p] && i > index_2_physical[h_act_block_index_p] ==> 0 <= cnt1 + 2 == cnt2 <= i;
            loop invariant 0 <= cnt1 <= cnt2 <= i;
            loop invariant cnt2 + count_clean(i) == i;
            loop invariant 0 < cnt1 ==> \exists integer i; 0 <= i < N_PHY_BLOCKS && i != index_2_physical[l_act_block_index_p] && i != index_2_physical[h_act_block_index_p] && clean[i] == false;
            
            //loop invariant \exists integer i; 0 <= i < N_PHY_BLOCKS && i != index_2_physical[l_act_block_index_p] && i != index_2_physical[h_act_block_index_p] && clean[i] == false
            //           ==> \exists integer j; 0 <= j < N_PHY_BLOCKS && j != l_act_block_index_p && j != h_act_block_index_p && clean[index_2_physical[j]] == false;
            //loop invariant 0 < cnt1 ==> \exists integer i; 0 <= i < N_PHY_BLOCKS && i != index_2_physical[l_act_block_index_p] && i != index_2_physical[h_act_block_index_p] && clean[i] == false
            //                        ==> \exists integer j; 0 <= j < N_PHY_BLOCKS && j != l_act_block_index_p && j != h_act_block_index_p && clean[index_2_physical[j]] == false;
            
            loop assigns i, cnt1, cnt2;
            loop variant N_PHY_BLOCKS - i;
        @/
        for (int i=0; i < N_PHY_BLOCKS; i++) {
            if (clean[i]==false) {
                if(i != index_2_physical[l_act_block_index_p] && i != index_2_physical[h_act_block_index_p]) {
                    cnt1++;
                }
                cnt2++;
                /@ assert 0 < cnt1 ==> \exists integer i; 0 <= i < N_PHY_BLOCKS && i != index_2_physical[l_act_block_index_p] && i != index_2_physical[h_act_block_index_p] && clean[i] == false; @/
                // assert \exists integer i; 0 <= i < N_PHY_BLOCKS && i != index_2_physical[l_act_block_index_p] && i != index_2_physical[h_act_block_index_p] && clean[i] == false
                //      ==> \exists integer j; 0 <= j < N_PHY_BLOCKS && j != l_act_block_index_p && j != h_act_block_index_p && clean[index_2_physical[j]] == false && (\exists integer j; 0 <= j < N_PHY_BLOCKS && index_2_physical[j] == i); @/
                // assert 0 < cnt1 ==> \exists integer i; 0 <= i < N_PHY_BLOCKS && i != index_2_physical[l_act_block_index_p] && i != index_2_physical[h_act_block_index_p] && clean[i] == false
                //                   ==> \exists integer j; 0 <= j < N_PHY_BLOCKS && j != l_act_block_index_p && j != h_act_block_index_p && clean[index_2_physical[j]] == false; @/
            }
        }
        */
        
        /* predicate bijection{L}(int i2p[N_PHY_BLOCKS]) =
         *      (\forall integer x, y; i2p[x] == i2p[y] ==> x == y) &&
         *      (\forall integer b; 0 <= b < N_PHY_BLOCKS ==> (\exists integer a; 0 <= a < N_PHY_BLOCKS ==> i2p[a] == b));
         * 
         * i2p:I->J
         *  存在b屬於B使得 clean[b] == false
         *  因F為bijection, 所以存在a屬於A使得 i2p[a] == j
         *  故存在clean[i2p[a]] == false
         * 
         * assert \exists integer j; 0 <= j < N_PHY_BLOCKS && j != index_2_physical[l_act_block_index_p] && j != index_2_physical[h_act_block_index_p] && clean[j] == false;
         * assert \exists integer i; 0 <= i < N_PHY_BLOCKS && i != l_act_block_index_p                   && i != h_act_block_index_p                   && clean[index_2_physical[i]] == false;
         */
         
        /* Problem:
         * (v) 存在b屬於B使得 clean[b] == false [line 265]
         * (v) 存在b屬於B使得 clean[b] == false ==> 存在a屬於A使得 i2p[a]==b && clean[i2p[a]] == clean[b] == false [line 274-276]
         * (X) 存在b屬於B使得 clean[b] == false &&  存在a屬於A使得 i2p[a]==b [line 278-280]
         * (/) 存在a屬於A使得 clean[i2p[a]] == clean[b] == false [line 283]
         */
        
        //@ assert \exists integer j; 0 <= j < N_PHY_BLOCKS && j != index_2_physical[l_act_block_index_p] && j != index_2_physical[h_act_block_index_p] && clean[j] == false;
        
        /*@ assert \forall integer j; 0 <= j < N_PHY_BLOCKS
               ==> \exists integer i; 0 <= i < N_PHY_BLOCKS ==> index_2_physical[i] == j;
        */
        /*@ assert \exists integer j; 0 <= j < N_PHY_BLOCKS && j != index_2_physical[l_act_block_index_p] && j != index_2_physical[h_act_block_index_p] && clean[j] == false
               ==> \exists integer i; 0 <= i < N_PHY_BLOCKS && index_2_physical[i] == j;
        */
        
        /*@ assert \exists integer j; 0 <= j < N_PHY_BLOCKS && j != index_2_physical[l_act_block_index_p] && j != index_2_physical[h_act_block_index_p] && clean[j] == false
               ==> \exists integer i; 0 <= i < N_PHY_BLOCKS && index_2_physical[i] == j && i != l_act_block_index_p && i != h_act_block_index_p && clean[index_2_physical[i]] == false;
        */
        
        /*@ assert \exists integer i, j; 0 <= j < N_PHY_BLOCKS && j != index_2_physical[l_act_block_index_p] && j != index_2_physical[h_act_block_index_p] && clean[j] == false &&
                   0 <= i < N_PHY_BLOCKS && index_2_physical[i] == j;
        */
        
        //@ assert \exists integer i; 0 <= i < N_PHY_BLOCKS && i != l_act_block_index_p && i != h_act_block_index_p && clean[index_2_physical[i]] == false;
        
        int idx = get_most_clean_efficient_block_idx();
        /*if( min_wear() + tau <= get_erase_count_by_idx(idx) ){
       	    data_migration();
        }*/
        erase_block_data(idx);
    }
}

/*@
    requires bijection(index_2_physical);
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS && l_act_block_index_p != h_act_block_index_p;
    requires clean[index_2_physical[l_act_block_index_p]] == false && clean[index_2_physical[h_act_block_index_p]] == false;
    requires clean_counter == count_clean(N_PHY_BLOCKS);
    requires 0 <= clean_counter < 2;
    requires \exists integer i; 0 <= i < N_PHY_BLOCKS && i != index_2_physical[l_act_block_index_p] && i != index_2_physical[h_act_block_index_p] && clean[i] == false;
    requires \exists integer i; 0 <= i < N_PHY_BLOCKS && i != index_2_physical[l_act_block_index_p] && i != index_2_physical[h_act_block_index_p] && clean[i] == false
         ==> \exists integer i; 0 <= i < N_PHY_BLOCKS && i != l_act_block_index_p && i != h_act_block_index_p && clean[index_2_physical[i]] == false;
    requires \exists integer i; 0 <= i < N_PHY_BLOCKS && i != l_act_block_index_p && i != h_act_block_index_p && clean[index_2_physical[i]] == false;
    
    assigns \nothing;
    
    ensures 0 <= \result < N_PHY_BLOCKS;
    //ensures \result != index_2_physical[l_act_block_index_p] && \result != index_2_physical[h_act_block_index_p] && clean[\result]  == false;
    ensures \result != l_act_block_index_p && \result != h_act_block_index_p && clean[index_2_physical[\result]]  == false;
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS && i != h_act_block_index_p && i != l_act_block_index_p && clean[index_2_physical[i]]  == false
        ==> count_efficiency(index_2_physical[\result], N_PAGE) >= count_efficiency(index_2_physical[i], N_PAGE);
*/
int get_most_clean_efficient_block_idx(void){
    //@ assert \exists integer i; 0 <= i < N_PHY_BLOCKS && i != l_act_block_index_p && i != h_act_block_index_p && clean[index_2_physical[i]] == false;
    int most_efficient_idx = 0;
    int n_of_max_invalid_or_clean_page = 0;
    /*@ ghost bool start = false; */
    
    /*@
        loop invariant 0 <= idx <= N_PHY_BLOCKS;
        loop invariant \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
        
        loop invariant 0 <= most_efficient_idx < N_PHY_BLOCKS;
        loop invariant 0 <= n_of_max_invalid_or_clean_page <= N_PAGE;
        
        loop invariant !start ==> most_efficient_idx == 0 && n_of_max_invalid_or_clean_page == 0;
        //loop invariant !start ==> \forall integer i; 0 <= i < idx ==> i == index_2_physical[h_act_block_index_p] || i == index_2_physical[l_act_block_index_p] || clean[i] == true;
        loop invariant !start ==> \forall integer i; 0 <= i < idx ==> i==h_act_block_index_p || i==l_act_block_index_p || clean[index_2_physical[i]] == true;
        
        loop invariant start ==> n_of_max_invalid_or_clean_page == count_efficiency(index_2_physical[most_efficient_idx], N_PAGE);
        loop invariant start ==> most_efficient_idx != l_act_block_index_p && most_efficient_idx != h_act_block_index_p && clean[index_2_physical[most_efficient_idx]]  == false;
        
        loop invariant \forall integer i; 0 <= i < idx && i != l_act_block_index_p && i != h_act_block_index_p && clean[index_2_physical[i]]  == false &&
             most_efficient_idx != l_act_block_index_p && most_efficient_idx != h_act_block_index_p && clean[index_2_physical[most_efficient_idx]]  == false ==>
                count_efficiency(index_2_physical[most_efficient_idx], N_PAGE) >= count_efficiency(index_2_physical[i], N_PAGE);
        
        loop assigns idx, most_efficient_idx, n_of_max_invalid_or_clean_page, start;
        loop variant N_PHY_BLOCKS - idx;
    */
    for(int idx = 0 ; idx < N_PHY_BLOCKS ; idx++){
        int pid = index_2_physical[idx];
        int n_of_invalid_or_clean_page = 0;

        if (idx == h_act_block_index_p || idx == l_act_block_index_p) {
            continue;
        }
        if (clean[pid] == true) continue;
        
        /*@
            loop invariant 0 <= pp <= N_PAGE;
            loop invariant 0 <= n_of_invalid_or_clean_page == count_efficiency(pid, pp) <= pp;
            loop assigns pp, n_of_invalid_or_clean_page;
            loop variant N_PAGE - pp;
        */
        for(int pp = 0 ; pp < N_PAGE ; pp++){
            if(is_valid_page[pid][pp] == false){
                n_of_invalid_or_clean_page += 1;
            }
        }
        
        if(n_of_invalid_or_clean_page >= n_of_max_invalid_or_clean_page){
            most_efficient_idx = idx;
            n_of_max_invalid_or_clean_page = n_of_invalid_or_clean_page;
        }
        /*@ ghost start = true; */
    }
    
    return most_efficient_idx;
}

/*@
    requires  0 <= idx < N_PHY_BLOCKS;
    requires idx != l_act_block_index_p && idx != h_act_block_index_p;
    requires clean[index_2_physical[idx]] == false;
    
    requires 0 <= tau <= MAX_WEAR_CNT;
    requires bijection(index_2_physical);
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    requires 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS && l_act_block_index_p != h_act_block_index_p;
    requires clean[index_2_physical[l_act_block_index_p]] == false && clean[index_2_physical[h_act_block_index_p]] == false;
    requires clean_counter == count_clean(N_PHY_BLOCKS);
    requires 1 <= clean_counter < N_PHY_BLOCKS - 2;
    
    assigns tau;
    assigns clean[0 .. (N_PHY_BLOCKS - 1)];
    assigns is_valid_page[0 .. (N_PHY_BLOCKS - 1)][0 .. (N_PAGE - 1)];
    assigns erase_count_index[0 .. (MAX_WEAR_CNT - 1)];
    assigns index_2_physical[0 .. (N_PHY_BLOCKS - 1)];
    assigns spare_area[0 .. (N_PHY_BLOCKS -1)][0 .. (N_PAGE - 1)];
    assigns disk[0 .. (N_PHY_BLOCKS - 1)][0 .. (N_PAGE - 1)];
    assigns l_to_p[0 .. (N_LOG_BLOCKS - 1)][0 .. (N_PAGE - 1)];
    assigns l_act_block_index_p, h_act_block_index_p;
    assigns l_act_page_p, h_act_page_p;
    assigns clean_counter;
    
    ensures 0 <= tau <= MAX_WEAR_CNT;
    ensures bijection(index_2_physical);
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    ensures \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    ensures 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS && l_act_block_index_p != h_act_block_index_p;
    ensures clean[index_2_physical[l_act_block_index_p]] == false && clean[index_2_physical[h_act_block_index_p]] == false;
    ensures \forall integer i; 0<=i<N_PAGE ==> is_valid_page[\old(index_2_physical[idx])][i] == false;
    ensures clean_counter == count_clean(N_PHY_BLOCKS);
    ensures 1 < clean_counter <= N_PHY_BLOCKS - 2;
        
    ensures clean[\old(index_2_physical[idx])] == true;
    ensures clean_counter == \old(clean_counter)+1;
*/
void erase_block_data(int idx){
    int pb = index_2_physical[idx];
    int pp = 0;
    
    //copy valid page to another space and set the page to clean
    /*@
        loop invariant 0 <= pp <= N_PAGE;
        loop invariant \forall integer i; 0<=i<pp ==> is_valid_page[pb][i] == false;
        loop assigns pp, is_valid_page[pb][0..(N_PAGE - 1)];
        loop variant N_PAGE - pp;
    */
    while(pp != N_PAGE){
        if(is_valid_page[pb][pp]){
            int la = _read_spare_area(pb, pp); //get logical addr
            // assert 0 <= la <= N_LOG_BLOCKS * N_PAGE;
            int lb = la / N_PAGE; //get logical block id
            int lp = la % N_PAGE;   //get logical page offset
            //write_helper(_r(pb,pp), lb, lp);
        }
        is_valid_page[pb][pp] = false;
        pp++;
    }

    _erase_block(pb);
    clean[pb] = true;
    clean_counter += 1;
    /*@ ghost
    /@ 
        loop invariant 0 <= i <= index_2_physical[idx] ;
        loop invariant count_clean(i) == count_clean{Pre}(i);
        loop assigns i;
        loop variant index_2_physical[idx] - i ;
    @/
    for(int i = 0; i < index_2_physical[idx]; i++);
    
    /@
        loop invariant index_2_physical[idx] < i <= N_PHY_BLOCKS;
        loop invariant count_clean(i) == 1 + count_clean{Pre}(i);
        loop assigns i;
        loop variant N_PHY_BLOCKS - i ;
    @/
    for(int i = index_2_physical[idx]+1; i < N_PHY_BLOCKS; i++);
    */
    // count_clean(N_PHY_BLOCKS) == 1 + count_clean{Pre}(N_PHY_BLOCKS);
    
    
    // assert \at(clean_counter,Pre) == N_PHY_BLOCKS - 3 ==> (\forall integer i; 0 <= i < N_PHY_BLOCKS && i != l_act_block_index_p && i != h_act_block_index_p ==> clean[index_2_physical[i]] == true);
    // assert clean_counter == N_PHY_BLOCKS - 2 ==> (\forall integer i; 0 <= i < N_PHY_BLOCKS && i != l_act_block_index_p && i != h_act_block_index_p ==> clean[index_2_physical[i]] == true);
    // assert clean_counter == N_PHY_BLOCKS - 2 ==> (\forall integer i; 0 <= i < N_PHY_BLOCKS && index_2_physical[i] != index_2_physical[l_act_block_index_p] && index_2_physical[i] != index_2_physical[h_act_block_index_p] ==> clean[i] == true);
    // assert clean_counter < N_PHY_BLOCKS - 2 ==> \exists integer i; 0 <= i < N_PHY_BLOCKS && i != l_act_block_index_p && i != h_act_block_index_p && clean[index_2_physical[i]] != true;
    
    //update erase count for pb
    increase_erase_count(idx);
}

/*@
    requires 0 <= idx < N_PHY_BLOCKS;
    requires idx != l_act_block_index_p && idx != h_act_block_index_p;
    
    requires bijection(index_2_physical);
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    requires 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS && l_act_block_index_p != h_act_block_index_p;
    requires clean[index_2_physical[l_act_block_index_p]] == false && clean[index_2_physical[h_act_block_index_p]] == false;
    
    
    assigns erase_count_index[0 .. (MAX_WEAR_CNT - 1)];
    assigns index_2_physical[0 .. (N_PHY_BLOCKS - 1)];
    assigns l_act_block_index_p, h_act_block_index_p;
    
    ensures bijection(index_2_physical);
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    ensures \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    ensures 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS && l_act_block_index_p != h_act_block_index_p;
    /// the clean information of pointers is still the same although the pointer changed
    ensures clean[index_2_physical[l_act_block_index_p]] == false && clean[index_2_physical[h_act_block_index_p]] == false;
    
    /// nothing change in index_2_physical excluding index_2_physical[idx] & index_2_physical[last_block_idx]
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS && i != idx && index_2_physical[i] != \old(index_2_physical[idx]) ==>
        index_2_physical[i] == \old(index_2_physical[i]);
    
    /// idx will be pointer only if last_block_idx is pointer
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS && index_2_physical[i] == \old(index_2_physical[idx]) ==>
        (i == \old(l_act_block_index_p) && idx == l_act_block_index_p) ||
        (i == \old(h_act_block_index_p) && idx == h_act_block_index_p) ||
        (idx != l_act_block_index_p && idx != h_act_block_index_p);
    
    /// the two pointers are still mapped to the same physical block whether last_block_idx is pointer or not
    ensures index_2_physical[l_act_block_index_p] == \old(index_2_physical[l_act_block_index_p]);
    ensures index_2_physical[h_act_block_index_p] == \old(index_2_physical[h_act_block_index_p]);
*/
void increase_erase_count(int idx){
    //swap the index_2_physical[idx] with the element which has teh same erase count
    int erase_count = get_erase_count_by_idx(idx); //get the erase cnt of idx
    if (erase_count == MAX_WEAR_CNT) return; // Q: Do what when erase_count == MAX_WEAR_CNT?
    int last_block_idx = erase_count_index[erase_count] - 1;    //get the ending index which has the same erase cnt
    L1:
    // let active block pointer stay with the same blockID
    if(last_block_idx == h_act_block_index_p){
        h_act_block_index_p = idx;
    }
    if(last_block_idx == l_act_block_index_p){
        l_act_block_index_p = idx;
    }
    //@ assert \forall integer i; 0 <= i < N_PHY_BLOCKS ==> index_2_physical[i] == \at(index_2_physical[i], Pre);
    int temp = index_2_physical[idx];
    index_2_physical[idx] = index_2_physical[last_block_idx];
    index_2_physical[last_block_idx] = temp;
    //@ assert \forall integer i; 0 <= i < N_PHY_BLOCKS && i != idx && i != last_block_idx ==> index_2_physical[i] == \at(index_2_physical[i], Pre);
    //@ assert index_2_physical[idx] == \at(index_2_physical[last_block_idx], L1);
    //@ assert index_2_physical[last_block_idx] == \at(index_2_physical[idx], L1);
    
    // update the erase_count boundary index
    erase_count_index[erase_count] -= 1;
}

/*@
    requires 0 <= idx < N_PHY_BLOCKS;
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    
    assigns \nothing;
    
    ensures 0 <= \result <= MAX_WEAR_CNT;
    ensures 0 <= \result < MAX_WEAR_CNT ==> 1 <= erase_count_index[\result] <= N_PHY_BLOCKS;
    ensures \result == MAX_WEAR_CNT ==> \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] <= idx;
*/
int get_erase_count_by_idx(int idx){

    /*@
        loop invariant 0 <= cur <=  MAX_WEAR_CNT;
        loop invariant \forall integer i; 0 <= i < cur ==> erase_count_index[i] <= idx;
        loop assigns cur;
        loop variant MAX_WEAR_CNT - cur;
    */
    for(int cur = 0 ; cur < MAX_WEAR_CNT ; cur++){
        if (erase_count_index[cur] > idx){
            return cur;
        }
    }
    return MAX_WEAR_CNT;
}

/*@
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    assigns \nothing;
    ensures -1 <= \result < MAX_WEAR_CNT;
    ensures 0 <= \result < MAX_WEAR_CNT ==>
            erase_count_index[\result] != 0 &&
            \forall integer i; 0 <= i < \result ==> erase_count_index[i] == 0;
    ensures \result == -1 ==>
            \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] == 0;
 */
int min_wear(void){
    /*@
        loop invariant 0 <= i <= MAX_WEAR_CNT;
        loop invariant \forall integer j; 0 <= j < i ==> erase_count_index[j] == 0;
        loop assigns i;
        loop variant MAX_WEAR_CNT - i;
    */
    for (int i = 0 ;  i< MAX_WEAR_CNT ; i++){
        if(erase_count_index[i] != 0){
            return i;
        }
    }
    return -1;    //hapens when rejuvenator just start, for all i, erase_count_index[i] == N_PHY_BLOCKS
}

/* Problem:
 * 如果沒有582、583行，會fail
 * 
 */
/*@
    requires \forall integer i; 0 <= i < 20 ==> 0 <= erase_count_index[i] < N_PHY_BLOCKS;
    requires \forall integer i; 20 <= i < MAX_WEAR_CNT ==> erase_count_index[i] == N_PHY_BLOCKS;
    
    requires monotone_decreasing(erase_count_index);
    
    assigns \nothing;
    
    ensures monotone_decreasing(erase_count_index);
    ensures -1 <= \result < MAX_WEAR_CNT;
    ensures \result == -1 ==>
            \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] < N_PHY_BLOCKS;
    ensures 0 <= \result < MAX_WEAR_CNT ==>
            \forall integer i; 0 <= i < \result ==> erase_count_index[i] < N_PHY_BLOCKS &&
            \forall integer i; \result <= i < MAX_WEAR_CNT ==> erase_count_index[i] == N_PHY_BLOCKS;
    ensures \result == count_max_wear(MAX_WEAR_CNT, -1);
 */
int max_wear (void) {
    int result = -1;

    /*@
        loop invariant 0 <= i <= MAX_WEAR_CNT;
        loop invariant -1 <= result < MAX_WEAR_CNT;
        loop invariant monotone_decreasing(erase_count_index);
        loop invariant result == -1 ==> \forall integer j; 0 <= j < i ==> erase_count_index[j] < N_PHY_BLOCKS;
        loop invariant result != -1 ==> \forall integer j; 0 <= j < result ==> erase_count_index[j] != N_PHY_BLOCKS;
        loop invariant result != -1 ==> \forall integer j; result <= j < i ==> erase_count_index[j] == N_PHY_BLOCKS;
        
        loop invariant -1 <= count_max_wear(i, -1) < i;
        loop invariant result == -1 ==> count_max_wear(i, -1) == -1;
        loop invariant result != -1 ==> count_max_wear(i, -1) == result;
        
        loop assigns i, result;
        loop variant MAX_WEAR_CNT - i;
    */
    for(int i = 0 ; i < MAX_WEAR_CNT ; i++){
        if (erase_count_index[i] == N_PHY_BLOCKS) {
            if (result == -1){
                result = i;
            }
        }
    }
    return result;
}