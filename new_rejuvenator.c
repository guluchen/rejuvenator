/************************************************************************************
 * modified rejuvenator in C                                                        *
 * Hong Wen, Chen                                                                   *
 * 2022/07/29                                                                       *
 * page addressing                                                                  *
 * We store logical address info in spare area in this version                      *
 * We replace phy_page_info array with is_valid_page array.                         *
 * / valid                                                                          *
 * \ not valid / clean  (active block is not clean)                                 *
 *             \ invalid                                                            *
 * Rule of triggering GC is modified to l_clean_cnt+h_clean_cnt < 1 in this version *
 * In this version, we maintain the invariant of l_clean_cnt + h_clean_cnt >= 1     *
 ***********************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#define CLEAN               (-1)
#define INVALID             (-2)
#define N_PHY_BLOCKS        150     //number of physical blocks in disk
#define N_LOG_BLOCKS        100     //number of logical blocks in disk (< N_PHY_BLOCKS)
#define N_PAGE              100     //number of page in a block
#define LRU_SIZE            100     //lru cache size by page
#define MAX_WEAR_CNT        1000    //user defined constant
#define DATA_MIGRATION_FREQ 100     //data migration frequency: after doing i times of GC, do data_migration once

void write(int d, int lb, int lp);
int isHotPage(int lb, int lp);
void write_helper(int d, int lb, int lp);
void update_lru(int lb, int lp);
void write_2_higher_number_list(int d, int lb, int lp);
void gc(void);
void _w(int d, int pb, int pg);
void write_2_lower_number_list(int d, int lb, int lp);
int find_vb(int start_idx, int end_idx);
void _erase_block(int pb);
void erase_block_data(int idx);
int get_most_clean_efficient_block_idx(void);
int read(int lb, int lp);
int get_erase_count_by_idx(int idx);
int min_wear(void);
int max_wear(void);
int _r(int pb, int pg);
void increase_erase_count(int idx);
int find_and_update(int la);
void replace_and_update(int la);
void _write_spare_area(int pb, int pp, int la);
int _read_spare_area(int pb, int pp);
void data_migration(void);

int tau = 20;                                           // max_wear <= min_wear + tau
bool clean[N_PHY_BLOCKS] = {true};                      // clean bit for physical block; phy block ID -> bool
bool is_valid_page[N_PHY_BLOCKS][N_PAGE];               // show whether this page is valid or not: [pb][pp] -> bool
int erase_count_index[MAX_WEAR_CNT] = {N_PHY_BLOCKS};   // erase count separator; erase count i -> end index of erase cnt=i in index_2_physical array
int index_2_physical[N_PHY_BLOCKS];                     // main list of rejuvenator; index -> phy block ID
int l_to_p[N_LOG_BLOCKS][N_PAGE];                       // page table: [lb][lp] -> physical address(by page addressing); initialize to -1
int spare_area[N_PHY_BLOCKS][N_PAGE];                   // to simulate spare area in the disk: [pb][pp] -> logical address ; this is called "phy_page_info_disk_api" in pseudo code
int disk[N_PHY_BLOCKS][N_PAGE];                         // to simulate physical disk: [pb][pp] -> data in the page

int h_act_block_index_p;    // high active block pointer based on index_2_physical
int h_act_page_p;           // high active page pointer for physical page
int l_act_block_index_p;    // low active block pointer based on index_2_physical
int l_act_page_p;           // low active page pointer for physical page
int clean_counter;

bool chance_arr[LRU_SIZE] = {false};    // second chance array of lru cache
int cache[LRU_SIZE] = {-1};             // cache of hot/cold data seperation, each element store logical address(page addressing)
int chance_index_p = 0;                 // index pointer in chance_arr
 
//TODO: update tau?
// when to invoke data migration?

/*@ // predicate & logci integer
    predicate in_L_range (integer lb, integer lp) =
        0 <= lb < N_LOG_BLOCKS && 0 <= lp < N_PAGE;

    predicate in_P_range (integer pb, integer pp) =
        0 <= pb < N_PHY_BLOCKS && 0 <= pp < N_PAGE;
    
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
    
*/
/*
    lemma same_count {L1,L2}:
        \forall integer size; 0<= size < N_PHY_BLOCKS ==>
            (\forall integer i; 0 <= i < size ==> \at(clean[i],L1) == \at(clean[i],L2)) ==>
                count_clean{L1}(size) == count_clean{L2}(size);
    
    lemma same_but_one {L1,L2}:
        \forall integer size; 0 <= size < N_PHY_BLOCKS ==>
            \forall integer i_diff; 0 <= i_diff < size ==>
                (\forall integer i; 0 <= i < size && i != i_diff ==> \at(clean[i],L1) == \at(clean[i],L2))
                && \at(clean[i_diff],L1) == false && \at(clean[i_diff],L2) == true ==>
                    count_clean{L1}(size) + 1 == count_clean{L2}(size);
*/
/*@ ghost
    int logical_disk[N_LOG_BLOCKS][N_PAGE];    // logical disk array
    int ghost_erase_count[N_PHY_BLOCKS];       // ghost erase count array
*/


/* TODO

1. logical_disk - record data in logical array
(1). Never write to a non-clean page
(2). Informal: the disk behaves likes an array indexed with logical address
            requires \forall lb1, lp1 . Ghost_disk[lb1][lp1] = Disk[l2p_b(lb1)][l2p_p(lp1)]
            ensures \forall lb1, lp1 . Ghost_disk[lb1][lp1] = Disk[l2p_b(lb1)][l2p_p(lp1)]
            ensures Ghost_disk[lb][lp] = d
            ensures \forall lb1, lp1 .  lb1!=lb \/ lp1!=lp.  \uf0e8 Ghost_disk[lb1][lp1] = \old(Ghost_disk[lb1][lp1])
            ensures Ghost_disk[lb][lp] = d = Disk[l2p_b(lb)][ l2p_p(lp)])

2. ghost_erase_count - record erase count of each block
(1). initial at initialize()
            ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> ghost_erase_count[i] == 0;
(2). invoke only at API, _erase_block(pb)
            ghost_erase_count[pb]++;
(3). ensure [max_wear - min_wear <= tau] in any function
            ensures \exists integer min, max;
                (0 <= min < N_PHY_BLOCKS && 0 <= max < N_PHY_BLOCKS) && 
                (\forall integer i; 0 <= i < N_PHY_BLOCKS ==> ghost_erase_count[min] <= ghost_erase_count[i]) &&
                (\forall integer i; 0 <= i < N_PHY_BLOCKS ==> ghost_erase_count[max] >= ghost_erase_count[i]) &&
                (ghost_erase_count[max] - ghost_erase_count[min] <= tau);

*/

/*@
    // tau
    ensures 0 <= tau <= MAX_WEAR_CNT;
    
    // clean
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS && i != h_act_block_index_p && i != l_act_block_index_p ==> clean[i] == true;
    ensures clean[index_2_physical[l_act_block_index_p]] == clean[index_2_physical[h_act_block_index_p]] == false;
    
    // is_valid_page
    ensures \forall integer i,j; 0 <= i < N_LOG_BLOCKS &&  0 <= j < N_PAGE ==> is_valid_page[i][j] == false;
    
    // erase_block_index
    ensures 0 <= index_2_physical[h_act_block_index_p] < N_PHY_BLOCKS;
    ensures \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] == N_PHY_BLOCKS;
    
    // index_2_physical
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    ensures bijection(index_2_physical);
    
    // spare_area
    ensures \forall integer i,j; 0 <= i < N_LOG_BLOCKS &&  0 <= j < N_PAGE ==> spare_area[i][j] == -1;
    
    // l_to_p
    ensures \forall integer i,j; 0 <= i < N_LOG_BLOCKS &&  0 <= j < N_PAGE ==> l_to_p[i][j] == -1;
    
    // spare_area
    ensures \forall integer i,j; 0 <= i < N_PHY_BLOCKS &&  0 <= j < N_PAGE ==> spare_area[i][j] == -1;
    
    // disk
    ensures \forall integer i,j; 0 <= i < N_PHY_BLOCKS &&  0 <= j < N_PAGE ==> disk[i][j] == -1;
    
    // logical_disk
    ensures \forall integer i,j; 0 <= i < N_PHY_BLOCKS &&  0 <= j < N_PAGE ==> logical_disk[i][j] == -1;
    
    // active pointer
    ensures in_P_range(h_act_block_index_p, h_act_page_p);
    ensures in_P_range(l_act_block_index_p, l_act_page_p);
    
    // clean_counter
    ensures clean_counter == N_PHY_BLOCKS - 2;
    ensures clean_counter == count_clean(N_PHY_BLOCKS);
    ensures count_clean(N_PHY_BLOCKS / 2) == N_PHY_BLOCKS/2 - 1;
    
    // cache
    ensures \forall integer i; 0 <= i < LRU_SIZE ==> chance_arr[i] == false;
    ensures \forall integer i; 0 <= i < LRU_SIZE ==> cache[i] == -1;
    ensures chance_index_p == 0;
 */
void initialize (void) {
    tau = 20;
    clean_counter = 0;
    
    // initialize clean, clean_counter, index_2_physical
    /*@
        loop invariant 0 <= i <= N_PHY_BLOCKS;
        loop invariant \forall integer j; 0 <= j < i ==> clean[j] ==true;
        loop invariant 0 <= i <= N_PHY_BLOCKS ==> clean_counter == count_clean(i);
        loop assigns i, clean_counter;
    */
    for(int i = 0 ; i < N_PHY_BLOCKS ; i++){
        clean[i] = true;
        clean_counter += 1;
        index_2_physical[i] = i;
    }
    
    // initialize l_to_p
    for(int i = 0 ; i < N_LOG_BLOCKS ; i++){
        for(int j = 0 ; j < N_PAGE ; j++){
            l_to_p[i][j] = -1;
        }
    }
    
    // initialize is_valid_page, spare_area
    for(int i = 0 ; i < N_PHY_BLOCKS ; i++){
        for(int j = 0 ; j < N_PAGE ; j++){
            is_valid_page[i][j] = false;
            spare_area[i][j] = -1;
        }
    }
    
    // initialize erase_block_index
    for (int i = 0 ; i < MAX_WEAR_CNT; i++) {
        erase_count_index[i] = N_PHY_BLOCKS;
    }
    
    // initialize active pointer
    h_act_block_index_p = N_PHY_BLOCKS / 2; //initialize h_act_block_index_p
    l_act_block_index_p = 0;                //initialoze l_act_block_index_p
    h_act_page_p = 0;
    l_act_page_p = 0;

    // active block is not a clean block
    clean[index_2_physical[l_act_block_index_p]] = false;
    clean[index_2_physical[h_act_block_index_p]] = false;
    clean_counter -= 2;
    
    // initialize cache
    for (int i = 0; i < LRU_SIZE; i++) {
        chance_arr[i] = false;
        cache[i] = -1;
    }
    chance_index_p = 0;
}

int read (int lb, int lp) {
    int pa = l_to_p[lb][lp];    //lookup page table to get physical address (page addressing)
    assert(pa != -1);   //when pa == -1, logical address map to nothing => error
    int pb = pa / N_PAGE;   //get physical block
    int pp = pa % N_PAGE;   //get physical page
    assert(is_valid_page[pb][pp] != false); //check if it is a vlaid page
    int data = _r(pb, pp);  //use api to read from the address
    return data;
}

int _r (int pb, int pg) {
   return disk[pb][pg];
}


/*@
/// Require ///
    /// General Constraints ///
    requires \exists integer i, j; 0 <= i < N_PHY_BLOCKS && 0 <= j < N_PHY_BLOCKS && i != j && clean[index_2_physical[i]] == clean[index_2_physical[j]] == true;
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    requires bijection(index_2_physical);
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE
        ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS * N_PAGE || l_to_p[i][j] == -1;
    requires 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS;
    requires 0 <= l_act_page_p < N_PAGE && 0 <= h_act_page_p < N_PAGE;
    requires clean[index_2_physical[l_act_block_index_p]] == clean[index_2_physical[h_act_block_index_p]] == false;
    requires 2 <= clean_counter == count_clean(N_PHY_BLOCKS) <= N_PHY_BLOCKS - 2;
    requires \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE && logical_disk[i][j] != -1 && (i != lb && j != lp)
         ==> logical_disk[i][j] == disk[l_to_p[i][j] / N_PAGE][l_to_p[i][j] % N_PAGE];
    requires 0 <= chance_index_p < LRU_SIZE;
    
    /// User > valid logical address ///
    requires 0 <= lb < N_LOG_BLOCKS && 0 <= lp < N_PAGE;
    
    /// System > active pointers point to empty pages ///
    requires \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE
        ==> l_to_p[i][j] != index_2_physical[l_act_block_index_p] * N_PAGE + l_act_page_p
         && l_to_p[i][j] != index_2_physical[h_act_block_index_p] * N_PAGE + h_act_page_p;
    requires disk[index_2_physical[l_act_block_index_p]][l_act_page_p]
          == disk[index_2_physical[h_act_block_index_p]][h_act_page_p] == -1;
    
/// Ensure ////
    /// General Constraints ///
    ensures \exists integer i, j; 0 <= i < N_PHY_BLOCKS && 0 <= j < N_PHY_BLOCKS && i != j
         && clean[index_2_physical[i]] == clean[index_2_physical[j]] == true;
    ensures \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    ensures bijection(index_2_physical);
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    ensures \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE
        ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS * N_PAGE || l_to_p[i][j] == -1;
    ensures 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS;
    ensures 0 <= l_act_page_p < N_PAGE && 0 <= h_act_page_p < N_PAGE;
    ensures clean[index_2_physical[l_act_block_index_p]] == clean[index_2_physical[h_act_block_index_p]] == false;
    ensures 2 <= clean_counter == count_clean(N_PHY_BLOCKS) <= N_PHY_BLOCKS - 2;
    ensures \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE && logical_disk[i][j] != -1 && (i != lb && j != lp)
        ==> \old(logical_disk[i][j]) == logical_disk[i][j] == disk[l_to_p[i][j] / N_PAGE][l_to_p[i][j] % N_PAGE];
    ensures 0 <= chance_index_p < LRU_SIZE;
    
    /// User > valid mapping & equivalent data ///
    ensures 0 <= l_to_p[lb][lp] < N_PHY_BLOCKS * N_PAGE;
    ensures d == logical_disk[lb][lp]
              == disk[l_to_p[lb][lp] / N_PAGE][l_to_p[lb][lp] % N_PAGE];
    
    /// System > active pointers point to empty pages & valid page ///
    ensures \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE
        ==> logical_disk[i][j] != index_2_physical[l_act_block_index_p] * N_PAGE + l_act_page_p
         && logical_disk[i][j] != index_2_physical[h_act_block_index_p] * N_PAGE + h_act_page_p;
    ensures disk[index_2_physical[l_act_block_index_p]][l_act_page_p]
         == disk[index_2_physical[h_act_block_index_p]][h_act_page_p] == -1;
    ensures \old(l_to_p[lb][lp]) != -1
        ==> is_valid_page[\old(l_to_p[lb][lp]) / N_PAGE][\old(l_to_p[lb][lp]) % N_PAGE] == false;
    ensures is_valid_page[l_to_p[lb][lp] / N_PAGE][l_to_p[lb][lp] % N_PAGE] == true;
    
/// Assign ///
    
*/
void write (int d, int lb, int lp) {
    /*@ ghost
         logical_disk[lb][lp] = d;
    */
    write_helper(d, lb, lp);
    
    update_lru(lb, lp);
    
     //if there is no clean block then GC
    if (clean_counter < 2){
        gc();
    }
}

/*
*   Write helper function
*    :param d:  data
*    :param lb: logical block address
*    :param lp: logical page number
*/
/*
NEED TO DO:
Requires: variable_in_range();  //use predicate

Requires: forall lb1, lp1 . Ghost_disk[lb1][lp1] = Disk[l2p_b(lb1) ][ l2p_p(lp1)]
Ensures: forall lb1, lp1 . Ghost_disk[lb1][lp1] = Disk[l2p_b(lb1) ][ l2p_p(lp1)]
Ensures: Ghost_disk[lb][lp] =d  //done
Ensures: forall lb1, lp1 .  lb1!=lb \/ lp1!=lp.   Ghost_disk[lb1][lp1] = \old(Ghost_disk[lb1][lp1])    //maybe use behavior to divide write_2_high/low

Ensures: Ghost_disk[lb][lp] =d = Disk[l2p_b(lb) ][ l2p_p(lp)]
*/
/*@
/// Require ///
    /// General Constraints ///
    requires \exists integer i, j; 0 <= i < N_PHY_BLOCKS && 0 <=j < N_PHY_BLOCKS && i != j
          && clean[index_2_physical[i]] == clean[index_2_physical[j]] == true;
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    requires bijection(index_2_physical);
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE
        ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS * N_PAGE || l_to_p[i][j] == -1;
    requires 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS;
    requires 0 <= l_act_page_p < N_PAGE && 0 <= h_act_page_p < N_PAGE;
    requires clean[index_2_physical[l_act_block_index_p]] == clean[index_2_physical[h_act_block_index_p]] == false;
    requires 2 <= clean_counter == count_clean(N_PHY_BLOCKS) <= N_PHY_BLOCKS - 2;
    requires \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE && logical_disk[i][j] != -1 && (i != lb && j != lp)
        ==> logical_disk[i][j] == disk[l_to_p[i][j] / N_PAGE][l_to_p[i][j] % N_PAGE];
    
    /// User > valid logical address ///
    requires 0 <= lb < N_LOG_BLOCKS && 0 <= lp < N_PAGE;
    requires d == logical_disk[lb][lp];
    
    /// System > active pointers point to empty pages ///
    requires \forall integer lb, lp; 0 <= lb < N_LOG_BLOCKS && 0 <= lp < N_PAGE
        ==> l_to_p[lb][lp] != index_2_physical[l_act_block_index_p] * N_PAGE + l_act_page_p
         && l_to_p[lb][lp] != index_2_physical[h_act_block_index_p] * N_PAGE + h_act_page_p;
    requires disk[index_2_physical[l_act_block_index_p]][l_act_page_p]
          == disk[index_2_physical[h_act_block_index_p]][h_act_page_p] == -1;
    
/// Ensure ////
    /// General Constraints ///
    ensures \exists integer i; 0 <= i < N_PHY_BLOCKS && clean[index_2_physical[i]] == true;
    ensures \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    ensures bijection(index_2_physical);
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    ensures \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE
        ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS * N_PAGE || l_to_p[i][j] == -1;
    ensures 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS;
    ensures 0 <= l_act_page_p < N_PAGE && 0 <= h_act_page_p < N_PAGE;
    ensures clean[index_2_physical[l_act_block_index_p]] == clean[index_2_physical[h_act_block_index_p]] == false;
    ensures 1 <= clean_counter == count_clean(N_PHY_BLOCKS) <= N_PHY_BLOCKS - 2;
    ensures \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE && logical_disk[i][j] != -1 && (i != lb && j != lp)
        ==> \old(logical_disk[i][j]) == logical_disk[i][j] == disk[l_to_p[i][j] / N_PAGE][l_to_p[i][j] % N_PAGE];
    
    /// User > valid mapping & equivalent data ///
    ensures 0 <= l_to_p[lb][lp] < N_PHY_BLOCKS * N_PAGE;
    ensures d == logical_disk[lb][lp]
              == disk[l_to_p[lb][lp] / N_PAGE][l_to_p[lb][lp] % N_PAGE];
    
    /// System > active pointers point to empty pages & valid page ///
    ensures \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE
        ==> logical_disk[i][j] != index_2_physical[l_act_block_index_p] * N_PAGE + l_act_page_p
         && logical_disk[i][j] != index_2_physical[h_act_block_index_p] * N_PAGE + h_act_page_p;
    ensures disk[index_2_physical[l_act_block_index_p]][l_act_page_p]
         == disk[index_2_physical[h_act_block_index_p]][h_act_page_p] == -1;
    ensures \old(l_to_p[lb][lp]) != -1
        ==> is_valid_page[\old(l_to_p[lb][lp]) / N_PAGE][\old(l_to_p[lb][lp]) % N_PAGE] == false;
    ensures is_valid_page[l_to_p[lb][lp] / N_PAGE][l_to_p[lb][lp] % N_PAGE] == true;
    
/// Assign ///
    
*/
void write_helper (int d, int lb, int lp) {
    //check the logical address is hot or cold
    int isHot = isHotPage(lb, lp);
    //@ assert logical_disk[lb][lp] == d;
    if(isHot != 1) { //cold data
        write_2_higher_number_list(d, lb, lp);
    } else {          //hot data
        write_2_lower_number_list(d, lb, lp);
    }
}

/*
*   Helper function of writting to higher num list
*    :param d: data
*    :param lb: logical block address
*    :param lp: logical page number
*/
/*
245    assigns is_valid_page[ l_to_p[lb][lp] / N_PAGE ][ l_to_p[lb][lp] % N_PAGE ];
246    assigns disk[(l_to_p[lb][lp] / N_PAGE)][(l_to_p[lb][lp] % N_PAGE)];
247    assigns spare_area[ l_to_p[lb][lp] / N_PAGE ][ l_to_p[lb][lp] % N_PAGE ];
    assigns clean[index_2_physical[h_act_block_index_p]];
*/
/*@
/// Require ///
    /// General Constraints ///
    requires \exists integer i, j; 0 <= i < N_PHY_BLOCKS && 0 <=j < N_PHY_BLOCKS && i != j
          && clean[index_2_physical[i]] == clean[index_2_physical[j]] == true;
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    requires bijection(index_2_physical);
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE
         ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS * N_PAGE || l_to_p[i][j] == -1;
    requires 0 <= h_act_block_index_p < N_PHY_BLOCKS;
    requires 0 <= h_act_page_p < N_PAGE;
    requires clean[index_2_physical[h_act_block_index_p]] == false;
    requires 2 <= clean_counter == count_clean(N_PHY_BLOCKS) <= N_PHY_BLOCKS - 2;
    requires \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE && logical_disk[i][j] != -1 && (i != lb && j != lp)
         ==> logical_disk[i][j] == disk[l_to_p[i][j] / N_PAGE][l_to_p[i][j] % N_PAGE];
    
    /// User > valid logical address && equivalent data ///
    requires 0 <= lb < N_LOG_BLOCKS && 0 <= lp < N_PAGE;
    requires d == logical_disk[lb][lp];
    
    /// System > active pointers point to empty pages ///
    requires \forall integer lb, lp; 0 <= lb < N_LOG_BLOCKS && 0 <= lp < N_PAGE
         ==> l_to_p[lb][lp] != index_2_physical[h_act_block_index_p] * N_PAGE + h_act_page_p;
    requires disk[index_2_physical[h_act_block_index_p]][h_act_page_p] == -1;
    requires d == logical_disk[lb][lp];
    
/// Ensure ////
    /// General Constraints ///
    ensures \exists integer i; 0 <= i < N_PHY_BLOCKS && clean[index_2_physical[i]] == true;
    ensures \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    ensures bijection(index_2_physical);
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    ensures \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE
        ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS * N_PAGE || l_to_p[i][j] == -1;
    ensures 0 <= h_act_block_index_p < N_PHY_BLOCKS;
    ensures 0 <= h_act_page_p < N_PAGE;
    ensures clean[index_2_physical[h_act_block_index_p]] == false;
    ensures 1 <= clean_counter == count_clean(N_PHY_BLOCKS) <= N_PHY_BLOCKS - 2;
    ensures \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE && logical_disk[i][j] != -1 && (i != lb && j != lp)
        ==> \old(logical_disk[i][j]) == logical_disk[i][j] == disk[l_to_p[i][j] / N_PAGE][l_to_p[i][j] % N_PAGE];
    
    /// User > valid mapping & equivalent data ///
    ensures l_to_p[lb][lp] == index_2_physical[\old(h_act_block_index_p)] * N_PAGE + \old(h_act_page_p);
    ensures d == logical_disk[lb][lp]
              == disk[l_to_p[lb][lp] / N_PAGE][l_to_p[lb][lp] % N_PAGE];
    
    /// System > active pointers point to empty page & valid page ///
    ensures \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE
        ==> logical_disk[i][j] != index_2_physical[h_act_block_index_p] * N_PAGE + h_act_page_p;
    ensures disk[index_2_physical[h_act_block_index_p]][h_act_page_p] == -1;
    ensures \old(l_to_p[lb][lp]) != -1
        ==> is_valid_page[\old(l_to_p[lb][lp]) / N_PAGE][\old(l_to_p[lb][lp]) % N_PAGE] == false;
    ensures is_valid_page[l_to_p[lb][lp] / N_PAGE][l_to_p[lb][lp] % N_PAGE] == true;
    behavior block_full:
        assumes h_act_page_p + 1 == N_PAGE;
        ensures \forall integer i; 0 <= i < N_PHY_BLOCKS && i != index_2_physical[h_act_block_index_p]
            ==> clean[i] == \old(clean[i]);
        ensures clean[index_2_physical[h_act_block_index_p]] == false;
        ensures h_act_page_p == 0;
    behavior block_not_full:
        assumes h_act_page_p + 1 != N_PAGE;
        ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> clean[i] == \old(clean[i]);
        ensures h_act_page_p == \old(h_act_page_p) + 1;
    complete behaviors;
    disjoint behaviors;
    
    //ensures spare_area[ l_to_p[lb][lp] / N_PAGE ][ l_to_p[lb][lp] % N_PAGE ] == lb * N_PAGE + lp;
    
/// Assign ///
    
*/
void write_2_higher_number_list (int d, int lb, int lp) {
    //invalidate old physical address
    if(l_to_p[lb][lp] != -1) {
        //clean previous physical address from the same logical address
        int old_addr = l_to_p[lb][lp];
        int opb = old_addr / N_PAGE; //turn page addressing to block id
        int opp = old_addr % N_PAGE; //turn page addressing to page offset
        is_valid_page[opb][opp] = false;
    }
    //@ assert l_to_p[lb][lp] != -1 ==> is_valid_page[l_to_p[lb][lp] / N_PAGE][l_to_p[lb][lp] % N_PAGE] == false;
    
    //write data to new physical address
    int pb = index_2_physical[h_act_block_index_p]; //get active block ID
    int pp = h_act_page_p;  //get active page
    _w(d, pb, pp);  //write data
    //@ assert d == disk[pb][pp] == logical_disk[lb][lp];
    
    //update logical to physical mapping
    int new_addr = pb * N_PAGE + pp;
    l_to_p[lb][lp] = new_addr;
    is_valid_page[pb][pp] = true;
    int log_addr = lb * N_PAGE + lp;
    _write_spare_area(pb, pp, log_addr);
    //@ assert l_to_p[lb][lp] == index_2_physical[h_act_block_index_p] * N_PAGE + h_act_page_p;
    //@ assert is_valid_page[l_to_p[lb][lp] / N_PAGE][l_to_p[lb][lp] % N_PAGE] == true;
    
    //update active pointer value
   if(h_act_page_p + 1 == N_PAGE) {
        // page + 1 == block size
        h_act_page_p = 0;
        
        // move the high pointer to the next clean block
        // firstly search a clean block from the head of the high number list
        h_act_block_index_p = N_PHY_BLOCKS / 2;
        /*@
            loop invariant N_PHY_BLOCKS / 2 <= h_act_block_index_p <= N_PHY_BLOCKS;
            loop invariant \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
            loop invariant \forall integer i; N_PHY_BLOCKS / 2 <= i < h_act_block_index_p ==> clean[index_2_physical[i]] == false;
            loop assigns h_act_block_index_p;
            loop variant N_PHY_BLOCKS - h_act_block_index_p;
        */
        while(h_act_block_index_p < N_PHY_BLOCKS){
            if (clean[index_2_physical[h_act_block_index_p]] == true) break; // find a clean block
            h_act_block_index_p ++;
        }
        
        //if no clean blocks in higher number list, then search clean block in lower number list
        if(h_act_block_index_p == N_PHY_BLOCKS){
            h_act_block_index_p = 0;
            /*@
                loop invariant 0 <= h_act_block_index_p < N_PHY_BLOCKS / 2;
                loop invariant \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
                loop invariant \forall integer i; 0 <= i < h_act_block_index_p ==> clean[index_2_physical[i]] == false;
                loop assigns h_act_block_index_p;
                loop variant N_PHY_BLOCKS / 2 - h_act_block_index_p;
            */
            while (h_act_block_index_p < N_PHY_BLOCKS / 2){
                if (clean[index_2_physical[h_act_block_index_p]] == true) break; // find a clean block
                h_act_block_index_p++;
                if (h_act_block_index_p == N_PHY_BLOCKS / 2) break; // out of range ???
            }
        }
        ///!ERROR: if (h_act_block_index_p == N_PHY_BLOCKS / 2) no any clean block
        //@ assert \exists integer i, j; 0 <= i < N_PHY_BLOCKS && 0 <=j < N_PHY_BLOCKS && i != j && clean[index_2_physical[i]] == clean[index_2_physical[i]] == true ==> h_act_block_index_p != N_PHY_BLOCKS / 2;
        //@ assert clean[index_2_physical[h_act_block_index_p]] == true;
        
        clean[index_2_physical[h_act_block_index_p]] = false;
        clean_counter -= 1;
        //@ assert clean_counter == count_clean(N_PHY_BLOCKS);
    }else{
        // page + 1 < block size
        h_act_page_p +=1;
    }
}

/*
*   Helper function of writting to lower num list
*    :param d: data
*    :param lb: logical block address
*    :param lp: logical page number
*/
/*@
/// Require ///
    /// General Constraints ///
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    requires bijection(index_2_physical);
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE
        ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS * N_PAGE || l_to_p[i][j] == -1;
    requires 0 <= l_act_block_index_p < N_PHY_BLOCKS;
    requires 0 <= l_act_page_p < N_PAGE;
    requires clean[index_2_physical[l_act_block_index_p]] == false;
    requires 2 <= clean_counter == count_clean(N_PHY_BLOCKS) <= N_PHY_BLOCKS - 2;
    requires \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE && logical_disk[i][j] != -1 && (i != lb && j != lp)
        ==> logical_disk[i][j] == disk[l_to_p[i][j] / N_PAGE][l_to_p[i][j] % N_PAGE];
    
    /// User > valid logical address && equivalent data ///
    requires 0 <= lb < N_LOG_BLOCKS && 0 <= lp < N_PAGE;
    requires d == logical_disk[lb][lp];
    
    /// System > active pointers point to empty pages ///
    requires \forall integer lb, lp; 0 <= lb < N_LOG_BLOCKS && 0 <= lp < N_PAGE
        ==> l_to_p[lb][lp] != index_2_physical[l_act_block_index_p] * N_PAGE + l_act_page_p;
    requires disk[index_2_physical[l_act_block_index_p]][l_act_page_p] == -1;
    requires d == logical_disk[lb][lp];
    
/// Ensure ////
    /// General Constraints ///
    ensures \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    ensures bijection(index_2_physical);
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    ensures \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE
        ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS * N_PAGE || l_to_p[i][j] == -1;
    ensures 0 <= l_act_block_index_p < N_PHY_BLOCKS;
    ensures 0 <= l_act_page_p < N_PAGE;
    ensures clean[index_2_physical[l_act_block_index_p]] == false;
    ensures 1 <= clean_counter == count_clean(N_PHY_BLOCKS) <= N_PHY_BLOCKS - 2;
    ensures \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE && logical_disk[i][j] != -1 && (i != lb && j != lp)
        ==> \old(logical_disk[i][j]) == logical_disk[i][j] == disk[l_to_p[i][j] / N_PAGE][l_to_p[i][j] % N_PAGE];
    
    /// User > valid mapping & equivalent data ///
    ensures l_to_p[lb][lp] == index_2_physical[\old(l_act_block_index_p)] * N_PAGE + \old(h_act_page_p);
    ensures d == logical_disk[lb][lp]
              == disk[l_to_p[lb][lp] / N_PAGE][l_to_p[lb][lp] % N_PAGE];
    
    /// System > active pointers point to empty page & valid page ///
    ensures \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE
        ==> logical_disk[i][j] != index_2_physical[l_act_block_index_p] * N_PAGE + l_act_page_p;
    ensures disk[index_2_physical[l_act_block_index_p]][l_act_page_p] == -1;
    ensures \old(l_to_p[lb][lp]) != -1
        ==> is_valid_page[\old(l_to_p[lb][lp]) / N_PAGE][\old(l_to_p[lb][lp]) % N_PAGE] == false;
    ensures is_valid_page[l_to_p[lb][lp] / N_PAGE][l_to_p[lb][lp] % N_PAGE] == true;
    behavior block_full:
        assumes l_act_page_p + 1 == N_PAGE;
        ensures \forall integer i; 0 <= i < N_PHY_BLOCKS && i != index_2_physical[l_act_block_index_p]
            ==> clean[i] == \old(clean[i]);
        ensures clean[index_2_physical[l_act_block_index_p]] == false;
        ensures l_act_page_p == 0;
    behavior block_not_full:
        assumes l_act_page_p + 1 != N_PAGE;
        ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> clean[i] == \old(clean[i]);
        ensures l_act_page_p == \old(l_act_page_p) + 1;
    complete behaviors;
    disjoint behaviors;
    
    //ensures spare_area[ l_to_p[lb][lp] / N_PAGE ][ l_to_p[lb][lp] % N_PAGE ] == lb * N_PAGE + lp;
    
/// Assign ///
    
*/
void write_2_lower_number_list (int d, int lb, int lp) {
    // invalidate old physical address
    if(l_to_p[lb][lp] != -1){
        //@ assert 0 <= l_to_p[lb][lp] < N_PHY_BLOCKS * N_PAGE ;
        //clean previous physical address from the same logical address
        int old_addr = l_to_p[lb][lp];
        int opb = old_addr / N_PAGE; //turn page addressing to block id
        int opp = old_addr % N_PAGE; //turn page addressing to page offset
        is_valid_page[opb][opp] = false;
    }
    
    //wirte data to new physical address
    int pb = index_2_physical[l_act_block_index_p]; //get active block ID
    int pp = l_act_page_p;  //get active page
    _w(d, pb, pp);  //write data
    
    //update logical to physical mapping
    int new_addr = pb * N_PAGE + pp;
    l_to_p[lb][lp] = new_addr;
    is_valid_page[pb][pp] = true;
    int log_addr = lb * N_PAGE + lp;
    _write_spare_area(pb, pp, log_addr);

    //update active pointer value
    if (l_act_page_p + 1 == N_PAGE){
        //page + 1 == block size
        l_act_page_p = 0;
        
        // move the low pointer to the next clean block
        // search a clean block from the head of the low number list
        // firstly we search clean block in lower number list
        // if we can't find any clean block in lower number list, then we search in higher number list
        l_act_block_index_p = 0;
        /*@
            loop invariant 0 <= l_act_block_index_p <= N_PHY_BLOCKS;
            loop invariant \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
            loop invariant \forall integer i; 0 <= i < l_act_block_index_p ==> clean[index_2_physical[i]] == false;
            loop assigns l_act_block_index_p;
            loop variant N_PHY_BLOCKS - l_act_block_index_p;
        */
        while(l_act_block_index_p < N_PHY_BLOCKS) {
            if (clean[index_2_physical[l_act_block_index_p ]] == true) break; // find a clean block
            l_act_block_index_p ++;
        }
        ///!ERROR: if (l_act_block_index_p == N_PHY_BLOCKS) no any clean block
        
        //@ assert 0 <= l_act_block_index_p < N_PHY_BLOCKS;
        //@ assert 0 <= index_2_physical[l_act_block_index_p] < N_PHY_BLOCKS ;
        
        clean[ index_2_physical[ l_act_block_index_p ] ] = false;
        clean_counter -= 1;
    }else{
        //page + 1 < block size
        l_act_page_p += 1;
    }
    //count_clean_array(0,N_PHY_BLOCKS/2);
}

/*
*   Perform garbage collection to ensure there is at least two clean block
*/
/*@
/// Require ///
    /// General Constraints ///
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    requires bijection(index_2_physical);
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE
        ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS * N_PAGE || l_to_p[i][j] == -1;
    requires 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS;
    requires 0 <= l_act_page_p < N_PAGE && 0 <= h_act_page_p < N_PAGE;
    requires clean[index_2_physical[l_act_block_index_p]] == clean[index_2_physical[h_act_block_index_p]] == false;
    requires 2 <= clean_counter == count_clean(N_PHY_BLOCKS) <= N_PHY_BLOCKS - 2;
    requires \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE && logical_disk[i][j] != -1
        ==> logical_disk[i][j] == disk[l_to_p[i][j] / N_PAGE][l_to_p[i][j] % N_PAGE];
    
    /// system > active pointers point to empty pages ///
    requires \forall integer lb, lp; 0 <= lb < N_LOG_BLOCKS && 0 <= lp < N_PAGE
        ==> l_to_p[lb][lp] != index_2_physical[l_act_block_index_p] * l_act_page_p
         && l_to_p[lb][lp] != index_2_physical[h_act_block_index_p] * h_act_page_p;
    requires disk[index_2_physical[l_act_block_index_p]][l_act_page_p]
          == disk[index_2_physical[h_act_block_index_p]][h_act_page_p] == -1;
    
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

/// Ensure ////
    /// General Constraints ///
    ensures \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    ensures bijection(index_2_physical);
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    ensures \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE
        ==> 0 <= l_to_p[i][j] < N_PHY_BLOCKS * N_PAGE || l_to_p[i][j] == -1;
    ensures 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS;
    ensures 0 <= l_act_page_p < N_PAGE && 0 <= h_act_page_p < N_PAGE;
    ensures clean[index_2_physical[l_act_block_index_p]] == clean[index_2_physical[h_act_block_index_p]] == false;
    ensures 2 <= clean_counter == count_clean(N_PHY_BLOCKS) <= N_PHY_BLOCKS - 2;
    ensures \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE && logical_disk[i][j] != -1
        ==> logical_disk[i][j] == disk[l_to_p[i][j] / N_PAGE][l_to_p[i][j] % N_PAGE];
    
    /// system > active pointers point to empty pages ///
    ensures \forall integer i, j; 0 <= i < N_LOG_BLOCKS && 0 <= j < N_PAGE
        ==> logical_disk[i][j] != index_2_physical[l_act_block_index_p] * l_act_page_p
         && logical_disk[i][j] != index_2_physical[h_act_block_index_p] * h_act_page_p;
    ensures disk[index_2_physical[l_act_block_index_p]][l_act_page_p]
          == disk[index_2_physical[h_act_block_index_p]][h_act_page_p] == -1;
*/
void gc (void) {
    /*@
        loop invariant 0 <= tau <= MAX_WEAR_CNT;
        loop invariant bijection(index_2_physical);
        loop invariant \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
        loop invariant \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
        loop invariant 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS;
        loop invariant clean[index_2_physical[l_act_block_index_p]] == clean[index_2_physical[h_act_block_index_p]] == false;
        loop invariant clean_counter == count_clean(N_PHY_BLOCKS);
        loop invariant 1 <= clean_counter <= N_PHY_BLOCKS - 2;
        //loop invariant clean_counter < N_PHY_BLOCKS - 2 ==>
        //    \exists integer i; 0 <= i < N_PHY_BLOCKS && i!=h_act_block_index_p && i!=l_act_block_index_p && clean[index_2_physical[i]]!=true;
        
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
        /*@ ghost
        int cnt1 = 0;
        int cnt2 = 0;
        */
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
        //@ assert \exists integer j; 0 <= j < N_PHY_BLOCKS && j != index_2_physical[l_act_block_index_p] && j != index_2_physical[h_act_block_index_p] && clean[j] == false;
        //@ assert \exists integer i; 0 <= i < N_PHY_BLOCKS && i != l_act_block_index_p && i != h_act_block_index_p && clean[index_2_physical[i]] == false;
        
        int idx = get_most_clean_efficient_block_idx();
        if( min_wear() + tau <= get_erase_count_by_idx(idx) ){
       	    data_migration();
        }
        erase_block_data(idx);
    }
}

/*
*   Perform data migration when victim block is in Maxwear
*/
/*@
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires 0 <= clean_counter < N_PHY_BLOCKS;
    requires 0 <= clean_counter < N_PHY_BLOCKS;
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] <= N_PHY_BLOCKS;
    assigns clean_counter;
    assigns clean[0..(N_PHY_BLOCKS - 1)];
    assigns h_act_block_index_p, l_act_block_index_p;
    assigns erase_count_index[0..(MAX_WEAR_CNT-1)];
    assigns index_2_physical[0..(N_PHY_BLOCKS-1)];
    
    assigns l_to_p[0..(N_LOG_BLOCKS - 1)][0..(N_PAGE)] ;  
    assigns h_act_page_p ;
    assigns l_act_page_p ;
    assigns clean[0..(N_PHY_BLOCKS - 1)];

    assigns spare_area[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)];
    assigns disk[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)];
    assigns is_valid_page[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)]; 
    */
void data_migration (void) {
    // move all the block in min_wear
    int idx;
    if(min_wear() == 0){
        idx = 0;
    }else{
        idx = erase_count_index[min_wear() - 1]; // set index to the front of erase count i
    }
    int end_idx = erase_count_index[ min_wear() ];
/*@
    loop assigns clean_counter;
    loop assigns clean[0..(N_PHY_BLOCKS - 1)];
    loop assigns h_act_block_index_p, l_act_block_index_p;
    loop assigns erase_count_index[0..(MAX_WEAR_CNT-1)];
    loop assigns index_2_physical[0..(N_PHY_BLOCKS-1)];
    
    loop assigns l_to_p[0..(N_LOG_BLOCKS - 1)][0..(N_PAGE)] ;  
    loop assigns h_act_page_p ;
    loop assigns l_act_page_p ;
    loop assigns clean[0..(N_PHY_BLOCKS - 1)];

    loop assigns spare_area[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)];
    loop assigns disk[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)];
    loop assigns is_valid_page[0..(N_PHY_BLOCKS - 1)][0..(N_PAGE-1)];
    loop assigns idx;
    */
    while(idx < end_idx){    
        erase_block_data(idx);
        idx +=1;
    }
}

/*
*   Get the erase count of min wear
*    :return: min_wear value, return -1
*/

/*@
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    assigns \nothing;
    ensures -1 <= \result <=  MAX_WEAR_CNT;
    ensures 0 <= \result < MAX_WEAR_CNT ==>
            erase_count_index[\result] != 0 &&
            \forall integer i; 0 <= i < \result ==> erase_count_index[i] == 0;
    ensures \result == -1 ==>
            \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] == 0;
 */
int min_wear (void) {
    /*@
        loop invariant 0 <= i <= MAX_WEAR_CNT;
        loop invariant \forall integer j; 0 <= j < i ==> erase_count_index[j] == 0;
        loop assigns i;
        loop variant MAX_WEAR_CNT - i;
    */
    for (int i=0 ; i<MAX_WEAR_CNT ; i++){
        if(erase_count_index[i] != 0){
            return i;
        }
    }
    return -1;    //hapens when rejuvenator just start, for all i, erase_count_index[i] == N_PHY_Blocks
}

/*
*   Get the erase count of max_wear value
*    :return: max_wear value; if error, return -1
*/
/*@
    assigns \nothing;
    ensures -1 <= \result <=  MAX_WEAR_CNT;
 */
int max_wear (void) {
    /*@ loop invariant 0 <= i <= MAX_WEAR_CNT;
        loop assigns i;
        loop variant MAX_WEAR_CNT-i;
    */
    for(int i = 0 ; i<MAX_WEAR_CNT ; i++){
        if (erase_count_index[i] == N_PHY_BLOCKS){
            return i;
        }
    }
    return -1;
}

/*
*   Get the erase count of the physical block indexed by idx in the index_2_physical
*    :param idx: index in the index_2_physical
*    :return: erase count
*/
/*@
    requires 0 <= idx < N_PHY_BLOCKS;
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    
    assigns \nothing;
    
    behavior not_reach_max_wear:
      assumes \exists integer i; 0 <= i < MAX_WEAR_CNT && erase_count_index[i] > idx;
      ensures 0 <= \result < MAX_WEAR_CNT;
      ensures erase_count_index[\result] > 0;
      
    behavior reach_max_wear:
      assumes \forall integer i; 0 <= i < MAX_WEAR_CNT ==> erase_count_index[i] <= idx;
      ensures \result == MAX_WEAR_CNT;

    disjoint behaviors;
    complete behaviors;
 */
int get_erase_count_by_idx (int idx) {
    /*@
        loop invariant 0 <= cur <=  MAX_WEAR_CNT;
        loop invariant \forall integer i; 0<=i<cur ==> erase_count_index[i] <= idx;
        loop assigns cur;
        loop variant MAX_WEAR_CNT-cur;
    */
    for(int cur = 0 ; cur < MAX_WEAR_CNT ; cur++){
        if (erase_count_index[cur] > idx){
            return cur;
        }
    }
    return MAX_WEAR_CNT;
}

/*
* this is similiar with _find_vb
* but it doesn't ignore blocks in Maxwear
*   :return: most_clean_efficient_idx
*/
/*@
    requires bijection(index_2_physical);
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS && l_act_block_index_p != h_act_block_index_p;
    requires clean[index_2_physical[l_act_block_index_p]] == false && clean[index_2_physical[h_act_block_index_p]] == false;
    requires clean_counter == count_clean(N_PHY_BLOCKS);
    requires 0 <= clean_counter < N_PHY_BLOCKS - 2;
    requires \exists integer i; 0 <= i < N_PHY_BLOCKS && i != index_2_physical[l_act_block_index_p] && i != index_2_physical[h_act_block_index_p] && clean[i] == false;
    requires \exists integer i; 0 <= i < N_PHY_BLOCKS && i != index_2_physical[l_act_block_index_p] && i != index_2_physical[h_act_block_index_p] && clean[i] == false
         ==> \exists integer i; 0 <= i < N_PHY_BLOCKS && i != l_act_block_index_p && i != h_act_block_index_p && clean[index_2_physical[i]] == false;
    requires \exists integer i; 0 <= i < N_PHY_BLOCKS && i != l_act_block_index_p && i != h_act_block_index_p && clean[index_2_physical[i]] == false;
    
    assigns \nothing;
    
    ensures 0 <= \result < N_PHY_BLOCKS;
    ensures \result != l_act_block_index_p && \result != h_act_block_index_p && clean[index_2_physical[\result]] != true;
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS && i != h_act_block_index_p && i != l_act_block_index_p && clean[index_2_physical[i]] != true
        ==> count_efficiency(index_2_physical[\result], N_PAGE) >= count_efficiency(index_2_physical[i], N_PAGE);
*/
int get_most_clean_efficient_block_idx (void) {
    int most_efficient_idx = 0;
    int n_of_max_invalid_or_clean_page = 0;
    /*@ ghost bool start = false; */

    /*@
        loop invariant 0 <= idx <= N_PHY_BLOCKS;
        loop invariant \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
        
        loop invariant 0 <= most_efficient_idx < N_PHY_BLOCKS;
        loop invariant 0 <= n_of_max_invalid_or_clean_page <= N_PAGE;
        
        loop invariant !start ==> most_efficient_idx == n_of_max_invalid_or_clean_page == 0;
        loop invariant !start ==> \forall integer i; 0 <= i < idx ==> i == h_act_block_index_p || i == l_act_block_index_p || clean[index_2_physical[i]] == true;
        
        loop invariant start ==> n_of_max_invalid_or_clean_page == count_efficiency(index_2_physical[most_efficient_idx], N_PAGE);
        loop invariant start ==> most_efficient_idx != l_act_block_index_p && most_efficient_idx != h_act_block_index_p && clean[index_2_physical[most_efficient_idx]] != true;
        
        loop invariant \forall integer i; 0 <= i < idx && i != l_act_block_index_p && i != h_act_block_index_p && clean[index_2_physical[i]] != true &&
            most_efficient_idx != l_act_block_index_p && most_efficient_idx != h_act_block_index_p && clean[index_2_physical[most_efficient_idx]] != true ==>
                count_efficiency(index_2_physical[most_efficient_idx], N_PAGE) >= count_efficiency(index_2_physical[i], N_PAGE);
        
        loop assigns idx, most_efficient_idx, n_of_max_invalid_or_clean_page, start;
        loop variant N_PHY_BLOCKS - idx;
    */
    for(int idx = 0 ; idx < N_PHY_BLOCKS ; idx++){
        int pid = index_2_physical[idx];    // get physical block id

        //ignore the block indexed by either active pointer
        if(idx == h_act_block_index_p || idx == l_act_block_index_p){
            continue;
        }
        //ignore the block with all clean pages
        if(clean[pid] == true){
            continue;
        }

        int n_of_invalid_or_clean_page = 0;
        
        /*@
            loop invariant 0 <= pp <= N_PAGE;
            loop invariant 0 <= n_of_invalid_or_clean_page <= pp;
            loop invariant n_of_invalid_or_clean_page == count_efficiency(pid, pp);
            loop assigns n_of_invalid_or_clean_page, pp;
            loop variant N_PAGE - pp;
        */
        for(int pp = 0 ; pp < N_PAGE ; pp++){
            if(is_valid_page[pid][pp] == false){
                n_of_invalid_or_clean_page +=1;
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

/*
*   Move valid page and erase this block; then increase erase cnt
*   :param idx: index in the index_2_physical
*/
/*@
    requires  0 <= idx < N_PHY_BLOCKS;
    requires idx != l_act_block_index_p && idx != h_act_block_index_p;
    requires clean[index_2_physical[idx]] == false;
    
    requires 0 <= tau <= MAX_WEAR_CNT;
    requires bijection(index_2_physical);
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    requires 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS;
    requires clean[index_2_physical[l_act_block_index_p]] == clean[index_2_physical[h_act_block_index_p]] == false;
    requires clean_counter == count_clean(N_PHY_BLOCKS);
    requires 1 <= clean_counter < N_PHY_BLOCKS - 2;
    
    requires \forall integer j; 0 <= j < N_PAGE && is_valid_page[index_2_physical[idx]][j] ==>
        logical_disk[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] == 
            disk[l_to_p[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] / N_PAGE][l_to_p[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] % N_PAGE];
    
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
    ensures 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS;
    ensures clean[index_2_physical[l_act_block_index_p]] == clean[index_2_physical[h_act_block_index_p]] == false;
    ensures \forall integer i; 0<=i<N_PAGE ==> is_valid_page[\old(index_2_physical[idx])][i] == false;
    ensures clean_counter == count_clean(N_PHY_BLOCKS);
    ensures 1 < clean_counter <= N_PHY_BLOCKS - 2;
    
    ensures clean[\old(index_2_physical[idx])] == true;
    ensures clean_counter == \old(clean_counter)+1;
    
    ensures \forall integer j; 0 <= j < N_PAGE && is_valid_page[index_2_physical[idx]][j] ==>
        logical_disk[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] == 
            disk[l_to_p[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] / N_PAGE][l_to_p[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] % N_PAGE];
*/
void erase_block_data (int idx) {
    int pb = index_2_physical[idx]; //get physical block
    int pp = 0; //get physical page
    //copy valid page to another space and set the page to clean
    /*@
        loop invariant 0 <= pp <= N_PAGE;
        loop invariant \forall integer i; 0 <= i < pp ==> is_valid_page[pb][i] == false;
        loop assigns is_valid_page[pb][0 .. (N_PAGE - 1)], pp;
        loop variant N_PAGE - pp;
    */
    while(pp != N_PAGE){
        if(is_valid_page[pb][pp]){
            int la = _read_spare_area(pb, pp); //get logical addr
            int lb = la / N_PAGE; //get logical block id
            int lp = la % N_PAGE;   //get logical page offset
            write_helper(_r(pb,pp), lb, lp);
        }
        is_valid_page[pb][pp] = false;
        pp++;
    }
    
    //erase the block by disk erase API
    _erase_block(pb);
    //update block clean status
    clean[pb] = true;

    //update clean counter
    clean_counter += 1;
    /*@ ghost
    /@ 
        loop invariant 0 <= i <= index_2_physical[idx] ;
        loop invariant count_clean(i) == count_clean{Pre}(i);
        loop assigns i;
        loop variant index_2_physical[idx] - i ;
    @/
    for(int i = 0 ; i < index_2_physical[idx] ; i++);
    
    /@
        loop invariant index_2_physical[idx] < i <= N_PHY_BLOCKS;
        loop invariant count_clean(i) == 1 + count_clean{Pre}(i);
        loop assigns i;
        loop variant N_PHY_BLOCKS - i ;
    @/
    for(int i = index_2_physical[idx]+1 ; i < N_PHY_BLOCKS ; i++);
    */
    
    //update erase count for pb
    increase_erase_count(idx);
}

/*  API
*   erase block
*    :param pb: physical block address
*/
/*@
    assigns  \nothing;
  */
void _erase_block (int pb) {
    //pass
}

/*
*   Increase the erase count by swapping idx with the last elment which has the same erase count
*    :param idx: index in the index_2_physical
*/
/* A example of FTLEraseOneBlock:
    index                          : 0, 1, 2, 3, 4, 5, 6
    erase count                    : 1, 2, 2, 2, 2, 3, 4
    index_2_physical store block ID: 1, 3, 2, 4, 5, 6, 7

    now we want to erase idx = 2;
    get its erase count:
        erase_count = _get_erase_count_by_idx(idx) = 2
    get the end index of the same "old erasecnt" in the index_2_physical:
        last_block_idx = erase_count_index[erase_count] - 1 = 5-1 = 4
    swap the block of index=2 and index=4 in index_2_physical, then get:
    index                          : 0, 1, 2, 3, 4, 5, 6
    erase count                    : 1, 2, 2, 2, 2, 3, 4
    index_2_physical store block ID: 1, 3, 5, 4, 2, 6, 7

    update erase count boundry:
        erase_count_index[erase_count] -=1  5->4
    index                          : 0, 1, 2, 3, 4, 5, 6
    erase count                    : 1, 2, 2, 2, 3, 3, 4
    index_2_physical store block ID: 1, 3, 5, 4, 2, 6, 7
*/
/*@
    requires 0 <= idx < N_PHY_BLOCKS;
    requires idx != l_act_block_index_p && idx != h_act_block_index_p;
    
    requires bijection(index_2_physical);
    requires \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    requires \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    requires 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS;
    requires clean[index_2_physical[l_act_block_index_p]] == clean[index_2_physical[h_act_block_index_p]] == false;
    
    requires \forall integer j; 0 <= j < N_PAGE && is_valid_page[index_2_physical[idx]][j] ==>
        logical_disk[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] == 
            disk[l_to_p[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] / N_PAGE][l_to_p[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] % N_PAGE];
    
    assigns erase_count_index[0 .. (MAX_WEAR_CNT - 1)];
    assigns index_2_physical[0 .. (N_PHY_BLOCKS - 1)];
    assigns l_act_block_index_p, h_act_block_index_p;
    
    ensures bijection(index_2_physical);
    ensures \forall integer i; 0 <= i < N_PHY_BLOCKS ==> 0 <= index_2_physical[i] < N_PHY_BLOCKS;
    ensures \forall integer i; 0 <= i < MAX_WEAR_CNT ==> 0 <= erase_count_index[i] <= N_PHY_BLOCKS;
    ensures 0 <= l_act_block_index_p < N_PHY_BLOCKS && 0 <= h_act_block_index_p < N_PHY_BLOCKS;
    /// the clean information of pointers is still the same although the pointer changed
    ensures clean[index_2_physical[l_act_block_index_p]] == clean[index_2_physical[h_act_block_index_p]] == false;
    
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
    
    ensures \forall integer j; 0 <= j < N_PAGE && is_valid_page[index_2_physical[idx]][j] ==>
        logical_disk[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] == 
            disk[l_to_p[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] / N_PAGE][l_to_p[(spare_area[index_2_physical[idx]][j] / N_PAGE)][(spare_area[index_2_physical[idx]][j] % N_PAGE)] % N_PAGE];
 */
void increase_erase_count (int idx) {
    //swap the index_2_physical[idx] with the element which has teh same erase count
    int erase_count = get_erase_count_by_idx(idx); //get the erase cnt of idx
    int last_block_idx = erase_count_index[erase_count] - 1;    //get the ending index which has the same erase cnt

    // let active block pointer stay with the same blockID
    if(last_block_idx == h_act_block_index_p){
        h_act_block_index_p = idx;
    }
    if(last_block_idx == l_act_block_index_p){
        l_act_block_index_p = idx;
    }
    
    int temp = index_2_physical[idx];
    index_2_physical[idx] = index_2_physical[last_block_idx];
    index_2_physical[last_block_idx] = temp;

    // update the erase_count boundary index
    erase_count_index[erase_count] -= 1;
}

/*  API
*   write data to physical address
*    :param d: data
*    :param pb: physical block
*    :param pg: physical page
*/
/*@
    requires -2147483648 <= d <= 2147483647;
    requires 0 <= pb < N_PHY_BLOCKS && 0 <= pp < N_PAGE;
    assigns disk[pb][pp];
    ensures disk[pb][pp] == d;
*/
void _w (int d, int pb, int pp) {
   disk[pb][pp] = d;
}

/*  DISK API
*   read logical page info from the space area
*    :param pb: physical block address
*    :param pp: physical page address
*    :return logical address:
*/
/*@
    requires in_P_range(pb, pp);
    assigns  \nothing;
  */
int _read_spare_area (int pb, int pp) {
    return spare_area[pb][pp];
}

/*  DISK API
*   write logical page info into the space area
*    :param pb: physical block address
*    :param pp: physical page address
*    :param la: logical address
*/
/*@
    requires 0 <= pb < N_PHY_BLOCKS ;
    requires 0 <= pp < N_PAGE ;
    requires in_P_range(pb, pp);

    requires  0 <= la < 100*N_PAGE ;
    requires 0 <= la < N_PHY_BLOCKS * N_PAGE;
    assigns  spare_area[pb][pp];
    ensures  spare_area[pb][pp] == la ;
  */
void _write_spare_area (int pb, int pp, int la) {
    spare_area[pb][pp] = la;
}

/*
*  Update lru_cache after write
*   :param lb: logical block ID
*   :param lp: logical page offset
*/
/*@
    requires 0 <=  chance_index_p < LRU_SIZE;
    requires 0 <= lb * N_PAGE + lp < N_PHY_BLOCKS * N_PAGE ;
    requires 0 <= lb < N_LOG_BLOCKS &&  0 <= lp < N_PAGE ;
    assigns chance_index_p ;
    assigns chance_arr[0..(LRU_SIZE-1)];
    assigns cache[0..(LRU_SIZE-1)];
    ensures 0 <=  chance_index_p < LRU_SIZE;
*/
void update_lru (int lb, int lp) {
    int la = lb * N_PAGE + lp;  //get locical address (page addressing)
    int exist = find_and_update(la);    //check whether la in cache or not
    if(exist != 1){
        replace_and_update(la);     //if la is not in cache, then update cache
    }
}

/*
*  Check whether logical addr la in cache
*   :param la: logical address
*   :return: if la in cache, then return 1; else return 0
*/
/*@
    requires 0 <= la < N_PHY_BLOCKS * N_PAGE ;
    assigns chance_arr[0..(LRU_SIZE-1)];
*/
int find_and_update (int la) {
    /*@
        loop invariant 0 <= i <= LRU_SIZE;
        loop assigns i;
        loop variant LRU_SIZE - i;
    */
    for(int i=0 ; i<LRU_SIZE ; i++){
        if(cache[i] == la){
            chance_arr[i] = true;
            return 1;
        }
    }
    return 0;
}

/*
*  Find an entry of no chance, replace it with la, update chance_arr
*   :param la: logical address
*/
/*@ requires 0 <=  chance_index_p < LRU_SIZE;
    requires 0 <= la < N_PHY_BLOCKS * N_PAGE ;
    assigns chance_index_p ;
    assigns cache[0..(LRU_SIZE-1)];
    assigns chance_arr[0..(LRU_SIZE-1)];
    ensures 0 <=  chance_index_p < LRU_SIZE;
 */
void replace_and_update (int la) {
    /*@ loop assigns cache[0..(LRU_SIZE-1)],chance_index_p, chance_arr[0..(LRU_SIZE-1)];
        loop invariant 0 <= chance_index_p < LRU_SIZE;
      */
    while(1){
        if(chance_arr[chance_index_p] == false){
            cache[chance_index_p] = la;
            chance_index_p = (chance_index_p + 1) % LRU_SIZE;
            return;
        }else{
            chance_arr[chance_index_p] = false;
            chance_index_p = (chance_index_p + 1) % LRU_SIZE;
        }
    }
}

/*
*  if la is in cache, la is a hot page
*   :param lb: logical block
*   :param lp: logical page
*   :return: if la is in cache, then return 1; else return 0
*/
/*@
/// Require ///
    /// User > input a valid logical address ///
    requires 0 <= lb < N_LOG_BLOCKS && 0 <= lp < N_PAGE;
    
/// Assign ///
    assigns \nothing;
    
/// Ensure ///
    behavior Hot:
      assumes \exists integer i; 0 <= i < N_LOG_BLOCKS * N_PAGE && cache[i] == lb * N_PAGE + lp;
      ensures \result == 1;
    behavior NoHot:
      assumes \forall integer i; 0 <= i < N_LOG_BLOCKS * N_PAGE && cache[i] != lb * N_PAGE + lp;
      ensures \result == 0;
    disjoint behaviors;
    complete behaviors;
*/
int isHotPage (int lb, int lp) {
    int la = lb * N_PAGE + lp;
    /*@
        loop invariant 0 <= i <= LRU_SIZE;
        loop assigns i;
    */
    for(int i=0 ; i<LRU_SIZE ; i++){
        if(cache[i] == la){
            return 1;
        }
    }
    return 0;
}

int main (void) {
    initialize();
    write(0,0,0);
}