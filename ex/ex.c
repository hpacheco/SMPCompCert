#include <stdio.h>
#include <stdbool.h>
#include "stdint.h"
#include "sharemind.h"

//void malloc2 (int v[volatile 10]) {
//    return;
//}

//int secret wx[secret 3] = {1,2,3};

int main() {
   //printf("%zu\n", sizeof(bool));  //1
   //printf("%zu\n", sizeof(_Bool)); //1
   //printf("%zu\n", sizeof(int));   //4
   
   
   
    int8_t vx;
    secret int8_t vy;
    vy = 1;
    vx = declassify_int8(vy);
    //print_int8();
    // = vx;
    //secret int8_t vz = vy;
   //
   //
   //int i;
   //while (true) {
   //	int wy[] = {1,2};      
   //    i++;
   //    wy[0];
   //}
   //
   //int volatile xxx[secret 10];
   //malloc2(xxx);
   //
   //printf("%d\n",10);

}
