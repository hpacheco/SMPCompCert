#include "stdio.h"
#include "stdlib.h"
#include "stdint.h"
#include "sharemind.h"

int8 secret*cut (int8 secret*aS,bool secret*mS, int size, int *sz)
{
    int i = 0;
    int j = 0;
    int8 secret *x = malloc(sizeof(int8 secret) * size);
    
    while(i < size)
    {
        if (declassify_bool(mS[i]))
        {
            x[j] = aS[i];
            j++;
        }
        ++i;
    }
    *sz = j;
    return x;
}

int main() {
    int8 secret aS[4] = {1,2,3,4};
    bool secret mS[4] = {true,false,true,false};
    int sz;
    int8 secret *res = cut(aS,mS,4,&sz);
    for (int i = 0; i < sz; ++i) print_int8(declassify_int8(res[i]));
}