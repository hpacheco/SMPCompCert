#include "stdio.h"
#include "stdlib.h"
#include "stdint.h"
#include "sharemind.h"

int8 *secret cut (int8 *secret aS,bool *secret mS)
{
    size_t size = size_int8_array(aS);
    bool* bS = malloc(sizeof(bool) * size);
    declassify_bool_array(mS,bS);
    
    size_t sz = 0;
    for (int i = 0; i < size; i++)
    {
        if (bS[i]) sz++;
    }
    int8 *secret x = new_int8_array(sz);
    
    for(int i = 0, j = 0; i < size; i++)
    {
        if (bS[i])
        {
            x[j] = aS[i];
            j++;
        }
    }
    free(bS);
    return x;
}

int main() {
    
    int8 aS[secret 4] = {1,2,3,4};
    bool mS[secret 4] = {true,false,true,false};
    
    int8 *secret res = cut(aS,mS);
    int sz = size_int8_array(res);
    
    for (int i = 0; i < sz; i++) print_int8(declassify_int8(res[i]));
    
}