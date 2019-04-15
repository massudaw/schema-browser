#include "postgres.h"
#include "utils/array.h"
#include <string.h>
#include "fmgr.h"
#include "catalog/pg_type.h"
#include "utils/array.h"
#include "utils/builtins.h"
#include "utils/memutils.h"


#ifdef PG_MODULE_MAGIC
PG_MODULE_MAGIC;
#endif
/* by value */

char take4(int i , int32 bitmap){
  if ((bitmap >> (i*4 +3)) & 0b1)

  {
    return ((bitmap >> i*4) & 0b111 ) | 0b11111000;
  }else
  {
    return (bitmap >> i*4) & 0b111;
  }
}

PG_FUNCTION_INFO_V1(dimensional_typmodout);

Datum
dimensional_typmodout(PG_FUNCTION_ARGS)
{
    int32   arg = PG_GETARG_INT32(0) ;

    Datum  transdatums[7];

    char * v = (char *) palloc(64);
    char * value = v;
      value += sprintf(value,  "(" );
    for(int i = 0; i<7 ;i++){
      value +=sprintf(value,  "%d", take4(7-i,arg) );
      value +=sprintf(value,  "," );
    }
      value +=sprintf(value,  "%d", take4(0,arg) );
      value +=sprintf(value,  ")" );

    PG_RETURN_CSTRING(v);

}
