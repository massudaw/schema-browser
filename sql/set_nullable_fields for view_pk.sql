update 
 pg_attribute set attnotnull = 't'
from pg_class 
 , metadata.view_pk   where attrelid = oid and attname in (select unnest(pk_column)) and table_name = pg_class.relname and attnotnull = 'f'