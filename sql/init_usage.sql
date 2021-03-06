﻿insert into metadata.ordering (schema,"table",usage) (select t.schema,oid,0 from metadata.tables2 t left join metadata.ordering o on "table"= t.oid and o.schema = t.schema where usage is null );

update 
 pg_attribute set attnotnull = 't'
from pg_class c
 , metadata.view_pk   where attrelid = c.oid and attname in (select unnest(pks)) and table_name = c.relname and attnotnull = 'f';

update 
 pg_attribute set attnotnull = 't'
from pg_class c
 , metadata.custom_unique where attrelid = c.oid and attname in (select unnest(pks)) and table_name = c.relname and attnotnull = 'f';


update
 pg_attribute set attnotnull = 't'
 where attname = 'oid'  and attnotnull = 'f';



-- UPDATE NOT NULL METADATA VIEW FIELDS

 -- select attname,relname,* from  
update  
 pg_attribute  set attnotnull = 't' 
  from pg_class 
    where attrelid = oid and array[attname :: text] <@ ARRAY['is_nullable','is_array','is_range','field_modifiers','ordinal_positionl','schema','table'] and array[relname ::text] <@ ARRAY['columns','catalog_columns'] and attnotnull = 'f';

update  
 pg_attribute  set attnotnull = 't' 
  from pg_class 
    where attrelid = oid and array[attname :: text] <@ ARRAY['table_type'] and array[relname ::text] <@ ARRAY['tables','catalog_tables'] and attnotnull = 'f';

update  
 pg_attribute  set attnotnull = 't' 
  from pg_class 
    where attrelid = oid and array[attname :: text] <@ ARRAY['rel_fks'] and array[relname ::text] <@ ARRAY['fks','catalog_fks'] and attnotnull = 'f';

update  
 pg_attribute  set attnotnull = 't' 
  from pg_class 
    where attrelid = oid and array[attname :: text] <@ ARRAY['pks'] and array[relname ::text] <@ ARRAY['pks','catalog_pks'] and attnotnull = 'f';
