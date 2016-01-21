insert into metadata.ordering (schema_name,table_name,usage) (select t.schema_name,t.table_name,0 from metadata.tables t left join metadata.ordering o on o.table_name= t.table_name and o.schema_name = t.schema_name where usage is null );

update 
 pg_attribute set attnotnull = 't'
from pg_class 
 , metadata.view_pk   where attrelid = oid and attname in (select unnest(pks)) and table_name = pg_class.relname and attnotnull = 'f';


-- UPDATE NOT NULL METADATA VIEW FIELDS

 -- select attname,relname,* from  
update  
 pg_attribute  set attnotnull = 't' 
  from pg_class 
    where attrelid = oid and array[attname :: text] <@ ARRAY['is_nullable','is_array','is_range','field_modifiers','ordinal_position'] and array[relname ::text] <@ ARRAY['columns','catalog_columns'] and attnotnull = 'f';
    
update  
 pg_attribute  set attnotnull = 't' 
  from pg_class 
    where attrelid = oid and array[attname :: text] <@ ARRAY['table_type'] and array[relname ::text] <@ ARRAY['tables','catalog_tables'] and attnotnull = 'f';


    update  
 pg_attribute  set attnotnull = 't' 
  from pg_class 
    where attrelid = oid and array[attname :: text] <@ ARRAY['rel_fks'] and array[relname ::text] <@ ARRAY['fks','catalog_fks'] and attnotnull = 'f';