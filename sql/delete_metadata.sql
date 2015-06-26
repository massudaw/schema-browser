delete from metadata.view_pk where table_schema = 'incendio';
delete from metadata.view_fks where origin_schema_name = 'incendio';
delete from metadata.ordering where schema_name = 'incendio';
delete from metadata.extra_table_fks where origin_schema_name = 'incendio';
delete from metadata.table_description where table_schema = 'incendio';
delete from metadata.table_name_translation where schema_name= 'incendio';