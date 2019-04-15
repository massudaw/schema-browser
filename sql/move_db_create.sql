DROP TABLE metadata.oid_table_map;

DROP TABLE metadata.oid_schema_map;

DROP TABLE metadata.oid_user_map;

CREATE TABLE metadata.oid_table_map AS
SELECT
    oid,
    schema_name,
    table_name
FROM
    metadata.tables;

CREATE TABLE metadata.oid_schema_map AS
SELECT
    oid,
    name
FROM
    metadata.schema;

CREATE TABLE metadata.oid_user_map AS
SELECT
    oid,
    usename
FROM
    metadata.user;

CREATE TABLE metadata.oid_column_map AS
SELECT
    SCHEMA,
    table_schema,
    "table",
    table_name,
    ordinal_position,
    column_name
FROM
    metadata.columns2;

