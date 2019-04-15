
BEGIN;

SELECT
    origin_schema_name,
    origin_table_name,
    origin_fks
FROM
    metadata.fks
    JOIN metadata.tables t ON t.table_name = origin_table_name
        AND t.schema_name = origin_schema_name
WHERE
    target_schema_name = 'metadata'
    AND target_table_name = 'schema2'
    AND table_type = 'BASE TABLE';

SELECT
    origin_schema_name,
    origin_table_name,
    origin_fks
FROM
    metadata.fks
    JOIN metadata.tables t ON t.table_name = origin_table_name
        AND t.schema_name = origin_schema_name
WHERE
    target_schema_name = 'metadata'
    AND target_table_name = 'tables2'
    AND table_type = 'BASE TABLE';

SELECT
    origin_schema_name,
    origin_table_name,
    origin_fks
FROM
    metadata.fks
    JOIN metadata.tables t ON t.table_name = origin_table_name
        AND t.schema_name = origin_schema_name
WHERE
    target_schema_name = 'metadata'
    AND target_table_name = 'columns2'
    AND table_type = 'BASE TABLE';

UPDATE
    metadata.accounts
SET
    "table" = noid
FROM (
    SELECT
        ot.oid AS ooid,
        nt.oid AS noid
    FROM
        metadata.oid_table_map ot
        JOIN metadata.tables nt ON ot.table_name = nt.table_name
            AND ot.schema_name = nt.schema_name) AS map
WHERE
    ooid = "table";

UPDATE
    metadata.accounts
SET
    "schema" = noid
FROM (
    SELECT
        ot.oid AS ooid,
        nt.oid AS noid
    FROM
        metadata.oid_schema_map ot
        JOIN metadata.schema nt ON ot.name = nt.name) AS map
WHERE
    ooid = "schema";

UPDATE
    metadata.metrics
SET
    "table" = noid
FROM (
    SELECT
        ot.oid AS ooid,
        nt.oid AS noid
    FROM
        metadata.oid_table_map ot
        JOIN metadata.tables nt ON ot.table_name = nt.table_name
            AND ot.schema_name = nt.schema_name) AS map
WHERE
    ooid = "table";

UPDATE
    metadata.metrics
SET
    "schema" = noid
FROM (
    SELECT
        ot.oid AS ooid,
        nt.oid AS noid
    FROM
        metadata.oid_schema_map ot
        JOIN metadata.schema nt ON ot.name = nt.name) AS map
WHERE
    ooid = "schema";

UPDATE
    metadata.geo
SET
    "table" = noid
FROM (
    SELECT
        ot.oid AS ooid,
        nt.oid AS noid
    FROM
        metadata.oid_table_map ot
        JOIN metadata.tables nt ON ot.table_name = nt.table_name
            AND ot.schema_name = nt.schema_name) AS map
WHERE
    ooid = "table";

UPDATE
    metadata.geo
SET
    "schema" = noid
FROM (
    SELECT
        ot.oid AS ooid,
        nt.oid AS noid
    FROM
        metadata.oid_schema_map ot
        JOIN metadata.schema nt ON ot.name = nt.name) AS map
WHERE
    ooid = "schema";

select * from metadata.event;
UPDATE
    metadata.event
SET
    "column" = nop 
FROM 
(
    SELECT
        ot.table AS otable,
        array_agg(nt.ordinal_position) AS nop
    FROM
        metadata.oid_column_map ot
        JOIN metadata.columns2 nt ON ot.table_name = nt.table_name
                                  AND ot.column_name = nt.column_name
            AND ot.table_schema = nt.table_schema
        JOIN metadata.event e on  e."table" =  ot."table" AND ot.ordinal_position in (select unnest(e."column"))
        group by otable

          ) AS map
WHERE
    otable = "table";


UPDATE
    metadata.event
SET
    "table" = noid
FROM (
    SELECT
        ot.oid AS ooid,
        nt.oid AS noid
    FROM
        metadata.oid_table_map ot
        JOIN metadata.tables nt ON ot.table_name = nt.table_name
            AND ot.schema_name = nt.schema_name) AS map
WHERE
    ooid = "table";

UPDATE
    metadata.event
SET
    "schema" = noid
FROM (
    SELECT
        ot.oid AS ooid,
        nt.oid AS noid
    FROM
        metadata.oid_schema_map ot
        JOIN metadata.schema nt ON ot.name = nt.name) AS map
WHERE
    ooid = "schema";

select * from metadata.event;

UPDATE
    metadata.schema_style
SET
    "schema" = noid
FROM (
    SELECT
        ot.oid AS ooid,
        nt.oid AS noid
    FROM
        metadata.oid_schema_map ot
        JOIN metadata.schema nt ON ot.name = nt.name) AS map
WHERE
    ooid = "schema";

UPDATE
    metadata.polling
SET
    "schema" = noid
FROM (
    SELECT
        ot.oid AS ooid,
        nt.oid AS noid
    FROM
        metadata.oid_schema_map ot
        JOIN metadata.schema nt ON ot.name = nt.name) AS map
WHERE
    ooid = "schema";

UPDATE
    metadata.polling_log
SET
    "schema" = noid
FROM (
    SELECT
        ot.oid AS ooid,
        nt.oid AS noid
    FROM
        metadata.oid_schema_map ot
        JOIN metadata.schema nt ON ot.name = nt.name) AS map
WHERE
    ooid = "schema";

UPDATE
    metadata.table_name_translation
SET
    "table" = noid
FROM (
    SELECT
        ot.oid AS ooid,
        nt.oid AS noid
    FROM
        metadata.oid_table_map ot
        JOIN metadata.tables nt ON ot.table_name = nt.table_name
            AND ot.schema_name = nt.schema_name) AS map
WHERE
    ooid = "table";

UPDATE
    metadata.table_name_translation
SET
    "schema" = noid
FROM (
    SELECT
        ot.oid AS ooid,
        nt.oid AS noid
    FROM
        metadata.oid_schema_map ot
        JOIN metadata.schema nt ON ot.name = nt.name) AS map
WHERE
    ooid = "schema";

UPDATE
    metadata.ordering
SET
    "table" = noid
FROM (
    SELECT
        ot.oid AS ooid,
        nt.oid AS noid
    FROM
        metadata.oid_table_map ot
        JOIN metadata.tables nt ON ot.table_name = nt.table_name
            AND ot.schema_name = nt.schema_name) AS map
WHERE
    ooid = "table";

UPDATE
    metadata.ordering
SET
    "schema" = noid
FROM (
    SELECT
        ot.oid AS ooid,
        nt.oid AS noid
    FROM
        metadata.oid_schema_map ot
        JOIN metadata.schema nt ON ot.name = nt.name) AS map
WHERE
    ooid = "schema";

select * from metadata.planner;
UPDATE
    metadata.planner
SET
    task = nop 
FROM (
    SELECT
        ot.table AS otable,
        ot.ordinal_position AS oop,
        nt.ordinal_position AS nop
    FROM
        metadata.oid_column_map ot
        JOIN metadata.columns2 nt ON ot.table_name = nt.table_name
                                  AND ot.column_name = nt.column_name
            AND ot.table_schema = nt.table_schema) AS map
WHERE
    otable = "table"

UPDATE
    metadata.planner
SET
    "table" = noid
FROM (
    SELECT
        ot.oid AS ooid,
        nt.oid AS noid
    FROM
        metadata.oid_table_map ot
        JOIN metadata.tables nt ON ot.table_name = nt.table_name
            AND ot.schema_name = nt.schema_name) AS map
WHERE
    ooid = "table";

UPDATE
    metadata.planner
SET
    "schema" = noid
FROM (
    SELECT
        ot.oid AS ooid,
        nt.oid AS noid
    FROM
        metadata.oid_schema_map ot
        JOIN metadata.schema nt ON ot.name = nt.name) AS map
WHERE
    ooid = "schema";

select * from metadata.planner;
COMMIT;
-- ROLLBACK;

