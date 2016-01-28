# schema-browser
Data browser generated with schema information


# Features :
 - support to rich types (Recursive,Interval,Arrays,Optional,Records) 
 - patch operations (diff,apply) 
 - table indexing (GiST) 
 - UI Generation (Threepenny)
 - multischema query and fk relations
 - backend per schema
 - plugins



# Code Organization:

Backends 
  -- Postgresql
    -- Query  (String concat)
    -- Insert (Postgresql-simple)
    -- Parser (Custom)
  -- OAuth
    -- Query  (String concat)
    -- Insert (Not implemented)
    -- Parser (JSON)

Core ADT 
  Types
  Indexes
  Patches

Runtime Data
  RuntimeTypes (Runtime ADT)
  Schema      (Schema metadata)
  SchemaQuery (Backend independent Query)

UI
  QueryWidgets  (Generate generic UI)
  Browsera (Main App)

Plugins 
  Step Module  (Arrow Plugin DSL)
  Plugins  (Defined Plugins)



