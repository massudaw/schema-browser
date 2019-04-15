DO
$$
DECLARE
    i integer;
begin
  for i in (select id from transito.linha offset 10 ) loop
      raise notice 'Value: %', i;
	insert into transito.linha_route (  select r.id as linha ,w.* from (select * 
		from transito.linha l 
		join lateral (select v.id as ini from transito.ways_vertices_pgr v join transito.match m on source = v.id and l.id = m.id  order by st_distance(st_startpoint(linha_ida_coordinates),v.the_geom) asc  limit 1 ) as f on true 
		join lateral (select v.id as endp from  transito.ways_vertices_pgr v join transito.match m on target  = v.id and l.id = m.id  order by st_distance(st_endpoint(linha_ida_coordinates),v.the_geom) asc limit 1 ) as e on true
		join lateral pgr_dijkstra('select gid as id ,source,target,cost from transito.match where id = ' || l.id::text,  ini,endp ,false) on true) as r 
	, transito.ways w where w.gid = edge  and id = i );
  end loop ;

end 
$$