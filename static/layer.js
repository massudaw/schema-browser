google.charts.load("current", {packages:["timeline"]});
google.charts.load("current", {packages:['corechart']});


function updateColor(el,c){
  el._jscLinkedInstance.fromString(c);
}

function setOpts(oSelect,selVals) {
  var opt, i = 0;
  while (opt = oSelect[0][i++]) {
    var sel= false
    for(var j =0 ; j< selVals.length;j ++){
      if(selVals[j] == opt.index)  sel = true;
    }
    opt.selected = sel;
  }
}

function fireCurrentPosition(el){

// Dispatch/Trigger/Fire the event
$(el).trigger('currentPosition',[]);
}

function getOpts(oSelect1) {
  var oSelect = oSelect1[0]
  var opt, i = 0, selVals = new Array();
  while (opt = oSelect[i++]) if (opt.selected) selVals[selVals.length] = opt.index;
  return selVals;
}

function readFileInput (f){
  var value = {};
  if (f[0].files.length == 1 ){
      value = f[0].files[0];
  }
  return value;
}
function handleFileSelect(fun,evt) {
    var files = evt.target.files; // FileList object
    // Loop through the FileList and render image files as thumbnails.
    for (var i = 0, f; f = files[i]; i++) {
      var reader = new FileReader();

      // Closure to capture the file information.
      reader.onload = (function(theFile) {
        return function(e) {
          // Render thumbnail.
          fun(e.target.result);
        };
      })(f);

      // Read in the image file as a data URL.
      reader.readAsDataURL(f);
    }
  }

function removeLayer (ref,tname){
    ref.mymap.removeLayer(ref.layer[tname]);
}

function createLayer(ref,tname,posj,nej,swj,features){
  var points = JSON.parse(features);
  if (ref.layer[tname] == null )
  {
    ref.layer[tname] = L.layerGroup().addTo(ref.mymap)
  }
  else {
    ref.layer[tname].clearLayers();
  }
  var layer = ref.layer[tname];
  layers = points.map(function (p){ 
  
  var feature ;
  if (p.position.constructor === Array && p.position[1].constructor ===Array ){
   latlonA = p.position.map(function(l){
     return L.latLng(l[0],l[1]);
   })
   var line =  L.polyline(latlonA,{color:p.color});
   line.on('click',function(e ){ref.eventClick(p,e);});
   layer.addLayer(line);
   var head = L.circle(latlonA[0],{radius: p.size,color:p.color});
   head.on('click',function(e ){ref.eventClick(p,e);});
   layer.addLayer(head);
   var tail = L.circle(latlonA[1],{radius: p.size/2,color:p.color});
   tail.on('click',function(e ){ref.eventClick(p,e);});
   layer.addLayer(tail);
  }
  else{
  feature = L.circle(p.position,{radius: p.size,color:p.color}).bindTooltip(p.title).openTooltip(); 
  feature.on('click',function(e ){ref.eventClick(p,e);});
  layer.addLayer(feature);
  }
  })
}


function createMap (ref,posj,nej,swj,features){
  pos = JSON.parse(posj);
  ref.mymap = L.map(ref);
  if (pos == null) {
      navigator.geolocation.getCurrentPosition(function(position) {
      var mtorad = 0.00000898315
      var mcdis = 4000*mtorad
      var bounds = L.latLngBounds([position.coords.latitude + mcdis , position.coords.longitude + mcdis],[position.coords.latitude - mcdis , position.coords.longitude - mcdis]);
      setPosition(ref,[position.coords.latitude, position.coords.longitude],bounds.getSouthWest(),bounds.getNorthEast());
    }, function() {
      handleLocationError(true, map.getCenter());
    });
  }else {
      ne = JSON.parse(nej);
      sw  = JSON.parse(swj);
    ref.mymap.fitBounds([ne,sw]);
  }
  ref.layer={}

  var osmUrl='https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png';
  var osmAttrib='Map data © <a href="https://openstreetmap.org">OpenStreetMap</a> contributors';
  var osm = L.tileLayer(osmUrl, { maxZoom: 18, attribution: osmAttrib}).addTo(ref.mymap);	
}


function handleLocationError(browserHasGeolocation, pos) {
  alert(browserHasGeolocation ?
                        'Error: The Geolocation service failed.' :
                        'Error: Your browser doesn\'t support geolocation.');
}

function removeChartColumns(el ){
  el.chart.clearChart();
}
function addChartColumns(el,table,fields,source){
  var dataInp = JSON.parse(source);
	var axisY = fields.map(function(i){return {lineThickness:2}});
	var ix = 0;
  var dataCol = fields.map(function(i){
	  var data = dataInp.map(function(r){
						return {label: r.title.slice(0,20),y:parseFloat(r.value[ix])}
				}); 
				return { type :'column'
               ,name : i
							 ,showInLegend : true
							 ,axisYIndex : ix++
               ,dataPoints : data
							}
			});
	var chart = new CanvasJS.Chart(el,
	{
		animationEnabled: true,
      	theme: "theme2",
    width:1000,
		title:{
			text: table
		},
    axisY: axisY,
    axisX:{labelMaxWidth:50,labelWrap:true},
		data: dataCol,
		legend: {
			cursor: "pointer",
			itemclick: function (e) {
				if (typeof(e.dataSeries.visible) === "undefined" || e.dataSeries.visible) {
					e.dataSeries.visible = false;
				} else {
					e.dataSeries.visible = true;
			}
			chart.render();
			}
		}
	});

	chart.render();
}
/*
function addChartColumns(el,table,fields,source){
  var data = JSON.parse(source);
  var chart = el.chart
  var dataTable = new google.visualization.DataTable();
          dataTable.addColumn({ type: 'string', id: 'Name' });
          fields.map(function(i){dataTable.addColumn({ type: 'number',id: i,label : i });});
          dataTable.addRows(data.filter(function (o){ return  o.value != null }).map(function(o){
            return [o.title].concat(o.value.map(parseFloat)) ;
          }));

          var ix = 0;
          var axis = fields.map(function(i){
              ix++; 
              return {title :i,textPosition:ix == 2 ? 'in' : 'out'};
          });
          var series ={};
          var ix= 0;
          fields.map(function(i){;
              var i = ix
              series [i] = {type :'bars',targetAxisIndex:i};
              ix++
              });
          var options = {
                width :1000,
                title: table,
                vAxes: axis,
                hAxis:{title : 'id'},
                series:series
                };

          chart.draw(dataTable, options);

}
*/
function createChart(el,tdate,view){
          var container = el ;
          var chart = new google.visualization.ComboChart(container);
          el.chart = chart;
};


function createAgenda(el,tdate,view){
  var date = new Date(tdate);
  var d = date.getDate();
  var m = date.getMonth();
  var y = date.getFullYear();

  $(el).fullCalendar({header: { left: '',center: 'title' , right: ''},defaultDate: date,lang: 'pt-br',editable: true,eventLimit: true, defaultView : view ,eventDrop : el.eventDrop , height : 450,eventResize: el.eventResize, schedulerLicenseKey: 'GPL-My-Project-Is-Open-Source' ,drop : el.drop, droppable:true ,eventClick: function(data, event, view) {
  el.eventClick(data,event,view);
          }});
  $(el).fullCalendar('render');
};

function renderCal(el){
  $(el).fullCalendar('render');
}

function removeSource(el,table){
  $(el).fullCalendar('removeEvents',function(e) { return e.table ==table});
}

function addSource(el,table,source){
  $(el).fullCalendar('addEventSource',JSON.parse(source));
}

function setPosition(el, center,sw,ne){
  el.mymap.fitBounds([
          sw,
          ne
  ]);
}

function clientHandlers(){
  return {'moveend': function(el,eventType,sendEvent){
    el.mymap.on(eventType,function(e) {
    var bounds = el.mymap.getBounds();
    var center =bounds.getCenter();
    var sw=bounds.getSouthWest();
    var ne=bounds.getNorthEast();
    sendEvent([center.lat,center.lng,0,ne.lat,ne.lng,0,sw.lat,sw.lng,0].map(function(e){return e.toString()}));
    return true;
    });
  }
   ,'onchange':function(el,eventType,sendEvent){
      $(el).on('change',function(i){
        sendEvent([]);})
      return true;
   }
   ,'eventClick' : function(el,eventType,sendEvent){
      el.eventClick=  function(e,delta,revert) {
      sendEvent([e.id,(new Date(e.start)).toISOString(),e.end === null ? null : new Date(e.end).toISOString()].filter(function(e) {return e !== null}).map(function(e){return  e.toString()}));
      return true;
      }; 
      }
   ,'eventDrop' : function(el,eventType,sendEvent){
      el.eventDrop =  function(e,delta,revert) {
      sendEvent([e.id,(new Date(e.start)).toISOString(),e.end === null ? null : new Date(e.end).toISOString()].filter(function(e) {return e !== null}).map(function(e){return  e.toString()}));
      return true;
      }; 
      }
   ,'eventResize' : function(el,eventType,sendEvent){
      el.eventResize =  function(e,delta,revert) {
      sendEvent([e.id,e == null ? null :new Date (e.start).toISOString(),e.end == null ? null:new Date (e.end).toISOString() ].filter(function(e) {return e !== null}).map(function(e){return e.toString()}));
      return true;
      }; 
      }
   ,'externalDrop' : function(el,eventType,sendEvent){
      el.drop =  function(e,revert) {
      var evdata = $(this).data('event');
      sendEvent([evdata.id,e == null ? null :new Date (e).toISOString() ].filter(function(e) {return e !== null}).map(function(e){return e.toString()}));
      return true;
      }; 
      }
   ,'mapEventClick' : function(el,eventType,sendEvent){
      el.eventClick=  function(e,pos) {
      sendEvent([e.id].filter(function(e) {return e !== null}).map(function(e){return  e.toString()}));
      return true;
      }; 
      }
   ,'currentPosition' : function(el,eventType ,sendEvent){
    $(el).bind(eventType,function(){
      navigator.geolocation.getCurrentPosition(function(position) {
        var mtorad = 0.00000898315
        var mcdis = 4000*mtorad
        var bounds = L.latLngBounds([position.coords.latitude + mcdis , position.coords.longitude + mcdis],[position.coords.latitude - mcdis , position.coords.longitude - mcdis]);
        var center =bounds.getCenter();
        var sw=bounds.getSouthWest();
        var ne=bounds.getNorthEast();
        sendEvent([center.lat,center.lng,0,ne.lat,ne.lng,0,sw.lat,sw.lng,0].map(function(e){return e.toString()}));

    }, function() {
      handleLocationError(true, map.getCenter());
    });
    });
   }

}
};
