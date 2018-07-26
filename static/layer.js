// google.charts.load("current", {packages:["timeline"]});
// google.charts.load("current", {packages:['corechart']});


function textAreaAdjust(o) {
  o.style.height = "1px";
  o.style.height = (25+o.scrollHeight)+"px";
}

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

function createBounds(ref,tname,features){
  var points = JSON.parse(features);
  if (ref.layer[tname] == null )
  {
  ref.bounds[tname] =  L.layerGroup();
  }else{
    ref.layer[tname].remove();
    ref.layer[tname]= L.layerGroup();
  }
}

function createLayer(ref,tname,features){
  var points = JSON.parse(features);
  if (ref.layer[tname] == null )
  {
    ref.layer[tname] = L.layerGroup();
  }
  else {
    ref.layer[tname].clearLayers().remove();
    ref.layer[tname]= L.layerGroup();
  }
  var layer = ref.layer[tname];
  points.map(function (t){ 
  var p =  Object.assign(t.label,t.style);
  var f = p.feature ;
  if (f.icon !== ''){ 
     var st = f.icon
     var bus = L.icon({iconUrl: st.url ,iconSize:st.size});
     var feature = L.marker(p.position,{icon:bus}).bindTooltip(p.title,{direction:'center',opacity:0.8,className :'pointTooltip'}).openTooltip(); 
     feature.on('click',function(e ){ref.eventClick(p,e);});
     layer.addLayer(feature);
  }
  if (f.point !== ''){
    var st = f.point;
    switch (f.point.geometry){
      case 'circle' :
        var feature = L.circle(p.position,{radius: parseFloat(st.size),color:p.color});
        feature.bindTooltip(p.title,{direction:'center',opacity:0.8,className :'pointTooltip'}).openTooltip(); 
        feature.on('click',function(e ){ref.eventClick(p,e);});
        layer.addLayer(feature);
      break;
      default :
        var feature = L.shapeMarker(p.position, {
                    shape: f.point.geometry ,
                    radius: parseFloat(st.size),
                    color : p.color
                });
        feature.bindTooltip(p.title,{direction:'center',opacity:0.8,className :'pointTooltip'}).openTooltip(); 
        feature.on('click',function(e ){ref.eventClick(p,e);});
        layer.addLayer(feature);

    }
  }
  if (f.point === '' && f.icon === '') {
    if (p.position.constructor === Array && p.position[0].constructor ===Array && p.position[0][0].constructor === Array && p.position[0][0][0].constructor === Array  && p.position[0][0][0][0].constructor == Array){
      p.position.map(function(mpos) {mpos.map(function(pos){
        var r = pos.map(function(l){ return l.map(function(b){return L.latLng(b[0],b[1])})})
        var poly = L.polygon(r,{color:p.color});
        poly.on('click',function(e ){ref.eventClick(p,e);});
        layer.addLayer(poly);});});
    }else
    if (p.position.constructor === Array && p.position[0].constructor ===Array && p.position[0][0].constructor === Array ){
      p.position.map(function(pos){
        var r = pos.map(function(l){ return l.map(function(b){return L.latLng(b[0],b[1])})})
        var poly = L.polygon(r,{color:p.color});
        poly.on('click',function(e ){ref.eventClick(p,e);});
        layer.addLayer(poly);});
    }else{
      if (p.position.constructor === Array && p.position[0].constructor ===Array ){
        var line ;
        latlonA = p.position.map(function(l){
           return L.latLng(l[0],l[1]);
         })
        if (f.line !== ''){
         line =  L.polyline(latlonA,{color:p.color,weight:f.line.width});

        }else{
         line =  L.polyline(latlonA,{color:p.color});
        }
         line.on('click',function(e ){ref.eventClick(p,e);});
         layer.addLayer(line);
      }
        else{
        var feature = L.circle(p.position,{radius: p.size,color:p.color}).bindTooltip(p.title,{direction:'center',opacity:0.8,className :'pointTooltip'}).openTooltip(); 
        feature.on('click',function(e ){ref.eventClick(p,e);});
        layer.addLayer(feature);
      }
    }
  }
  })
  layer.addTo(ref.mymap);

}


function createMap (ref,nej,swj){
  ref.mymap = L.map(ref);
  ne = JSON.parse(nej);
  sw  = JSON.parse(swj);
  if (ne == null || sw == null ) {
    /*    navigator.geolocation.getCurrentPosition(function(position) {
      var mtorad = 0.00000898315
      var mcdis = 4000*mtorad
      var bounds = L.latLngBounds([position.coords.latitude + mcdis , position.coords.longitude + mcdis],[position.coords.latitude - mcdis , position.coords.longitude - mcdis]);
      setPosition(ref,bounds.getSouthWest(),bounds.getNorthEast());
    }, function() {
      handleLocationError(true, map.getCenter());
    });(*/
  }else {
    ref.mymap.fitBounds([ne,sw],{animate:false});
  }
  ref.layer={}

  var osmUrl='https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png';
  var osmAttrib='Map data © <a href="https://openstreetmap.org">OpenStreetMap</a> contributors';
  var osm = L.tileLayer(osmUrl, { maxZoom: 18, attribution: osmAttrib}).addTo(ref.mymap);	
}


function handleLocationError(browserHasGeolocation, pos) {
  
}

function removeChartColumns(el ){
  el.chart.clearChart();
}
function addChartColumns(el,table,fields,source,chart){
  var dataInp = JSON.parse(source);
	var axisY = fields.map(function(i){return {lineThickness:2}});
	var ix = 0;
  var dataCol = fields.map(function(i){
	  var data = dataInp.filter(function(i){ return i}).map(function(r){
						return {label:  r.title.slice(0,20)  ,y:parseFloat(r.value[ix])}
				}); 
				return { type :chart
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

function createChart(el){
      var container = el ;
      var chart = new google.visualization.ComboChart(container);
      el.chart = chart;
};


function createAgenda(el,tdate,view){
  var date = moment(tdate,"YYYY-MM-DDTHH:mm:ss.SSS").toDate();
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

function setPosition(el, sw,ne){
  el.mymap.fitBounds([ne,sw],{animate:false});
}

function clientHandlers(){
  return {'moveend': function(el,eventType,sendEvent){
    var bf = function(e) {
    var bounds = el.mymap.getBounds();
    var sw=bounds.getSouthWest();
    var ne=bounds.getNorthEast();
    sendEvent([ne.lat,ne.lng,0,sw.lat,sw.lng,0].map(function(e){return e.toString()}));
    return true;
    }
    el.mymap.on(eventType,bf);
    return  bf;
  }
   ,'eventClick' : function(el,eventType,sendEvent){
      el.eventClick=  function(e,delta,revert) {
      sendEvent([e.id,(new Date(e.start)).toISOString(),e.end === null ? null : new Date(e.end).toISOString()].filter(function(e) {return e !== null}).map(function(e){return  e.toString()}));
      return true;
      }; 
      return el.eventClick;
      }
   ,'eventDrop' : function(el,eventType,sendEvent){
      el.eventDrop =  function(e,delta,revert) {
      sendEvent([e.id,(new Date(e.start)).toISOString(),e.end === null ? null : new Date(e.end).toISOString()].filter(function(e) {return e !== null}).map(function(e){return  e.toString()}));
      return true;
      }; 
      return el.eventDrop;
      }
   ,'eventResize' : function(el,eventType,sendEvent){
      el.eventResize =  function(e,delta,revert) {
      sendEvent([e.id,e == null ? null :new Date (e.start).toISOString(),e.end == null ? null:new Date (e.end).toISOString() ].filter(function(e) {return e !== null}).map(function(e){return e.toString()}));
      return true;
      };
      return el.eventResize;
      }
   ,'drop' : function(el,eventType,sendEvent){
      el.drop =  function(e,revert) {
      var evdata = $(this).data('event');
      sendEvent([evdata.id,e == null ? null :new Date (e).toISOString() ].filter(function(e) {return e !== null}).map(function(e){return e.toString()}));
      return true;
      }; 
      return el.drop;
      }
   ,'mapEventClick' : function(el,eventType,sendEvent){
      el.eventClick=  function(e,pos) {

        sendEvent([e.id,pos.originalEvent.shiftKey].filter(function(e) {return e !== null}).map(function(e){return  e.toString()}));
        return true;
      }; 
      return el.eventClick;
      }
   ,'currentPosition' : function(el,eventType ,sendEvent){
    fun = function(){
      navigator.geolocation.getCurrentPosition(function(position) {
        var mtorad = 0.00000898315
        var mcdis = 4000*mtorad
        var bounds = L.latLngBounds([position.coords.latitude + mcdis , position.coords.longitude + mcdis],[position.coords.latitude - mcdis , position.coords.longitude - mcdis]);
        var sw=bounds.getSouthWest();
        var ne=bounds.getNorthEast();
        sendEvent([ne.lat,ne.lng,0,sw.lat,sw.lng,0].map(function(e){return e.toString()}));

    }, function() {
      handleLocationError(true, null );
    });
    }
    $(el).bind(eventType,fun);
    return fun;
   }

}
};
