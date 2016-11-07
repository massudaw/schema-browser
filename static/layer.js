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
   var head = L.circle(latlonA[0],p.size/3,{color:p.color});
   head.on('click',function(e ){ref.eventClick(p,e);});
   layer.addLayer(head);
   var tail = L.circle(latlonA[1],p.size/4,{color:p.color});
   tail.on('click',function(e ){ref.eventClick(p,e);});
   layer.addLayer(tail);
  }
  else{
  feature = L.circle(p.position,p.size,{color:p.color}); 
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


function createAgenda(el,tdate,view){
  var date = new Date(tdate);
  var d = date.getDate();
  var m = date.getMonth();
  var y = date.getFullYear();

  $(el).fullCalendar({header: { left: '',center: 'title' , right: ''},defaultDate: date,lang: 'pt-br',editable: true,eventLimit: true, defaultView : view ,eventDrop : el.eventDrop , eventResize: el.eventResize, drop : el.drop, droppable:true ,eventClick: function(data, event, view) {
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
