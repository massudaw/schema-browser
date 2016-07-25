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
function handleFileSelect(evt) {
    var files = evt.target.files; // FileList object
    // Loop through the FileList and render image files as thumbnails.
    for (var i = 0, f; f = files[i]; i++) {
      var reader = new FileReader();

      // Closure to capture the file information.
      reader.onload = (function(theFile) {
        return function(e) {
          // Render thumbnail.
          theFile.filevalue = e.target.result
        };
      })(f);

      // Read in the image file as a data URL.
      reader.readAsDataURL(f);
    }
  }

function createLayers (ref,posj,nej,swj,features){
  var points = JSON.parse(features);
  ref.layer.clearLayers();
  layers = points.map (function (l){ l.map (function (p){ 
  var popup = L.popup()
        .setLatLng(p.position)
            .setContent(p.title + '\n' + p.position.toString());
  ref.layer.addLayer(L.circle(p.position,p.size,{color:p.color}).bindPopup(popup));})})
}


function createMap (ref,posj,nej,swj,features){
  pos = JSON.parse(posj);
  ref.mymap = L.map(ref);
  if (pos == null) {
      navigator.geolocation.getCurrentPosition(function(position) {
      ref.mymap.setView([position.coords.latitude, position.coords.longitude], 12);
    }, function() {
      handleLocationError(true, map.getCenter());
    });
  }else {
      ne = JSON.parse(nej);
      sw  = JSON.parse(swj);
    ref.mymap.fitBounds([ne,sw]);
  }
  ref.layer= L.layerGroup().addTo(ref.mymap);

  var osmUrl='http://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png';
  var osmAttrib='Map data © <a href="http://openstreetmap.org">OpenStreetMap</a> contributors';
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
  var content = '<h3>'+data.title+'</h3>' + 
      '<p><b>'+ data.field +':</b> '+new Date(data.start).toString()+'<br />' + 
      (data.end && '<p><b>End:</b> '+data.end+'</p>' || '');
  if (el.opentip != null ){
    $('.qtip').each(function(){
        $(this).data('qtip').destroy();
    })
  }
  var tooltip = $('<div/>').qtip({
    prerender: true,
    content: {
      text: ' ',
      title: {
        button: true
      }
    },
    position: {
      my: 'bottom center',
      at: 'top center',
      target: 'mouse',
      adjust: {
        mouse: false,
        scroll: false
      }
    },
    show: false,
    hide: false,
    style: 'qtip-light'
  }).qtip('api');

  tooltip.set({'content.text': content
              }).reposition(event).show(event);
  el.opentip = tooltip;
          }});
  $(el).fullCalendar('render');
};

function renderCal(el){
  $(el).fullCalendar('render');
}

function addSource(el,table,source){
  $(el).fullCalendar('removeEvents',function(e) { return e.table ==table});
  $(el).fullCalendar('addEventSource',JSON.parse(source));
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
   ,'currentPosition' : function(el,eventType ,sendEvent){
    $(el).bind(eventType,function(){
      navigator.geolocation.getCurrentPosition(function(position) {
        el.mymap.setView([position.coords.latitude, position.coords.longitude], 12);
        var bounds = el.mymap.getBounds();
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
