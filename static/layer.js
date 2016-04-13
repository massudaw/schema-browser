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

function createMap (ref,posj,nej,swj,features){
  var points = JSON.parse(features);
      pos = JSON.parse(posj);
      
  mymap = L.map(ref);
  if (pos == null) {
      navigator.geolocation.getCurrentPosition(function(position) {
      mymap.setView([position.coords.latitude, position.coords.longitude], 12);
    }, function() {
      handleLocationError(true, map.getCenter());
    });
  }else {
      ne = JSON.parse(nej);
      sw  = JSON.parse(swj);
    mymap.fitBounds([ne,sw]);
  }

  points.map (function (l){ l.map (function (p){ 
    var popup = L.popup()
          .setLatLng(p.position)
              .setContent(p.title);
    
    L.circle(p.position,p.size,{color:p.color}).addTo(mymap).bindPopup(popup);})})
	var osmUrl='http://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png';
	var osmAttrib='Map data © <a href="http://openstreetmap.org">OpenStreetMap</a> contributors';
	var osm = L.tileLayer(osmUrl, { maxZoom: 18, attribution: osmAttrib}).addTo(mymap);	
}


function handleLocationError(browserHasGeolocation, pos) {
  alert(browserHasGeolocation ?
                        'Error: The Geolocation service failed.' :
                        'Error: Your browser doesn\'t support geolocation.');
}


function createAgenda(el,date,evs,view){
$(el).fullCalendar({header: { left: '',center: 'title' , right: ''},defaultDate: date,lang: 'pt-br',editable: true,eventLimit: true,events: JSON.parse(evs), defaultView : view ,eventDrop : el.eventDrop , eventResize: el.eventResize, drop : el.drop, droppable:true});

};

function clientHandlers(){
  return {'moveend': function(el,elid,eventType,sendEvent){
    mymap.on(eventType,function(e) {
    var bounds = mymap.getBounds();
    var center =bounds.getCenter();
    var sw=bounds.getSouthWest();
    var ne=bounds.getNorthEast();
    sendEvent(elid,eventType,[center.lat,center.lng,ne.lat,ne.lng,sw.lat,sw.lng].map(function(e){return e.toString()}));
    return true;
    });
    }
   ,'eventDrop' : function(el,elid,eventType,sendEvent){
      el.eventDrop =  function(e,delta,revert) {
      sendEvent(elid,eventType,[e.id,(new Date(e.start)).toISOString(),e.end === null ? null : new Date(e.end).toISOString()].filter(function(e) {return e !== null}).map(function(e){return  e.toString()}));
      return true;
      }; 
      }
   ,'eventResize' : function(el,elid,eventType,sendEvent){
      el.eventResize =  function(e,delta,revert) {
      sendEvent(elid,eventType,[e.id,e == null ? null :new Date (e.start).toISOString(),e.end == null ? null:new Date (e.end).toISOString() ].filter(function(e) {return e !== null}).map(function(e){return e.toString()}));
      return true;
      }; 
      }
   
   ,'externalDrop' : function(el,elid,eventType,sendEvent){
      el.drop =  function(e,revert) {
      var evdata = $(this).data('event');
      sendEvent(elid,eventType,[evdata.id,e == null ? null :new Date (e).toISOString() ].filter(function(e) {return e !== null}).map(function(e){return e.toString()}));
      return true;
      }; 
      }
   }

};
