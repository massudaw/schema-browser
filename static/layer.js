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

  points.map (function (l){ l.map (function (p){ L.circle(p.position,p.size,{color:p.color}).addTo(mymap);})})
	var osmUrl='http://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png';
	var osmAttrib='Map data © <a href="http://openstreetmap.org">OpenStreetMap</a> contributors';
	var osm = L.tileLayer(osmUrl, { maxZoom: 18, attribution: osmAttrib}).addTo(mymap);	
}


function handleLocationError(browserHasGeolocation, pos) {
  alert(browserHasGeolocation ?
                        'Error: The Geolocation service failed.' :
                        'Error: Your browser doesn\'t support geolocation.');
}


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
  }}}
