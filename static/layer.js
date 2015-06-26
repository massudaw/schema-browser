function setOpts(oSelect,selVals) {
  var opt, i = 0;
  while (opt = oSelect[i++]) {
    var sel= false
    for(var j =0 ; j< selVals.length;j ++){
      if(selVals[i] == opt.index)  sel = true;
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
  var value = [];
  if (f[0].files.length == 1 ){
      value = [f[0].files[0].filevalue];
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

