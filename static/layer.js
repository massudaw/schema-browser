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


