/*
HtmlClipper v0.1

Made by Florentin Sardan
florentinwww (at) gmail.com

Project's page:
  http://www.betterprogramming.com/htmlclipper.html
My portfolio:
  http://www.betterprogramming.com
*/

String.prototype.startsWith = function(str) {return (this.match("^"+str)==str);};
String.prototype.endsWith = function(str) {return (this.match(str+"$")==str);};
String.prototype.format = function(){
  var pattern = /\{\d+\}/g;
  var args = arguments;
  return this.replace(pattern, function(capture){ return args[capture.match(/\d+/)]; });
};
String.prototype.trim = function() {  return this.replace(/^\s+|\s+$/g,""); };
// var result = "Hello {0}! This is {1}.".format("world","foo bar");

Array.prototype.contains = function(obj) {
    var i = this.length;
    while (i--) {
        if (this[i].toLowerCase() == obj.toLowerCase()) {
            return true;
        }
    }
    return false;
};


var flo = new function() {
  var d = document;
  var sessionCode = randomString(3);
  var lastObj = [];
  var activeObj = null;
  var cachedStyles = {};
  var global = []; // temporary tests
  var styleTpl = ".{0} { {1} }\n";
  var properties = ["opacity","filter","azimuth","background","background-attachment","background-color","background-image","background-position","background-repeat","border","border-collapse","border-color","border-spacing","border-style","border-top","border-right","border-bottom","border-left","border-top-color","border-right-color","border-bottom-color","border-left-color","border-top-style","border-right-style","border-bottom-style","border-left-style","border-top-width","border-right-width","border-bottom-width","border-left-width","border-width","bottom","caption-side","clear","clip","color","content","counter-increment","counter-reset","cue","cue-after","cue-before","cursor","direction","display","elevation","empty-cells","css-float","font","font-family","font-size","font-size-adjust","font-stretch","font-style","font-variant","font-weight","height","left","letter-spacing","line-height","list-style","list-style-image","list-style-position","list-style-type","margin","margin-top","margin-right","margin-bottom","margin-left","marker-offset","marks","max-height","max-width","min-height","min-width","orphans","outline","outline-color","outline-style","outline-width","overflow","padding","padding-top","padding-right","padding-bottom","padding-left","page","page-break-after","page-break-before","page-break-inside","pause","pause-after","pause-before","pitch","pitch-range","play-during","position","quotes","richness","right","size","speak","speak-header","speak-numeral","speak-punctuation","speech-rate","stress","table-layout","text-align","text-decoration","text-indent","text-shadow","text-transform","top","unicode-bidi","vertical-align","visibility","voice-family","volume","white-space","widows","width","word-spacing","z-index"].sort();

  
  /* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  */
  /*  SHA-1 implementation in JavaScript (c) Chris Veness 2002-2009                                 */
  /* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  */

  function sha1Hash(msg) {
      // constants [§4.2.1]
      var K = [0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xca62c1d6];

      // PREPROCESSING 
   
      msg += String.fromCharCode(0x80); // add trailing '1' bit (+ 0's padding) to string [§5.1.1]

      // convert string msg into 512-bit/16-integer blocks arrays of ints [§5.2.1]
      var l = msg.length/4 + 2;  // length (in 32-bit integers) of msg + ‘1’ + appended length
      var N = Math.ceil(l/16);   // number of 16-integer-blocks required to hold 'l' ints
      var M = new Array(N);
      for (var i=0; i<N; i++) {
          M[i] = new Array(16);
          for (var j=0; j<16; j++) {  // encode 4 chars per integer, big-endian encoding
              M[i][j] = (msg.charCodeAt(i*64+j*4)<<24) | (msg.charCodeAt(i*64+j*4+1)<<16) | 
                        (msg.charCodeAt(i*64+j*4+2)<<8) | (msg.charCodeAt(i*64+j*4+3));
          }
      }
      // add length (in bits) into final pair of 32-bit integers (big-endian) [5.1.1]
      // note: most significant word would be (len-1)*8 >>> 32, but since JS converts
      // bitwise-op args to 32 bits, we need to simulate this by arithmetic operators
      M[N-1][14] = ((msg.length-1)*8) / Math.pow(2, 32); M[N-1][14] = Math.floor(M[N-1][14]);
      M[N-1][15] = ((msg.length-1)*8) & 0xffffffff;

      // set initial hash value [§5.3.1]
      var H0 = 0x67452301;
      var H1 = 0xefcdab89;
      var H2 = 0x98badcfe;
      var H3 = 0x10325476;
      var H4 = 0xc3d2e1f0;

      // HASH COMPUTATION [§6.1.2]

      var W = new Array(80); var a, b, c, d, e;
      for (var i=0; i<N; i++) {

          // 1 - prepare message schedule 'W'
          for (var t=0;  t<16; t++) W[t] = M[i][t];
          for (var t=16; t<80; t++) W[t] = ROTL(W[t-3] ^ W[t-8] ^ W[t-14] ^ W[t-16], 1);

          // 2 - initialise five working variables a, b, c, d, e with previous hash value
          a = H0; b = H1; c = H2; d = H3; e = H4;

          // 3 - main loop
          for (var t=0; t<80; t++) {
              var s = Math.floor(t/20); // seq for blocks of 'f' functions and 'K' constants
              var T = (ROTL(a,5) + f(s,b,c,d) + e + K[s] + W[t]) & 0xffffffff;
              e = d;
              d = c;
              c = ROTL(b, 30);
              b = a;
              a = T;
          }

          // 4 - compute the new intermediate hash value
          H0 = (H0+a) & 0xffffffff;  // note 'addition modulo 2^32'
          H1 = (H1+b) & 0xffffffff; 
          H2 = (H2+c) & 0xffffffff; 
          H3 = (H3+d) & 0xffffffff; 
          H4 = (H4+e) & 0xffffffff;
      }

      return H0.toHexStr() + H1.toHexStr() + H2.toHexStr() + H3.toHexStr() + H4.toHexStr();
  }

  //
  // function 'f' [§4.1.1]
  //
  function f(s, x, y, z) {
  	switch (s) {
  	case 0: return (x & y) ^ (~x & z);           // Ch()
  	case 1: return x ^ y ^ z;                    // Parity()
  	case 2: return (x & y) ^ (x & z) ^ (y & z);  // Maj()
  	case 3: return x ^ y ^ z;                    // Parity()
  	}
  }

  //
  // rotate left (circular left shift) value x by n positions [§3.2.5]
  //
  function ROTL(x, n) {
    return (x<<n) | (x>>>(32-n));
  }

  //
  // extend Number class with a tailored hex-string method 
//     (note toString(16) is implementation-dependant, and 
//     in IE returns signed numbers when used on full words)
  //
  Number.prototype.toHexStr = function() {
      var s="", v;
      for (var i=7; i>=0; i--) { v = (this>>>(i*4)) & 0xf; s += v.toString(16); }
      return s;
  };
  /* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  */

  function convertRGB(str) {
    var start = str.indexOf('rgb(');
    var end = str.indexOf(')', start);
    if (start == -1 || end == -1) {
        return str;
    }

    var col = str.slice(start + 4, end).replace(/ +/g, '');
    var rgbArray = col.split(',');
    var colourStr = '#' + (rgbArray[0] << 16 | rgbArray[1] << 8 | rgbArray[2]).toString(16);
    while (colourStr.length < 7) {
        colourStr += '0';
    }
    return str.substr(0, start) + colourStr + str.substring(end + 1);
  };
  
  function unquoteXml (result) {
    result = result.replace(/&lt;/g, "<");
    result = result.replace(/&gt;/g, ">");
    result = result.replace(/&quot;/g, "\"");
    result = result.replace(/&apos;/g, "'");
    return result;
  }

  function len(obj) {
    var total = 0; 
    for(var key in obj) { 
      total +=1; 
    };
    return total;
  };
  
  function getXPathForElement(el, xml) {
    var xpath = '';
    var pos, tempitem2;
    
    while(el !== xml.documentElement) {   
      pos = 0;
      tempitem2 = el;
      while(tempitem2) {
        if (tempitem2.nodeType === 1 && tempitem2.nodeName === el.nodeName) { // If it is ELEMENT_NODE of the same name
          pos += 1;
        }
        tempitem2 = tempitem2.previousSibling;
      }
      //xpath = "*[name()='"+el.nodeName+"']["+pos+']'+'/'+xpath;
      xpath = el.nodeName+"["+pos+']'+'/'+xpath;
      el = el.parentNode;
    }
    //xpath = '/*'+"[name()='"+xml.documentElement.nodeName+"']"+'/'+xpath;
    xpath = '/'+xml.documentElement.nodeName+'/'+xpath;
    xpath = xpath.replace(/\/$/, '');
    return xpath;
  };

  function so_removeObj() {
    activeObj.parentNode.removeChild(activeObj);
  }
  
  function so_cleanUp() {
    var popup = d.getElementById('flo-popup');
    if (popup)
      d.documentElement.removeChild(popup);
  };
  
  function count(obj) {
    var element_count = 0;
    for (e in obj) { element_count++; }
    return element_count;
  };
  
  function so_showParentObj() {
    if(activeObj.parentNode && activeObj.tagName != "HTML") {
      change_active(activeObj.parentNode);
    }
  };
  
  function randomString(length) {
    var length = length ? length : 10;
    var chars = "abcdefghijklmnopqrstuvwxyz";
    var pass = "";
    for(var x=0;x<length;x++) {
       var i = Math.floor(Math.random() * 26);
       pass += chars.charAt(i);
    }
    return pass;
  };
  
  function getView(node, doc) {
    if (node && node.nodeType==1) {
      var view = doc.defaultView ? doc.defaultView.getComputedStyle(node, null):node.currentStyle;
    }
    else {
      var view = null;
    }
    return view;
  };
  
  function getPopup() {
    var popup = d.createElement("div");
    popup.setAttribute('id', 'flo-popup');
    popup.style.cssText='position: absolute;top: 10%;left: 10%;width: 80%;height: 80%;padding: 16px;border: 16px solid orange;background-color: white;z-index:10000000000;overflow: auto;';
    return popup;
  };
  
  function getTextarea() {
    var ta = d.createElement("textarea");
    ta.setAttribute('id', 'flo-textarea');
    ta.style.cssText='width:99%;height:200px';
    return ta;
  };
  
  function getIframe() {
    var iframe = d.createElement("iframe");
    iframe.src = "/";
    iframe.setAttribute('id', 'flo-iframe');
    iframe.style.width = '99%';
    iframe.style.height = '70%';
    iframe.style.background = '#FFF';
    
    /*
    //idoc.open();
    idoc.write(htmlcontent);
    idoc.close();
    */
    return iframe;
  };
  
  function getStyle(node, doc) {
    // return all the style attributes of a node
    var result = {};
    var ncs = getView(node, doc);
    if (!ncs) return result;

    for (var i=0; i<ncs.length; ++i) {
      var e = ncs.item(i); // style name
      if (e==undefined) continue;
      if (e.startsWith('-moz-')) continue;
      // TODO: enable this ?
      //if (!properties.contains(e)) continue;
      var v = ncs.getPropertyValue(e); // style value
      /*
      if (v.startsWith('rgb')) {
        v = convertRGB(v);
      }
      */
      result[e] = v;
    }
    return result;
  };
  
  function unserializeStyle(str) {
    var result = {};
    if (!str) return result;
    var parts = str.split(' ; ');
    //parts.pop(); // str ends with ; so parts[-1] will be empty

    for (var i=0;i<parts.length;i++) {
      if (!parts[i]) continue;
      var ev = parts[i].split(' : ');
      result[ev[0]] = ev[1];
    }
    return result;
  };
  
  function serializeStyle(obj) {
    var result = '';
    for (var key in obj) {
      result += key+" : "+obj[key]+" ; ";
    }
    return result.trim();
  };
  
  function getTargetNode(node) {
    // given node, sets an attribute called "flo-style" on each child with the current style
    var backupNode = node.cloneNode(true);
    setStyleOnNode(node);
    node.parentNode.replaceChild(backupNode, node);
    delete backupNode;
    return node;
  };
  
  /*
  function deleteAllStyles(doc) {
    for (var i=0;i < doc.styleSheets.length;i++) {
      var sstyle = doc.styleSheets.item(i);
      var srules = sstyle.cssRules;
      for(var j=0;j<srules.length;i++) {
        sstyle.deleteRule(j);
      }
    }
  }
  */
  
  function disableAllStyles(doc, how) {
    if (how==null) how = true;
    for (var i in doc.styleSheets.length) {
      doc.styleSheets.item(i).disabled = how;
    }
  };
  
  function diffStyle(defaultStyle, nodeStyle) {
    result = {};
    for (var key in nodeStyle) {
      if ( defaultStyle[key]!=nodeStyle[key] ) { // key.match('^border\-.*?\-width$') ||
        result[key] = nodeStyle[key];
      }
    }
    return result;
  }
  
  function setStyleOnNode(node) {
    var newStyle = getStyle(node, d);
    var hash = sha1Hash(newStyle);
    var nodeId = node.tagName.toLowerCase()+"-"+len(cachedStyles)+"-"+sessionCode;
    
    cachedStyles[nodeId] = {'master':newStyle, 'style':newStyle, 'cls':nodeId, 'hash':hash}; // style, class name, style hash
    node.setAttribute('flo-id', nodeId); // overwrite any old classes

    for (var i=0, l=node.children.length;i<l;i++) {
      setStyleOnNode(node.children.item(i));
    }
  };
  
  function cleanIframeStyleNode(doc, node, dontfollow) {
    // reads the final node style, removes it's class, reads the default style, compute the difference and update the styles cache
    // later all the styles are rescribed
    var nodeId = node.getAttribute('flo-id');
    if (nodeId==null) return false;

    var cachedStyle = cachedStyles[nodeId];
    
    // remove existing class and style
    node.removeAttribute('class');
    node.removeAttribute('style');
    //node.setAttribute('class', cachedStyle.cls);
    
    var defaultStyle = getStyle(node, doc);
    var floStyle = cachedStyle.master;
    var diffObj = diffStyle(defaultStyle, floStyle);

    function whatup(diffObj) {
      cachedStyle.style = diffObj;
      setClassForStyle(doc, cachedStyle);
      replaceIframeStyle(doc, cachedStyle.cls, cachedStyle.style);
      node.setAttribute('class', cachedStyle.cls);
    }
    
    if (len(diffObj)) {
      whatup(diffObj);

      var newStyle = getStyle(node, doc);
      var diffObjNew = diffStyle(newStyle, floStyle);
      // more differences ?
      if (len(diffObjNew)) {
        for (var key in diffObjNew) {
          diffObj[key] = diffObjNew[key];
        }
        whatup(diffObj);
      }
    }
    else {
      cachedStyle.style = null;
      replaceIframeStyle(doc, cachedStyle.cls);
    }
    
    node.removeAttribute('flo-style');
    node.removeAttribute('flo-id');
    
    if (dontfollow==undefined) {
      cleanIframeStyle(doc, node);
    }
  }
  
  function cleanIframeStyle(doc, node) {
    var children=node.children;
    if (!children.length) return;
    for (var i=0;i < children.length;i++) {
      cleanIframeStyleNode(doc, children.item(i));
    }
  }
  
  function setClassForStyle(doc, cachedStyle) {
    // TODO: need to fix this, only choose a style of a node which was already processed
    for (var key in cachedStyles) {
      if (cachedStyles[key].cls==cachedStyle.cls) return false;
      if (serializeStyle(cachedStyles[key].style)==serializeStyle(cachedStyle.style)) {
        replaceIframeStyle(doc, cachedStyle.cls); // remove unused class
        cachedStyle.cls = cachedStyles[key].cls;
        return true;
      }
    }
    return false;
  }
  
  function replaceIframeStyle(doc, className, styleObj) {
    var styleText = serializeStyle(styleObj);
    // if cachedStyle is undefined, only delete the className rule
    var sstyle = doc.styleSheets.item(1);
    var srules = sstyle.cssRules;

    for (var index=0;index<srules.length;index++) {
      if (srules.item(index).selectorText=="."+className) {
        sstyle.deleteRule(index);
        if (styleText) {
          sstyle.insertRule(styleTpl.format(className,  styleText) , index);
        }
      }
    }
  }
  
  function renewIframeStyles(doc) {
    // TODO: remove old styles
    var sstyle = doc.styleSheets.item(1);
    var srules = sstyle.cssRules;
    
    for (var key in cachedStyles) {
      sstyle.insertRule(styleTpl.format(cachedStyles[key].cls,  serializeStyle(cachedStyles[key].style)) , srules.length);
    }
  }

  function getIframeWindow(iframeElement){
    return iframeElement.contentWindow || iframeElement.contentDocument.parentWindow;
  }
  
  function showStyle() {
    clean_active();
    cachedStyles = {}; // clean style cache
    // TODO: don't use global cachedStyles anymore

    var node = activeObj;
    var targetNode = getTargetNode(node);

    var popup = getPopup();
    var iframe = getIframe();
    var textarea = getTextarea();
    
    d.documentElement.appendChild(popup);
    popup.appendChild(iframe);
    
    var iframewin = getIframeWindow(iframe);
    var idoc = iframewin.document;
    if(idoc == null) throw "Document not initialized";
    
    var tempNode = idoc.createElement('div');
    tempNode.appendChild(targetNode);
    
    //var resetCss = '<link rel="stylesheet" type="text/css" href="http://yui.yahooapis.com/2.8.0r4/build/reset/reset-min.css" />'+"\n";
    var xresetCss = '<style type="text/css">html{color:#000;background:#FFF;}body,div,dl,dt,dd,ul,ol,li,h1,h2,h3,h4,h5,h6,pre,code,form,fieldset,legend,input,button,textarea,p,blockquote,th,td{margin:0;padding:0;}table{border-collapse:collapse;border-spacing:0;}fieldset,img{border:0;}address,caption,cite,code,dfn,em,strong,th,var,optgroup{font-style:inherit;font-weight:inherit;}del,ins{text-decoration:none;}li{list-style:none;}caption,th{text-align:left;}h1,h2,h3,h4,h5,h6{font-size:100%;font-weight:normal;}q:before,q:after{content:\'\';}abbr,acronym{border:0;font-variant:normal;}sup{vertical-align:baseline;}sub{vertical-align:baseline;}legend{color:#000;}input,button,textarea,select,optgroup,option{font-family:inherit;font-size:inherit;font-style:inherit;font-weight:inherit;}input,button,textarea,select{*font-size:100%;}body{font:13px/1.231 arial,helvetica,clean,sans-serif;*font-size:small;*font:x-small;}select,input,button,textarea,button{font:99% arial,helvetica,clean,sans-serif;}table{font-size:inherit;font:100%;}pre,code,kbd,samp,tt{font-family:monospace;*font-size:108%;line-height:100%;}body{text-align:center;}#doc,#doc2,#doc3,#doc4,.yui-t1,.yui-t2,.yui-t3,.yui-t4,.yui-t5,.yui-t6,.yui-t7{margin:auto;text-align:left;width:57.69em;*width:56.25em;}#doc2{width:73.076em;*width:71.25em;}#doc3{margin:auto 10px;width:auto;}#doc4{width:74.923em;*width:73.05em;}.yui-b{position:relative;}.yui-b{_position:static;}'+
                    '#yui-main .yui-b{position:static;}#yui-main,.yui-g .yui-u .yui-g{width:100%;}.yui-t1 #yui-main,.yui-t2 #yui-main,.yui-t3 #yui-main{float:right;margin-left:-25em;}.yui-t4 #yui-main,.yui-t5 #yui-main,.yui-t6 #yui-main{float:left;margin-right:-25em;}.yui-t1 .yui-b{float:left;width:12.30769em;*width:12.00em;}.yui-t1 #yui-main .yui-b{margin-left:13.30769em;*margin-left:13.05em;}.yui-t2 .yui-b{float:left;width:13.8461em;*width:13.50em;}.yui-t2 #yui-main .yui-b{margin-left:14.8461em;*margin-left:14.55em;}.yui-t3 .yui-b{float:left;width:23.0769em;*width:22.50em;}.yui-t3 #yui-main .yui-b{margin-left:24.0769em;*margin-left:23.62em;}.yui-t4 .yui-b{float:right;width:13.8456em;*width:13.50em;}.yui-t4 #yui-main .yui-b{margin-right:14.8456em;*margin-right:14.55em;}.yui-t5 .yui-b{float:right;width:18.4615em;*width:18.00em;}.yui-t5 #yui-main .yui-b{margin-right:19.4615em;*margin-right:19.125em;}.yui-t6 .yui-b{float:right;width:23.0769em;*width:22.50em;}.yui-t6 #yui-main .yui-b{margin-right:24.0769em;*margin-right:23.62em;}.yui-t7 #yui-main .yui-b{display:block;margin:0 0 1em 0;}#yui-main .yui-b{float:none;width:auto;}.yui-gb .yui-u,.yui-g .yui-gb .yui-u,.yui-gb .yui-g,.yui-gb .yui-gb,.yui-gb .yui-gc,.yui-gb .yui-gd,.yui-gb .yui-ge,.yui-gb .yui-gf,.yui-gc .yui-u,.yui-gc .yui-g,.yui-gd .yui-u{float:left;}'+
                    '.yui-g .yui-u,.yui-g .yui-g,.yui-g .yui-gb,.yui-g .yui-gc,.yui-g .yui-gd,.yui-g .yui-ge,.yui-g .yui-gf,.yui-gc .yui-u,.yui-gd .yui-g,.yui-g .yui-gc .yui-u,.yui-ge .yui-u,.yui-ge .yui-g,.yui-gf .yui-g,.yui-gf .yui-u{float:right;}.yui-g div.first,.yui-gb div.first,.yui-gc div.first,.yui-gd div.first,.yui-ge div.first,.yui-gf div.first,.yui-g .yui-gc div.first,.yui-g .yui-ge div.first,.yui-gc div.first div.first{float:left;}.yui-g .yui-u,.yui-g .yui-g,.yui-g .yui-gb,.yui-g .yui-gc,.yui-g .yui-gd,.yui-g .yui-ge,.yui-g .yui-gf{width:49.1%;}.yui-gb .yui-u,.yui-g .yui-gb .yui-u,.yui-gb .yui-g,.yui-gb .yui-gb,.yui-gb .yui-gc,.yui-gb .yui-gd,.yui-gb .yui-ge,.yui-gb .yui-gf,.yui-gc .yui-u,.yui-gc .yui-g,.yui-gd .yui-u{width:32%;margin-left:1.99%;}.yui-gb .yui-u{*margin-left:1.9%;*width:31.9%;}.yui-gc div.first,.yui-gd .yui-u{width:66%;}.yui-gd div.first{width:32%;}.yui-ge div.first,.yui-gf .yui-u{width:74.2%;}.yui-ge .yui-u,.yui-gf div.first{width:24%;}.yui-g .yui-gb div.first,.yui-gb div.first,.yui-gc div.first,.yui-gd div.first{margin-left:0;}.yui-g .yui-g .yui-u,.yui-gb .yui-g .yui-u,.yui-gc .yui-g .yui-u,.yui-gd .yui-g .yui-u,.yui-ge .yui-g .yui-u,.yui-gf .yui-g .yui-u{width:49%;*width:48.1%;*margin-left:0;}.yui-g .yui-g .yui-u{width:48.1%;}.yui-g .yui-gb div.first,.yui-gb .yui-gb div.first{*margin-right:0;*width:32%;_width:31.7%;}.yui-g .yui-gc div.first,.yui-gd .yui-g{width:66%;}.yui-gb .yui-g div.first{*margin-right:4%;_margin-right:1.3%;}.yui-gb .yui-gc div.first,.yui-gb .yui-gd div.first{*margin-right:0;}.yui-gb .yui-gb .yui-u,.yui-gb .yui-gc .yui-u{*margin-left:1.8%;_margin-left:4%;}'+
                    '.yui-g .yui-gb .yui-u{_margin-left:1.0%;}.yui-gb .yui-gd .yui-u{*width:66%;_width:61.2%;}.yui-gb .yui-gd div.first{*width:31%;_width:29.5%;}.yui-g .yui-gc .yui-u,.yui-gb .yui-gc .yui-u{width:32%;_float:right;margin-right:0;_margin-left:0;}.yui-gb .yui-gc div.first{width:66%;*float:left;*margin-left:0;}.yui-gb .yui-ge .yui-u,.yui-gb .yui-gf .yui-u{margin:0;}.yui-gb .yui-gb .yui-u{_margin-left:.7%;}.yui-gb .yui-g div.first,.yui-gb .yui-gb div.first{*margin-left:0;}.yui-gc .yui-g .yui-u,.yui-gd .yui-g .yui-u{*width:48.1%;*margin-left:0;}.yui-gb .yui-gd div.first{width:32%;}.yui-g .yui-gd div.first{_width:29.9%;}.yui-ge .yui-g{width:24%;}.yui-gf .yui-g{width:74.2%;}.yui-gb .yui-ge div.yui-u,.yui-gb .yui-gf div.yui-u{float:right;}.yui-gb .yui-ge div.first,.yui-gb .yui-gf div.first{float:left;}.yui-gb .yui-ge .yui-u,.yui-gb .yui-gf div.first{*width:24%;_width:20%;}.yui-gb .yui-ge div.first,.yui-gb .yui-gf .yui-u{*width:73.5%;_width:65.5%;}.yui-ge div.first .yui-gd .yui-u{width:65%;}.yui-ge div.first .yui-gd div.first{width:32%;}#hd:after,#bd:after,#ft:after,.yui-g:after,.yui-gb:after,.yui-gc:after,.yui-gd:after,.yui-ge:after,.yui-gf:after{content:".";display:block;height:0;clear:both;visibility:hidden;}#hd,#bd,#ft,.yui-g,.yui-gb,.yui-gc,.yui-gd,.yui-ge,.yui-gf{zoom:1;}</style>';
    var xresetCss = '<style type="text/css">html, body, div, span, object, iframe, h1, h2, h3, h4, h5, h6, p, blockquote, pre, a, abbr, acronym, address, code, del, dfn, em, img, q, dl, dt, dd, ol, ul, li, fieldset, form, label, legend, table, caption, tbody, tfoot, thead, tr, th, td {margin:0;padding:0;border:0;font-weight:inherit;font-style:inherit;font-size:100%;font-family:inherit;vertical-align:baseline;}body {line-height:1.5;}table {border-collapse:separate;border-spacing:0;}caption, th, td {text-align:left;font-weight:normal;}table, td, th {vertical-align:middle;}blockquote:before, blockquote:after, q:before, q:after {content:"";}blockquote, q {quotes:"" "";}a img {border:none;}</style>';
    var resetCss = '<style type="text/css"></style>';
    var tpl = '<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">'+"\n"+
              '<html><head><meta http-equiv="Content-Type" content="text/html; charset=utf-8" />'+"\n"+
              resetCss+
              '<style type="text/css">'+"\n{0}\n</style>\n"+
              "</head><body>\n{1}\n</body></html>";
    idoc.write(tpl.format('', tempNode.innerHTML));
    
    //disableAllStyles(d, true);
    renewIframeStyles(idoc); // append each style from cachedStyles to the iframe's stylesheets
    cleanIframeStyle(idoc, idoc.body); // .children[0] (leave the parent node alone)
    //disableAllStyles(d, false);
    idoc.close();

    // read all styles
    var cssText = '';
    var sheet=idoc.styleSheets.item(1);
    var rules = sheet.cssRules;
    for(var i=0;i<rules.length;i++) {
      cssText += rules.item(i).cssText+"\n";
    }
    textarea.value = tpl.format(cssText, idoc.body.innerHTML); 
    popup.appendChild(textarea);
  };
  
  function clean_active() {
    if (activeObj) activeObj.style.outline = '';
    el = d.getElementById('flo-xpath');
    if (el) el.parentNode.removeChild(el);
    //activeObj.removeChild(activeObj.getElementById('xpath'));
  };
  
  function change_active(newobj, undo) {
    if (newobj) {
      if (activeObj) {
        clean_active();
        if (!undo)
          lastObj.push(activeObj);
      }

      newobj.style.outline = '#f00 solid 2px';
      activeObj = newobj;
      var tempNode = d.createElement('div');
      tempNode.setAttribute('id', 'flo-xpath');
      tempNode.style.cssText='background-color:yellow;font-size:10px;top:0px;left:0px;position:absolute;';
      tempNode.innerHTML = getXPathForElement(activeObj, d);
      d.documentElement.appendChild(tempNode);
    }
  };
  
  function clickEvent(event) {
    event.preventDefault();
    var node = event.target;
    // ignore click on my own elements
    if (!node.getAttribute('id') || !node.getAttribute('id').startsWith('flo-')) {
      change_active(node);
    }
  }
  
  function so_exit() {
    clean_active();
    d.removeEventListener('keydown', so_captureKeyDownEvent, false);
    d.removeEventListener('click', clickEvent, false);
    alert("HtmlClipper is Off !");
  }
  
  function browser_supported() {
    if(navigator.product == 'Gecko')
      return true;
    else
      return false;
  }
  
  this.init = function() {
    if(!browser_supported()) {
      alert("HtmlClipper only works on Firefox or Chrome.");
      return false;
    }
    d.addEventListener('keydown', so_captureKeyDownEvent, false);
    d.addEventListener('click', clickEvent, false);
    /*
    d.addEventListener('mouseover', downEvent, false)
    */
    
    alert("HtmlClipper is On !\n\n" +
    		 "Click anywhere to select an element.\n"+
    		 "type W to select the parent element\n"+
    		 "type Q to undo selection of parent element\n"+
    		 "type R to remove the selected element\n"+
    		 "type S to clip the selected element\n"+
    		 "type ESC to remove the clip window\n"+
    		 "type X to exit HtmlClipper\n"
    )
  };
  
  function so_captureKeyDownEvent(e) {
    var keyCode = d.all?window.event.keyCode:e.keyCode;

    switch(keyCode) {
      case 27: // esc
        so_cleanUp();
        break;
      case 82: // R
        so_removeObj();
        break;
      case 83: // S
        showStyle();
        //showStylePop();
        break;
      case 81: // Q
        change_active(lastObj.pop(), true);
        break;
      case 87: // W
        so_showParentObj();
        break;
      case 88: // x
        so_exit();
        break;
    }
  };  

};

flo.init();

// TODO: parent/body background ?

// TODO: replace relative urls with absolute ones
// TODO: wrapper element must have full class
// TODO: a:hover
// TODO: add siblings
