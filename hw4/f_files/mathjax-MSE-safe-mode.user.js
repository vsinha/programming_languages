// ==UserScript==
// @name           Remove unsafe TeX macros StackExchange
// @namespace      http://www.mathjax.org/
// @description    Redefines or removes MathJax TeX macros that can be abused in StackExchange
// @include        http://stats.stackexchange.com/*
// @include        http://meta.stats.stackexchange.com/*
// @include        http://math.stackexchange.com/*
// @include        http://meta.math.stackexchange.com/*
// @include        http://cstheory.stackexchange.com/*
// @include        http://meta.cstheory.stackexchange.com/*
// @include        http://electronics.stackexchange.com/*
// @include        http://meta.electronics.stackexchange.com/*
// @include        http://physics.stackexchange.com/*
// @include        http://quant.stackexchange.com/*
// @include        http://meta.quant.stackexchange.com/*
// @include        http://crypto.stackexchange.com/*
// @include        http://dsp.stackexchange.com/*
// @include        http://scicomp.stackexchange.com/*
// @include        http://mathematica.stackexchange.com/*
// @include        http://cogsci.stackexchange.com/*
// @include        http://cs.stackexchange.com/*
// @include        http://chemistry.stackexchange.com/*
// ==/UserScript==

/*****************************************************************/

(function () {

  function PatchMathJax() {
    MathJax.Ajax.Styles({
      ".post-taglist, table.fw, .comment-user, .comment-date, .comment-actions, .votecell": {
        position: "relative",
        "z-index": 10
      }
    });
    MathJax.Hub.Register.StartupHook("TeX Jax Ready",function () {
      var TEX = MathJax.InputJax.TeX;
      //
      //  Remove abusable macros
      //
      TEX.Macro("class","",1);
      TEX.Macro("cssId","",1);
      TEX.Macro("style","",1);
      TEX.Macro("href","",1);
      TEX.Macro("Huge","");
      TEX.Macro("huge","");
      TEX.Macro("LARGE","");
      TEX.Macro("Tiny","");
      TEX.Macro("Tiny","");
      //
      //  Remove abusable attributes from \mmlToken
      //
      var ALLOW = TEX.Parse.prototype.MmlTokenAllow;
      delete ALLOW.fontsize;
      delete ALLOW.id;
      delete ALLOW.style;
      delete ALLOW["class"];
      delete ALLOW.href;
      //
      //  Remove \bbox (but process the brackets)
      //
      MathJax.Hub.Register.StartupHook("TeX bbox Ready",function () {
        TEX.Parse.Augment({
          BBox: function(name) {this.GetBrackets(name)}
        });
      });
    });
  };

  if (!window.MathJax) {
    //
    //  Firefox and Chrome run in a sandbox, so inject script into the page.
    //
    var script = document.createElement("script");
    script.type = "text/javascript";
    script.text = "(" + PatchMathJax + ")()";
    var parent = (document.head || document.body || document.documentElement);
    setTimeout(function () {
      parent.appendChild(script);
      parent.removeChild(script);
    },0);
  } else {
    //
    //  Safari, Opera, and IE have direct access to DOM.
    //
    PatchMathJax();
  }

})();
