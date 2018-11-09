module VDOM.VDOM

import HTML.Types
import HTML.Elements

%access public export
%include JavaScript "vdom.js"

jscall : (fname : String) -> (ty : Type) ->
          {auto fty : FTy FFI_JS [] ty} -> ty
jscall fname ty = foreign FFI_JS fname ty

makeJSList : List Ptr -> JS_IO Ptr
makeJSList [] = jscall "[]" (() -> JS_IO Ptr) ()
makeJSList (x::xs) =
  do
    res <- makeJSList xs
    jscall "%0.unshift(%1)" (Ptr -> Ptr -> JS_IO ()) res x
    pure res

makeJSObj : List (String, Ptr) -> JS_IO Ptr
makeJSObj [] =
  jscall "{}" (() -> JS_IO Ptr) ()
makeJSObj ((k,v)::xs) =
  do
    o <- makeJSObj xs
    jscall "%0[%1]=%2" (Ptr -> String -> Ptr -> JS_IO ()) o k v
    pure o

mkAtt : Ptr -> Attr -> JS_IO Ptr
mkAtt obj (MkAttr name value) =
    jscall "window.pamperscript.makeAttr(%0, %1, %2)"
        (Ptr -> String -> String -> JS_IO Ptr)
        obj name value

attrsToPtr : List Attr -> JS_IO Ptr
attrsToPtr attrs = do
    obj <- makeJSObj []
    foldlM mkAtt obj attrs

htmlToJs : HTMLElement -> JS_IO Ptr
htmlToJs (MkHTMLTextNode (MkTextNode s)) =
    jscall "window.pamperscript.makeElement('text', null, null, %0)" (String -> JS_IO Ptr) s
htmlToJs (MkHTMLElement (MkElement type omitTag attrs children)) = do
    jsAttrs <- attrsToPtr attrs
    children' <- traverse htmlToJs children
    jsChildren <- makeJSList children'
    jscall "window.pamperscript.makeElement(%0, %1, %2)" (String -> Ptr -> Ptr -> JS_IO Ptr) (show type) jsAttrs jsChildren
