module VDOM.VDOM

import HTML.Types
import HTML.Elements
import Data.Vect

%access public export
%include JavaScript "vdom.js"

jscall : (fname : String) -> (ty : Type) ->
          {auto fty : FTy FFI_JS [] ty} -> ty
jscall fname ty = foreign FFI_JS fname ty

makeJSList : Vect n Ptr -> JS_IO Ptr
makeJSList [] = jscall "[]" (() -> JS_IO Ptr) ()
makeJSList (x::xs) =
  do
    res <- makeJSList xs
    jscall "%1.unshift(%0)" (Ptr -> Ptr -> JS_IO ()) x res
    pure res

--
-- makeJSObj : List (String, Ptr) -> JS_IO Ptr
-- makeJSObj [] =
--   jscall "{}" (() -> JS_IO Ptr) ()
-- makeJSObj ((k,v)::xs) =
--   do
--     o <- makeJSObj xs
--     jscall "%2[%0]=%1" (String -> Ptr -> Ptr -> JS_IO ()) k v o
--     pure o
--
-- attrsToPtr : Vect n Attr -> Ptr
-- attrsToPtr attrs =
--     let attrsPtr = unsafePerformIO $
--         (makeJSList $ map (\(MkAttribute x) => x) attrs) >>=
--             jscall "$JSLIB$virtualdom.attributesListToObj(%0)" (Ptr -> JS_IO Ptr)
--
-- elementToPtr : HTMLElement -> Ptr
-- elementToPtr (MkHTMLElement (MkElement type omit attrs children)) =
--     unsafePerformIO $
--         jscall "{type: %0, attrs: %1, text: '', children: %2}"
--         (String -> Ptr -> Ptr -> JS_IO Ptr) (show tag) (attrsToPtr attrs) (elementToPtr children)
-- elementToPtr (MkHTMLTextNode s) =
--     unsafePerformIO $ jscall "{type: 'text', attrs: [], text: %0, children: []}" (String -> JS_IO Ptr) s

-- node : String -> List (Attribute b a) -> List (Node c a) -> Node c a
-- node tag attrs childs =
--   let attrsPtr =
--       unsafePerformIO $
--         (makeJSList $ map (\(MkAttribute x) => x) attrs) >>=
--           jscall "$JSLIB$virtualdom.attributesListToObj(%0)" (Ptr -> JS_IO Ptr)
--       childsPtr = unsafePerformIO $ makeJSList $ map (\(MkNode x) => x) childs
--   in MkNode $ unsafePerformIO $ jscall "{type: 'n', tag: %0, attrs: %1, childs: %2}" (String -> Ptr -> Ptr -> JS_IO Ptr) tag attrsPtr childsPtr

makeJSObj : List (String, Ptr) -> JS_IO Ptr
makeJSObj [] =
  jscall "{}" (() -> JS_IO Ptr) ()
makeJSObj ((k,v)::xs) =
  do
    o <- makeJSObj xs
    jscall "%2[%0]=%1" (String -> Ptr -> Ptr -> JS_IO ()) k v o
    pure o

mkatt : Ptr -> Attr -> JS_IO Ptr
mkatt obj (MkAttr name value) =
    jscall "window.pamperscript.makeAttr(%0, %1, %2)"
    (String -> String -> Ptr -> JS_IO Ptr)
    name value obj

attrsToPtr : Vect n Attr -> JS_IO Ptr
attrsToPtr attrs = do
    obj <- makeJSObj []
    foldlM mkatt obj attrs


-- w.pamperscript.makeAttr

htmlToJs : HTMLElement -> JS_IO Ptr
htmlToJs (MkHTMLTextNode (MkTextNode s)) =
    foreign FFI_JS "window.pamperscript.makeElement('text', [], %0, [])" (String -> JS_IO Ptr) s
htmlToJs (MkHTMLElement (MkElement type omitTag attrs children)) = do
    jsAttrs <- attrsToPtr attrs
    children' <- traverse htmlToJs children
    jsChildren <- makeJSList children'
    foreign FFI_JS "window.pamperscript.makeElement(%0, %1, '', %2)" (String -> Ptr -> Ptr -> JS_IO Ptr) (show type) jsAttrs jsChildren

    -- foreign FFI_JS "makeElement(%0, %1, %2)" (String -> Ptr -> String -> Ptr -> JS_IO Ptr) (show type) jsAttrs "" jsChildren

-- type : TypeTag
-- omitTag : Bool
-- transparent : Bool
-- attrs : Vect n Attr
-- children : Vect m HTMLElement
