module HTML.Elements

import HTML.Types

import Data.Vect

-- TODO: FIX ACCESS
%access public export

isFlowContent : HTMLElement -> Bool
isFlowContent (MkHTMLElement (MkElement A _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Abbr _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Address _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Article _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Aside _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Audio _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement B _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Bdo _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Bdi _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Blockquote _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Br _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Button _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Canvas _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Cite _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Code _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Data _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Datalist _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Del _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Details _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Dfn _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Div _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Dl _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Em _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Embed _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Fieldset _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Figure _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Footer _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Form _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement H1 _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement H2 _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement H3 _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement H4 _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement H5 _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement H6 _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Header _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Hgroup _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Hr _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement I _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Iframe _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Img _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Input _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Ins _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Kbd _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Label _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Main _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Map _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Mark _ _ _)) = True
-- isFlowContent (MkHTMLElement (MkElement Math _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Menu _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Meter _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Nav _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Noscript _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Object _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Ol _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Output _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement P _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Pre _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Progress _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Q _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Ruby _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement S _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Samp _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Script _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Section _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Select _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Small _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Span _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Strong _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Sub _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Sup _ _ _)) = True
-- isFlowContent (MkHTMLElement (MkElement Svg _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Table _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Template _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Textarea _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Time _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Ul _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Var _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Video _ _ _)) = True
isFlowContent (MkHTMLElement (MkElement Wbr _ _ _)) = True
isFlowContent (MkHTMLTextNode _) = True
isFlowContent _ = False

isSectioningContent : HTMLElement -> Bool
isSectioningContent (MkHTMLElement (MkElement Article _ _ _)) = True
isSectioningContent (MkHTMLElement (MkElement Aside _ _ _)) = True
isSectioningContent (MkHTMLElement (MkElement Nav _ _ _)) = True
isSectioningContent (MkHTMLElement (MkElement Section _ _ _)) = True
isSectioningContent _ = False

isLabelableContent : HTMLElement -> Bool
isLabelableContent (MkHTMLElement (MkElement Button _ _ _)) = True
isLabelableContent (MkHTMLElement (MkElement Input _ _ _)) = True
isLabelableContent (MkHTMLElement (MkElement Meter _ _ _)) = True
isLabelableContent (MkHTMLElement (MkElement Output _ _ _)) = True
isLabelableContent (MkHTMLElement (MkElement Progress _ _ _)) = True
isLabelableContent (MkHTMLElement (MkElement Select _ _ _)) = True
isLabelableContent (MkHTMLElement (MkElement Textarea _ _ _)) = True
isLabelableContent _ = False

isHTag : HTMLElement -> Bool
isHTag (MkHTMLElement (MkElement H1 _ _ _)) = True
isHTag (MkHTMLElement (MkElement H2 _ _ _)) = True
isHTag (MkHTMLElement (MkElement H3 _ _ _)) = True
isHTag (MkHTMLElement (MkElement H4 _ _ _)) = True
isHTag (MkHTMLElement (MkElement H5 _ _ _)) = True
isHTag (MkHTMLElement (MkElement H6 _ _ _)) = True
isHTag _ = False

isHeadingContent : HTMLElement -> Bool
isHeadingContent (MkHTMLElement (MkElement Hgroup _ _ _)) = True
isHeadingContent elem = isHTag elem

isPhrasingContent : HTMLElement -> Bool
isPhrasingContent (MkHTMLElement (MkElement Abbr _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Audio _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement B _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Bdo _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Br _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Button _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Canvas _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Cite _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Code _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Data _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Datalist _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Dfn _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Em _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Embed _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement I _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Iframe _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Img _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Input _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Kbd _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Label _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Mark _ _ _)) = True
-- isPhrasingContent (MkHTMLElement (MkElement Math _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Meter _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Noscript _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Object _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Output _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Progress _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Q _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Ruby _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Samp _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Script _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Select _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Small _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Span _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Strong _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Sub _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Sup _ _ _)) = True
-- isPhrasingContent (MkHTMLElement (MkElement Svg _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Textarea _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Time _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Var _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Video _ _ _)) = True
isPhrasingContent (MkHTMLElement (MkElement Wbr _ _ _)) = True
isPhrasingContent (MkHTMLTextNode _) = True
isPhrasingContent _ = False
{-
<a>, if it contains only phrasing content
<area>, if it is a descendant of a <map> element
<del>, if it contains only phrasing content
<ins>, if it contains only phrasing content
<link>, if the itemprop attribute is present
<map>, if it contains only phrasing content
<meta>, if the itemprop attribute is present
-}

isEmbeddedContent : HTMLElement -> Bool
isEmbeddedContent (MkHTMLElement (MkElement Audio _ _ _)) = True
isEmbeddedContent (MkHTMLElement (MkElement Canvas _ _ _)) = True
isEmbeddedContent (MkHTMLElement (MkElement Embed _ _ _)) = True
isEmbeddedContent (MkHTMLElement (MkElement Iframe _ _ _)) = True
isEmbeddedContent (MkHTMLElement (MkElement Img _ _ _)) = True
-- isEmbeddedContent (MkHTMLElement (MkElement Math _ _ _)) = True
isEmbeddedContent (MkHTMLElement (MkElement Object _ _ _)) = True
-- isEmbeddedContent (MkHTMLElement (MkElement Svg _ _ _)) = True
isEmbeddedContent (MkHTMLElement (MkElement Video _ _ _)) = True
isEmbeddedContent _ = False
{-
<audio>, if the controls attribute is present
<img>, if the usemap attribute is present
<input>, if the type attribute is not in the hidden state
<menu>, if the type attribute is in the toolbar state
<object>, if the usemap attribute is present
<video>, if the controls attribute is present
-}

isInteractiveContent : HTMLElement -> Bool
isInteractiveContent (MkHTMLElement (MkElement A _ _ _)) = True
isInteractiveContent (MkHTMLElement (MkElement Button _ _ _)) = True
isInteractiveContent (MkHTMLElement (MkElement Details _ _ _)) = True
isInteractiveContent (MkHTMLElement (MkElement Embed _ _ _)) = True
isInteractiveContent (MkHTMLElement (MkElement Iframe _ _ _)) = True
isInteractiveContent (MkHTMLElement (MkElement Label _ _ _)) = True
isInteractiveContent (MkHTMLElement (MkElement Select _ _ _)) = True
isInteractiveContent (MkHTMLElement (MkElement Textarea _ _ _)) = True
isInteractiveContent _ = False

isFormAssociatedContent : HTMLElement -> Bool
isFormAssociatedContent (MkHTMLElement (MkElement Button _ _ _)) = True
isFormAssociatedContent (MkHTMLElement (MkElement Fieldset _ _ _)) = True
isFormAssociatedContent (MkHTMLElement (MkElement Input _ _ _)) = True
isFormAssociatedContent (MkHTMLElement (MkElement Label _ _ _)) = True
isFormAssociatedContent (MkHTMLElement (MkElement Meter _ _ _)) = True
isFormAssociatedContent (MkHTMLElement (MkElement Object _ _ _)) = True
isFormAssociatedContent (MkHTMLElement (MkElement Output _ _ _)) = True
isFormAssociatedContent (MkHTMLElement (MkElement Progress _ _ _)) = True
isFormAssociatedContent (MkHTMLElement (MkElement Select _ _ _)) = True
isFormAssociatedContent (MkHTMLElement (MkElement Textarea _ _ _)) = True
isFormAssociatedContent _ = False

isTransparentContent : HTMLElement -> Bool
isTransparentContent (MkHTMLElement (MkElement Textarea _ _ _)) = True
isTransparentContent _ = False

isTextNode : HTMLElement -> Bool
isTextNode (MkHTMLTextNode _) = True
isTextNode _ = False

mkElement : TypeTag -> {default False omit : Bool} -> Vect n Attr -> Vect m HTMLElement -> HTMLElement
mkElement type {omit} attrs children = MkHTMLElement (MkElement type omit attrs children)

text : String -> HTMLElement
text s = MkHTMLTextNode (MkTextNode s)

validChildren : (HTMLElement -> Bool) -> Vect n HTMLElement -> Bool
validChildren _ Nil = True
validChildren pred (x :: xs) = pred x && validChildren pred xs

anyChildren : Vect n HTMLElement -> Bool
anyChildren _ = True

isTag : TypeTag -> HTMLElement -> Bool
isTag t (MkHTMLElement (MkElement t' _ _ Nil)) = (t == t')
isTag _ _ = False

validDescendants : (HTMLElement -> Bool) -> Vect n HTMLElement -> Bool
validDescendants _ Nil = True
validDescendants pred (x :: xs) = pred x && validDescendants pred xs &&
    case x of
        MkHTMLElement (MkElement _ _ _ Nil) => True
        MkHTMLElement (MkElement _ _ _ children) => validDescendants pred children
        _ => True

textChildren : Vect m HTMLElement -> Bool
textChildren = validDescendants isTextNode

emptyChildren : Vect n HTMLElement -> Bool
emptyChildren children = length children == 0

flowChildren : Vect n HTMLElement -> Bool
flowChildren = validChildren isFlowContent

phrasingChildren : Vect n HTMLElement -> Bool
phrasingChildren = validChildren isPhrasingContent

-- TODO: should isFlowContent recurse? or just no header/footer?
flowChildrenSansHeaderFooterDescendant : Vect m HTMLElement -> Bool
flowChildrenSansHeaderFooterDescendant Nil = True
flowChildrenSansHeaderFooterDescendant (x :: xs) = validFlowContentSansHeaderFooter x && flowChildrenSansHeaderFooterDescendant xs
    where
        validFlowContentSansHeaderFooter (MkHTMLElement (MkElement Header _ _ _)) = False
        validFlowContentSansHeaderFooter (MkHTMLElement (MkElement Footer _ _ _)) = False
        validFlowContentSansHeaderFooter elem =
            isFlowContent elem &&
            case elem of
                MkHTMLElement (MkElement _ _ _ Nil) => True
                MkHTMLElement (MkElement _ _ _ children) => flowChildrenSansHeaderFooterDescendant children
                _ => True

{--
-- Elements
--}

validAddressChildren : Vect m HTMLElement -> Bool
validAddressChildren Nil = True
validAddressChildren (x :: xs) = validAddressContent x && validAddressChildren xs
    where
        validAddressContent : HTMLElement -> Bool
        validAddressContent (MkHTMLElement (MkElement Header _ _ _)) = False
        validAddressContent (MkHTMLElement (MkElement Footer _ _ _)) = False
        validAddressContent (MkHTMLElement (MkElement Address _ _ _)) = False
        validAddressContent elem =
            not (isHeadingContent elem) &&
            not (isSectioningContent elem) &&
            case elem of
                MkHTMLElement (MkElement _ _ _ Nil) => True
                MkHTMLElement (MkElement _ _ _ children') => validAddressChildren children'
                _ => True

address_ :
    Vect n Attr ->
    (children : Vect m HTMLElement) ->
    HTMLElement
address_ attrs children = mkElement Address attrs children


address :
    Vect n Attr ->
    (children : Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.validAddressChildren children) = True} ->
    HTMLElement
address attrs children = address_ attrs children

article :
    Vect n Attr ->
    (children : Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
article attrs children = mkElement Article attrs children

aside :
    Vect n Attr ->
    (children : Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
aside attrs children = mkElement Aside attrs children


footer :
    Vect n Attr ->
    (children : Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildrenSansHeaderFooterDescendant children) = True} ->
    HTMLElement
footer attrs children = mkElement Footer attrs children

h1 :
    Vect n Attr ->
    (children : Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
h1 attrs children = mkElement H1 attrs children

h2 :
    Vect n Attr ->
    (children : Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
h2 attrs children = mkElement H2 attrs children

h3 :
    Vect n Attr ->
    (children : Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
h3 attrs children = mkElement H3 attrs children

h4 :
    Vect n Attr ->
    (children : Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
h4 attrs children = mkElement H4 attrs children

h5 :
    Vect n Attr ->
    (children : Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
h5 attrs children = mkElement H5 attrs children

h6 :
    Vect n Attr ->
    (children : Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
h6 attrs children = mkElement H6 attrs children

header :
    Vect n Attr ->
    (children : Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildrenSansHeaderFooterDescendant children) = True} ->
    HTMLElement
header attrs children = mkElement Header attrs children

hgroupChildren : Vect m HTMLElement -> Bool
hgroupChildren children = (not (emptyChildren children)) && (validChildren isHTag children)

hgroup :
    Vect n Attr ->
    (children : Vect m HTMLElement) ->
    {auto prf : HTML.Elements.hgroupChildren children = True} ->
    HTMLElement
hgroup attrs children = mkElement Hgroup attrs children

main :
    Vect n Attr ->
    (children : Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
main attrs children = mkElement Main attrs children

nav :
    Vect n Attr ->
    (children : Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
nav attrs children = mkElement Nav attrs children


section :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
section attrs children = mkElement Section attrs children

blockquote :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
blockquote attrs children = mkElement Blockquote attrs children

dd :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
dd attrs children = mkElement Dd attrs children

div :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
div attrs children = mkElement Div attrs children

dlChildren : Vect n HTMLElement -> Bool
dlChildren Nil = True
dlChildren children = dlDtChildren children || dlDivChildren children
    where
        -- TODO: DO THIS
        dlDtChildren : Vect n HTMLElement -> Bool
        dlDtChildren _ = True -- Either: Zero or more groups each consisting of one or more <dt> elements followed by one or more <dd> elements, optionally intermixed with <script> and <template> elements.
        dlDivChildren : Vect n HTMLElement -> Bool
        dlDivChildren _ = True -- Or: One or more <div> elements, optionally intermixed with <script> and <template> elements.

dl :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.dlChildren children) = True} ->
    HTMLElement
dl attrs children = mkElement Dl attrs children

dtChildren : Vect n HTMLElement -> Bool
dtChildren Nil = True
dtChildren (x :: xs) = validDtContent x && dtChildren xs
    where
        validDtContent (MkHTMLElement (MkElement Header _ _ _)) = False
        validDtContent (MkHTMLElement (MkElement Footer _ _ _)) = False
        validDtContent elem =
            not (isSectioningContent elem) &&
            case elem of
                MkHTMLElement (MkElement _ _ _ Nil) => True
                MkHTMLElement (MkElement _ _ _ children) => flowChildrenSansHeaderFooterDescendant children
                _ => True

dt :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.dtChildren children) = True} ->
    HTMLElement
dt attrs children = mkElement Dt attrs children

figcaption :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
figcaption attrs children = mkElement Figcaption attrs children

figureChildren : Vect m HTMLElement -> Bool
figureChildren Nil = True
figureChildren xs = figcaptionThenFlow xs || flowThenFigcaption xs || flowChildren xs
    where
        isFigCaption : HTMLElement -> Bool
        isFigCaption (MkHTMLElement (MkElement Figcaption _ _ _)) = True
        isFigCaption _ = False
        figcaptionThenFlow : Vect n HTMLElement -> Bool
        figcaptionThenFlow Nil = False
        figcaptionThenFlow (x::xs::Nil) = False
        figcaptionThenFlow {n = S n'} children = isFigCaption (head children) && flowChildren (tail children)
        flowThenFigcaption : Vect n HTMLElement -> Bool
        flowThenFigcaption Nil = False
        flowThenFigcaption (x::xs::Nil) = False
        flowThenFigcaption {n = S n'} children = flowChildren (init children) && isFigCaption (last children)

figure :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.figureChildren children) = True} ->
    HTMLElement
figure attrs children = mkElement Figure attrs children

hr :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : HTML.Elements.emptyChildren children = True} ->
    HTMLElement
hr attrs children = mkElement Hr {omit = True} attrs children

li_ :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    HTMLElement
li_ attrs children = mkElement Li attrs children

li :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
li attrs children = li_ attrs children

ol :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.validChildren (HTML.Elements.isTag Li) children) = True} ->
    HTMLElement
ol attrs children = mkElement Ol attrs children

p :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
p attrs children = mkElement P attrs children

pre :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
pre attrs children = mkElement Pre attrs children

ul_ :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    HTMLElement
ul_ attrs children = mkElement Ul attrs children

ul :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.validChildren (HTML.Elements.isTag Li) children) = True} ->
    HTMLElement
ul attrs children = ul_ attrs children

aChildren : Vect m HTMLElement -> Bool
aChildren Nil = True
aChildren (x :: xs) = aContent x && aChildren xs
    where
        aContent : HTMLElement -> Bool
        aContent elem =
            (isFlowContent elem && not (isInteractiveContent elem)) ||
            isPhrasingContent elem

a :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.aChildren children) = True} ->
    HTMLElement
a attrs children = mkElement A attrs children

abbr :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
abbr attrs children = mkElement Abbr attrs children

b :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
b attrs children = mkElement B attrs children

bdi :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
bdi attrs children = mkElement Bdi attrs children

bdo :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
bdo attrs children = mkElement Bdo attrs children

br :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
br attrs children = mkElement Br {omit = True} attrs children

cite :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
cite attrs children = mkElement Cite attrs children

code :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
code attrs children = mkElement Code attrs children

data_ :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
data_ attrs children = mkElement Data attrs children

dfnChildren : Vect m HTMLElement -> Bool
dfnChildren Nil = True
dfnChildren xs = dfnChildren' xs && validDescendants (not . isDfn) xs
    where
        isDfn : HTMLElement -> Bool
        isDfn (MkHTMLElement (MkElement Dfn _ _ _)) = True
        isDfn _ = False
        dfnContent : HTMLElement -> Bool
        dfnContent elem = isPhrasingContent elem
        dfnChildren' : Vect m HTMLElement -> Bool
        dfnChildren' Nil = True
        dfnChildren' (x :: xs) = (dfnContent x) && (dfnChildren' xs)

dfn :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.dfnChildren children) = True} ->
    HTMLElement
dfn attrs children = mkElement Dfn attrs children

em :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
em attrs children = mkElement Em attrs children

i :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
i attrs children = mkElement I attrs children

kbd :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
kbd attrs children = mkElement Kbd attrs children

mark :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
mark attrs children = mkElement Mark attrs children

q :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
q attrs children = mkElement Q attrs children

rb :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
rb attrs children = mkElement Rb attrs children

rp :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
rp attrs children = mkElement Rp attrs children

rt :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
rt attrs children = mkElement Rt attrs children

rtcChildren : Vect m HTMLElement -> Bool
rtcChildren Nil = True
rtcChildren (x :: xs) = rtcContent x && rtcChildren xs
    where
        isRtc : HTMLElement -> Bool
        isRtc (MkHTMLElement (MkElement Rtc _ _ _)) = True
        isRtc _ = False
        rtcContent : HTMLElement -> Bool
        rtcContent elem = isPhrasingContent elem || isRtc elem

rtc :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.rtcChildren children) = True} ->
    HTMLElement
rtc attrs children = mkElement Rtc attrs children

ruby :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
ruby attrs children = mkElement Ruby attrs children

s :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
s attrs children = mkElement S attrs children

samp :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
samp attrs children = mkElement Samp attrs children

small :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
small attrs children = mkElement Small attrs children

span :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
span attrs children = mkElement Span attrs children

strong :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
strong attrs children = mkElement Strong attrs children

sub :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
sub attrs children = mkElement Sub attrs children

sup :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
sup attrs children = mkElement Sup attrs children

time :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
time attrs children = mkElement Time attrs children

u :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
u attrs children = mkElement U attrs children

var :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
var attrs children = mkElement Var attrs children

wbr :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
wbr attrs children = mkElement Wbr {omit = True} attrs children

area :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
area attrs children = mkElement Area {omit = True} attrs children

audioChildren : Vect m HTMLElement -> Bool
-- TODO: FIX
audioChildren Nil = True
audioChildren (x :: xs) = True
-- If the element has a src attribute: zero or more <track> elements followed by transparent content that contains no <audio> or <video> media elements.
-- Else: zero or more <source> elements followed by zero or more <track> elements followed by transparent content that contains no <audio> or <video> media elements.

audio :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
audio attrs children = mkElement Audio attrs children

img :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
img attrs children = mkElement Img {omit = True} attrs children

map :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    -- TODO: Any transparent element.
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
map attrs children = mkElement Map attrs children

track :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
track attrs children = mkElement Track {omit = True} attrs children

videoChildren : Vect m HTMLElement -> Bool
-- TODO: FIX
videoChildren xs = True
-- If the element has a src attribute: zero or more <track> elements, followed by transparent content that contains no media elements–that is no <audio> or <video>
-- Else: zero or more <source> elements, followed by zero or more <track> elements, followed by transparent content that contains no media elements–that is no <audio> or <video>.

video :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
video attrs children = mkElement Video attrs children

embed :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
embed attrs children = mkElement Embed {omit = True} attrs children

iframeChildren : Vect m HTMLElement -> Bool
-- TODO: FIX
iframeChildren xs = True
-- Fallback content, i.e. content that is normally not rendered, but that browsers not supporting the <iframe> element will render.

iframe :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
iframe attrs children = mkElement Iframe attrs children

objectChildren : Vect m HTMLElement -> Bool
-- TODO: FIX
objectChildren xs = True
-- zero or more <param> elements, then transparent.

object :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
object attrs children = mkElement Object attrs children

param :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
param attrs children = mkElement Param {omit = True} attrs children

pictureChildren : Vect m HTMLElement -> Bool
-- TODO: FIX
pictureChildren xs = True
-- Zero or more <source> elements, followed by one <img> element, optionally intermixed with script-supporting elements.

picture :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
picture attrs children = mkElement Picture attrs children

source :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
source attrs children = mkElement Source {omit = True} attrs children

canvasChildren : Vect m HTMLElement -> Bool
-- TODO: FIX
canvasChildren xs = True
-- Transparent but with no interactive content descendants except for <a> elements, <button> elements, <input> elements whose type attribute is checkbox, radio, or button.

canvas :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
canvas attrs children = mkElement Canvas attrs children

noscriptChildren : Vect m HTMLElement -> Bool
-- TODO: FIX
noscriptChildren xs = True
-- When scripting is disabled and when it is a descendant of the <head> element: in any order, zero or more <link> elements, zero or more <style> elements, and zero or more <meta> elements.
-- When scripting is disabled and when it isn't a descendant of the <head> element: any transparent content, but no <noscript> element must be among its descendants.
-- Otherwise: flow content or phrasing content.

noscript :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
noscript attrs children = mkElement Noscript attrs children

scriptChildren : Vect m HTMLElement -> Bool
-- TODO: FIX
scriptChildren xs = True

script :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
-- TODO: OMIT?
script attrs children = mkElement Script attrs children

delChildren : Vect m HTMLElement -> Bool
-- TODO: FIX
-- Transparent.
delChildren xs = True

del :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
del attrs children = mkElement Del attrs children

insChildren : Vect m HTMLElement -> Bool
-- TODO: FIX
-- Transparent.
insChildren xs = True

ins :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
ins attrs children = mkElement Ins attrs children

caption :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
caption attrs children = mkElement Caption attrs children

col :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
col attrs children = mkElement Col {omit = True} attrs children

colgroupChildren : Vect m HTMLElement -> Bool
-- TODO: FIX
colgroupChildren xs = True
-- If the span attribute is present: none, it is an empty element.
-- If the attribute is not present: zero or more <col> element

colgroup :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
colgroup attrs children = mkElement Colgroup attrs children

tableChildren : Vect m HTMLElement -> Bool
-- TODO: FIX
tableChildren xs = True
-- In this order:
--      an optional <caption> element,
--      zero or more <colgroup> elements,
--      an optional <thead> element,
--      either one of the following:
--      zero or more <tbody> elements
--      one or more <tr> elements
--      an optional <tfoot> element

table :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
table attrs children = mkElement Table attrs children

tbodyChildren : Vect m HTMLElement -> Bool
tbodyChildren Nil = True
tbodyChildren (x :: xs) = isTr x && tbodyChildren xs
    where
        isTr : HTMLElement -> Bool
        isTr (MkHTMLElement (MkElement Tr _ _ _)) = True
        isTr _ = False

tbody :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.tbodyChildren children) = True} ->
    HTMLElement
tbody attrs children = mkElement Tbody attrs children

td :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
td attrs children = mkElement Td attrs children

tfootChildren : Vect m HTMLElement -> Bool
tfootChildren = tbodyChildren

tfoot :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.tfootChildren children) = True} ->
    HTMLElement
tfoot attrs children = mkElement Tfoot attrs children

thChildren : Vect m HTMLElement -> Bool
-- TODO: FIX
thChildren xs = True
-- Flow content, but with no header, footer, sectioning content, or heading content descendants.
th :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
th attrs children = mkElement Th attrs children

theadChildren : Vect m HTMLElement -> Bool
theadChildren = tbodyChildren

thead :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.theadChildren children) = True} ->
    HTMLElement
thead attrs children = mkElement Thead attrs children

trChildren : Vect m HTMLElement -> Bool
-- TODO: FIX
trChildren xs = True
-- Zero or more <td> and/or <th> elements; script-supporting elements (<script> and <template>) are also allowed

tr :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
tr attrs children = mkElement Tr attrs children

buttonChildren : Vect m HTMLElement -> Bool
buttonChildren Nil = True
buttonChildren (x :: xs) = isPhrasingContent x && not (isInteractiveContent x) && buttonChildren xs

button :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.buttonChildren children) = True} ->
    HTMLElement
button attrs children = mkElement Button attrs children

datalistChildren : Vect m HTMLElement -> Bool
-- TODO: FIX
datalistChildren xs = True
-- Either phrasing content or zero or more <option> elements.

datalist :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
datalist attrs children = mkElement Datalist attrs children

fieldsetChildren : Vect m HTMLElement -> Bool
-- TODO: FIX
fieldsetChildren xs = True
-- An optional <legend> element, followed by flow content.

fieldset :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
fieldset attrs children = mkElement Fieldset attrs children

validFormDescendant : HTMLElement -> Bool
validFormDescendant child = isFlowContent child && (not (isTag Form child))

formChildren : Vect m HTMLElement -> Bool
formChildren = validDescendants validFormDescendant

form :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.formChildren children) = True} ->
    HTMLElement
form attrs children = mkElement Form attrs children

input :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
input attrs children = mkElement Input attrs children

validLabelDescendant : HTMLElement -> Bool
validLabelDescendant child = isPhrasingContent child && (not (isTag Label child))
-- TODO: FIX
-- No labelable elements other than the labeled control are allowed.

labelChildren : Vect m HTMLElement -> Bool
labelChildren = validDescendants validLabelDescendant

label :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.labelChildren children) = True} ->
    HTMLElement
label attrs children = mkElement Label attrs children

legend :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
legend attrs children = mkElement Legend attrs children

validMeterDescendant : HTMLElement -> Bool
validMeterDescendant child = isPhrasingContent child && (not (isTag Meter child))

meterChildren : Vect m HTMLElement -> Bool
meterChildren = validDescendants validMeterDescendant

meter :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.meterChildren children) = True} ->
    HTMLElement
meter attrs children = mkElement Meter attrs children

validOptgroupDescendant : HTMLElement -> Bool
validOptgroupDescendant = isTag Option

optgroupChildren : Vect m HTMLElement -> Bool
optgroupChildren = validDescendants validOptgroupDescendant

optgroup :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.optgroupChildren children) = True} ->
    HTMLElement
optgroup attrs children = mkElement Optgroup attrs children

option :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.textChildren children) = True} ->
    HTMLElement
option attrs children = mkElement Option attrs children

output :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
output attrs children = mkElement Output attrs children

progressChildren : Vect m HTMLElement -> Bool
progressChildren = validDescendants validProgressDescendant
    where
        validProgressDescendant : HTMLElement -> Bool
        validProgressDescendant child = isPhrasingContent child && (not (isTag Progress child))

progress :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.progressChildren children) = True} ->
    HTMLElement
progress attrs children = mkElement Progress attrs children

selectChildren : Vect m HTMLElement -> Bool
selectChildren = validChildren validSelectChildren
    where
        validSelectChildren : HTMLElement -> Bool
        validSelectChildren child = (isTag Option child) || (isTag Optgroup child)

select :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.selectChildren children) = True} ->
    HTMLElement
select attrs children = mkElement Select attrs children

textarea :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.textChildren children) = True} ->
    HTMLElement
textarea attrs children = mkElement Textarea attrs children

detailsChildren : Vect m HTMLElement -> Bool
detailsChildren (x :: xs) = (isTag Summary x) && (validChildren isFlowContent xs)
detailsChildren _ = False

details :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.detailsChildren children) = True} ->
    HTMLElement
details attrs children = mkElement Details attrs children

dialog :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
dialog attrs children = mkElement Dialog attrs children

-- menu :
--     Vect n Attr ->
--     (children: Vect m HTMLElement) ->
--     {auto prf : (HTML.Elements.flowChildren children) = True} ->
--     HTMLElement
-- menu attrs children = mkElement Menu attrs children
-- If the element is in the list menu state: flow content, or alternatively, zero or more occurrences of <li>, <script>, and <template>.
-- If the element is in the context menu state: zero or more occurrences, in any order, of <menu> (context menu state only), <menuitem {deprecated}>, <hr>, <script>, and <template>.
-- TODO: oof...
--

summaryChildren : Vect m HTMLElement -> Bool
summaryChildren (x :: Nil) = isHeadingContent x
summaryChildren children = phrasingChildren children

summary :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.summaryChildren children) = True} ->
    HTMLElement
summary attrs children = mkElement Summary attrs children

template :
    Vect n Attr ->
    (children: Vect m HTMLElement) ->
    {auto prf : (HTML.Elements.anyChildren children) = True} ->
    HTMLElement
template attrs children = mkElement Template attrs children
