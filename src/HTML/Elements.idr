module HTML.Elements

import HTML.Types

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

mkElement : TypeTag -> {default False omit : Bool} -> List Attr -> List HTMLElement -> HTMLElement
mkElement type {omit} attrs children = MkHTMLElement (MkElement type omit attrs children)

text : String -> HTMLElement
text s = MkHTMLTextNode (MkTextNode s)

validChildren : (HTMLElement -> Bool) -> List HTMLElement -> Bool
validChildren _ Nil = True
validChildren pred (x :: xs) = pred x && validChildren pred xs

anyChildren : List HTMLElement -> Bool
anyChildren _ = True

isTag : TypeTag -> HTMLElement -> Bool
isTag t (MkHTMLElement (MkElement t' _ _ Nil)) = (t == t')
isTag _ _ = False

validDescendants : (HTMLElement -> Bool) -> List HTMLElement -> Bool
validDescendants _ Nil = True
validDescendants pred (x :: xs) = pred x && validDescendants pred xs &&
    case x of
        MkHTMLElement (MkElement _ _ _ Nil) => True
        MkHTMLElement (MkElement _ _ _ children) => validDescendants pred children
        _ => True

textChildren : List HTMLElement -> Bool
textChildren = validDescendants isTextNode

emptyChildren : List HTMLElement -> Bool
emptyChildren [] = True
emptyChildren _ = False

flowChildren : List HTMLElement -> Bool
flowChildren = validChildren isFlowContent

phrasingChildren : List HTMLElement -> Bool
phrasingChildren = validChildren isPhrasingContent

-- TODO: should isFlowContent recurse? or just no header/footer?
flowChildrenSansHeaderFooterDescendant : List HTMLElement -> Bool
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

validAddressChildren : List HTMLElement -> Bool
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
    List Attr ->
    (children : List HTMLElement) ->
    HTMLElement
address_ attrs children = mkElement Address attrs children


address :
    List Attr ->
    (children : List HTMLElement) ->
    {auto prf : (HTML.Elements.validAddressChildren children) = True} ->
    HTMLElement
address attrs children = address_ attrs children

article :
    List Attr ->
    (children : List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
article attrs children = mkElement Article attrs children

aside :
    List Attr ->
    (children : List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
aside attrs children = mkElement Aside attrs children


footer :
    List Attr ->
    (children : List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildrenSansHeaderFooterDescendant children) = True} ->
    HTMLElement
footer attrs children = mkElement Footer attrs children

h1 :
    List Attr ->
    (children : List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
h1 attrs children = mkElement H1 attrs children

h2 :
    List Attr ->
    (children : List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
h2 attrs children = mkElement H2 attrs children

h3 :
    List Attr ->
    (children : List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
h3 attrs children = mkElement H3 attrs children

h4 :
    List Attr ->
    (children : List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
h4 attrs children = mkElement H4 attrs children

h5 :
    List Attr ->
    (children : List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
h5 attrs children = mkElement H5 attrs children

h6 :
    List Attr ->
    (children : List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
h6 attrs children = mkElement H6 attrs children

header :
    List Attr ->
    (children : List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildrenSansHeaderFooterDescendant children) = True} ->
    HTMLElement
header attrs children = mkElement Header attrs children

hgroupChildren : List HTMLElement -> Bool
hgroupChildren children = (not (emptyChildren children)) && (validChildren isHTag children)

hgroup :
    List Attr ->
    (children : List HTMLElement) ->
    {auto prf : HTML.Elements.hgroupChildren children = True} ->
    HTMLElement
hgroup attrs children = mkElement Hgroup attrs children

main :
    List Attr ->
    (children : List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
main attrs children = mkElement Main attrs children

nav :
    List Attr ->
    (children : List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
nav attrs children = mkElement Nav attrs children


section :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
section attrs children = mkElement Section attrs children

blockquote :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
blockquote attrs children = mkElement Blockquote attrs children

dd :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
dd attrs children = mkElement Dd attrs children

div :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
div attrs children = mkElement Div attrs children

dlChildren : List HTMLElement -> Bool
dlChildren Nil = True
dlChildren children = dlDtChildren children || dlDivChildren children
    where
        -- TODO: DO THIS
        dlDtChildren : List HTMLElement -> Bool
        dlDtChildren _ = True -- Either: Zero or more groups each consisting of one or more <dt> elements followed by one or more <dd> elements, optionally intermixed with <script> and <template> elements.
        dlDivChildren : List HTMLElement -> Bool
        dlDivChildren _ = True -- Or: One or more <div> elements, optionally intermixed with <script> and <template> elements.

dl :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.dlChildren children) = True} ->
    HTMLElement
dl attrs children = mkElement Dl attrs children

dtChildren : List HTMLElement -> Bool
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
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.dtChildren children) = True} ->
    HTMLElement
dt attrs children = mkElement Dt attrs children

figcaption :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
figcaption attrs children = mkElement Figcaption attrs children

figureChildren : List HTMLElement -> Bool
figureChildren Nil = True
figureChildren xs = figcaptionThenFlow xs || flowThenFigcaption xs || flowChildren xs
    where
        isFigCaption : HTMLElement -> Bool
        isFigCaption (MkHTMLElement (MkElement Figcaption _ _ _)) = True
        isFigCaption _ = False
        figcaptionThenFlow : List HTMLElement -> Bool
        figcaptionThenFlow [] = False
        figcaptionThenFlow (x::xs::Nil) = False
        figcaptionThenFlow (x::xs) = isFigCaption x && flowChildren xs
        flowThenFigcaption : List HTMLElement -> Bool
        flowThenFigcaption [] = False
        flowThenFigcaption (x::xs::Nil) = False
        flowThenFigcaption children@(_::_) = flowChildren (init children) && isFigCaption (last children)

figure :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.figureChildren children) = True} ->
    HTMLElement
figure attrs children = mkElement Figure attrs children

hr :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : HTML.Elements.emptyChildren children = True} ->
    HTMLElement
hr attrs children = mkElement Hr {omit = True} attrs children

li_ :
    List Attr ->
    (children: List HTMLElement) ->
    HTMLElement
li_ attrs children = mkElement Li attrs children

li :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
li attrs children = li_ attrs children

ol :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.validChildren (HTML.Elements.isTag Li) children) = True} ->
    HTMLElement
ol attrs children = mkElement Ol attrs children

p :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
p attrs children = mkElement P attrs children

pre :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
pre attrs children = mkElement Pre attrs children

ul_ :
    List Attr ->
    (children: List HTMLElement) ->
    HTMLElement
ul_ attrs children = mkElement Ul attrs children

ul :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.validChildren (HTML.Elements.isTag Li) children) = True} ->
    HTMLElement
ul attrs children = ul_ attrs children

aChildren : List HTMLElement -> Bool
aChildren Nil = True
aChildren (x :: xs) = aContent x && aChildren xs
    where
        aContent : HTMLElement -> Bool
        aContent elem =
            (isFlowContent elem && not (isInteractiveContent elem)) ||
            isPhrasingContent elem

a :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.aChildren children) = True} ->
    HTMLElement
a attrs children = mkElement A attrs children

abbr :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
abbr attrs children = mkElement Abbr attrs children

b :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
b attrs children = mkElement B attrs children

bdi :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
bdi attrs children = mkElement Bdi attrs children

bdo :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
bdo attrs children = mkElement Bdo attrs children

br :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
br attrs children = mkElement Br {omit = True} attrs children

cite :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
cite attrs children = mkElement Cite attrs children

code :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
code attrs children = mkElement Code attrs children

data_ :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
data_ attrs children = mkElement Data attrs children

dfnChildren : List HTMLElement -> Bool
dfnChildren Nil = True
dfnChildren xs = dfnChildren' xs && validDescendants (not . isDfn) xs
    where
        isDfn : HTMLElement -> Bool
        isDfn (MkHTMLElement (MkElement Dfn _ _ _)) = True
        isDfn _ = False
        dfnContent : HTMLElement -> Bool
        dfnContent elem = isPhrasingContent elem
        dfnChildren' : List HTMLElement -> Bool
        dfnChildren' Nil = True
        dfnChildren' (x :: xs) = (dfnContent x) && (dfnChildren' xs)

dfn :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.dfnChildren children) = True} ->
    HTMLElement
dfn attrs children = mkElement Dfn attrs children

em :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
em attrs children = mkElement Em attrs children

i :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
i attrs children = mkElement I attrs children

kbd :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
kbd attrs children = mkElement Kbd attrs children

mark :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
mark attrs children = mkElement Mark attrs children

q :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
q attrs children = mkElement Q attrs children

rb :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
rb attrs children = mkElement Rb attrs children

rp :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
rp attrs children = mkElement Rp attrs children

rt :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
rt attrs children = mkElement Rt attrs children

rtcChildren : List HTMLElement -> Bool
rtcChildren Nil = True
rtcChildren (x :: xs) = rtcContent x && rtcChildren xs
    where
        isRtc : HTMLElement -> Bool
        isRtc (MkHTMLElement (MkElement Rtc _ _ _)) = True
        isRtc _ = False
        rtcContent : HTMLElement -> Bool
        rtcContent elem = isPhrasingContent elem || isRtc elem

rtc :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.rtcChildren children) = True} ->
    HTMLElement
rtc attrs children = mkElement Rtc attrs children

ruby :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
ruby attrs children = mkElement Ruby attrs children

s :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
s attrs children = mkElement S attrs children

samp :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
samp attrs children = mkElement Samp attrs children

small :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
small attrs children = mkElement Small attrs children

span :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
span attrs children = mkElement Span attrs children

strong :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
strong attrs children = mkElement Strong attrs children

sub :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
sub attrs children = mkElement Sub attrs children

sup :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
sup attrs children = mkElement Sup attrs children

time :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
time attrs children = mkElement Time attrs children

u :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
u attrs children = mkElement U attrs children

var :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
var attrs children = mkElement Var attrs children

wbr :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
wbr attrs children = mkElement Wbr {omit = True} attrs children

area :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
area attrs children = mkElement Area {omit = True} attrs children

audioChildren : List HTMLElement -> Bool
-- TODO: FIX
audioChildren Nil = True
audioChildren (x :: xs) = True
-- If the element has a src attribute: zero or more <track> elements followed by transparent content that contains no <audio> or <video> media elements.
-- Else: zero or more <source> elements followed by zero or more <track> elements followed by transparent content that contains no <audio> or <video> media elements.

audio :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
audio attrs children = mkElement Audio attrs children

img :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
img attrs children = mkElement Img {omit = True} attrs children

map :
    List Attr ->
    (children: List HTMLElement) ->
    -- TODO: Any transparent element.
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
map attrs children = mkElement Map attrs children

track :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
track attrs children = mkElement Track {omit = True} attrs children

videoChildren : List HTMLElement -> Bool
-- TODO: FIX
videoChildren xs = True
-- If the element has a src attribute: zero or more <track> elements, followed by transparent content that contains no media elements–that is no <audio> or <video>
-- Else: zero or more <source> elements, followed by zero or more <track> elements, followed by transparent content that contains no media elements–that is no <audio> or <video>.

video :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
video attrs children = mkElement Video attrs children

embed :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
embed attrs children = mkElement Embed {omit = True} attrs children

iframeChildren : List HTMLElement -> Bool
-- TODO: FIX
iframeChildren xs = True
-- Fallback content, i.e. content that is normally not rendered, but that browsers not supporting the <iframe> element will render.

iframe :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
iframe attrs children = mkElement Iframe attrs children

objectChildren : List HTMLElement -> Bool
-- TODO: FIX
objectChildren xs = True
-- zero or more <param> elements, then transparent.

object :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
object attrs children = mkElement Object attrs children

param :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
param attrs children = mkElement Param {omit = True} attrs children

pictureChildren : List HTMLElement -> Bool
-- TODO: FIX
pictureChildren xs = True
-- Zero or more <source> elements, followed by one <img> element, optionally intermixed with script-supporting elements.

picture :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
picture attrs children = mkElement Picture attrs children

source :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
source attrs children = mkElement Source {omit = True} attrs children

canvasChildren : List HTMLElement -> Bool
-- TODO: FIX
canvasChildren xs = True
-- Transparent but with no interactive content descendants except for <a> elements, <button> elements, <input> elements whose type attribute is checkbox, radio, or button.

canvas :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
canvas attrs children = mkElement Canvas attrs children

noscriptChildren : List HTMLElement -> Bool
-- TODO: FIX
noscriptChildren xs = True
-- When scripting is disabled and when it is a descendant of the <head> element: in any order, zero or more <link> elements, zero or more <style> elements, and zero or more <meta> elements.
-- When scripting is disabled and when it isn't a descendant of the <head> element: any transparent content, but no <noscript> element must be among its descendants.
-- Otherwise: flow content or phrasing content.

noscript :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
noscript attrs children = mkElement Noscript attrs children

scriptChildren : List HTMLElement -> Bool
-- TODO: FIX
scriptChildren xs = True

script :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
-- TODO: OMIT?
script attrs children = mkElement Script attrs children

delChildren : List HTMLElement -> Bool
-- TODO: FIX
-- Transparent.
delChildren xs = True

del :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
del attrs children = mkElement Del attrs children

insChildren : List HTMLElement -> Bool
-- TODO: FIX
-- Transparent.
insChildren xs = True

ins :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
ins attrs children = mkElement Ins attrs children

caption :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
caption attrs children = mkElement Caption attrs children

col :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
col attrs children = mkElement Col {omit = True} attrs children

colgroupChildren : List HTMLElement -> Bool
-- TODO: FIX
colgroupChildren xs = True
-- If the span attribute is present: none, it is an empty element.
-- If the attribute is not present: zero or more <col> element

colgroup :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
colgroup attrs children = mkElement Colgroup attrs children

tableChildren : List HTMLElement -> Bool
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
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
table attrs children = mkElement Table attrs children

tbodyChildren : List HTMLElement -> Bool
tbodyChildren Nil = True
tbodyChildren (x :: xs) = isTr x && tbodyChildren xs
    where
        isTr : HTMLElement -> Bool
        isTr (MkHTMLElement (MkElement Tr _ _ _)) = True
        isTr _ = False

tbody :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.tbodyChildren children) = True} ->
    HTMLElement
tbody attrs children = mkElement Tbody attrs children

td :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
td attrs children = mkElement Td attrs children

tfootChildren : List HTMLElement -> Bool
tfootChildren = tbodyChildren

tfoot :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.tfootChildren children) = True} ->
    HTMLElement
tfoot attrs children = mkElement Tfoot attrs children

thChildren : List HTMLElement -> Bool
-- TODO: FIX
thChildren xs = True
-- Flow content, but with no header, footer, sectioning content, or heading content descendants.
th :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
th attrs children = mkElement Th attrs children

theadChildren : List HTMLElement -> Bool
theadChildren = tbodyChildren

thead :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.theadChildren children) = True} ->
    HTMLElement
thead attrs children = mkElement Thead attrs children

trChildren : List HTMLElement -> Bool
-- TODO: FIX
trChildren xs = True
-- Zero or more <td> and/or <th> elements; script-supporting elements (<script> and <template>) are also allowed

tr :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
tr attrs children = mkElement Tr attrs children

buttonChildren : List HTMLElement -> Bool
buttonChildren Nil = True
buttonChildren (x :: xs) = isPhrasingContent x && not (isInteractiveContent x) && buttonChildren xs

button :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.buttonChildren children) = True} ->
    HTMLElement
button attrs children = mkElement Button attrs children

datalistChildren : List HTMLElement -> Bool
-- TODO: FIX
datalistChildren xs = True
-- Either phrasing content or zero or more <option> elements.

datalist :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
datalist attrs children = mkElement Datalist attrs children

fieldsetChildren : List HTMLElement -> Bool
-- TODO: FIX
fieldsetChildren xs = True
-- An optional <legend> element, followed by flow content.

fieldset :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
fieldset attrs children = mkElement Fieldset attrs children

validFormDescendant : HTMLElement -> Bool
validFormDescendant child = isFlowContent child && (not (isTag Form child))

formChildren : List HTMLElement -> Bool
formChildren = validDescendants validFormDescendant

form :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.formChildren children) = True} ->
    HTMLElement
form attrs children = mkElement Form attrs children

input :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.emptyChildren children) = True} ->
    HTMLElement
input attrs children = mkElement Input attrs children

validLabelDescendant : HTMLElement -> Bool
validLabelDescendant child = isPhrasingContent child && (not (isTag Label child))
-- TODO: FIX
-- No labelable elements other than the labeled control are allowed.

labelChildren : List HTMLElement -> Bool
labelChildren = validDescendants validLabelDescendant

label :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.labelChildren children) = True} ->
    HTMLElement
label attrs children = mkElement Label attrs children

legend :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
legend attrs children = mkElement Legend attrs children

validMeterDescendant : HTMLElement -> Bool
validMeterDescendant child = isPhrasingContent child && (not (isTag Meter child))

meterChildren : List HTMLElement -> Bool
meterChildren = validDescendants validMeterDescendant

meter :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.meterChildren children) = True} ->
    HTMLElement
meter attrs children = mkElement Meter attrs children

validOptgroupDescendant : HTMLElement -> Bool
validOptgroupDescendant = isTag Option

optgroupChildren : List HTMLElement -> Bool
optgroupChildren = validDescendants validOptgroupDescendant

optgroup :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.optgroupChildren children) = True} ->
    HTMLElement
optgroup attrs children = mkElement Optgroup attrs children

option :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.textChildren children) = True} ->
    HTMLElement
option attrs children = mkElement Option attrs children

output :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.phrasingChildren children) = True} ->
    HTMLElement
output attrs children = mkElement Output attrs children

progressChildren : List HTMLElement -> Bool
progressChildren = validDescendants validProgressDescendant
    where
        validProgressDescendant : HTMLElement -> Bool
        validProgressDescendant child = isPhrasingContent child && (not (isTag Progress child))

progress :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.progressChildren children) = True} ->
    HTMLElement
progress attrs children = mkElement Progress attrs children

selectChildren : List HTMLElement -> Bool
selectChildren = validChildren validSelectChildren
    where
        validSelectChildren : HTMLElement -> Bool
        validSelectChildren child = (isTag Option child) || (isTag Optgroup child)

select :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.selectChildren children) = True} ->
    HTMLElement
select attrs children = mkElement Select attrs children

textarea :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.textChildren children) = True} ->
    HTMLElement
textarea attrs children = mkElement Textarea attrs children

detailsChildren : List HTMLElement -> Bool
detailsChildren (x :: xs) = (isTag Summary x) && (validChildren isFlowContent xs)
detailsChildren _ = False

details :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.detailsChildren children) = True} ->
    HTMLElement
details attrs children = mkElement Details attrs children

dialog :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.flowChildren children) = True} ->
    HTMLElement
dialog attrs children = mkElement Dialog attrs children

-- menu :
--     List Attr ->
--     (children: List HTMLElement) ->
--     {auto prf : (HTML.Elements.flowChildren children) = True} ->
--     HTMLElement
-- menu attrs children = mkElement Menu attrs children
-- If the element is in the list menu state: flow content, or alternatively, zero or more occurrences of <li>, <script>, and <template>.
-- If the element is in the context menu state: zero or more occurrences, in any order, of <menu> (context menu state only), <menuitem {deprecated}>, <hr>, <script>, and <template>.
-- TODO: oof...
--

summaryChildren : List HTMLElement -> Bool
summaryChildren (x :: Nil) = isHeadingContent x
summaryChildren children = phrasingChildren children

summary :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.summaryChildren children) = True} ->
    HTMLElement
summary attrs children = mkElement Summary attrs children

template :
    List Attr ->
    (children: List HTMLElement) ->
    {auto prf : (HTML.Elements.anyChildren children) = True} ->
    HTMLElement
template attrs children = mkElement Template attrs children
