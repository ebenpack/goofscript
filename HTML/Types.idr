module HTML.Types

import Data.Vect

-- TODO: FIX ACCESS
%access public export

data TypeTag =
      Address
    | Article
    | Aside
    | Footer
    | H1
    | H2
    | H3
    | H4
    | H5
    | H6
    | Header
    | Hgroup
    | Main
    | Nav
    | Section
    | Blockquote
    | Dd
    | Div
    | Dl
    | Dt
    | Figcaption
    | Figure
    | Hr
    | Li
    | Ol
    | P
    | Pre
    | Ul
    | A
    | Abbr
    | B
    | Bdi
    | Bdo
    | Br
    | Cite
    | Code
    | Data
    | Dfn
    | Em
    | I
    | Kbd
    | Mark
    | Q
    | Rb
    | Rp
    | Rt
    | Rtc
    | Ruby
    | S
    | Samp
    | Small
    | Span
    | Strong
    | Sub
    | Sup
    | Time
    | U
    | Var
    | Wbr
    | Area
    | Audio
    | Img
    | Map
    | Track
    | Video
    | Embed
    | Iframe
    | Object
    | Param
    | Picture
    | Source
    | Canvas
    | Noscript
    | Script
    | Del
    | Ins
    | Caption
    | Col
    | Colgroup
    | Table
    | Tbody
    | Td
    | Tfoot
    | Th
    | Thead
    | Tr
    | Button
    | Datalist
    | Fieldset
    | Form
    | Input
    | Label
    | Legend
    | Meter
    | Optgroup
    | Option
    | Output
    | Progress
    | Select
    | Textarea
    | Details
    | Dialog
    | Menu
    | Menuitem
    | Summary
    | Slot
    | Template
    {-
    | Math
    | Svg
    -}

Eq TypeTag where
    Address == Address = True
    Article == Article = True
    Aside == Aside = True
    Footer == Footer = True
    H1 == H1 = True
    H2 == H2 = True
    H3 == H3 = True
    H4 == H4 = True
    H5 == H5 = True
    H6 == H6 = True
    Header == Header = True
    Hgroup == Hgroup = True
    Main == Main = True
    Nav == Nav = True
    Section == Section = True
    Blockquote == Blockquote = True
    Dd == Dd = True
    Div == Div = True
    Dl == Dl = True
    Dt == Dt = True
    Figcaption == Figcaption = True
    Figure == Figure = True
    Hr == Hr = True
    Li == Li = True
    Ol == Ol = True
    P == P = True
    Pre == Pre = True
    Ul == Ul = True
    A == A = True
    Abbr == Abbr = True
    B == B = True
    Bdi == Bdi = True
    Bdo == Bdo = True
    Br == Br = True
    Cite == Cite = True
    Code == Code = True
    Data == Data = True
    Dfn == Dfn = True
    Em == Em = True
    I == I = True
    Kbd == Kbd = True
    Mark == Mark = True
    Q == Q = True
    Rb == Rb = True
    Rp == Rp = True
    Rt == Rt = True
    Rtc == Rtc = True
    Ruby == Ruby = True
    S == S = True
    Samp == Samp = True
    Small == Small = True
    Span == Span = True
    Strong == Strong = True
    Sub == Sub = True
    Sup == Sup = True
    Time == Time = True
    U == U = True
    Var == Var = True
    Wbr == Wbr = True
    Area == Area = True
    Audio == Audio = True
    Img == Img = True
    Map == Map = True
    Track == Track = True
    Video == Video = True
    Embed == Embed = True
    Iframe == Iframe = True
    Object == Object = True
    Param == Param = True
    Picture == Picture = True
    Source == Source = True
    Canvas == Canvas = True
    Noscript == Noscript = True
    Script == Script = True
    Del == Del = True
    Ins == Ins = True
    Caption == Caption = True
    Col == Col = True
    Colgroup == Colgroup = True
    Table == Table = True
    Tbody == Tbody = True
    Td == Td = True
    Tfoot == Tfoot = True
    Th == Th = True
    Thead == Thead = True
    Tr == Tr = True
    Button == Button = True
    Datalist == Datalist = True
    Fieldset == Fieldset = True
    Form == Form = True
    Input == Input = True
    Label == Label = True
    Legend == Legend = True
    Meter == Meter = True
    Optgroup == Optgroup = True
    Option == Option = True
    Output == Output = True
    Progress == Progress = True
    Select == Select = True
    Textarea == Textarea = True
    Details == Details = True
    Dialog == Dialog = True
    Menu == Menu = True
    Menuitem == Menuitem = True
    Summary == Summary = True
    Slot == Slot = True
    Template == Template = True
    _ == _ = False

Show TypeTag where
    show type = case type of
        Address => "address"
        Article => "article"
        Aside => "aside"
        Footer => "footer"
        H1 => "h1"
        H2 => "h2"
        H3 => "h3"
        H4 => "h4"
        H5 => "h5"
        H6 => "h6"
        Header => "header"
        Hgroup => "hgroup"
        Main => "main"
        Nav => "nav"
        Section => "section"
        Blockquote => "blockquote"
        Dd => "dd"
        Div => "div"
        Dl => "dl"
        Dt => "dt"
        Figcaption => "figcaption"
        Figure => "figure"
        Hr => "hr"
        Li => "li"
        Ol => "ol"
        P => "p"
        Pre => "pre"
        Ul => "ul"
        A => "a"
        Abbr => "abbr"
        B => "b"
        Bdi => "bdi"
        Bdo => "bdo"
        Br => "br"
        Cite => "cite"
        Code => "code"
        Data => "data"
        Dfn => "dfn"
        Em => "em"
        I => "i"
        Kbd => "kbd"
        Mark => "mark"
        Q => "q"
        Rb => "rb"
        Rp => "rp"
        Rt => "rt"
        Rtc => "rtc"
        Ruby => "ruby"
        S => "s"
        Samp => "samp"
        Small => "small"
        Span => "span"
        Strong => "strong"
        Sub => "sub"
        Sup => "sup"
        Time => "time"
        U => "u"
        Var => "var"
        Wbr => "wbr"
        Area => "area"
        Audio => "audio"
        Img => "img"
        Map => "map"
        Track => "track"
        Video => "video"
        Embed => "embed"
        Iframe => "iframe"
        Object => "object"
        Param => "param"
        Picture => "picture"
        Source => "source"
        Canvas => "canvas"
        Noscript => "noscript"
        Script => "script"
        Del => "del"
        Ins => "ins"
        Caption => "caption"
        Col => "col"
        Colgroup => "colgroup"
        Table => "table"
        Tbody => "tbody"
        Td => "td"
        Tfoot => "tfoot"
        Th => "th"
        Thead => "thead"
        Tr => "tr"
        Button => "button"
        Datalist => "datalist"
        Fieldset => "fieldset"
        Form => "form"
        Input => "input"
        Label => "label"
        Legend => "legend"
        Meter => "meter"
        Optgroup => "optgroup"
        Option => "option"
        Output => "output"
        Progress => "progress"
        Select => "select"
        Textarea => "textarea"
        Details => "details"
        Dialog => "dialog"
        Menu => "menu"
        Menuitem => "menuitem"
        Summary => "summary"
        Slot => "slot"
        Template => "template"

record Attr where
  constructor MkAttr
  name, value : String

Show Attr where
    show (MkAttr name value) = name ++ "=\"" ++ value ++ "\""

data TextNode = MkTextNode String

Show TextNode where
    show (MkTextNode s) = s

mutual
    record Element where
        constructor MkElement
        type : TypeTag
        omitTag : Bool
        attrs : Vect n Attr
        children : Vect m HTMLElement

    data HTMLElement = MkHTMLElement Element | MkHTMLTextNode TextNode

mutual
    showHTMLElement : HTMLElement -> String
    showHTMLElement (MkHTMLElement elem) = showElement elem
    showHTMLElement (MkHTMLTextNode text) = show text

    showElement : Element -> String
    showElement (MkElement type omitTag attrs children) =
        "<" ++ (show type) ++ (showAttrs attrs) ++ (if omitTag then "/" else "") ++ ">" ++
        (showChildren children) ++
        (if not omitTag then "</" ++ (show type) ++ ">" else "")
        where
            showAttrs : Vect n Attr -> String
            showAttrs Nil = ""
            showAttrs attrs' = " " ++ (foldl (++) "" $ intersperse " " $ map show attrs')
            showChildren : Vect m HTMLElement -> String
            showChildren children' = foldl (\acc, elem => acc ++ (showHTMLElement elem)) "" children'


Show HTMLElement where
    show = showHTMLElement

Show Element where
    show = showElement
