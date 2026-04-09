import logging
from enum import Enum
from typing import Any

from parsimonious.grammar import Grammar
from parsimonious.nodes import Node, NodeVisitor

from data_types import *
from file_formats.fields import *
from file_formats.parsers.text.textformat import *
from file_formats.specialized_types import *


class PartialSpec:
    """
    Represents a spec that may not be complete.
    This is particularly useful for attributes where
    special attribute types are combined with the declaration
    such that multiple specs are returned via the AST that
    actually represent one final spec.
    """

    def __init__(self, spec):
        self._spec = spec

    @property
    def spec(self) -> SpecData:
        """
        Retrieves the spec that may need to be combined with others.
        """
        return self._spec


class ListOpType(Enum):
    explicit = 1
    append = 2
    prepend = 3
    delete = 4


grammar = Grammar(
    r"""
    start = layerspec
    slash = "/"
    backslash = "\\"
    singlequote = "'"
    doublequote = "\""
    leftparen = "("
    rightparen = ")"
    leftbracket = "["
    rightbracket = "]"
    leftcurlybrace = "{"
    rightcurlybrace = "}"
    leftanglebracket = "<"
    rightanglebracket = ">"
    ampersand = "&"
    asterisk = "*"
    at = "@"
    colon = ":"
    comma = ","
    dot = "."
    equals = "="
    minus = "-"
    plus = "+"
    pound = "#"
    semicolon = ";"
    underscore = "_"
    verticalbar = "|"
    digit = ~"[0-9]"
    exponent = "e" / "E"
    utf8character = ~"[\r\n\t]" / ~"[ -~]" / ~"[ -퟿]" / ~"[豈-﷏]" / ~"[ﷰ-￯]" / ~"[𐀀-🿽]" / ~"[𠀀-𯿽]" / ~"[𰀀-𿿽]" / ~"[񀀀-񏿽]" / ~"[񐀀-񟿽]" / ~"[񠀀-񯿽]" / ~"[񰀀-񿿽]" / ~"[򀀀-򏿽]" / ~"[򐀀-򟿽]" / ~"[򠀀-򯿽]" / ~"[򰀀-򿿽]" / ~"[󀀀-󏿽]" / ~"[󐀀-󟿽]"
    crlf = ~"[\r\n|\r|\n]"
    space = ~"[ \t]"
    noncrlfutf8character = !crlf utf8character
    nondoublequotenoncrlfutf8character = !doublequote (noncrlfutf8character / verticalbar)
    nondoublequoteutf8character = !doublequote (utf8character / verticalbar)
    nonsinglequotenoncrlfutf8character = !singlequote (noncrlfutf8character / verticalbar)
    nonsinglequoteutf8character = !singlequote (utf8character / verticalbar)
    inf = "inf"
    nan = "nan"
    basepart = (digit+ (dot (digit)*)?) / (dot (digit)+)
    exponentpart = exponent (plus / minus)? digit digit*
    number = ((minus)? (inf / (basepart exponentpart?))) / nan / inf
    hexdigit = ~"[0-9A-F]"
    octdigit = ~"[0-7]"
    escapesinglecharacter = backslash / "a" / "b" / "f" / "n" / "r" / "t" / "v" / singlequote / doublequote
    escapehex = "x" hexdigit{,2}
    escapeoct = octdigit (octdigit (octdigit)?)?
    escaped = backslash (escapesinglecharacter / escapehex / escapeoct)
    singlelinesinglequotecontents = escaped / nonsinglequotenoncrlfutf8character
    singlelinedoublequotecontents = escaped / nondoublequotenoncrlfutf8character
    singlelinesinglequotestring = singlequote (singlelinesinglequotecontents)* singlequote
    singlelinedoublequotestring = doublequote (singlelinedoublequotecontents)* doublequote
    multilinesinglequotecontents = escaped / nonsinglequoteutf8character
    multilinedoublequotecontents = escaped / nondoublequoteutf8character
    threesinglequotes = singlequote singlequote singlequote
    multilinesinglequotestring = threesinglequotes (multilinesinglequotecontents)* threesinglequotes
    threedoublequotes = doublequote doublequote doublequote
    multilinedoublequotestring = threedoublequotes (multilinedoublequotecontents)* threedoublequotes
    singlequotestring = multilinesinglequotestring / singlelinesinglequotestring
    doublequotestring = multilinedoublequotestring / singlelinedoublequotestring
    string = singlequotestring / doublequotestring
    pythonstylecomment = pound (noncrlfutf8character / verticalbar)*
    cppstylesinglelinecomment = slash slash (noncrlfutf8character / verticalbar)*
    cppstylemultilineopen = slash asterisk
    cppstylemultilineclose = asterisk slash
    cppstylemultilinecomment = cppstylemultilineopen (!(cppstylemultilineclose) (utf8character / verticalbar))* cppstylemultilineclose
    cppstylecomment = cppstylemultilinecomment / cppstylesinglelinecomment
    comment = pythonstylecomment / cppstylecomment
    inlinepadding = space / cppstylemultilinecomment
    singlelinepadding = space / comment
    multilinepadding = space / crlf / comment
    listseparator = comma
    statementseparator = crlf / semicolon
    assignment = (inlinepadding)* equals (inlinepadding)*
    keywordappend = "append"
    keywordbezier = "bezier"
    keywordclass = "class"
    keywordconnect = "connect"
    keywordcurve = "curve"
    keywordcustom = "custom"
    keywordcustomdata = "customData"
    keyworddefault = "default"
    keyworddef = "def"
    keyworddelete = "delete"
    keyworddictionary = "dictionary"
    keyworddoc = "doc"
    keywordheld = "held"
    keywordhermite = "hermite"
    keywordinherits = "inherits"
    keywordkind = "kind"
    keywordlinear = "linear"
    keywordloop = "loop"
    keywordnamechildren = "nameChildren"
    keywordbignone = "None"
    keywordnone = "none"
    keywordoffset = "offset"
    keywordoscillate = "oscillate"
    keywordover = "over"
    keywordpayload = "payload"
    keywordpost = "post"
    keywordpre = "pre"
    keywordprepend = "prepend"
    keywordproperties = "properties"
    keywordreferences = "references"
    keywordrelocates = "relocates"
    keywordrel = "rel"
    keywordreorder = "reorder"
    keywordrepeat = "repeat"
    keywordreset = "reset"
    keywordrootprims = "rootPrims"
    keywordscale = "scale"
    keywordsloped = "sloped"
    keywordsublayers = "subLayers"
    keywordspecializes = "specializes"
    keywordspline = "spline"
    keywordtimesamples = "timeSamples"
    keyworduniform = "uniform"
    keywordvariantset = "variantSet"
    keywordvariantsets = "variantSets"
    keywordvariants = "variants"
    keywordvarying = "varying"
    keyword = keywordappend / keywordbezier / keywordclass / keywordconnect / keywordcurve / keywordcustomdata / keywordcustom / keyworddefault / keyworddef / keyworddelete / keyworddictionary / keyworddoc / keywordheld / keywordhermite / keywordinherits / keywordkind / keywordlinear / keywordloop / keywordnamechildren / keywordbignone / keywordnone / keywordoffset / keywordoscillate / keywordover / keywordpayload / keywordpost / keywordprepend / keywordpre / keywordproperties / keywordreferences / keywordrelocates / keywordrel / keywordreorder / keywordrepeat / keywordreset / keywordrootprims / keywordscale / keywordsloped / keywordsublayers / keywordspecializes / keywordspline / keywordtimesamples / keyworduniform / keywordvariantsets / keywordvariantset / keywordvariants / keywordvarying
    xidstart = ~"[A-Z]" / ~"[a-z]" / ~"[ª]" / ~"[µ]" / ~"[º]" / ~"[À-Ö]" / ~"[Ø-ö]" / ~"[ø-ƺ]" / ~"[ƻ]" / ~"[Ƽ-ƿ]" / ~"[ǀ-ǃ]" / ~"[Ǆ-ʓ]" / ~"[ʔ]" / ~"[ʕ-ʯ]" / ~"[ʰ-ˁ]" / ~"[ˆ-ˑ]" / ~"[ˠ-ˤ]" / ~"[ˬ]" / ~"[ˮ]" / ~"[Ͱ-ͳ]" / ~"[ʹ]" / ~"[Ͷ-ͷ]" / ~"[ͻ-ͽ]" / ~"[Ϳ]" / ~"[Ά]" / ~"[Έ-Ί]" / ~"[Ό]" / ~"[Ύ-Ρ]" / ~"[Σ-ϵ]" / ~"[Ϸ-ҁ]" / ~"[Ҋ-ԯ]" / ~"[Ա-Ֆ]" / ~"[ՙ]" / ~"[ՠ-ֈ]" / ~"[א-ת]" / ~"[ׯ-ײ]" / ~"[ؠ-ؿ]" / ~"[ـ]" / ~"[ف-ي]" / ~"[ٮ-ٯ]" / ~"[ٱ-ۓ]" / ~"[ە]" / ~"[ۥ-ۦ]" / ~"[ۮ-ۯ]" / ~"[ۺ-ۼ]" / ~"[ۿ]" / ~"[ܐ]" / ~"[ܒ-ܯ]" / ~"[ݍ-ޥ]" / ~"[ޱ]" / ~"[ߊ-ߪ]" / ~"[ߴ-ߵ]" / ~"[ߺ]" / ~"[ࠀ-ࠕ]" / ~"[ࠚ]" / ~"[ࠤ]" / ~"[ࠨ]" / ~"[ࡀ-ࡘ]" / ~"[ࡠ-ࡪ]" / ~"[ࡰ-ࢇ]" / ~"[ࢉ-ࢎ]" / ~"[ࢠ-ࣈ]" / ~"[ࣉ]" / ~"[ऄ-ह]" / ~"[ऽ]" / ~"[ॐ]" / ~"[क़-ॡ]" / ~"[ॱ]" / ~"[ॲ-ঀ]" / ~"[অ-ঌ]" / ~"[এ-ঐ]" / ~"[ও-ন]" / ~"[প-র]" / ~"[ল]" / ~"[শ-হ]" / ~"[ঽ]" / ~"[ৎ]" / ~"[ড়-ঢ়]" / ~"[য়-ৡ]" / ~"[ৰ-ৱ]" / ~"[ৼ]" / ~"[ਅ-ਊ]" / ~"[ਏ-ਐ]" / ~"[ਓ-ਨ]" / ~"[ਪ-ਰ]" / ~"[ਲ-ਲ਼]" / ~"[ਵ-ਸ਼]" / ~"[ਸ-ਹ]" / ~"[ਖ਼-ੜ]" / ~"[ਫ਼]" / ~"[ੲ-ੴ]" / ~"[અ-ઍ]" / ~"[એ-ઑ]" / ~"[ઓ-ન]" / ~"[પ-ર]" / ~"[લ-ળ]" / ~"[વ-હ]" / ~"[ઽ]" / ~"[ૐ]" / ~"[ૠ-ૡ]" / ~"[ૹ]" / ~"[ଅ-ଌ]" / ~"[ଏ-ଐ]" / ~"[ଓ-ନ]" / ~"[ପ-ର]" / ~"[ଲ-ଳ]" / ~"[ଵ-ହ]" / ~"[ଽ]" / ~"[ଡ଼-ଢ଼]" / ~"[ୟ-ୡ]" / ~"[ୱ]" / ~"[ஃ]" / ~"[அ-ஊ]" / ~"[எ-ஐ]" / ~"[ஒ-க]" / ~"[ங-ச]" / ~"[ஜ]" / ~"[ஞ-ட]" / ~"[ண-த]" / ~"[ந-ப]" / ~"[ம-ஹ]" / ~"[ௐ]" / ~"[అ-ఌ]" / ~"[ఎ-ఐ]" / ~"[ఒ-న]" / ~"[ప-హ]" / ~"[ఽ]" / ~"[ౘ-ౚ]" / ~"[ౝ]" / ~"[ౠ-ౡ]" / ~"[ಀ]" / ~"[ಅ-ಌ]" / ~"[ಎ-ಐ]" / ~"[ಒ-ನ]" / ~"[ಪ-ಳ]" / ~"[ವ-ಹ]" / ~"[ಽ]" / ~"[ೝ-ೞ]" / ~"[ೠ-ೡ]" / ~"[ೱ-ೲ]" / ~"[ഄ-ഌ]" / ~"[എ-ഐ]" / ~"[ഒ-ഺ]" / ~"[ഽ]" / ~"[ൎ]" / ~"[ൔ-ൖ]" / ~"[ൟ-ൡ]" / ~"[ൺ-ൿ]" / ~"[අ-ඖ]" / ~"[ක-න]" / ~"[ඳ-ර]" / ~"[ල]" / ~"[ව-ෆ]" / ~"[ก-ะ]" / ~"[า]" / ~"[เ-ๅ]" / ~"[ๆ]" / ~"[ກ-ຂ]" / ~"[ຄ]" / ~"[ຆ-ຊ]" / ~"[ຌ-ຣ]" / ~"[ລ]" / ~"[ວ-ະ]" / ~"[າ]" / ~"[ຽ]" / ~"[ເ-ໄ]" / ~"[ໆ]" / ~"[ໜ-ໟ]" / ~"[ༀ]" / ~"[ཀ-ཇ]" / ~"[ཉ-ཬ]" / ~"[ྈ-ྌ]" / ~"[က-ဪ]" / ~"[ဿ]" / ~"[ၐ-ၕ]" / ~"[ၚ-ၝ]" / ~"[ၡ]" / ~"[ၥ-ၦ]" / ~"[ၮ-ၰ]" / ~"[ၵ-ႁ]" / ~"[ႎ]" / ~"[Ⴀ-Ⴥ]" / ~"[Ⴧ]" / ~"[Ⴭ]" / ~"[ა-ჺ]" / ~"[ჼ]" / ~"[ჽ-ჿ]" / ~"[ᄀ-ቈ]" / ~"[ቊ-ቍ]" / ~"[ቐ-ቖ]" / ~"[ቘ]" / ~"[ቚ-ቝ]" / ~"[በ-ኈ]" / ~"[ኊ-ኍ]" / ~"[ነ-ኰ]" / ~"[ኲ-ኵ]" / ~"[ኸ-ኾ]" / ~"[ዀ]" / ~"[ዂ-ዅ]" / ~"[ወ-ዖ]" / ~"[ዘ-ጐ]" / ~"[ጒ-ጕ]" / ~"[ጘ-ፚ]" / ~"[ᎀ-ᎏ]" / ~"[Ꭰ-Ᏽ]" / ~"[ᏸ-ᏽ]" / ~"[ᐁ-ᙬ]" / ~"[ᙯ-ᙿ]" / ~"[ᚁ-ᚚ]" / ~"[ᚠ-ᛪ]" / ~"[ᛮ-ᛰ]" / ~"[ᛱ-ᛸ]" / ~"[ᜀ-ᜑ]" / ~"[ᜟ-ᜱ]" / ~"[ᝀ-ᝑ]" / ~"[ᝠ-ᝬ]" / ~"[ᝮ-ᝰ]" / ~"[ក-ឳ]" / ~"[ៗ]" / ~"[ៜ]" / ~"[ᠠ-ᡂ]" / ~"[ᡃ]" / ~"[ᡄ-ᡸ]" / ~"[ᢀ-ᢄ]" / ~"[ᢅ-ᢆ]" / ~"[ᢇ-ᢨ]" / ~"[ᢪ]" / ~"[ᢰ-ᣵ]" / ~"[ᤀ-ᤞ]" / ~"[ᥐ-ᥭ]" / ~"[ᥰ-ᥴ]" / ~"[ᦀ-ᦫ]" / ~"[ᦰ-ᧉ]" / ~"[ᨀ-ᨖ]" / ~"[ᨠ-ᩔ]" / ~"[ᪧ]" / ~"[ᬅ-ᬳ]" / ~"[ᭅ-ᭌ]" / ~"[ᮃ-ᮠ]" / ~"[ᮮ-ᮯ]" / ~"[ᮺ-ᯥ]" / ~"[ᰀ-ᰣ]" / ~"[ᱍ-ᱏ]" / ~"[ᱚ-ᱷ]" / ~"[ᱸ-ᱽ]" / ~"[ᲀ-ᲈ]" / ~"[Ა-Ჺ]" / ~"[Ჽ-Ჿ]" / ~"[ᳩ-ᳬ]" / ~"[ᳮ-ᳳ]" / ~"[ᳵ-ᳶ]" / ~"[ᳺ]" / ~"[ᴀ-ᴫ]" / ~"[ᴬ-ᵪ]" / ~"[ᵫ-ᵷ]" / ~"[ᵸ]" / ~"[ᵹ-ᶚ]" / ~"[ᶛ-ᶿ]" / ~"[Ḁ-ἕ]" / ~"[Ἐ-Ἕ]" / ~"[ἠ-ὅ]" / ~"[Ὀ-Ὅ]" / ~"[ὐ-ὗ]" / ~"[Ὑ]" / ~"[Ὓ]" / ~"[Ὕ]" / ~"[Ὗ-ώ]" / ~"[ᾀ-ᾴ]" / ~"[ᾶ-ᾼ]" / ~"[ι]" / ~"[ῂ-ῄ]" / ~"[ῆ-ῌ]" / ~"[ῐ-ΐ]" / ~"[ῖ-Ί]" / ~"[ῠ-Ῥ]" / ~"[ῲ-ῴ]" / ~"[ῶ-ῼ]" / ~"[ⁱ]" / ~"[ⁿ]" / ~"[ₐ-ₜ]" / ~"[ℂ]" / ~"[ℇ]" / ~"[ℊ-ℓ]" / ~"[ℕ]" / ~"[℘]" / ~"[ℙ-ℝ]" / ~"[ℤ]" / ~"[Ω]" / ~"[ℨ]" / ~"[K-ℭ]" / ~"[℮]" / ~"[ℯ-ℴ]" / ~"[ℵ-ℸ]" / ~"[ℹ]" / ~"[ℼ-ℿ]" / ~"[ⅅ-ⅉ]" / ~"[ⅎ]" / ~"[Ⅰ-ↂ]" / ~"[Ↄ-ↄ]" / ~"[ↅ-ↈ]" / ~"[Ⰰ-ⱻ]" / ~"[ⱼ-ⱽ]" / ~"[Ȿ-ⳤ]" / ~"[Ⳬ-ⳮ]" / ~"[Ⳳ-ⳳ]" / ~"[ⴀ-ⴥ]" / ~"[ⴧ]" / ~"[ⴭ]" / ~"[ⴰ-ⵧ]" / ~"[ⵯ]" / ~"[ⶀ-ⶖ]" / ~"[ⶠ-ⶦ]" / ~"[ⶨ-ⶮ]" / ~"[ⶰ-ⶶ]" / ~"[ⶸ-ⶾ]" / ~"[ⷀ-ⷆ]" / ~"[ⷈ-ⷎ]" / ~"[ⷐ-ⷖ]" / ~"[ⷘ-ⷞ]" / ~"[々]" / ~"[〆]" / ~"[〇]" / ~"[〡-〩]" / ~"[〱-〵]" / ~"[〸-〺]" / ~"[〻]" / ~"[〼]" / ~"[ぁ-ゖ]" / ~"[ゝ-ゞ]" / ~"[ゟ]" / ~"[ァ-ヺ]" / ~"[ー-ヾ]" / ~"[ヿ]" / ~"[ㄅ-ㄯ]" / ~"[ㄱ-ㆎ]" / ~"[ㆠ-ㆿ]" / ~"[ㇰ-ㇿ]" / ~"[㐀-䶿]" / ~"[一-ꀔ]" / ~"[ꀕ]" / ~"[ꀖ-ꒌ]" / ~"[ꓐ-ꓷ]" / ~"[ꓸ-ꓽ]" / ~"[ꔀ-ꘋ]" / ~"[ꘌ]" / ~"[ꘐ-ꘟ]" / ~"[ꘪ-ꘫ]" / ~"[Ꙁ-ꙭ]" / ~"[ꙮ]" / ~"[ꙿ]" / ~"[Ꚁ-ꚛ]" / ~"[ꚜ-ꚝ]" / ~"[ꚠ-ꛥ]" / ~"[ꛦ-ꛯ]" / ~"[ꜗ-ꜟ]" / ~"[Ꜣ-ꝯ]" / ~"[ꝰ]" / ~"[ꝱ-ꞇ]" / ~"[ꞈ]" / ~"[Ꞌ-ꞎ]" / ~"[ꞏ]" / ~"[Ꞑ-ꟊ]" / ~"[Ꟑ-ꟑ]" / ~"[ꟓ]" / ~"[ꟕ-ꟙ]" / ~"[ꟲ-ꟴ]" / ~"[Ꟶ-ꟶ]" / ~"[ꟷ]" / ~"[ꟸ-ꟹ]" / ~"[ꟺ]" / ~"[ꟻ-ꠁ]" / ~"[ꠃ-ꠅ]" / ~"[ꠇ-ꠊ]" / ~"[ꠌ-ꠢ]" / ~"[ꡀ-ꡳ]" / ~"[ꢂ-ꢳ]" / ~"[ꣲ-ꣷ]" / ~"[ꣻ]" / ~"[ꣽ-ꣾ]" / ~"[ꤊ-ꤥ]" / ~"[ꤰ-ꥆ]" / ~"[ꥠ-ꥼ]" / ~"[ꦄ-ꦲ]" / ~"[ꧏ]" / ~"[ꧠ-ꧤ]" / ~"[ꧦ]" / ~"[ꧧ-ꧯ]" / ~"[ꧺ-ꧾ]" / ~"[ꨀ-ꨨ]" / ~"[ꩀ-ꩂ]" / ~"[ꩄ-ꩋ]" / ~"[ꩠ-ꩯ]" / ~"[ꩰ]" / ~"[ꩱ-ꩶ]" / ~"[ꩺ]" / ~"[ꩾ-ꪯ]" / ~"[ꪱ]" / ~"[ꪵ-ꪶ]" / ~"[ꪹ-ꪽ]" / ~"[ꫀ]" / ~"[ꫂ]" / ~"[ꫛ-ꫜ]" / ~"[ꫝ]" / ~"[ꫠ-ꫪ]" / ~"[ꫲ]" / ~"[ꫳ-ꫴ]" / ~"[ꬁ-ꬆ]" / ~"[ꬉ-ꬎ]" / ~"[ꬑ-ꬖ]" / ~"[ꬠ-ꬦ]" / ~"[ꬨ-ꬮ]" / ~"[ꬰ-ꭚ]" / ~"[ꭜ-ꭟ]" / ~"[ꭠ-ꭨ]" / ~"[ꭩ]" / ~"[ꭰ-ꮿ]" / ~"[ꯀ-ꯢ]" / ~"[가-힣]" / ~"[ힰ-ퟆ]" / ~"[ퟋ-ퟻ]" / ~"[豈-舘]" / ~"[並-龎]" / ~"[ﬀ-ﬆ]" / ~"[ﬓ-ﬗ]" / ~"[יִ]" / ~"[ײַ-ﬨ]" / ~"[שׁ-זּ]" / ~"[טּ-לּ]" / ~"[מּ]" / ~"[נּ-סּ]" / ~"[ףּ-פּ]" / ~"[צּ-ﮱ]" / ~"[ﯓ-ﱝ]" / ~"[ﱤ-ﴽ]" / ~"[ﵐ-ﶏ]" / ~"[ﶒ-ﷇ]" / ~"[ﷰ-ﷹ]" / ~"[ﹱ]" / ~"[ﹳ]" / ~"[ﹷ]" / ~"[ﹹ]" / ~"[ﹻ]" / ~"[ﹽ]" / ~"[ﹿ-ﻼ]" / ~"[Ａ-Ｚ]" / ~"[ａ-ｚ]" / ~"[ｦ-ｯ]" / ~"[ｰ]" / ~"[ｱ-ﾝ]" / ~"[ﾠ-ﾾ]" / ~"[ￂ-ￇ]" / ~"[ￊ-ￏ]" / ~"[ￒ-ￗ]" / ~"[ￚ-ￜ]" / ~"[𐀀-𐀋]" / ~"[𐀍-𐀦]" / ~"[𐀨-𐀺]" / ~"[𐀼-𐀽]" / ~"[𐀿-𐁍]" / ~"[𐁐-𐁝]" / ~"[𐂀-𐃺]" / ~"[𐅀-𐅴]" / ~"[𐊀-𐊜]" / ~"[𐊠-𐋐]" / ~"[𐌀-𐌟]" / ~"[𐌭-𐍀]" / ~"[𐍁]" / ~"[𐍂-𐍉]" / ~"[𐍊]" / ~"[𐍐-𐍵]" / ~"[𐎀-𐎝]" / ~"[𐎠-𐏃]" / ~"[𐏈-𐏏]" / ~"[𐏑-𐏕]" / ~"[𐐀-𐑏]" / ~"[𐑐-𐒝]" / ~"[𐒰-𐓓]" / ~"[𐓘-𐓻]" / ~"[𐔀-𐔧]" / ~"[𐔰-𐕣]" / ~"[𐕰-𐕺]" / ~"[𐕼-𐖊]" / ~"[𐖌-𐖒]" / ~"[𐖔-𐖕]" / ~"[𐖗-𐖡]" / ~"[𐖣-𐖱]" / ~"[𐖳-𐖹]" / ~"[𐖻-𐖼]" / ~"[𐘀-𐜶]" / ~"[𐝀-𐝕]" / ~"[𐝠-𐝧]" / ~"[𐞀-𐞅]" / ~"[𐞇-𐞰]" / ~"[𐞲-𐞺]" / ~"[𐠀-𐠅]" / ~"[𐠈]" / ~"[𐠊-𐠵]" / ~"[𐠷-𐠸]" / ~"[𐠼]" / ~"[𐠿-𐡕]" / ~"[𐡠-𐡶]" / ~"[𐢀-𐢞]" / ~"[𐣠-𐣲]" / ~"[𐣴-𐣵]" / ~"[𐤀-𐤕]" / ~"[𐤠-𐤹]" / ~"[𐦀-𐦷]" / ~"[𐦾-𐦿]" / ~"[𐨀]" / ~"[𐨐-𐨓]" / ~"[𐨕-𐨗]" / ~"[𐨙-𐨵]" / ~"[𐩠-𐩼]" / ~"[𐪀-𐪜]" / ~"[𐫀-𐫇]" / ~"[𐫉-𐫤]" / ~"[𐬀-𐬵]" / ~"[𐭀-𐭕]" / ~"[𐭠-𐭲]" / ~"[𐮀-𐮑]" / ~"[𐰀-𐱈]" / ~"[𐲀-𐲲]" / ~"[𐳀-𐳲]" / ~"[𐴀-𐴣]" / ~"[𐺀-𐺩]" / ~"[𐺰-𐺱]" / ~"[𐼀-𐼜]" / ~"[𐼧]" / ~"[𐼰-𐽅]" / ~"[𐽰-𐾁]" / ~"[𐾰-𐿄]" / ~"[𐿠-𐿶]" / ~"[𑀃-𑀷]" / ~"[𑁱-𑁲]" / ~"[𑁵]" / ~"[𑂃-𑂯]" / ~"[𑃐-𑃨]" / ~"[𑄃-𑄦]" / ~"[𑅄]" / ~"[𑅇]" / ~"[𑅐-𑅲]" / ~"[𑅶]" / ~"[𑆃-𑆲]" / ~"[𑇁-𑇄]" / ~"[𑇚]" / ~"[𑇜]" / ~"[𑈀-𑈑]" / ~"[𑈓-𑈫]" / ~"[𑊀-𑊆]" / ~"[𑊈]" / ~"[𑊊-𑊍]" / ~"[𑊏-𑊝]" / ~"[𑊟-𑊨]" / ~"[𑊰-𑋞]" / ~"[𑌅-𑌌]" / ~"[𑌏-𑌐]" / ~"[𑌓-𑌨]" / ~"[𑌪-𑌰]" / ~"[𑌲-𑌳]" / ~"[𑌵-𑌹]" / ~"[𑌽]" / ~"[𑍐]" / ~"[𑍝-𑍡]" / ~"[𑐀-𑐴]" / ~"[𑑇-𑑊]" / ~"[𑑟-𑑡]" / ~"[𑒀-𑒯]" / ~"[𑓄-𑓅]" / ~"[𑓇]" / ~"[𑖀-𑖮]" / ~"[𑗘-𑗛]" / ~"[𑘀-𑘯]" / ~"[𑙄]" / ~"[𑚀-𑚪]" / ~"[𑚸]" / ~"[𑜀-𑜚]" / ~"[𑝀-𑝆]" / ~"[𑠀-𑠫]" / ~"[𑢠-𑣟]" / ~"[𑣿-𑤆]" / ~"[𑤉]" / ~"[𑤌-𑤓]" / ~"[𑤕-𑤖]" / ~"[𑤘-𑤯]" / ~"[𑤿]" / ~"[𑥁]" / ~"[𑦠-𑦧]" / ~"[𑦪-𑧐]" / ~"[𑧡]" / ~"[𑧣]" / ~"[𑨀]" / ~"[𑨋-𑨲]" / ~"[𑨺]" / ~"[𑩐]" / ~"[𑩜-𑪉]" / ~"[𑪝]" / ~"[𑪰-𑫸]" / ~"[𑰀-𑰈]" / ~"[𑰊-𑰮]" / ~"[𑱀]" / ~"[𑱲-𑲏]" / ~"[𑴀-𑴆]" / ~"[𑴈-𑴉]" / ~"[𑴋-𑴰]" / ~"[𑵆]" / ~"[𑵠-𑵥]" / ~"[𑵧-𑵨]" / ~"[𑵪-𑶉]" / ~"[𑶘]" / ~"[𑻠-𑻲]" / ~"[𑾰]" / ~"[𒀀-𒎙]" / ~"[𒐀-𒑮]" / ~"[𒒀-𒕃]" / ~"[𒾐-𒿰]" / ~"[𓀀-𓐮]" / ~"[𔐀-𔙆]" / ~"[𖠀-𖨸]" / ~"[𖩀-𖩞]" / ~"[𖩰-𖪾]" / ~"[𖫐-𖫭]" / ~"[𖬀-𖬯]" / ~"[𖭀-𖭃]" / ~"[𖭣-𖭷]" / ~"[𖭽-𖮏]" / ~"[𖹀-𖹿]" / ~"[𖼀-𖽊]" / ~"[𖽐]" / ~"[𖾓-𖾟]" / ~"[𖿠-𖿡]" / ~"[𖿣]" / ~"[𗀀-𘟷]" / ~"[𘠀-𘳕]" / ~"[𘴀-𘴈]" / ~"[𚿰-𚿳]" / ~"[𚿵-𚿻]" / ~"[𚿽-𚿾]" / ~"[𛀀-𛄢]" / ~"[𛅐-𛅒]" / ~"[𛅤-𛅧]" / ~"[𛅰-𛋻]" / ~"[𛰀-𛱪]" / ~"[𛱰-𛱼]" / ~"[𛲀-𛲈]" / ~"[𛲐-𛲙]" / ~"[𝐀-𝑔]" / ~"[𝑖-𝒜]" / ~"[𝒞-𝒟]" / ~"[𝒢]" / ~"[𝒥-𝒦]" / ~"[𝒩-𝒬]" / ~"[𝒮-𝒹]" / ~"[𝒻]" / ~"[𝒽-𝓃]" / ~"[𝓅-𝔅]" / ~"[𝔇-𝔊]" / ~"[𝔍-𝔔]" / ~"[𝔖-𝔜]" / ~"[𝔞-𝔹]" / ~"[𝔻-𝔾]" / ~"[𝕀-𝕄]" / ~"[𝕆]" / ~"[𝕊-𝕐]" / ~"[𝕒-𝚥]" / ~"[𝚨-𝛀]" / ~"[𝛂-𝛚]" / ~"[𝛜-𝛺]" / ~"[𝛼-𝜔]" / ~"[𝜖-𝜴]" / ~"[𝜶-𝝎]" / ~"[𝝐-𝝮]" / ~"[𝝰-𝞈]" / ~"[𝞊-𝞨]" / ~"[𝞪-𝟂]" / ~"[𝟄-𝟋]" / ~"[𝼀-𝼉]" / ~"[𝼊]" / ~"[𝼋-𝼞]" / ~"[𞄀-𞄬]" / ~"[𞄷-𞄽]" / ~"[𞅎]" / ~"[𞊐-𞊭]" / ~"[𞋀-𞋫]" / ~"[𞟠-𞟦]" / ~"[𞟨-𞟫]" / ~"[𞟭-𞟮]" / ~"[𞟰-𞟾]" / ~"[𞠀-𞣄]" / ~"[𞤀-𞥃]" / ~"[𞥋]" / ~"[𞸀-𞸃]" / ~"[𞸅-𞸟]" / ~"[𞸡-𞸢]" / ~"[𞸤]" / ~"[𞸧]" / ~"[𞸩-𞸲]" / ~"[𞸴-𞸷]" / ~"[𞸹]" / ~"[𞸻]" / ~"[𞹂]" / ~"[𞹇]" / ~"[𞹉]" / ~"[𞹋]" / ~"[𞹍-𞹏]" / ~"[𞹑-𞹒]" / ~"[𞹔]" / ~"[𞹗]" / ~"[𞹙]" / ~"[𞹛]" / ~"[𞹝]" / ~"[𞹟]" / ~"[𞹡-𞹢]" / ~"[𞹤]" / ~"[𞹧-𞹪]" / ~"[𞹬-𞹲]" / ~"[𞹴-𞹷]" / ~"[𞹹-𞹼]" / ~"[𞹾]" / ~"[𞺀-𞺉]" / ~"[𞺋-𞺛]" / ~"[𞺡-𞺣]" / ~"[𞺥-𞺩]" / ~"[𞺫-𞺻]" / ~"[𠀀-𪛟]" / ~"[𪜀-𫜸]" / ~"[𫝀-𫠝]" / ~"[𫠠-𬺡]" / ~"[𬺰-𮯠]" / ~"[丽-𪘀]" / ~"[𰀀-𱍊]" / ~"[_]"
    xidcontinue = ~"[0-9]" / ~"[A-Z]" / ~"[_]" / ~"[a-z]" / ~"[ª]" / ~"[µ]" / ~"[·]" / ~"[º]" / ~"[À-Ö]" / ~"[Ø-ö]" / ~"[ø-ƺ]" / ~"[ƻ]" / ~"[Ƽ-ƿ]" / ~"[ǀ-ǃ]" / ~"[Ǆ-ʓ]" / ~"[ʔ]" / ~"[ʕ-ʯ]" / ~"[ʰ-ˁ]" / ~"[ˆ-ˑ]" / ~"[ˠ-ˤ]" / ~"[ˬ]" / ~"[ˮ]" / ~"[̀-ͯ]" / ~"[Ͱ-ͳ]" / ~"[ʹ]" / ~"[Ͷ-ͷ]" / ~"[ͻ-ͽ]" / ~"[Ϳ]" / ~"[Ά]" / ~"[·]" / ~"[Έ-Ί]" / ~"[Ό]" / ~"[Ύ-Ρ]" / ~"[Σ-ϵ]" / ~"[Ϸ-ҁ]" / ~"[҃-҇]" / ~"[Ҋ-ԯ]" / ~"[Ա-Ֆ]" / ~"[ՙ]" / ~"[ՠ-ֈ]" / ~"[֑-ֽ]" / ~"[ֿ]" / ~"[ׁ-ׂ]" / ~"[ׄ-ׅ]" / ~"[ׇ]" / ~"[א-ת]" / ~"[ׯ-ײ]" / ~"[ؐ-ؚ]" / ~"[ؠ-ؿ]" / ~"[ـ]" / ~"[ف-ي]" / ~"[ً-ٟ]" / ~"[٠-٩]" / ~"[ٮ-ٯ]" / ~"[ٰ]" / ~"[ٱ-ۓ]" / ~"[ە]" / ~"[ۖ-ۜ]" / ~"[۟-ۤ]" / ~"[ۥ-ۦ]" / ~"[ۧ-ۨ]" / ~"[۪-ۭ]" / ~"[ۮ-ۯ]" / ~"[۰-۹]" / ~"[ۺ-ۼ]" / ~"[ۿ]" / ~"[ܐ]" / ~"[ܑ]" / ~"[ܒ-ܯ]" / ~"[ܰ-݊]" / ~"[ݍ-ޥ]" / ~"[ަ-ް]" / ~"[ޱ]" / ~"[߀-߉]" / ~"[ߊ-ߪ]" / ~"[߫-߳]" / ~"[ߴ-ߵ]" / ~"[ߺ]" / ~"[߽]" / ~"[ࠀ-ࠕ]" / ~"[ࠖ-࠙]" / ~"[ࠚ]" / ~"[ࠛ-ࠣ]" / ~"[ࠤ]" / ~"[ࠥ-ࠧ]" / ~"[ࠨ]" / ~"[ࠩ-࠭]" / ~"[ࡀ-ࡘ]" / ~"[࡙-࡛]" / ~"[ࡠ-ࡪ]" / ~"[ࡰ-ࢇ]" / ~"[ࢉ-ࢎ]" / ~"[࢘-࢟]" / ~"[ࢠ-ࣈ]" / ~"[ࣉ]" / ~"[࣊-࣡]" / ~"[ࣣ-ं]" / ~"[ः]" / ~"[ऄ-ह]" / ~"[ऺ]" / ~"[ऻ]" / ~"[़]" / ~"[ऽ]" / ~"[ा-ी]" / ~"[ु-ै]" / ~"[ॉ-ौ]" / ~"[्]" / ~"[ॎ-ॏ]" / ~"[ॐ]" / ~"[॑-ॗ]" / ~"[क़-ॡ]" / ~"[ॢ-ॣ]" / ~"[०-९]" / ~"[ॱ]" / ~"[ॲ-ঀ]" / ~"[ঁ]" / ~"[ং-ঃ]" / ~"[অ-ঌ]" / ~"[এ-ঐ]" / ~"[ও-ন]" / ~"[প-র]" / ~"[ল]" / ~"[শ-হ]" / ~"[়]" / ~"[ঽ]" / ~"[া-ী]" / ~"[ু-ৄ]" / ~"[ে-ৈ]" / ~"[ো-ৌ]" / ~"[্]" / ~"[ৎ]" / ~"[ৗ]" / ~"[ড়-ঢ়]" / ~"[য়-ৡ]" / ~"[ৢ-ৣ]" / ~"[০-৯]" / ~"[ৰ-ৱ]" / ~"[ৼ]" / ~"[৾]" / ~"[ਁ-ਂ]" / ~"[ਃ]" / ~"[ਅ-ਊ]" / ~"[ਏ-ਐ]" / ~"[ਓ-ਨ]" / ~"[ਪ-ਰ]" / ~"[ਲ-ਲ਼]" / ~"[ਵ-ਸ਼]" / ~"[ਸ-ਹ]" / ~"[਼]" / ~"[ਾ-ੀ]" / ~"[ੁ-ੂ]" / ~"[ੇ-ੈ]" / ~"[ੋ-੍]" / ~"[ੑ]" / ~"[ਖ਼-ੜ]" / ~"[ਫ਼]" / ~"[੦-੯]" / ~"[ੰ-ੱ]" / ~"[ੲ-ੴ]" / ~"[ੵ]" / ~"[ઁ-ં]" / ~"[ઃ]" / ~"[અ-ઍ]" / ~"[એ-ઑ]" / ~"[ઓ-ન]" / ~"[પ-ર]" / ~"[લ-ળ]" / ~"[વ-હ]" / ~"[઼]" / ~"[ઽ]" / ~"[ા-ી]" / ~"[ુ-ૅ]" / ~"[ે-ૈ]" / ~"[ૉ]" / ~"[ો-ૌ]" / ~"[્]" / ~"[ૐ]" / ~"[ૠ-ૡ]" / ~"[ૢ-ૣ]" / ~"[૦-૯]" / ~"[ૹ]" / ~"[ૺ-૿]" / ~"[ଁ]" / ~"[ଂ-ଃ]" / ~"[ଅ-ଌ]" / ~"[ଏ-ଐ]" / ~"[ଓ-ନ]" / ~"[ପ-ର]" / ~"[ଲ-ଳ]" / ~"[ଵ-ହ]" / ~"[଼]" / ~"[ଽ]" / ~"[ା]" / ~"[ି]" / ~"[ୀ]" / ~"[ୁ-ୄ]" / ~"[େ-ୈ]" / ~"[ୋ-ୌ]" / ~"[୍]" / ~"[୕-ୖ]" / ~"[ୗ]" / ~"[ଡ଼-ଢ଼]" / ~"[ୟ-ୡ]" / ~"[ୢ-ୣ]" / ~"[୦-୯]" / ~"[ୱ]" / ~"[ஂ]" / ~"[ஃ]" / ~"[அ-ஊ]" / ~"[எ-ஐ]" / ~"[ஒ-க]" / ~"[ங-ச]" / ~"[ஜ]" / ~"[ஞ-ட]" / ~"[ண-த]" / ~"[ந-ப]" / ~"[ம-ஹ]" / ~"[ா-ி]" / ~"[ீ]" / ~"[ு-ூ]" / ~"[ெ-ை]" / ~"[ொ-ௌ]" / ~"[்]" / ~"[ௐ]" / ~"[ௗ]" / ~"[௦-௯]" / ~"[ఀ]" / ~"[ఁ-ః]" / ~"[ఄ]" / ~"[అ-ఌ]" / ~"[ఎ-ఐ]" / ~"[ఒ-న]" / ~"[ప-హ]" / ~"[఼]" / ~"[ఽ]" / ~"[ా-ీ]" / ~"[ు-ౄ]" / ~"[ె-ై]" / ~"[ొ-్]" / ~"[ౕ-ౖ]" / ~"[ౘ-ౚ]" / ~"[ౝ]" / ~"[ౠ-ౡ]" / ~"[ౢ-ౣ]" / ~"[౦-౯]" / ~"[ಀ]" / ~"[ಁ]" / ~"[ಂ-ಃ]" / ~"[ಅ-ಌ]" / ~"[ಎ-ಐ]" / ~"[ಒ-ನ]" / ~"[ಪ-ಳ]" / ~"[ವ-ಹ]" / ~"[಼]" / ~"[ಽ]" / ~"[ಾ]" / ~"[ಿ]" / ~"[ೀ-ೄ]" / ~"[ೆ]" / ~"[ೇ-ೈ]" / ~"[ೊ-ೋ]" / ~"[ೌ-್]" / ~"[ೕ-ೖ]" / ~"[ೝ-ೞ]" / ~"[ೠ-ೡ]" / ~"[ೢ-ೣ]" / ~"[೦-೯]" / ~"[ೱ-ೲ]" / ~"[ഀ-ഁ]" / ~"[ം-ഃ]" / ~"[ഄ-ഌ]" / ~"[എ-ഐ]" / ~"[ഒ-ഺ]" / ~"[഻-഼]" / ~"[ഽ]" / ~"[ാ-ീ]" / ~"[ു-ൄ]" / ~"[െ-ൈ]" / ~"[ൊ-ൌ]" / ~"[്]" / ~"[ൎ]" / ~"[ൔ-ൖ]" / ~"[ൗ]" / ~"[ൟ-ൡ]" / ~"[ൢ-ൣ]" / ~"[൦-൯]" / ~"[ൺ-ൿ]" / ~"[ඁ]" / ~"[ං-ඃ]" / ~"[අ-ඖ]" / ~"[ක-න]" / ~"[ඳ-ර]" / ~"[ල]" / ~"[ව-ෆ]" / ~"[්]" / ~"[ා-ෑ]" / ~"[ි-ු]" / ~"[ූ]" / ~"[ෘ-ෟ]" / ~"[෦-෯]" / ~"[ෲ-ෳ]" / ~"[ก-ะ]" / ~"[ั]" / ~"[า-ำ]" / ~"[ิ-ฺ]" / ~"[เ-ๅ]" / ~"[ๆ]" / ~"[็-๎]" / ~"[๐-๙]" / ~"[ກ-ຂ]" / ~"[ຄ]" / ~"[ຆ-ຊ]" / ~"[ຌ-ຣ]" / ~"[ລ]" / ~"[ວ-ະ]" / ~"[ັ]" / ~"[າ-ຳ]" / ~"[ິ-ຼ]" / ~"[ຽ]" / ~"[ເ-ໄ]" / ~"[ໆ]" / ~"[່-ໍ]" / ~"[໐-໙]" / ~"[ໜ-ໟ]" / ~"[ༀ]" / ~"[༘-༙]" / ~"[༠-༩]" / ~"[༵]" / ~"[༷]" / ~"[༹]" / ~"[༾-༿]" / ~"[ཀ-ཇ]" / ~"[ཉ-ཬ]" / ~"[ཱ-ཾ]" / ~"[ཿ]" / ~"[ྀ-྄]" / ~"[྆-྇]" / ~"[ྈ-ྌ]" / ~"[ྍ-ྗ]" / ~"[ྙ-ྼ]" / ~"[࿆]" / ~"[က-ဪ]" / ~"[ါ-ာ]" / ~"[ိ-ူ]" / ~"[ေ]" / ~"[ဲ-့]" / ~"[း]" / ~"[္-်]" / ~"[ျ-ြ]" / ~"[ွ-ှ]" / ~"[ဿ]" / ~"[၀-၉]" / ~"[ၐ-ၕ]" / ~"[ၖ-ၗ]" / ~"[ၘ-ၙ]" / ~"[ၚ-ၝ]" / ~"[ၞ-ၠ]" / ~"[ၡ]" / ~"[ၢ-ၤ]" / ~"[ၥ-ၦ]" / ~"[ၧ-ၭ]" / ~"[ၮ-ၰ]" / ~"[ၱ-ၴ]" / ~"[ၵ-ႁ]" / ~"[ႂ]" / ~"[ႃ-ႄ]" / ~"[ႅ-ႆ]" / ~"[ႇ-ႌ]" / ~"[ႍ]" / ~"[ႎ]" / ~"[ႏ]" / ~"[႐-႙]" / ~"[ႚ-ႜ]" / ~"[ႝ]" / ~"[Ⴀ-Ⴥ]" / ~"[Ⴧ]" / ~"[Ⴭ]" / ~"[ა-ჺ]" / ~"[ჼ]" / ~"[ჽ-ჿ]" / ~"[ᄀ-ቈ]" / ~"[ቊ-ቍ]" / ~"[ቐ-ቖ]" / ~"[ቘ]" / ~"[ቚ-ቝ]" / ~"[በ-ኈ]" / ~"[ኊ-ኍ]" / ~"[ነ-ኰ]" / ~"[ኲ-ኵ]" / ~"[ኸ-ኾ]" / ~"[ዀ]" / ~"[ዂ-ዅ]" / ~"[ወ-ዖ]" / ~"[ዘ-ጐ]" / ~"[ጒ-ጕ]" / ~"[ጘ-ፚ]" / ~"[፝-፟]" / ~"[፩-፱]" / ~"[ᎀ-ᎏ]" / ~"[Ꭰ-Ᏽ]" / ~"[ᏸ-ᏽ]" / ~"[ᐁ-ᙬ]" / ~"[ᙯ-ᙿ]" / ~"[ᚁ-ᚚ]" / ~"[ᚠ-ᛪ]" / ~"[ᛮ-ᛰ]" / ~"[ᛱ-ᛸ]" / ~"[ᜀ-ᜑ]" / ~"[ᜒ-᜔]" / ~"[᜕]" / ~"[ᜟ-ᜱ]" / ~"[ᜲ-ᜳ]" / ~"[᜴]" / ~"[ᝀ-ᝑ]" / ~"[ᝒ-ᝓ]" / ~"[ᝠ-ᝬ]" / ~"[ᝮ-ᝰ]" / ~"[ᝲ-ᝳ]" / ~"[ក-ឳ]" / ~"[឴-឵]" / ~"[ា]" / ~"[ិ-ួ]" / ~"[ើ-ៅ]" / ~"[ំ]" / ~"[ះ-ៈ]" / ~"[៉-៓]" / ~"[ៗ]" / ~"[ៜ]" / ~"[៝]" / ~"[០-៩]" / ~"[᠋-᠍]" / ~"[᠏]" / ~"[᠐-᠙]" / ~"[ᠠ-ᡂ]" / ~"[ᡃ]" / ~"[ᡄ-ᡸ]" / ~"[ᢀ-ᢄ]" / ~"[ᢅ-ᢆ]" / ~"[ᢇ-ᢨ]" / ~"[ᢩ]" / ~"[ᢪ]" / ~"[ᢰ-ᣵ]" / ~"[ᤀ-ᤞ]" / ~"[ᤠ-ᤢ]" / ~"[ᤣ-ᤦ]" / ~"[ᤧ-ᤨ]" / ~"[ᤩ-ᤫ]" / ~"[ᤰ-ᤱ]" / ~"[ᤲ]" / ~"[ᤳ-ᤸ]" / ~"[᤹-᤻]" / ~"[᥆-᥏]" / ~"[ᥐ-ᥭ]" / ~"[ᥰ-ᥴ]" / ~"[ᦀ-ᦫ]" / ~"[ᦰ-ᧉ]" / ~"[᧐-᧙]" / ~"[᧚]" / ~"[ᨀ-ᨖ]" / ~"[ᨗ-ᨘ]" / ~"[ᨙ-ᨚ]" / ~"[ᨛ]" / ~"[ᨠ-ᩔ]" / ~"[ᩕ]" / ~"[ᩖ]" / ~"[ᩗ]" / ~"[ᩘ-ᩞ]" / ~"[᩠]" / ~"[ᩡ]" / ~"[ᩢ]" / ~"[ᩣ-ᩤ]" / ~"[ᩥ-ᩬ]" / ~"[ᩭ-ᩲ]" / ~"[ᩳ-᩼]" / ~"[᩿]" / ~"[᪀-᪉]" / ~"[᪐-᪙]" / ~"[ᪧ]" / ~"[᪰-᪽]" / ~"[ᪿ-ᫎ]" / ~"[ᬀ-ᬃ]" / ~"[ᬄ]" / ~"[ᬅ-ᬳ]" / ~"[᬴]" / ~"[ᬵ]" / ~"[ᬶ-ᬺ]" / ~"[ᬻ]" / ~"[ᬼ]" / ~"[ᬽ-ᭁ]" / ~"[ᭂ]" / ~"[ᭃ-᭄]" / ~"[ᭅ-ᭌ]" / ~"[᭐-᭙]" / ~"[᭫-᭳]" / ~"[ᮀ-ᮁ]" / ~"[ᮂ]" / ~"[ᮃ-ᮠ]" / ~"[ᮡ]" / ~"[ᮢ-ᮥ]" / ~"[ᮦ-ᮧ]" / ~"[ᮨ-ᮩ]" / ~"[᮪]" / ~"[᮫-ᮭ]" / ~"[ᮮ-ᮯ]" / ~"[᮰-᮹]" / ~"[ᮺ-ᯥ]" / ~"[᯦]" / ~"[ᯧ]" / ~"[ᯨ-ᯩ]" / ~"[ᯪ-ᯬ]" / ~"[ᯭ]" / ~"[ᯮ]" / ~"[ᯯ-ᯱ]" / ~"[᯲-᯳]" / ~"[ᰀ-ᰣ]" / ~"[ᰤ-ᰫ]" / ~"[ᰬ-ᰳ]" / ~"[ᰴ-ᰵ]" / ~"[ᰶ-᰷]" / ~"[᱀-᱉]" / ~"[ᱍ-ᱏ]" / ~"[᱐-᱙]" / ~"[ᱚ-ᱷ]" / ~"[ᱸ-ᱽ]" / ~"[ᲀ-ᲈ]" / ~"[Ა-Ჺ]" / ~"[Ჽ-Ჿ]" / ~"[᳐-᳒]" / ~"[᳔-᳠]" / ~"[᳡]" / ~"[᳢-᳨]" / ~"[ᳩ-ᳬ]" / ~"[᳭]" / ~"[ᳮ-ᳳ]" / ~"[᳴]" / ~"[ᳵ-ᳶ]" / ~"[᳷]" / ~"[᳸-᳹]" / ~"[ᳺ]" / ~"[ᴀ-ᴫ]" / ~"[ᴬ-ᵪ]" / ~"[ᵫ-ᵷ]" / ~"[ᵸ]" / ~"[ᵹ-ᶚ]" / ~"[ᶛ-ᶿ]" / ~"[᷀-᷿]" / ~"[Ḁ-ἕ]" / ~"[Ἐ-Ἕ]" / ~"[ἠ-ὅ]" / ~"[Ὀ-Ὅ]" / ~"[ὐ-ὗ]" / ~"[Ὑ]" / ~"[Ὓ]" / ~"[Ὕ]" / ~"[Ὗ-ώ]" / ~"[ᾀ-ᾴ]" / ~"[ᾶ-ᾼ]" / ~"[ι]" / ~"[ῂ-ῄ]" / ~"[ῆ-ῌ]" / ~"[ῐ-ΐ]" / ~"[ῖ-Ί]" / ~"[ῠ-Ῥ]" / ~"[ῲ-ῴ]" / ~"[ῶ-ῼ]" / ~"[‿-⁀]" / ~"[⁔]" / ~"[ⁱ]" / ~"[ⁿ]" / ~"[ₐ-ₜ]" / ~"[⃐-⃜]" / ~"[⃡]" / ~"[⃥-⃰]" / ~"[ℂ]" / ~"[ℇ]" / ~"[ℊ-ℓ]" / ~"[ℕ]" / ~"[℘]" / ~"[ℙ-ℝ]" / ~"[ℤ]" / ~"[Ω]" / ~"[ℨ]" / ~"[K-ℭ]" / ~"[℮]" / ~"[ℯ-ℴ]" / ~"[ℵ-ℸ]" / ~"[ℹ]" / ~"[ℼ-ℿ]" / ~"[ⅅ-ⅉ]" / ~"[ⅎ]" / ~"[Ⅰ-ↂ]" / ~"[Ↄ-ↄ]" / ~"[ↅ-ↈ]" / ~"[Ⰰ-ⱻ]" / ~"[ⱼ-ⱽ]" / ~"[Ȿ-ⳤ]" / ~"[Ⳬ-ⳮ]" / ~"[⳯-⳱]" / ~"[Ⳳ-ⳳ]" / ~"[ⴀ-ⴥ]" / ~"[ⴧ]" / ~"[ⴭ]" / ~"[ⴰ-ⵧ]" / ~"[ⵯ]" / ~"[⵿]" / ~"[ⶀ-ⶖ]" / ~"[ⶠ-ⶦ]" / ~"[ⶨ-ⶮ]" / ~"[ⶰ-ⶶ]" / ~"[ⶸ-ⶾ]" / ~"[ⷀ-ⷆ]" / ~"[ⷈ-ⷎ]" / ~"[ⷐ-ⷖ]" / ~"[ⷘ-ⷞ]" / ~"[ⷠ-ⷿ]" / ~"[々]" / ~"[〆]" / ~"[〇]" / ~"[〡-〩]" / ~"[〪-〭]" / ~"[〮-〯]" / ~"[〱-〵]" / ~"[〸-〺]" / ~"[〻]" / ~"[〼]" / ~"[ぁ-ゖ]" / ~"[゙-゚]" / ~"[ゝ-ゞ]" / ~"[ゟ]" / ~"[ァ-ヺ]" / ~"[ー-ヾ]" / ~"[ヿ]" / ~"[ㄅ-ㄯ]" / ~"[ㄱ-ㆎ]" / ~"[ㆠ-ㆿ]" / ~"[ㇰ-ㇿ]" / ~"[㐀-䶿]" / ~"[一-ꀔ]" / ~"[ꀕ]" / ~"[ꀖ-ꒌ]" / ~"[ꓐ-ꓷ]" / ~"[ꓸ-ꓽ]" / ~"[ꔀ-ꘋ]" / ~"[ꘌ]" / ~"[ꘐ-ꘟ]" / ~"[꘠-꘩]" / ~"[ꘪ-ꘫ]" / ~"[Ꙁ-ꙭ]" / ~"[ꙮ]" / ~"[꙯]" / ~"[ꙴ-꙽]" / ~"[ꙿ]" / ~"[Ꚁ-ꚛ]" / ~"[ꚜ-ꚝ]" / ~"[ꚞ-ꚟ]" / ~"[ꚠ-ꛥ]" / ~"[ꛦ-ꛯ]" / ~"[꛰-꛱]" / ~"[ꜗ-ꜟ]" / ~"[Ꜣ-ꝯ]" / ~"[ꝰ]" / ~"[ꝱ-ꞇ]" / ~"[ꞈ]" / ~"[Ꞌ-ꞎ]" / ~"[ꞏ]" / ~"[Ꞑ-ꟊ]" / ~"[Ꟑ-ꟑ]" / ~"[ꟓ]" / ~"[ꟕ-ꟙ]" / ~"[ꟲ-ꟴ]" / ~"[Ꟶ-ꟶ]" / ~"[ꟷ]" / ~"[ꟸ-ꟹ]" / ~"[ꟺ]" / ~"[ꟻ-ꠁ]" / ~"[ꠂ]" / ~"[ꠃ-ꠅ]" / ~"[꠆]" / ~"[ꠇ-ꠊ]" / ~"[ꠋ]" / ~"[ꠌ-ꠢ]" / ~"[ꠣ-ꠤ]" / ~"[ꠥ-ꠦ]" / ~"[ꠧ]" / ~"[꠬]" / ~"[ꡀ-ꡳ]" / ~"[ꢀ-ꢁ]" / ~"[ꢂ-ꢳ]" / ~"[ꢴ-ꣃ]" / ~"[꣄-ꣅ]" / ~"[꣐-꣙]" / ~"[꣠-꣱]" / ~"[ꣲ-ꣷ]" / ~"[ꣻ]" / ~"[ꣽ-ꣾ]" / ~"[ꣿ]" / ~"[꤀-꤉]" / ~"[ꤊ-ꤥ]" / ~"[ꤦ-꤭]" / ~"[ꤰ-ꥆ]" / ~"[ꥇ-ꥑ]" / ~"[ꥒ-꥓]" / ~"[ꥠ-ꥼ]" / ~"[ꦀ-ꦂ]" / ~"[ꦃ]" / ~"[ꦄ-ꦲ]" / ~"[꦳]" / ~"[ꦴ-ꦵ]" / ~"[ꦶ-ꦹ]" / ~"[ꦺ-ꦻ]" / ~"[ꦼ-ꦽ]" / ~"[ꦾ-꧀]" / ~"[ꧏ]" / ~"[꧐-꧙]" / ~"[ꧠ-ꧤ]" / ~"[ꧥ]" / ~"[ꧦ]" / ~"[ꧧ-ꧯ]" / ~"[꧰-꧹]" / ~"[ꧺ-ꧾ]" / ~"[ꨀ-ꨨ]" / ~"[ꨩ-ꨮ]" / ~"[ꨯ-ꨰ]" / ~"[ꨱ-ꨲ]" / ~"[ꨳ-ꨴ]" / ~"[ꨵ-ꨶ]" / ~"[ꩀ-ꩂ]" / ~"[ꩃ]" / ~"[ꩄ-ꩋ]" / ~"[ꩌ]" / ~"[ꩍ]" / ~"[꩐-꩙]" / ~"[ꩠ-ꩯ]" / ~"[ꩰ]" / ~"[ꩱ-ꩶ]" / ~"[ꩺ]" / ~"[ꩻ]" / ~"[ꩼ]" / ~"[ꩽ]" / ~"[ꩾ-ꪯ]" / ~"[ꪰ]" / ~"[ꪱ]" / ~"[ꪲ-ꪴ]" / ~"[ꪵ-ꪶ]" / ~"[ꪷ-ꪸ]" / ~"[ꪹ-ꪽ]" / ~"[ꪾ-꪿]" / ~"[ꫀ]" / ~"[꫁]" / ~"[ꫂ]" / ~"[ꫛ-ꫜ]" / ~"[ꫝ]" / ~"[ꫠ-ꫪ]" / ~"[ꫫ]" / ~"[ꫬ-ꫭ]" / ~"[ꫮ-ꫯ]" / ~"[ꫲ]" / ~"[ꫳ-ꫴ]" / ~"[ꫵ]" / ~"[꫶]" / ~"[ꬁ-ꬆ]" / ~"[ꬉ-ꬎ]" / ~"[ꬑ-ꬖ]" / ~"[ꬠ-ꬦ]" / ~"[ꬨ-ꬮ]" / ~"[ꬰ-ꭚ]" / ~"[ꭜ-ꭟ]" / ~"[ꭠ-ꭨ]" / ~"[ꭩ]" / ~"[ꭰ-ꮿ]" / ~"[ꯀ-ꯢ]" / ~"[ꯣ-ꯤ]" / ~"[ꯥ]" / ~"[ꯦ-ꯧ]" / ~"[ꯨ]" / ~"[ꯩ-ꯪ]" / ~"[꯬]" / ~"[꯭]" / ~"[꯰-꯹]" / ~"[가-힣]" / ~"[ힰ-ퟆ]" / ~"[ퟋ-ퟻ]" / ~"[豈-舘]" / ~"[並-龎]" / ~"[ﬀ-ﬆ]" / ~"[ﬓ-ﬗ]" / ~"[יִ]" / ~"[ﬞ]" / ~"[ײַ-ﬨ]" / ~"[שׁ-זּ]" / ~"[טּ-לּ]" / ~"[מּ]" / ~"[נּ-סּ]" / ~"[ףּ-פּ]" / ~"[צּ-ﮱ]" / ~"[ﯓ-ﱝ]" / ~"[ﱤ-ﴽ]" / ~"[ﵐ-ﶏ]" / ~"[ﶒ-ﷇ]" / ~"[ﷰ-ﷹ]" / ~"[︀-️]" / ~"[︠-︯]" / ~"[︳-︴]" / ~"[﹍-﹏]" / ~"[ﹱ]" / ~"[ﹳ]" / ~"[ﹷ]" / ~"[ﹹ]" / ~"[ﹻ]" / ~"[ﹽ]" / ~"[ﹿ-ﻼ]" / ~"[０-９]" / ~"[Ａ-Ｚ]" / ~"[＿]" / ~"[ａ-ｚ]" / ~"[ｦ-ｯ]" / ~"[ｰ]" / ~"[ｱ-ﾝ]" / ~"[ﾞ-ﾟ]" / ~"[ﾠ-ﾾ]" / ~"[ￂ-ￇ]" / ~"[ￊ-ￏ]" / ~"[ￒ-ￗ]" / ~"[ￚ-ￜ]" / ~"[𐀀-𐀋]" / ~"[𐀍-𐀦]" / ~"[𐀨-𐀺]" / ~"[𐀼-𐀽]" / ~"[𐀿-𐁍]" / ~"[𐁐-𐁝]" / ~"[𐂀-𐃺]" / ~"[𐅀-𐅴]" / ~"[𐇽]" / ~"[𐊀-𐊜]" / ~"[𐊠-𐋐]" / ~"[𐋠]" / ~"[𐌀-𐌟]" / ~"[𐌭-𐍀]" / ~"[𐍁]" / ~"[𐍂-𐍉]" / ~"[𐍊]" / ~"[𐍐-𐍵]" / ~"[𐍶-𐍺]" / ~"[𐎀-𐎝]" / ~"[𐎠-𐏃]" / ~"[𐏈-𐏏]" / ~"[𐏑-𐏕]" / ~"[𐐀-𐑏]" / ~"[𐑐-𐒝]" / ~"[𐒠-𐒩]" / ~"[𐒰-𐓓]" / ~"[𐓘-𐓻]" / ~"[𐔀-𐔧]" / ~"[𐔰-𐕣]" / ~"[𐕰-𐕺]" / ~"[𐕼-𐖊]" / ~"[𐖌-𐖒]" / ~"[𐖔-𐖕]" / ~"[𐖗-𐖡]" / ~"[𐖣-𐖱]" / ~"[𐖳-𐖹]" / ~"[𐖻-𐖼]" / ~"[𐘀-𐜶]" / ~"[𐝀-𐝕]" / ~"[𐝠-𐝧]" / ~"[𐞀-𐞅]" / ~"[𐞇-𐞰]" / ~"[𐞲-𐞺]" / ~"[𐠀-𐠅]" / ~"[𐠈]" / ~"[𐠊-𐠵]" / ~"[𐠷-𐠸]" / ~"[𐠼]" / ~"[𐠿-𐡕]" / ~"[𐡠-𐡶]" / ~"[𐢀-𐢞]" / ~"[𐣠-𐣲]" / ~"[𐣴-𐣵]" / ~"[𐤀-𐤕]" / ~"[𐤠-𐤹]" / ~"[𐦀-𐦷]" / ~"[𐦾-𐦿]" / ~"[𐨀]" / ~"[𐨁-𐨃]" / ~"[𐨅-𐨆]" / ~"[𐨌-𐨏]" / ~"[𐨐-𐨓]" / ~"[𐨕-𐨗]" / ~"[𐨙-𐨵]" / ~"[𐨸-𐨺]" / ~"[𐨿]" / ~"[𐩠-𐩼]" / ~"[𐪀-𐪜]" / ~"[𐫀-𐫇]" / ~"[𐫉-𐫤]" / ~"[𐫥-𐫦]" / ~"[𐬀-𐬵]" / ~"[𐭀-𐭕]" / ~"[𐭠-𐭲]" / ~"[𐮀-𐮑]" / ~"[𐰀-𐱈]" / ~"[𐲀-𐲲]" / ~"[𐳀-𐳲]" / ~"[𐴀-𐴣]" / ~"[𐴤-𐴧]" / ~"[𐴰-𐴹]" / ~"[𐺀-𐺩]" / ~"[𐺫-𐺬]" / ~"[𐺰-𐺱]" / ~"[𐼀-𐼜]" / ~"[𐼧]" / ~"[𐼰-𐽅]" / ~"[𐽆-𐽐]" / ~"[𐽰-𐾁]" / ~"[𐾂-𐾅]" / ~"[𐾰-𐿄]" / ~"[𐿠-𐿶]" / ~"[𑀀]" / ~"[𑀁]" / ~"[𑀂]" / ~"[𑀃-𑀷]" / ~"[𑀸-𑁆]" / ~"[𑁦-𑁯]" / ~"[𑁰]" / ~"[𑁱-𑁲]" / ~"[𑁳-𑁴]" / ~"[𑁵]" / ~"[𑁿-𑂁]" / ~"[𑂂]" / ~"[𑂃-𑂯]" / ~"[𑂰-𑂲]" / ~"[𑂳-𑂶]" / ~"[𑂷-𑂸]" / ~"[𑂹-𑂺]" / ~"[𑃂]" / ~"[𑃐-𑃨]" / ~"[𑃰-𑃹]" / ~"[𑄀-𑄂]" / ~"[𑄃-𑄦]" / ~"[𑄧-𑄫]" / ~"[𑄬]" / ~"[𑄭-𑄴]" / ~"[𑄶-𑄿]" / ~"[𑅄]" / ~"[𑅅-𑅆]" / ~"[𑅇]" / ~"[𑅐-𑅲]" / ~"[𑅳]" / ~"[𑅶]" / ~"[𑆀-𑆁]" / ~"[𑆂]" / ~"[𑆃-𑆲]" / ~"[𑆳-𑆵]" / ~"[𑆶-𑆾]" / ~"[𑆿-𑇀]" / ~"[𑇁-𑇄]" / ~"[𑇉-𑇌]" / ~"[𑇎]" / ~"[𑇏]" / ~"[𑇐-𑇙]" / ~"[𑇚]" / ~"[𑇜]" / ~"[𑈀-𑈑]" / ~"[𑈓-𑈫]" / ~"[𑈬-𑈮]" / ~"[𑈯-𑈱]" / ~"[𑈲-𑈳]" / ~"[𑈴]" / ~"[𑈵]" / ~"[𑈶-𑈷]" / ~"[𑈾]" / ~"[𑊀-𑊆]" / ~"[𑊈]" / ~"[𑊊-𑊍]" / ~"[𑊏-𑊝]" / ~"[𑊟-𑊨]" / ~"[𑊰-𑋞]" / ~"[𑋟]" / ~"[𑋠-𑋢]" / ~"[𑋣-𑋪]" / ~"[𑋰-𑋹]" / ~"[𑌀-𑌁]" / ~"[𑌂-𑌃]" / ~"[𑌅-𑌌]" / ~"[𑌏-𑌐]" / ~"[𑌓-𑌨]" / ~"[𑌪-𑌰]" / ~"[𑌲-𑌳]" / ~"[𑌵-𑌹]" / ~"[𑌻-𑌼]" / ~"[𑌽]" / ~"[𑌾-𑌿]" / ~"[𑍀]" / ~"[𑍁-𑍄]" / ~"[𑍇-𑍈]" / ~"[𑍋-𑍍]" / ~"[𑍐]" / ~"[𑍗]" / ~"[𑍝-𑍡]" / ~"[𑍢-𑍣]" / ~"[𑍦-𑍬]" / ~"[𑍰-𑍴]" / ~"[𑐀-𑐴]" / ~"[𑐵-𑐷]" / ~"[𑐸-𑐿]" / ~"[𑑀-𑑁]" / ~"[𑑂-𑑄]" / ~"[𑑅]" / ~"[𑑆]" / ~"[𑑇-𑑊]" / ~"[𑑐-𑑙]" / ~"[𑑞]" / ~"[𑑟-𑑡]" / ~"[𑒀-𑒯]" / ~"[𑒰-𑒲]" / ~"[𑒳-𑒸]" / ~"[𑒹]" / ~"[𑒺]" / ~"[𑒻-𑒾]" / ~"[𑒿-𑓀]" / ~"[𑓁]" / ~"[𑓂-𑓃]" / ~"[𑓄-𑓅]" / ~"[𑓇]" / ~"[𑓐-𑓙]" / ~"[𑖀-𑖮]" / ~"[𑖯-𑖱]" / ~"[𑖲-𑖵]" / ~"[𑖸-𑖻]" / ~"[𑖼-𑖽]" / ~"[𑖾]" / ~"[𑖿-𑗀]" / ~"[𑗘-𑗛]" / ~"[𑗜-𑗝]" / ~"[𑘀-𑘯]" / ~"[𑘰-𑘲]" / ~"[𑘳-𑘺]" / ~"[𑘻-𑘼]" / ~"[𑘽]" / ~"[𑘾]" / ~"[𑘿-𑙀]" / ~"[𑙄]" / ~"[𑙐-𑙙]" / ~"[𑚀-𑚪]" / ~"[𑚫]" / ~"[𑚬]" / ~"[𑚭]" / ~"[𑚮-𑚯]" / ~"[𑚰-𑚵]" / ~"[𑚶]" / ~"[𑚷]" / ~"[𑚸]" / ~"[𑛀-𑛉]" / ~"[𑜀-𑜚]" / ~"[𑜝-𑜟]" / ~"[𑜠-𑜡]" / ~"[𑜢-𑜥]" / ~"[𑜦]" / ~"[𑜧-𑜫]" / ~"[𑜰-𑜹]" / ~"[𑝀-𑝆]" / ~"[𑠀-𑠫]" / ~"[𑠬-𑠮]" / ~"[𑠯-𑠷]" / ~"[𑠸]" / ~"[𑠹-𑠺]" / ~"[𑢠-𑣟]" / ~"[𑣠-𑣩]" / ~"[𑣿-𑤆]" / ~"[𑤉]" / ~"[𑤌-𑤓]" / ~"[𑤕-𑤖]" / ~"[𑤘-𑤯]" / ~"[𑤰-𑤵]" / ~"[𑤷-𑤸]" / ~"[𑤻-𑤼]" / ~"[𑤽]" / ~"[𑤾]" / ~"[𑤿]" / ~"[𑥀]" / ~"[𑥁]" / ~"[𑥂]" / ~"[𑥃]" / ~"[𑥐-𑥙]" / ~"[𑦠-𑦧]" / ~"[𑦪-𑧐]" / ~"[𑧑-𑧓]" / ~"[𑧔-𑧗]" / ~"[𑧚-𑧛]" / ~"[𑧜-𑧟]" / ~"[𑧠]" / ~"[𑧡]" / ~"[𑧣]" / ~"[𑧤]" / ~"[𑨀]" / ~"[𑨁-𑨊]" / ~"[𑨋-𑨲]" / ~"[𑨳-𑨸]" / ~"[𑨹]" / ~"[𑨺]" / ~"[𑨻-𑨾]" / ~"[𑩇]" / ~"[𑩐]" / ~"[𑩑-𑩖]" / ~"[𑩗-𑩘]" / ~"[𑩙-𑩛]" / ~"[𑩜-𑪉]" / ~"[𑪊-𑪖]" / ~"[𑪗]" / ~"[𑪘-𑪙]" / ~"[𑪝]" / ~"[𑪰-𑫸]" / ~"[𑰀-𑰈]" / ~"[𑰊-𑰮]" / ~"[𑰯]" / ~"[𑰰-𑰶]" / ~"[𑰸-𑰽]" / ~"[𑰾]" / ~"[𑰿]" / ~"[𑱀]" / ~"[𑱐-𑱙]" / ~"[𑱲-𑲏]" / ~"[𑲒-𑲧]" / ~"[𑲩]" / ~"[𑲪-𑲰]" / ~"[𑲱]" / ~"[𑲲-𑲳]" / ~"[𑲴]" / ~"[𑲵-𑲶]" / ~"[𑴀-𑴆]" / ~"[𑴈-𑴉]" / ~"[𑴋-𑴰]" / ~"[𑴱-𑴶]" / ~"[𑴺]" / ~"[𑴼-𑴽]" / ~"[𑴿-𑵅]" / ~"[𑵆]" / ~"[𑵇]" / ~"[𑵐-𑵙]" / ~"[𑵠-𑵥]" / ~"[𑵧-𑵨]" / ~"[𑵪-𑶉]" / ~"[𑶊-𑶎]" / ~"[𑶐-𑶑]" / ~"[𑶓-𑶔]" / ~"[𑶕]" / ~"[𑶖]" / ~"[𑶗]" / ~"[𑶘]" / ~"[𑶠-𑶩]" / ~"[𑻠-𑻲]" / ~"[𑻳-𑻴]" / ~"[𑻵-𑻶]" / ~"[𑾰]" / ~"[𒀀-𒎙]" / ~"[𒐀-𒑮]" / ~"[𒒀-𒕃]" / ~"[𒾐-𒿰]" / ~"[𓀀-𓐮]" / ~"[𔐀-𔙆]" / ~"[𖠀-𖨸]" / ~"[𖩀-𖩞]" / ~"[𖩠-𖩩]" / ~"[𖩰-𖪾]" / ~"[𖫀-𖫉]" / ~"[𖫐-𖫭]" / ~"[𖫰-𖫴]" / ~"[𖬀-𖬯]" / ~"[𖬰-𖬶]" / ~"[𖭀-𖭃]" / ~"[𖭐-𖭙]" / ~"[𖭣-𖭷]" / ~"[𖭽-𖮏]" / ~"[𖹀-𖹿]" / ~"[𖼀-𖽊]" / ~"[𖽏]" / ~"[𖽐]" / ~"[𖽑-𖾇]" / ~"[𖾏-𖾒]" / ~"[𖾓-𖾟]" / ~"[𖿠-𖿡]" / ~"[𖿣]" / ~"[𖿤]" / ~"[𖿰-𖿱]" / ~"[𗀀-𘟷]" / ~"[𘠀-𘳕]" / ~"[𘴀-𘴈]" / ~"[𚿰-𚿳]" / ~"[𚿵-𚿻]" / ~"[𚿽-𚿾]" / ~"[𛀀-𛄢]" / ~"[𛅐-𛅒]" / ~"[𛅤-𛅧]" / ~"[𛅰-𛋻]" / ~"[𛰀-𛱪]" / ~"[𛱰-𛱼]" / ~"[𛲀-𛲈]" / ~"[𛲐-𛲙]" / ~"[𛲝-𛲞]" / ~"[𜼀-𜼭]" / ~"[𜼰-𜽆]" / ~"[𝅥-𝅦]" / ~"[𝅧-𝅩]" / ~"[𝅭-𝅲]" / ~"[𝅻-𝆂]" / ~"[𝆅-𝆋]" / ~"[𝆪-𝆭]" / ~"[𝉂-𝉄]" / ~"[𝐀-𝑔]" / ~"[𝑖-𝒜]" / ~"[𝒞-𝒟]" / ~"[𝒢]" / ~"[𝒥-𝒦]" / ~"[𝒩-𝒬]" / ~"[𝒮-𝒹]" / ~"[𝒻]" / ~"[𝒽-𝓃]" / ~"[𝓅-𝔅]" / ~"[𝔇-𝔊]" / ~"[𝔍-𝔔]" / ~"[𝔖-𝔜]" / ~"[𝔞-𝔹]" / ~"[𝔻-𝔾]" / ~"[𝕀-𝕄]" / ~"[𝕆]" / ~"[𝕊-𝕐]" / ~"[𝕒-𝚥]" / ~"[𝚨-𝛀]" / ~"[𝛂-𝛚]" / ~"[𝛜-𝛺]" / ~"[𝛼-𝜔]" / ~"[𝜖-𝜴]" / ~"[𝜶-𝝎]" / ~"[𝝐-𝝮]" / ~"[𝝰-𝞈]" / ~"[𝞊-𝞨]" / ~"[𝞪-𝟂]" / ~"[𝟄-𝟋]" / ~"[𝟎-𝟿]" / ~"[𝨀-𝨶]" / ~"[𝨻-𝩬]" / ~"[𝩵]" / ~"[𝪄]" / ~"[𝪛-𝪟]" / ~"[𝪡-𝪯]" / ~"[𝼀-𝼉]" / ~"[𝼊]" / ~"[𝼋-𝼞]" / ~"[𞀀-𞀆]" / ~"[𞀈-𞀘]" / ~"[𞀛-𞀡]" / ~"[𞀣-𞀤]" / ~"[𞀦-𞀪]" / ~"[𞄀-𞄬]" / ~"[𞄰-𞄶]" / ~"[𞄷-𞄽]" / ~"[𞅀-𞅉]" / ~"[𞅎]" / ~"[𞊐-𞊭]" / ~"[𞊮]" / ~"[𞋀-𞋫]" / ~"[𞋬-𞋯]" / ~"[𞋰-𞋹]" / ~"[𞟠-𞟦]" / ~"[𞟨-𞟫]" / ~"[𞟭-𞟮]" / ~"[𞟰-𞟾]" / ~"[𞠀-𞣄]" / ~"[𞣐-𞣖]" / ~"[𞤀-𞥃]" / ~"[𞥄-𞥊]" / ~"[𞥋]" / ~"[𞥐-𞥙]" / ~"[𞸀-𞸃]" / ~"[𞸅-𞸟]" / ~"[𞸡-𞸢]" / ~"[𞸤]" / ~"[𞸧]" / ~"[𞸩-𞸲]" / ~"[𞸴-𞸷]" / ~"[𞸹]" / ~"[𞸻]" / ~"[𞹂]" / ~"[𞹇]" / ~"[𞹉]" / ~"[𞹋]" / ~"[𞹍-𞹏]" / ~"[𞹑-𞹒]" / ~"[𞹔]" / ~"[𞹗]" / ~"[𞹙]" / ~"[𞹛]" / ~"[𞹝]" / ~"[𞹟]" / ~"[𞹡-𞹢]" / ~"[𞹤]" / ~"[𞹧-𞹪]" / ~"[𞹬-𞹲]" / ~"[𞹴-𞹷]" / ~"[𞹹-𞹼]" / ~"[𞹾]" / ~"[𞺀-𞺉]" / ~"[𞺋-𞺛]" / ~"[𞺡-𞺣]" / ~"[𞺥-𞺩]" / ~"[𞺫-𞺻]" / ~"[🯰-🯹]" / ~"[𠀀-𪛟]" / ~"[𪜀-𫜸]" / ~"[𫝀-𫠝]" / ~"[𫠠-𬺡]" / ~"[𬺰-𮯠]" / ~"[丽-𪘀]" / ~"[𰀀-𱍊]" / ~"[󠄀-󠇯]"
    asciistart = ~"[A-Z]" / ~"[a-z]" / ~"[_]"
    asciicontinue = ~"[A-Z]" / ~"[a-z]" / ~"[_]" / ~"[0-9]"
    baseidentifier = xidstart (xidcontinue)*
    keywordlessidentifier = !(keyword !(xidstart / xidcontinue)) baseidentifier
    identifier = keywordlessidentifier
    namespacedname = baseidentifier (colon baseidentifier)*
    primname = identifier
    variantsetname = identifier
    variantname = (dot (xidcontinue / verticalbar / minus)*) / (xidcontinue / verticalbar / minus)+
    variantselection = leftcurlybrace (space)? variantsetname assignment (variantname)? (space)? rightcurlybrace
    variantselections = (variantselection)+
    primelements = (primname (&(slash primname) slash primname)* (variantselections)?) / (primname (&(variantselections primname) variantselections primname)* (variantselections)?)
    propertyname = identifier (colon identifier)*
    propelements = dot propertyname
    pathelements = (primelements (propelements)*) / (!(primelements) propelements)
    primfirstpathelements = primelements (propelements)?
    path = (slash (primfirstpathelements)?) / (dot dot (slash pathelements)?) / pathelements / dot
    pathref = leftanglebracket path? rightanglebracket
    assetrefcharacter = !(at) noncrlfutf8character
    tripleassetrefcharacter = !(at at at) noncrlfutf8character
    assetref = (at at at (tripleassetrefcharacter)* (!(at at at) at at)? at at at) / (at (assetrefcharacter)* at)
    layeroffset = (keywordoffset / keywordscale) assignment number
    atomicvalue = number / identifier / string / assetref
    tupleitem = atomicvalue / tuplevalue
    tuplevalue = leftparen (multilinepadding)* tuplecontents (multilinepadding)* rightparen
    tuplecontents = tupleitem ((inlinepadding)* listseparator (multilinepadding)* tupleitem)* (inlinepadding)* (listseparator (multilinepadding)*)?
    listitem = atomicvalue / listvalue / tuplevalue
    listvalue = leftbracket (multilinepadding)* listcontents (multilinepadding)* rightbracket
    listcontents = listitem ((inlinepadding)* listseparator (multilinepadding)* listitem)* (inlinepadding)* (listseparator (multilinepadding)*)?
    arraytype = leftbracket (inlinepadding)* rightbracket
    arraytypevalue = leftbracket (inlinepadding)* rightbracket
    typedvalue = atomicvalue / tuplevalue / arraytypevalue / listvalue / pathref
    dictionarykey = string / baseidentifier
    dictionarytype = identifier ((inlinepadding)* arraytype)?
    dictionaryvalueitem = (keyworddictionary (inlinepadding)+ dictionarykey assignment dictionaryvalue) / (dictionarytype (inlinepadding)+ dictionarykey assignment typedvalue)
    dictionaryvalue = leftcurlybrace (multilinepadding)* (dictionarycontents (multilinepadding)*)? rightcurlybrace
    dictionarycontents = dictionaryvalueitem ((singlelinepadding)* statementseparator (multilinepadding)* dictionaryvalueitem)* (singlelinepadding)* (statementseparator (multilinepadding)*)?
    stringdictionaryitem = string (inlinepadding)* colon (inlinepadding)* string
    stringdictionary = leftcurlybrace (multilinepadding)* (stringdictionarycontents (multilinepadding)*)? rightcurlybrace
    stringdictionarycontents = stringdictionaryitem ((singlelinepadding)* statementseparator (multilinepadding)* stringdictionaryitem)* (singlelinepadding)* (statementseparator (multilinepadding)*)?
    namelistcontents = string ((inlinepadding)* listseparator (multilinepadding)* string)* (inlinepadding)* (listseparator (multilinepadding)*)?
    namelist = string / (leftbracket (multilinepadding)* namelistcontents (multilinepadding)? rightbracket)
    timesample = number (inlinepadding)* colon (inlinepadding)* (keywordbignone / typedvalue)
    timesamplemap = leftcurlybrace (multilinepadding)* (timesamplemapcontents (multilinepadding)*)? rightcurlybrace
    timesamplemapcontents = timesample ((inlinepadding)* listseparator (multilinepadding)* timesample)* (inlinepadding)* (listseparator (multilinepadding)*)?
    splinecurvetypeitem = keywordbezier / keywordhermite
    splineextrapolationitem = (keywordpre (inlinepadding)* colon (inlinepadding)* splineextrapolation) / (keywordpost (inlinepadding)* colon (inlinepadding)* splineextrapolation)
    loopoption = keywordrepeat / keywordreset / keywordoscillate
    splineextrapolation = keywordnone / keywordheld / keywordlinear / (keywordsloped (inlinepadding)+ leftparen (inlinepadding)* number (inlinepadding)* rightparen) / (keywordloop (inlinepadding)+ loopoption)
    splineloopitem = keywordloop (inlinepadding)* colon (inlinepadding)* leftparen (inlinepadding)* number (inlinepadding)* comma (inlinepadding)* number (inlinepadding)* comma (inlinepadding)* number (inlinepadding)* comma (inlinepadding)* number (inlinepadding)* comma (inlinepadding)* number (inlinepadding)* rightparen
    splineknotitem = number (inlinepadding)* colon (inlinepadding)* splineknotvalues (inlinepadding)* (splineknotparameters)*
    splineknotvalues = (number (inlinepadding)* ampersand (inlinepadding)* number) / number
    splineknotparameters = semicolon (inlinepadding)* splineknotparameterlist
    splineknotparameterlist = splineknotparameter ((inlinepadding)* semicolon (inlinepadding)* splineknotparameter)*
    splineknotparameter = (keywordpre (inlinepadding)+ splinetangent) / (keywordpost (inlinepadding)+ splineinterpmode ((inlinepadding)+ splinetangent)?) / dictionaryvalue
    splineinterpmode = keywordnone / keywordheld / keywordlinear / keywordcurve
    splinetangent = leftparen (inlinepadding)* splinetangentcontent (inlinepadding)* rightparen
    splinetangentcontent = (number (inlinepadding)* comma (inlinepadding)* number) / number
    splineitem = splinecurvetypeitem / splineextrapolationitem / splineloopitem / splineknotitem
    splinemapcontents = splineitem ((inlinepadding)* listseparator (multilinepadding)* splineitem)* (inlinepadding)* (listseparator (multilinepadding)*)?
    splinemap = leftcurlybrace (multilinepadding)* (splinemapcontents (multilinepadding)*)? rightcurlybrace
    metadatavalue = keywordbignone / dictionaryvalue / typedvalue
    keyvaluemetadata = (identifier / keywordcustomdata) assignment metadatavalue
    docmetadata = keyworddoc assignment string
    listop = keyworddelete / keywordappend / keywordprepend
    listopvalue = keywordbignone / listvalue
    listopmetadata = listop (inlinepadding)+ identifier assignment listopvalue
    sharedmetadata = string / keyvaluemetadata / docmetadata
    attributemetadataitem = sharedmetadata / listopmetadata
    attributemetadata = leftparen (multilinepadding)* (attributemetadatacontents (multilinepadding)*)? rightparen
    attributemetadatacontents = attributemetadataitem ((singlelinepadding)* statementseparator (multilinepadding)* attributemetadataitem)* (singlelinepadding)* (statementseparator (multilinepadding)*)?
    attributevariability = keyworduniform
    attributetype = (attributevariability (inlinepadding)+)? identifier ((inlinepadding)* arraytype)?
    attributecustomdeclaration = keywordcustom (inlinepadding)+
    attributedeclaration = (attributecustomdeclaration)? attributetype (inlinepadding)+ namespacedname
    attributeassignment = (assignment keywordbignone) / (assignment typedvalue)
    attributemetadatablock = attributemetadata (inlinepadding)*
    connectvalue = keywordbignone / pathref / (leftbracket (multilinepadding)* (connectvaluecontents (multilinepadding)*)? rightbracket)
    connectvaluecontents = pathref ((inlinepadding)* listseparator (multilinepadding)* pathref)* (inlinepadding)* (listseparator (multilinepadding)*)?
    specialattributetype = (keywordtimesamples assignment timesamplemap) / (keywordconnect assignment connectvalue) / (keywordspline assignment splinemap)
    listopconnect = listop (inlinepadding)+ attributedeclaration (inlinepadding)* dot (inlinepadding)* keywordconnect assignment connectvalue
    regularattribute = attributedeclaration (attributeassignment)? (inlinepadding)* (attributemetadatablock)?
    specialattribute = (attributedeclaration (inlinepadding)* dot (inlinepadding)* specialattributetype)
    attributespec = specialattribute / listopconnect / regularattribute
    relationshipmetadataitem = sharedmetadata / listopmetadata
    relationshipmetadatacontents = relationshipmetadataitem ((singlelinepadding)* statementseparator (multilinepadding)* relationshipmetadataitem)* (singlelinepadding)* (statementseparator (multilinepadding)*)?
    relationshipmetadata = leftparen (multilinepadding)* (relationshipmetadatacontents (multilinepadding)*)? rightparen
    relationshiptype = keywordrel / (keywordcustom (inlinepadding)+ keywordrel)
    pathreflistcontents = pathref ((inlinepadding)* listseparator (multilinepadding)* pathref)* (inlinepadding)* (listseparator (multilinepadding)*)?
    relationshipassignment = (assignment keywordbignone) / (assignment pathref) / (assignment leftbracket (multilinepadding)* (pathreflistcontents (multilinepadding)*)? rightbracket)
    listoprelationship = listop (inlinepadding)+ relationshiptype (inlinepadding)+ namespacedname (relationshipassignment)?
    relationshippathref = relationshiptype (inlinepadding)+ namespacedname (inlinepadding)? leftbracket (inlinepadding)* pathref (inlinepadding)* rightbracket
    relationshipstandard = relationshiptype (inlinepadding)+ namespacedname (relationshipassignment)? (inlinepadding)* (relationshipmetadata)?
    relationshipspec = relationshipstandard / relationshippathref / listoprelationship
    inheritsorspecializeslist = (keywordbignone) / (pathref) / (leftbracket (multilinepadding)* (pathreflistcontents (multilinepadding)*)? rightbracket)
    specializesmetadata = (listop (inlinepadding)+)? keywordspecializes assignment inheritsorspecializeslist
    inheritsmetadata = (listop (inlinepadding)+)? keywordinherits assignment inheritsorspecializeslist
    referenceparameter = (keywordcustomdata assignment dictionaryvalue) / (layeroffset)
    referenceparameterscontent = referenceparameter ((singlelinepadding)* statementseparator (multilinepadding)* referenceparameter)* (singlelinepadding)* (statementseparator (multilinepadding)*)?
    referenceparameters = leftparen (multilinepadding)* (referenceparameterscontent (multilinepadding)*)? rightparen
    referencelistitem = (assetref (inlinepadding)* (pathref)? (inlinepadding)* (referenceparameters)?) / (pathref (inlinepadding)* (referenceparameters)?)
    referencelistcontents = referencelistitem ((inlinepadding)* listseparator (multilinepadding)* referencelistitem)* (inlinepadding)* (listseparator (multilinepadding)*)?
    referencelist = (keywordbignone) / (referencelistitem) / (leftbracket (multilinepadding)* (referencelistcontents (multilinepadding)*)? rightbracket)
    referencesmetadata = (listop (inlinepadding)+)? keywordreferences assignment referencelist
    payloadparameterscontent = layeroffset ((singlelinepadding)* statementseparator (multilinepadding)* layeroffset)* (singlelinepadding)* (statementseparator (multilinepadding)*)?
    payloadparameters = leftparen (multilinepadding)* (payloadparameterscontent (multilinepadding)*)? rightparen
    payloadlistitem = (assetref (inlinepadding)* (pathref)? (inlinepadding)* (payloadparameters)?) / (pathref (inlinepadding)* (payloadparameters)?)
    payloadlistcontents = payloadlistitem ((inlinepadding)* listseparator (multilinepadding)* payloadlistitem)* (inlinepadding)* (listseparator (multilinepadding)*)?
    payloadlist = (keywordbignone) / (payloadlistitem) / (leftbracket (multilinepadding)* (payloadlistcontents (multilinepadding)*)? rightbracket)
    payloadmetadata = (listop (inlinepadding)+)? keywordpayload assignment payloadlist
    relocatesitem = pathref (inlinepadding)* colon (inlinepadding)* pathref
    relocatesmetadatacontent = relocatesitem ((inlinepadding)* listseparator (multilinepadding)* relocatesitem)* (inlinepadding)* (listseparator (multilinepadding)*)?
    relocatesmetadata = keywordrelocates assignment leftcurlybrace (multilinepadding)* (relocatesmetadatacontent (multilinepadding)*)? rightcurlybrace
    variantsmetadata = keywordvariants assignment dictionaryvalue
    variantsetsmetadata = (listop (inlinepadding)+)? keywordvariantsets assignment namelist
    kindmetadata = keywordkind assignment string
    primmetadataitem = sharedmetadata / listopmetadata / kindmetadata / payloadmetadata / inheritsmetadata / specializesmetadata/ referencesmetadata / relocatesmetadata / variantsmetadata / variantsetsmetadata
    primmetadatacontents = primmetadataitem ((singlelinepadding)* statementseparator (multilinepadding)* primmetadataitem)* (singlelinepadding)* (statementseparator (multilinepadding)*)?
    primmetadata = leftparen (multilinepadding)* (primmetadatacontents (multilinepadding)*)? rightparen
    propertyspec = attributespec / relationshipspec
    childorpropertyorderstatement = (keywordreorder (inlinepadding)+ keywordnamechildren assignment namelist) / (keywordreorder (inlinepadding)+ keywordproperties assignment namelist)
    primtypename = asciistart (asciicontinue)*
    variantstatement = string (multilinepadding)* (primmetadata (multilinepadding)*)? leftcurlybrace primcontents rightcurlybrace
    variantsetstatement = keywordvariantset (inlinepadding)+ string assignment (multilinepadding)* leftcurlybrace ((multilinepadding)* variantstatement (multilinepadding)*)+ rightcurlybrace
    primitem = (childorpropertyorderstatement (singlelinepadding)* statementseparator) / (propertyspec (singlelinepadding)* statementseparator) / (primspec (singlelinepadding)* crlf) / (variantsetstatement (singlelinepadding)* crlf)
    primcontents = (multilinepadding)* (primitem (multilinepadding)*)*
    primspecifier = keyworddef / keywordover / keywordclass
    primdeclaration = primspecifier (inlinepadding)+ (primtypename (inlinepadding)+)? string
    primspec = primdeclaration (multilinepadding)* (primmetadata (multilinepadding)*)? leftcurlybrace primcontents rightcurlybrace
    layeroffsetlist = layeroffset ((singlelinepadding)* statementseparator (multilinepadding)* layeroffset)* (singlelinepadding)* (statementseparator (multilinepadding)*)?
    sublayeritem = assetref (inlinepadding)* (leftparen (multilinepadding)* (layeroffsetlist (multilinepadding)*)? rightparen)?
    sublayermetadatacontents = sublayeritem ((inlinepadding)* listseparator (multilinepadding)* sublayeritem)* (inlinepadding)* (listseparator (multilinepadding)*)?
    sublayermetadata = keywordsublayers assignment leftbracket (multilinepadding)* (sublayermetadatacontents (multilinepadding)*)? rightbracket
    layeritem = (keywordreorder (inlinepadding)+ keywordrootprims assignment namelist) / primspec
    layermetadataitem = sharedmetadata / listopmetadata / sublayermetadata / relocatesmetadata
    layermetadatacontents = layermetadataitem ((singlelinepadding)* statementseparator (multilinepadding)* layermetadataitem)* (singlelinepadding)* (statementseparator (multilinepadding)*)?
    layermetadata = leftparen (multilinepadding)* (layermetadatacontents (multilinepadding)*)? rightparen
    layerheader = pound "usda" (inlinepadding)* (digit)+ dot (digit)+ (dot (digit)+)?
    layerspec = layerheader (multilinepadding)* (layermetadata (multilinepadding)*)? (layeritem (multilinepadding)*)*
    """
)


class UsdaVisitor(NodeVisitor):
    def __init__(self):
        """
        Initializes the visitor.
        """
        self._format = TextFormat()
        self._prim_paths = []

    def _process_listop_redefinition(self, listop1: listop.ListOp, listop2: listop.ListOp) -> listop.ListOp:
        """
        Processes the partial listop operations that were parsed for a spec.
        Each listop operation results in a new listop.  These are combined as
        follows:
        1. The final listop can be explicit or composeable, but not both
        2. If the final listop parsed for the spec is explicit, the final
           listop for the spec will be explicit and all composeable operations
           up to that point are discarded.
        3. If a new version of a specific composeable operation (e.g., append,
           prepend, delete) is detected, it overrides the previous.
        4. Composeable operations combine with each other, but are all discarded
           upon seeing an explicit operation.  If a composeable operation is
           encountered after seeing an explicit operation, the explicit operation
           is discarded in favor of the new composeable.
        """
        if not listop2 and (
            len(listop2.appended_items) == 0 and len(listop2.deleted_items) == 0 and len(listop2.prepended_items) == 0
        ):
            # this is an inert explicit operation
            return listop.ListOp()
        if listop2.is_explicit:
            # this is an explicit operation, everything previously
            # is discarded
            return listop.ListOp(explicit_items=listop2.explicit_items)
        elif len(listop2.appended_items) > 0:
            # this throws away any explicit operation
            # but if there is a composeable active it overrides
            # the appended part
            return listop.ListOp(
                appended_items=listop2.appended_items,
                prepended_items=listop1.prepended_items,
                deleted_items=listop1.deleted_items,
            )
        elif len(listop2.prepended_items) > 0:
            # this throws away any explicit operation
            # but if there is a composeable active, it overrides
            # the prepended part
            return listop.ListOp(
                appended_items=listop1.appended_items,
                prepended_items=listop2.prepended_items,
                deleted_items=listop1.deleted_items,
            )
        elif len(listop2.deleted_items) > 0:
            # this throws away any explicit operation
            # but if there is a composeable active, it overrides
            # the deleted part
            return listop.ListOp(
                appended_items=listop1.appended_items,
                prepended_items=listop1.prepended_items,
                deleted_items=listop2.deleted_items,
            )

        # listop 2 doesn't have anything, so just return the original
        return listop1

    def _consolidate_metadata(self, metadata: Any):
        """
        Consolidates listop related metadata such that one ListOp
        instance reflects all items of metadata processed.
        """
        processing_list = {}
        final_metadata_items = []
        for metadata_item in metadata:
            if isinstance(metadata_item, tuple):
                if isinstance(metadata_item[1], listop.ListOp):
                    if metadata_item[0] in processing_list:
                        # this might be a list op type that
                        # has been redefined - for example
                        # a = [</my/path>]
                        # a = None
                        # is acceptable syntactically, but
                        # semantically this redefining the
                        # list op operations, so we neeed
                        # to be careful with just combining
                        # them without checking
                        processing_list[metadata_item[0]] = self._process_listop_redefinition(
                            processing_list[metadata_item[0]], metadata_item[1]
                        )
                    else:
                        processing_list[metadata_item[0]] = metadata_item[1]
                else:
                    final_metadata_items.append(metadata_item)
            else:
                final_metadata_items.append(metadata_item)

        for key, value in processing_list.items():
            final_metadata_items.append((key, value))

        return final_metadata_items

    def _add_metadata(self, spec: SpecData, key: Token, value: Any):
        """
        Adds metadata to the spec by first translating the metadata
        key to a well known metadata key, validating the type of the
        value against the well known metadata type, and adding the value.
        If the metadata key does not specify well known spec metadata,
        the value will be of a type inferred from the parse rules themselves.

        If the type of the value provided is different than the
        expected type a TypeError will be raised.
        """
        # look up the field definition associated with the key
        field_registry = fields.FieldRegistry()
        if key in field_registry:
            field = field_registry[key]
            if field.verifier is not None:
                field.verifier(value)

        spec.write_field(key, value)

    def _fix_paths(self, layer_spec: SpecData):
        """
        Fixes the paths in all specs by walking the spec tree
        and prepending the missing path items.
        """
        if layer_spec.has_field(Token("primChildren")):
            prim_children = layer_spec.read_field(Token("primChildren"))

            # fix up the path for all children
            for prim_spec in prim_children:
                self._fix_path(prim_spec, "")

            # now remove the child specs and replace with
            # the name of the child and add the spec to
            # the layer data
            prim_child_names = []
            for i in range(len(prim_children) - 1, -1, -1):
                spec = prim_children.pop(i)
                self._format.add_spec(spec.path, spec)
                prim_child_names.insert(0, spec.name)

            if len(prim_child_names) > 0:
                layer_spec.write_field(Token("primChildren"), prim_child_names)

    def _fix_path(self, spec: SpecData, prepend_path: str):
        """
        Fixes the path in the spec by prepending
        the given prepend_path.
        """
        if (spec._form & SpecFormFlags.Prim == SpecFormFlags.Prim) or (
            spec._form & SpecFormFlags.Variant == SpecFormFlags.Variant
        ):
            if spec._form == SpecFormFlags.Variant:
                parent_path = prepend_path
                parent_path = parent_path[0 : len(parent_path) - 1]
                spec.path = parent_path + spec.path + "}"
            else:
                spec.path = "/".join([prepend_path, spec.path])

            if spec.has_field(Token("primChildren")):
                prim_children = spec.read_field(Token("primChildren"))
                for prim_spec in prim_children:
                    self._fix_path(prim_spec, spec.path)

                # now remove the child specs and replace with
                # the name of the child and add the spec to
                # the layer data
                prim_child_names = []
                for i in range(len(prim_children) - 1, -1, -1):
                    child_spec = prim_children.pop(i)
                    self._format.add_spec(child_spec.path, child_spec)
                    prim_child_names.insert(0, child_spec.name)

                if len(prim_child_names) > 0:
                    spec.write_field(Token("primChildren"), prim_child_names)

            if spec.has_field(Token("propertyChildren")):
                property_children = spec.read_field(Token("propertyChildren"))
                for property_spec in property_children:
                    self._fix_path(property_spec, spec.path)

                # now remove the child specs and replace with
                # the name of the child and add the spec to
                # the layer data
                property_child_names = []
                for i in range(len(property_children) - 1, -1, -1):
                    child_spec = property_children.pop(i)
                    self._format.add_spec(child_spec.path, child_spec)
                    property_child_names.insert(0, child_spec.name)

                if len(property_child_names) > 0:
                    spec.write_field(Token("propertyChildren"), property_child_names)

            if spec.has_field(Token("variantSetChildren")):
                # variant set children
                variant_set_children = spec.read_field(Token("variantSetChildren"))
                for variant_set_spec in variant_set_children:
                    self._fix_path(variant_set_spec, spec.path)

                # now remove the child specs and replace with name of child
                variant_set_child_names = []
                for i in range(len(variant_set_children) - 1, -1, -1):
                    child_spec = variant_set_children.pop(i)
                    self._format.add_spec(child_spec.path, child_spec)
                    variant_set_child_names.insert(0, child_spec.name)

                if len(variant_set_child_names) > 0:
                    spec.write_field(Token("variantSetChildren"), variant_set_child_names)
        elif (spec._form & SpecFormFlags.Attribute == SpecFormFlags.Attribute) or (
            spec._form & SpecFormFlags.Relationship == SpecFormFlags.Relationship
        ):
            spec.path = ".".join([prepend_path, spec.path])
        elif spec._form == SpecFormFlags.VariantSet == SpecFormFlags.VariantSet:
            spec.path = prepend_path + "{" + spec.path + "=}"
            if spec.has_field(Token("variantChildren")):
                variant_children = spec.read_field(Token("variantChildren"))
                for variant_spec in variant_children:
                    self._fix_path(variant_spec, spec.path)

                # now remove the child spec and replace with name of child
                variant_child_names = []
                for i in range(len(variant_children) - 1, -1, -1):
                    child_spec = variant_children.pop(i)
                    self._format.add_spec(child_spec.path, child_spec)
                    variant_child_names.insert(0, child_spec.name)

                if len(variant_child_names) > 0:
                    spec.write_field(Token("variantChildren"), variant_child_names)

    # --------------------------------------------------
    # TIME SAMPLES
    # -------------------------------------------------
    def visit_timesamplemap(self, node, visited_children):
        """
        Processes a time sample map.
        """
        # timesamplemap = leftcurlybrace (multilinepadding)* (timesamplemapcontents (multilinepadding)*)? rightcurlybrace
        _, _, content, _ = visited_children
        time_samples = {}
        if isinstance(content, list):
            time_samples, _ = content[0]

        logging.getLogger("usdavisitor").info("TIME SAMPLE MAP {time_samples}")

        return time_samples

    def visit_timesamplemapcontents(self, node, visited_children):
        """
        Processes time sample map content.
        """
        # timesamplemapcontents = timesample ((inlinepadding)* listseparator (multilinepadding)* timesample)* (inlinepadding)* (listseparator (multilinepadding)*)?
        first_time_sample, additional_time_samples, _, _ = visited_children

        time_samples = {}
        time_samples.update(first_time_sample)
        if isinstance(additional_time_samples, list):
            for additional_time_sample in additional_time_samples:
                _, _, _, next_time_sample = additional_time_sample
                time_samples.update(next_time_sample)

        return time_samples

    def visit_timesample(self, node, visited_children):
        """
        Processes a time sample.
        """
        # timesample = number (inlinepadding)* colon (inlinepadding)* (keywordbignone / typedvalue)
        key, _, _, _, value = visited_children

        time_sample = {}
        time_sample.update({key: value[0]})

        return time_sample

    # --------------------------------------------------
    # METADATA
    # -------------------------------------------------
    def visit_listop(self, node, visited_children):
        """
        Processes a list op.
        """
        # listop = keyworddelete / keywordappend / keywordprepend
        return node.text

    def visit_listopvalue(self, node, visited_children):
        """
        Processes a list op value.
        """
        return visited_children[0]

    def visit_listopmetadata(self, node, visited_children):
        """
        Processes list op metadata.
        """
        # listopmetadata = listop (inlinepadding)+ identifier assignment listopvalue
        listop_type, _, identifier, _, value = visited_children
        if value is None:
            value = []

        listop_type = ListOpType[listop_type]
        if listop_type == ListOpType.explicit:
            listop_instance = listop.ListOp(explicit_items=value)
        elif listop_type == ListOpType.append:
            listop_instance = listop.ListOp(appended_items=value)
        elif listop_type == ListOpType.delete:
            listop_instance = listop.ListOp(deleted_items=value)
        elif listop_type == ListOpType.prepend:
            listop_instance = listop.ListOp(prepended_items=value)

        return (identifier, listop_instance)

    def visit_sharedmetadata(self, node, visited_children):
        """
        Processes shared metadata.
        """
        # sharedmetadata = string / keyvaluemetadata / docmetadata
        if isinstance(visited_children[0], str):
            return (Token("comment"), visited_children[0])

        return visited_children[0]

    def visit_keyvaluemetadata(self, node, visited_children):
        """
        Processes key value metadata.
        """
        # keyvaluemetadata = identifier assignment metadatavalue
        key, _, value = visited_children
        logging.getLogger("usdavisitor").info(f"KEY VALUE METADATA {key} {value}")

        return (Token(key[0]), value)

    def visit_docmetadata(self, node, visited_children):
        """
        Processes documentation metadata.
        """
        # docmetadata = keyworddoc assignment string
        _, _, value = visited_children
        logging.getLogger("usdavisitor").info(f"DOC METADATA {value}")

        # keyword doc gets mapped to the "documentation" metadata value key
        return ("documentation", value)

    def visit_metadatavalue(self, node, visited_children):
        """
        Processes a metadata value.
        """
        # metadatavalue = keywordbignone / dictionaryvalue / typedvalue
        logging.getLogger("usdavisitor").info(f"METADATA VALUE {visited_children[0]}")
        return visited_children[0]

    # --------------------------------------------------
    # LAYER
    # -------------------------------------------------
    def visit_layermetadata(self, node, visited_children):
        """
        Processes layer metadata.
        """
        # layermetadata = leftparen (multilinepadding)* (layermetadatacontents (multilinepadding)*)? rightparen
        layer_metadata_contents = []
        _, _, layer_metadata_content, _ = visited_children
        if isinstance(layer_metadata_content, list):
            layer_metadata_contents, _ = layer_metadata_content[0]

        logging.getLogger("usdavisitor").info(f"LAYER METADATA {layer_metadata_contents}")
        return layer_metadata_contents

    def visit_layermetadatacontents(self, node, visited_children):
        """
        Processes layer metadata content.
        """
        # layermetadatacontents = layermetadataitem ((singlelinepadding)* statementseparator (multilinepadding)* layermetadataitem)* (singlelinepadding)* (statementseparator (multilinepadding)*)?
        metadata_items = []
        first_item, other_items, _, _ = visited_children
        metadata_items.append(first_item)
        for other_item in other_items:
            _, _, _, next_item = other_item
            metadata_items.append(next_item)

        return metadata_items

    def visit_layermetadataitem(self, node, visited_children):
        """
        Processes a layer metadata item.
        """
        # layermetadataitem = sharedmetadata / listopmetadata / sublayermetadata
        return visited_children[0]

    def visit_layeroffsetlist(self, node, visited_children):
        """
        Processes a layer offset list.
        """
        # layeroffsetlist = layeroffset ((singlelinepadding)* statementseparator (multilinepadding)* layeroffset)* (singlelinepadding)* (statementseparator (multilinepadding)*)?
        first_offset, additional_offsets, _, _ = visited_children
        layer_offsets = [first_offset]
        if isinstance(additional_offsets, list):
            for additional_offset in additional_offsets:
                _, _, _, next_offset = additional_offset
                layer_offsets.append(next_offset)

        return layer_offsets

    def visit_relocatesmetadata(self, node, visited_children):
        """
        Processes relocates metadata.
        """
        # relocatesmetadata = keywordrelocates assignment leftcurlybrace (multilinepadding)* (relocatesmetadatacontent (multilinepadding)*)? rightcurlybrace
        _, _, _, _, content, _ = visited_children
        relocates_items = []
        if isinstance(content, list):
            relocates_items, _ = content

        return (Token("layerRelocates"), relocates_items)

    def visit_relocatesmetadatacontent(self, node, visited_children):
        """
        Processes relocates metdata content.
        """
        # relocatesmetadatacontent = relocatesitem ((inlinepadding)* listseparator (multilinepadding)* relocatesitem)* (inlinepadding)* (listseparator (multilinepadding)*)?
        first_item, additional_items, _, _ = visited_children
        relocates_items = [first_item]
        if isinstance(additional_items, list):
            for additional_item in additional_items:
                _, _, _, next_item = additional_item
                relocates_items.append(next_item)

        return relocates_items

    def visit_relocatesitem(self, node, visited_children):
        """
        Processes a relocates item.
        """
        # relocatesitem = pathref (inlinepadding)* colon (inlinepadding)* pathref
        first_item, _, _, _, second_item = visited_children
        return Relocate(first_item, second_item)

    def visit_sublayeritem(self, node, visited_children):
        """
        Processes a sublayer item.
        """
        # sublayeritem = assetref (inlinepadding)* (leftparen (multilinepadding)* (layeroffsetlist (multilinepadding)*)? rightparen)?
        asset_ref, _, layer_offset_list = visited_children

        # for sublayer offsets, the list must be the same length
        # as the sublayer asset list, so even though we could
        # end up with the default Retiming, we explicitly store it
        # here so that the list is of the same length and there
        # are no None values in there
        offset = 0.0
        scale = 1.0
        layer_offset = Retiming()
        if isinstance(layer_offset_list, list):
            _, _, layer_offset_list, _ = layer_offset_list[0]
            if isinstance(layer_offset_list, list):
                layer_offset_list, _ = layer_offset_list[0]
                for layer_offset_item in layer_offset_list:
                    if layer_offset_item[0] == "offset":
                        offset = layer_offset_item[1]
                    else:
                        scale = layer_offset_item[1]

                layer_offset = Retiming(offset, scale)

        return (asset_ref, layer_offset)

    def visit_sublayermetadatacontents(self, node, visited_children):
        """
        Processes the content of sublayer metadata.
        """
        # sublayermetadatacontents = sublayeritem ((inlinepadding)* listseparator (multilinepadding)* sublayeritem)* (inlinepadding)* (listseparator (multilinepadding)*)?
        first_item, additional_items, _, _ = visited_children
        sublayers = [first_item[0]]
        sublayer_offsets = [first_item[1]]
        if isinstance(additional_items, list):
            for additional_item in additional_items:
                _, _, _, next_item = additional_item
                sublayers.append(next_item[0])
                sublayer_offsets.append(next_item[1])

        return ("subLayers", ("subLayers", sublayers), ("subLayerOffsets", sublayer_offsets))

    def visit_sublayermetadata(self, node, visited_children):
        """
        Processes sublayer metadata.
        """
        # sublayermetadata = keywordsublayers assignment leftbracket (multilinepadding)* (sublayermetadatacontents (multilinepadding)*)? rightbracket
        _, _, _, _, content, _ = visited_children
        if isinstance(content, list):
            content, _ = content[0]

        # this metadata unfortunately has two different items
        # so we can't just return a key / value tuple like every other metadata item
        return content

    def visit_layeritem(self, node, visited_children):
        """
        Processes a layer item.
        """
        # layeritem = (keywordreorder (inlinepadding)+ keywordrootprims assignment namelist) / primspec
        return visited_children[0]

    def visit_layerheader(self, node, visited_children):
        """
        Processes the layer header.
        """
        # layerheader = pound usda (inlinepadding)* (digit)+ dot (digit)+ (dot (digit)+)?
        _, _, _, major, _, minor, patch = visited_children
        if not isinstance(major, list) or len(major) > 1 or major[0].text != "1":
            raise RuntimeError("Major version in layer header not set to 1")

        if not isinstance(minor, list) or len(minor) > 1 or minor[0].text != "0":
            raise RuntimeError("Minor version in layer header not set to 0")

        # patch can be anything

    def visit_layerspec(self, node, visited_children):
        """
        Processes the layer spec.
        """
        # layerspec = layerheader (multilinepadding)* (layermetadata (multilinepadding)*)? (layeritem (multilinepadding)*)*
        prim_specs = []
        prim_order = None
        _, _, layer_metadata, layer_items = visited_children
        for layer_item in layer_items:
            item, _ = layer_item
            if isinstance(item, SpecData):
                # this is a prim spec
                prim_specs.append(item)
            else:
                # this is a reorder rootPrims statement
                # and should contain a list of strings
                prim_order = item

        metadata_items = []
        if isinstance(layer_metadata, list):
            layer_metadata = layer_metadata[0]
            metadata_items, _ = layer_metadata

        # create the layer spec
        spec = SpecData("/", SpecFormFlags.Layer)
        if len(prim_specs) > 0:
            spec.write_field(Token("primChildren"), prim_specs)
            if prim_order is not None:
                spec.write_field(Token("primOrder"), prim_order)

        for metadata_item in metadata_items:
            if isinstance(metadata_item, tuple):
                if metadata_item[0] == "subLayers":
                    # this is actually two separate tuples
                    self._add_metadata(spec, metadata_item[1][0], metadata_item[1][1])
                    self._add_metadata(spec, metadata_item[2][0], metadata_item[2][1])
                else:
                    # this was key / value metadata
                    self._add_metadata(spec, metadata_item[0], metadata_item[1])

        # at this point, we have everything, so we can now do a second
        # pass to fix up the prim / property paths
        self._fix_paths(spec)
        logging.getLogger("usdavisitor").info("LAYER SPEC")
        logging.getLogger("usdavisitor").info(spec.json_encode())

        self._format.add_spec("/", spec)

        return self._format

    # --------------------------------------------------
    # PRIMS
    # -------------------------------------------------
    def visit_primitem(self, node, visited_children):
        """
        Processes a prim item.
        """
        # primitem = (childorpropertyorderstatement (singlelinepadding)* statementseparator) / (propertyspec (singlelinepadding)* statementseparator) / (primspec (singlelinepadding)* crlf) / (variantsetstatement (singlelinepadding)* crlf)
        first_item, _, _ = visited_children[0]
        return first_item

    def visit_primcontents(self, node, visited_children):
        """
        Processes the prim contents.
        """
        # primcontents = (multilinepadding)* (primitem (multilinepadding)*)*
        prim_items = []
        _, item_list = visited_children
        for item in item_list:
            prim_item, _ = item
            prim_items.append(prim_item)

        return prim_items

    def visit_primspec(self, node, visited_children):
        """
        Processes a prim spec.
        """
        # primspec = primdeclaration (multilinepadding)* (primmetadata (multilinepadding)*)? leftcurlybrace primcontents rightcurlybrace
        prim_declaration, _, prim_metadata, _, prim_contents, _ = visited_children
        prim_children = []
        property_children = []
        variant_set_children = []
        spec = prim_declaration
        partial_specs = []
        spec_map = {}
        for prim_item in prim_contents:
            if isinstance(prim_item, PartialSpec):
                # this is a partial attribute spec
                # that needs to be combined at the end
                partial_specs.append(prim_item)
            elif isinstance(prim_item, SpecData):
                if (prim_item._form & SpecFormFlags.Attribute == SpecFormFlags.Attribute) or (
                    prim_item._form & SpecFormFlags.Relationship == SpecFormFlags.Relationship
                ):
                    property_children.append(prim_item)
                elif prim_item._form == SpecFormFlags.Prim:
                    prim_children.append(prim_item)
                elif prim_item._form == SpecFormFlags.VariantSet:
                    variant_set_children.append(prim_item)

                spec_map.update({prim_item.path: prim_item})

            else:
                # child or property order statement
                # this is a tuple of (operation, name_list)
                if prim_item[0] == "nameChildren":
                    spec.write_field(Token("primOrder"), prim_item[1])
                else:
                    spec.write_field(Token("propertyOrder"), prim_item[1])

        # we've processed all specs, now combine the partial specs
        # with the specs to form the full spec
        for partial_spec in partial_specs:
            if partial_spec.spec.path in spec_map:
                if partial_spec.spec.has_field(Token("connectionPaths")):
                    # this is a listop connection path that needs to be combined
                    existing_spec = spec_map[partial_spec.spec.path]
                    listop_instance = partial_spec.spec.read_field(Token("connectionPaths"))
                    if existing_spec.has_field(Token("connectionPaths")):
                        existing_listop = existing_spec.read_field(Token("connectionPaths"))
                        existing_spec.write_field(
                            Token("connectionPaths"),
                            self._process_listop_redefinition(existing_listop, listop_instance),
                        )
                    else:
                        existing_spec.write_field(Token("connectionPaths"), listop_instance)

                if partial_spec.spec.has_field(Token("timeSamples")):
                    # the time sample map doesn't get combined - last one wins
                    existing_spec = spec_map[partial_spec.spec.path]
                    existing_spec.write_field(Token("timeSamples"), partial_spec.spec.read_field(Token("timeSamples")))

                if partial_spec.spec.has_field(Token("targetPaths")):
                    # targetPaths is a listop
                    existing_spec = spec_map[partial_spec.spec.path]
                    listop_instance = partial_spec.spec.read_field(Token("targetPaths"))
                    if existing_spec.has_field(Token("targetPaths")):
                        existing_listop = existing_spec.read_field(Token("targetPaths"))
                        existing_spec.write_field(
                            Token("targetPaths"), self._process_listop_redefinition(existing_listop, listop_instance)
                        )
                    else:
                        existing_spec.write_field(Token("targetPaths"), listop_instance)
            else:
                # there was no spec there currently
                # so just use this as the source spec
                property_children.append(partial_spec.spec)
                spec_map.update({partial_spec.spec.path: partial_spec.spec})

        if len(prim_children) > 0:
            spec.write_field(Token("primChildren"), prim_children)

        if len(property_children) > 0:
            spec.write_field(Token("propertyChildren"), property_children)

        if len(variant_set_children) > 0:
            spec.write_field(Token("variantSetChildren"), variant_set_children)

        # process metadata
        if isinstance(prim_metadata, list):
            prim_metadata, _ = prim_metadata[0]
            prim_metadata = self._consolidate_metadata(prim_metadata)
            for prim_metadata_item in prim_metadata:
                self._add_metadata(spec, prim_metadata_item[0], prim_metadata_item[1])

        logging.getLogger("usdavisitor").info("PRIM SPEC")
        logging.getLogger("usdavisitor").info(spec.json_encode())

        self._prim_paths.pop()

        return spec

    def visit_primdeclaration(self, node, visited_children):
        """
        Processes a prim declaration.
        """
        # primdeclaration = primspecifier (inlinepadding)+ (primtypename (inlinepadding)+)? string
        specifier, _, prim_type_name, identifier = visited_children

        # validate prim according to prim naming rules
        # primname = identifier
        try:
            grammar["primname"].parse(identifier)
        except Exception as e:
            raise ValueError(f"Specified prim identifier {identifier} is not a valid prim identifier!") from e

        # this is a new prim spec
        # we don't have the full path yet, so we just add the name
        # this will get fixed up later
        if len(self._prim_paths) == 0:
            self._prim_paths.append("/" + identifier)
        else:
            self._prim_paths.append(self._prim_paths[-1] + "/" + identifier)

        spec = SpecData(identifier, SpecFormFlags.Prim)
        spec.write_field(Token("specifier"), specifier)

        if isinstance(prim_type_name, list):
            type_name, _ = prim_type_name[0]
            spec.write_field(Token("typeName"), type_name)

        logging.getLogger("usdavisitor").info(f"PRIM DECLARATION {specifier} {prim_type_name} {identifier}")

        return spec

    def visit_primspecifier(self, node, visited_children):
        """
        Processes a prim specifier.
        """
        # primspecifier = keyworddef / keywordover / keywordclass

        return Specifier[node.text[0].upper() + node.text[1:]]

    def visit_primtypename(self, node, visited_children):
        """
        Processes a prim type name.
        """
        # primtypename = asciistart (asciicontinue)*
        first_part, other_parts = visited_children
        parts = first_part[0].text
        for other_part in other_parts:
            parts += other_part[0].text

        type_name = parts
        logging.getLogger("usdavisitor").info(f"PRIM TYPE NAME {type_name}")

        return type_name

    def visit_primmetadata(self, node, visited_children):
        """
        Processes prim metadata.
        """
        # primmetadata = leftparen (multilinepadding)* (primmetadatacontents (multilinepadding)*)? rightparen
        _, _, prim_metadata_contents, _ = visited_children
        if isinstance(prim_metadata_contents, list):
            prim_metadata_contents, _ = prim_metadata_contents[0]

        return prim_metadata_contents

    def visit_primmetadatacontents(self, node, visited_children):
        """
        Processes the content of prim metadata.
        """
        # primmetadatacontents = primmetadataitem ((singlelinepadding)* statementseparator (multilinepadding)* primmetadataitem)* (singlelinepadding)* (statementseparator (multilinepadding)*)?
        first_item, additional_items, _, _ = visited_children
        items = [first_item]
        if isinstance(additional_items, list):
            for additional_item in additional_items:
                _, _, _, next_item = additional_item
                items.append(next_item)

        return items

    def visit_primmetadataitem(self, node, visited_children):
        """
        Processes a prim metadata item.
        """
        # primmetadataitem = sharedmetadata / listopmetadata / kindmetadata / payloadmetadata / inheritsmetadata / specializesmetadata/ referencesmetadata  / variantsmetadata / variantsetsmetadata
        return visited_children[0]

    def visit_kindmetadata(self, node, visited_children):
        """
        Processes kind metadata.
        """
        # kindmetadata = keywordkind assignment string
        _, _, kind_type = visited_children
        return ("kind", kind_type)

    def visit_payloadmetadata(self, node, visited_children):
        """
        Processes payload metadata.
        """
        # payloadmetadata = (listop (inlinepadding)+)? keywordpayload assignment payloadlist
        listop_type, _, _, payload_list = visited_children
        if isinstance(listop_type, list):
            listop_type, _ = listop_type[0]
            listop_type = ListOpType[listop_type]
        else:
            listop_type = ListOpType.explicit

        if payload_list is not None and len(payload_list) > 0:
            if listop_type == ListOpType.explicit:
                listop_instance = listop.ListOp(explicit_items=payload_list)
            elif listop_type == ListOpType.append:
                listop_instance = listop.ListOp(appended_items=payload_list)
            elif listop_type == ListOpType.delete:
                listop_instance = listop.ListOp(deleted_items=payload_list)
            elif listop_type == ListOpType.prepend:
                listop_instance = listop.ListOp(prepended_items=payload_list)
        elif payload_list is None:
            listop_instance = listop.ListOp()

        return ("payload", listop_instance)

    def visit_payloadlist(self, node, visited_children):
        """
        Processes a payload list.
        """
        # payloadlist = (keywordbignone) / (payloadlistitem) / (leftbracket (multilinepadding)* (payloadlistcontents (multilinepadding)*)? rightbracket)
        payload_list = visited_children[0]
        if payload_list is None:
            return None

        if isinstance(payload_list, Payload):
            return [payload_list]

        _, _, payload_list, _ = payload_list
        if isinstance(payload_list, list):
            payload_list, _ = payload_list[0]
            return payload_list
        else:
            return []

    def visit_payloadlistcontents(self, node, visited_children):
        """
        Processes the content of a payload list.
        """
        # payloadlistcontents = payloadlistitem ((inlinepadding)* listseparator (multilinepadding)* payloadlistitem)* (inlinepadding)* (listseparator (multilinepadding)*)?
        first_item, additional_items, _, _ = visited_children
        payload_list = [first_item]
        if isinstance(additional_items, list):
            for additional_item in additional_items:
                _, _, _, next_item = additional_item
                payload_list.append(next_item)

        return payload_list

    def visit_payloadlistitem(self, node, visited_children):
        """
        Processes a single payload item.
        """
        # payloadlistitem = (assetref (inlinepadding)* (pathref)? (inlinepadding)* (payloadparameters)?) / (pathref (inlinepadding)* (payloadparameters)?)
        first_item, *_ = visited_children[0]
        if isinstance(first_item, Asset.__origin__):
            asset_ref, _, path_ref, _, payload_parameters = visited_children[0]
            if isinstance(payload_parameters, list):
                payload_parameters = payload_parameters[0]
            else:
                payload_parameters = None

            if isinstance(path_ref, list):
                path_ref = path_ref[0]
                return Payload((asset_ref, path_ref), payload_parameters)

            return Payload(asset_ref, payload_parameters)
        else:
            path_ref, _, payload_parameters = visited_children[0]
            if isinstance(payload_parameters, list):
                payload_parameters = payload_parameters[0]
            else:
                payload_parameters = None

            return Payload(path_ref, payload_parameters)

    def visit_payloadparameters(self, node, visited_children):
        """
        Processes the parameters of a payload item.
        """
        # payloadparameters = leftparen (multilinepadding)* (payloadparameterscontent (multilinepadding)*)? rightparen
        _, _, payload_parameters, _ = visited_children
        if isinstance(payload_parameters, list):
            payload_parameters, _ = payload_parameters[0]
        else:
            payload_parameters = None

        return payload_parameters

    def visit_payloadparameterscontent(self, node, visited_children):
        """
        Processes the content of a parameter list for a payload item.
        """
        # payloadparameterscontent = layeroffset ((singlelinepadding)* statementseparator (multilinepadding)* layeroffset)* (singlelinepadding)* (statementseparator (multilinepadding)*)?
        offset = 0.0
        scale = 1.0
        first_item, additional_items, _, _ = visited_children
        items = [first_item]
        if isinstance(additional_items, list):
            for additional_item in additional_items:
                _, _, _, next_item = additional_item
                items.append(next_item)

        for item in items:
            if item[0] == "offset":
                offset = item[1]
            else:
                scale = item[1]

        return Retiming(offset, scale)

    def visit_layeroffset(self, node, visited_children):
        """
        Processes a layer offset.
        """
        # layeroffset = (keywordoffset / keywordscale) assignment number
        offset_scale, _, value = visited_children
        offset_scale = offset_scale[0]
        if offset_scale.text == "offset":
            return ("offset", value)
        else:
            return ("scale", value)

    def visit_inheritsorspecializeslist(self, node, visited_children):
        """
        Processes an inherits or specializes list.
        """
        # inheritsorspecializeslist = (keywordbignone) / (pathref) / (leftbracket (multilinepadding)* (pathreflistcontents (multilinepadding)*)? rightbracket)
        child = visited_children[0]
        if child is None:
            return None

        if isinstance(child, ObjectPath):
            return [child]

        paths = []
        _, _, path_refs, _ = child
        if isinstance(path_refs, list):
            paths, _ = path_refs[0]

        return paths

    def visit_specializesmetadata(self, node, visited_children):
        """
        Processes specializes metadata.
        """
        # specializesmetadata = (listop (inlinepadding)+)? keywordspecializes assignment inheritsorspecializeslist
        listop_type, _, _, specializes_list = visited_children
        if isinstance(listop_type, list):
            listop_type, _ = listop_type[0]
            listop_type = ListOpType[listop_type]
        else:
            listop_type = ListOpType.explicit

        if specializes_list is not None and len(specializes_list) > 0:
            if listop_type == ListOpType.explicit:
                listop_instance = listop.ListOp(explicit_items=specializes_list)
            elif listop_type == ListOpType.append:
                listop_instance = listop.ListOp(appended_items=specializes_list)
            elif listop_type == ListOpType.delete:
                listop_instance = listop.ListOp(deleted_items=specializes_list)
            elif listop_type == ListOpType.prepend:
                listop_instance = listop.ListOp(prepended_items=specializes_list)
        elif specializes_list is None:
            listop_instance = listop.ListOp()

        return ("specializes", listop_instance)

    def visit_inheritsmetadata(self, node, visited_children):
        """
        Processes inherits metadata.
        """
        # inheritsmetadata = (listop (inlinepadding)+)? keywordinherits assignment inheritsorspecializeslist
        listop_type, _, _, inherits_list = visited_children
        if isinstance(listop_type, list):
            listop_type, _ = listop_type[0]
            listop_type = ListOpType[listop_type]
        else:
            listop_type = ListOpType.explicit

        if inherits_list is not None and len(inherits_list) > 0:
            if listop_type == ListOpType.explicit:
                listop_instance = listop.ListOp(explicit_items=inherits_list)
            elif listop_type == ListOpType.append:
                listop_instance = listop.ListOp(appended_items=inherits_list)
            elif listop_type == ListOpType.delete:
                listop_instance = listop.ListOp(deleted_items=inherits_list)
            elif listop_type == ListOpType.prepend:
                listop_instance = listop.ListOp(prepended_items=inherits_list)
        elif inherits_list is None:
            listop_instance = listop.ListOp()

        return ("inheritPaths", listop_instance)

    def visit_referencesmetadata(self, node, visited_children):
        """
        Processes references metadata.
        """
        # referencesmetadata = (listop (inlinepadding)+)? keywordreferences assignment referencelist
        listop_type, _, _, reference_list = visited_children
        if isinstance(listop_type, list):
            listop_type, _ = listop_type[0]
            listop_type = ListOpType[listop_type]
        else:
            listop_type = ListOpType.explicit

        if reference_list is not None and len(reference_list) > 0:
            if listop_type == ListOpType.explicit:
                listop_instance = listop.ListOp(explicit_items=reference_list)
            elif listop_type == ListOpType.append:
                listop_instance = listop.ListOp(appended_items=reference_list)
            elif listop_type == ListOpType.delete:
                listop_instance = listop.ListOp(deleted_items=reference_list)
            elif listop_type == ListOpType.prepend:
                listop_instance = listop.ListOp(prepended_items=reference_list)
        elif reference_list is None:
            listop_instance = listop.ListOp()

        return ("references", listop_instance)

    def visit_referencelist(self, node, visited_children):
        """
        Processes a reference list.
        """
        # referencelist = (keywordbignone) / (referencelistitem) / (leftbracket (multilinepadding)* (referencelistcontents (multilinepadding)*)? rightbracket)
        content = visited_children[0]
        if content is None:
            return None

        if isinstance(content, Reference):
            return [content]

        references = []
        _, _, reference_list_contents, _ = content
        if isinstance(reference_list_contents, list):
            references, _ = reference_list_contents[0]

        return references

    def visit_referencelistcontents(self, node, visited_children):
        """
        Processes the contents of reference list.
        """
        # referencelistcontents = referencelistitem ((inlinepadding)* listseparator (multilinepadding)* referencelistitem)* (inlinepadding)* (listseparator (multilinepadding)*)?
        first_item, additional_items, _, _ = visited_children
        reference_items = [first_item]
        if isinstance(additional_items, list):
            for additional_item in additional_items:
                _, _, _, next_item = additional_item
                reference_items.append(next_item)

        return reference_items

    def visit_referencelistitem(self, node, visited_children):
        """
        Processes a reference list item.
        """
        # referencelistitem = (assetref (inlinepadding)* (pathref)? (inlinepadding)* (referenceparameters)?) / (pathref (inlinepadding)* (referenceparameters)?)
        item = visited_children[0]
        first_token, *_ = item
        if isinstance(first_token, Asset.__origin__):
            asset_ref, _, path_ref, _, reference_parameters = item
            if isinstance(path_ref, list):
                path_ref = path_ref[0]
            else:
                path_ref = None

            if isinstance(reference_parameters, list):
                reference_parameters = reference_parameters[0]
            else:
                reference_parameters = None
        else:
            asset_ref = None
            path_ref, _, reference_parameters = item
            if isinstance(reference_parameters, list):
                reference_parameters = reference_parameters[0]
            else:
                reference_parameters = None

        # the reference parameters contained both a layer offset and custom data
        layer_offset = None
        custom_data = {}
        if reference_parameters is not None:
            layer_offset = reference_parameters["layerOffset"]
            custom_data = reference_parameters["customData"]

        if asset_ref is None:
            return Reference(path_ref, layer_offset)
        elif path_ref is None:
            return Reference(asset_ref, layer_offset)

        return Reference((asset_ref, path_ref), layer_offset)

    def visit_referenceparameters(self, node, visited_children):
        """
        Processes reference parameters.
        """
        # referenceparameters = leftparen (multilinepadding)* (referenceparameterscontent (multilinepadding)*)? rightparen
        _, _, content, _ = visited_children
        reference_parameters = None
        if isinstance(content, list):
            reference_parameters, _ = content[0]

        return reference_parameters

    def visit_referenceparameterscontent(self, node, visited_children):
        """
        Processes reference parameter content.
        """
        # referenceparameterscontent = referenceparameter ((singlelinepadding)* statementseparator (multilinepadding)* referenceparameter)* (singlelinepadding)* (statementseparator (multilinepadding)*)?
        offset = 0.0
        scale = 1.0
        custom_data = {}
        first_item, additional_items, _, _ = visited_children
        items = [first_item]
        if isinstance(additional_items, list):
            for additional_item in additional_items:
                _, _, _, next_item = additional_item
                items.append(next_item)

        for item in items:
            if isinstance(item, tuple):
                if item[0] == "offset":
                    offset = item[1]
                else:
                    scale = item[1]
            else:
                custom_data = item

        return {"layerOffset": Retiming(offset, scale), "customData": custom_data}

    def visit_referenceparameter(self, node, visited_children):
        """
        Processes a single reference parameter.
        """
        # referenceparameter = (keywordcustomdata assignment dictionaryvalue) / (layeroffset)
        content = visited_children[0]
        if isinstance(content, tuple):
            # was a layer offset
            return content

        _, _, value = content

        return value

    def visit_childorpropertyorderstatement(self, node, visited_children):
        """
        Processes a child or property order statement.
        """
        # childorpropertyorderstatement = (keywordreorder (inlinepadding)+ keywordnamechildren assignment namelist) / (keywordreorder (inlinepadding)+ keywordproperties assignment namelist)
        _, _, op, _, name_list = visited_children[0]

        # the op is either a signal to reorder name children
        # or to reorder property children
        op = op.text
        return (op, name_list)

    def visit_variantsmetadata(self, node, visited_children):
        """
        Processes variants metadata.
        """
        # variantsmetadata = keywordvariants assignment dictionaryvalue
        _, _, value = visited_children
        return (Token("variantSelection"), value)

    def visit_variantsetsmetadata(self, node, visited_children):
        """
        Processes variant set metadata.
        """
        # variantsetsmetadata = (listop (inlinepadding)+)? keywordvariantsets assignment namelist
        listop_type, _, _, name_list = visited_children
        if isinstance(listop_type, list):
            listop_type, _ = listop_type[0]
            listop_type = ListOpType[listop_type]
        else:
            listop_type = ListOpType.explicit

        if name_list is None:
            name_list = []

        if listop_type == ListOpType.explicit:
            listop_instance = listop.ListOp(explicit_items=name_list)
        elif listop_type == ListOpType.append:
            listop_instance = listop.ListOp(appended_items=name_list)
        elif listop_type == ListOpType.delete:
            listop_instance = listop.ListOp(deleted_items=name_list)
        elif listop_type == ListOpType.prepend:
            listop_instance = listop.ListOp(prepended_items=name_list)

        return (Token("variantSetNames"), listop_instance)

    def visit_namelist(self, node, visited_children):
        """
        Processes a name list.
        """
        # namelist = string / (leftbracket (multilinepadding)* namelistcontents (multilinepadding)? rightbracket)
        first_token, *_ = visited_children
        if isinstance(first_token, str):
            return [first_token]

        _, _, name_list, _, _ = visited_children[0]
        return name_list

    def visit_namelistcontents(self, node, visited_children):
        """
        Visits the content of a name list.
        """
        # namelistcontents = string ((inlinepadding)* listseparator (multilinepadding)* string)* (inlinepadding)* (listseparator (multilinepadding)*)?
        first_item, additional_items, *_ = visited_children
        names = [first_item]
        if isinstance(additional_items, list):
            for additional_item in additional_items:
                _, _, _, next_item = additional_item
                names.append(next_item)

        return names

    def visit_variantstatement(self, node, visited_children):
        """
        Processes a variant statement.
        """
        # variantstatement = string (multilinepadding)* (primmetadata (multilinepadding)*)? leftcurlybrace primcontents rightcurlybrace
        variant_name, _, variant_metadata, _, variant_contents, _ = visited_children

        # validate variant_name according to variant naming rules
        # variantname = (dot (xidcontinue / verticalbar / minus)*) / (xidcontinue / verticalbar / minus)+
        try:
            grammar["variantname"].parse(variant_name)
        except Exception as e:
            raise ValueError(f"Specified variant name {variant_name} is not a valid variant name!") from e

        # create a new variant spec
        spec = SpecData(variant_name, SpecFormFlags.Variant)
        prim_children = []
        property_children = []
        variant_set_children = []
        for variant_item in variant_contents:
            if isinstance(variant_item, SpecData):
                if (variant_item._form & SpecFormFlags.Attribute == SpecFormFlags.Attribute) or (
                    variant_item._form & SpecFormFlags.Relationship == SpecFormFlags.Relationship
                ):
                    property_children.append(variant_item)
                elif variant_item._form & SpecFormFlags.Prim == SpecFormFlags.Prim:
                    prim_children.append(variant_item)
                elif variant_item._form & SpecFormFlags.VariantSet == SpecFormFlags.VariantSet:
                    variant_set_children.append(variant_item)
            else:
                # child or property order statement
                # this is a tuple of (operation, name_list)
                if variant_item[0] == "nameChildren":
                    spec.write_field(Token("primOrder"), variant_item[1])
                else:
                    spec.write_field(Token("propertyOrder"), variant_item[1])

        if len(prim_children) > 0:
            spec.write_field(Token("primChildren"), prim_children)

        if len(property_children) > 0:
            spec.write_field(Token("propertyChildren"), property_children)

        if len(variant_set_children) > 0:
            spec.write_field(Token("variantSetChildren"), variant_set_children)

        # process metadata
        if isinstance(variant_metadata, list):
            variant_metadata, _ = variant_metadata[0]
            variant_metadata = self._consolidate_metadata(variant_metadata)
            for variant_metadata_item in variant_metadata:
                spec.write_field(variant_metadata_item[0], variant_metadata_item[1])

        logging.getLogger("usdavisitor").info("VARIANT SPEC")
        logging.getLogger("usdavisitor").info(spec.json_encode())

        return spec

    def visit_variantsetstatement(self, node, visited_children):
        """
        Processes a variant set statement.
        """
        # variantsetstatement = keywordvariantset (inlinepadding)+ string assignment (multilinepadding)* leftcurlybrace ((multilinepadding)* variantstatement (multilinepadding)*)+ rightcurlybrace
        _, _, variant_set_name, _, _, _, variant_statements, _ = visited_children
        variants = []
        if isinstance(variant_statements, list):
            for variant_statement in variant_statements:
                _, variant_statement, _ = variant_statement
                variants.append(variant_statement)

        # validate variant set name according to prim naming rules
        # primname = identifier
        try:
            grammar["primname"].parse(variant_set_name)
        except Exception as e:
            raise ValueError(f"Specified variant set name {variant_set_name} is not a valid variant set name!") from e

        spec = SpecData(variant_set_name, SpecFormFlags.VariantSet)
        spec.write_field(Token("variantChildren"), variants)

        return spec

    # --------------------------------------------------
    # PROPERTIES
    # -------------------------------------------------
    def visit_propertyspec(self, node, visited_children):
        """
        Process a property spec.
        """
        # propertyspec = attributespec / relationshipspec
        logging.getLogger("usdavisitor").info("PROPERTY SPEC")
        logging.getLogger("usdavisitor").info(visited_children[0])
        return visited_children[0]

    def visit_namespacedname(self, node, visited_children):
        """
        Processes a namespaced name.
        """
        logging.getLogger("usdavisitor").info(f"NAMESPACED NAME {node.text}")
        return node.text

    # --------------------------------------------------
    # ATTRIBUTES
    # -------------------------------------------------
    def visit_attributeassignment(self, node, visited_children):
        """
        Processes an attribute assignment.
        """
        # attributeassignment = (assignment keywordbignone) / (assignment typedvalue)
        _, value = visited_children[0]
        logging.getLogger("usdavisitor").info(f"ATTRIBUTE ASSIGNMENT {value}")
        if value is None:
            # sentinel blocking value
            return ValueBlockSentinel()
        else:
            return DefaultValue(value)

    def visit_attributedeclaration(self, node, visited_children):
        """
        Processes an attribute declaration.
        """
        # attributedeclaration = (attributecustomdeclaration)? attributetype (inlinepadding)+ namespacedname
        is_custom = False
        custom_declaration, attribute_type, _, namespaced_name = visited_children
        if isinstance(custom_declaration, list):
            if custom_declaration[0]:
                is_custom = True

        logging.getLogger("usdavisitor").info(f"ATTRIBUTE DECLARATION {is_custom} {attribute_type} {namespaced_name}")

        # this is a new attribute spec
        # at this point, we don't have the prim to form the full path name
        # so we only add a spec that includes the attribute name
        # it will get fixed up later
        spec = SpecData(namespaced_name, SpecFormFlags.Attribute | SpecFormFlags.Property)
        variability, type_name = attribute_type
        spec.write_field(Token("typeName"), type_name)
        if is_custom:
            spec.write_field(Token("custom"), is_custom)

        if variability == Variability.Uniform:
            spec.write_field(Token("variability"), variability)

        return spec

    def visit_attributecustomdeclaration(self, node, visited_children):
        """
        Processes the custom keyword.
        """
        logging.getLogger("usdavisitor").info("ATTRIBUTE CUSTOM")
        return True

    def visit_attributespec(self, node, visited_children):
        """
        Processes an attribute spec.
        """
        # attributespec = regularattribute / specialattribute / listopconnect
        logging.getLogger("usdavisitor").info("ATTRIBUTE SPEC")
        logging.getLogger("usdavisitor").info(visited_children[0])
        return visited_children[0]

    def visit_listopconnect(self, node, visited_children):
        """
        Processes a list op connect value.
        """
        # listopconnect = listop (inlinepadding)+ attributedeclaration (inlinepadding)* dot (inlinepadding)* keywordconnect assignment connectvalue
        listoptype, _, attribute_declaration, _, _, _, _, _, connect_value = visited_children
        spec = attribute_declaration
        listop_type = ListOpType[listoptype]
        if connect_value is None:
            connect_value = []

        if listop_type == ListOpType.explicit:
            listop_instance = listop.ListOp(explicit_items=connect_value)
        elif listop_type == ListOpType.append:
            listop_instance = listop.ListOp(appended_items=connect_value)
        elif listop_type == ListOpType.delete:
            listop_instance = listop.ListOp(deleted_items=connect_value)
        elif listop_type == ListOpType.prepend:
            listop_instance = listop.ListOp(prepended_items=connect_value)

        spec.write_field(Token("connectionPaths"), listop_instance)

        return PartialSpec(spec)

    def visit_connectvalue(self, node, visited_children):
        """
        Processes a connect value.
        """
        # connectvalue = keywordbignone / pathref / (leftbracket (multilinepadding)* (connectvaluecontents (multilinepadding)*)? rightbracket)
        value = visited_children[0]
        if value is None:
            logging.getLogger("usdavisitor").info("CONNECT VALUE {value}")
            return value

        # single path ref
        if isinstance(value, ObjectPath):
            logging.getLogger("usdavisitor").info("CONNECT VALUE {value}")
            return [value]

        # list of path refs
        _, _, connect_value_contents, _ = value
        if isinstance(connect_value_contents, list):
            connect_value_contents, _ = connect_value_contents[0]

        logging.getLogger("usdavisitor").info("CONNECT VALUE {connect_value_contents}")
        return connect_value_contents

    def visit_connectvaluecontents(self, node, visited_children):
        """
        Processes connect value content.
        """
        # connectvaluecontents = pathref ((inlinepadding)* listseparator (multilinepadding)* pathref)* (inlinepadding)* (listseparator (multilinepadding)*)?
        first_path_ref, additional_path_refs, _, _ = visited_children
        path_refs = [first_path_ref]
        for additional_path_ref in additional_path_refs:
            _, _, _, next_path_ref = additional_path_ref
            path_refs.append(next_path_ref)

        return path_refs

    def visit_specialattributetype(self, node, visited_children):
        """
        Processes a special attribute type.
        """
        # specialattributetype = (keywordtimesamples assignment timesamplemap) / (keywordconnect assignment connectvalue) / (keywordspline assignment splinemap)
        attribute_type, _, value = visited_children[0]
        if attribute_type.text == "timeSamples":
            # time sample assignment
            return (attribute_type.text, value)
        elif attribute_type.text == "connect":
            # this is an explicit list op, so the resulting list of connections
            # need to be set as a list op on the "connectionPaths" metadata field
            # NOTE: this doesn't check for duplicate paths in the list
            listop_instance = listop.ListOp(explicit_items=value)
            return ("connectionPaths", listop_instance)
        else:
            # should be a spline
            return ("spline", value)

    def visit_specialattribute(self, node, visited_children):
        """
        Processes a special attribute.
        """
        # specialattribute = (attributedeclaration (inlinepadding)* dot (inlinepadding)* specialattributetype)
        attribute_declaration, _, _, _, attribute_value = visited_children
        spec = attribute_declaration
        spec.write_field(Token(attribute_value[0]), attribute_value[1])

        return PartialSpec(spec)

    def visit_regularattribute(self, node, visited_children):
        """
        Processes a regular attribute.
        """
        # regularattribute = attributedeclaration (attributeassignment)? (inlinepadding)* (attribute_metadata_block)?
        attribute_declaration, attribute_assignment, _, attribute_metadata_block = visited_children
        logging.getLogger("usdavisitor").info(f"REGULAR ATTRIBUTE {attribute_declaration} {attribute_assignment}")

        spec = attribute_declaration
        attribute_value_set = False
        attribute_value = None
        if isinstance(attribute_assignment, list):
            attribute_value_set = True
            attribute_value = attribute_assignment[0]

        # we use a separate variable to track setting because the value "None"
        # is a meaningful block
        if attribute_value_set:
            if spec.has_field(Token("typeName")) and spec.read_field(Token("typeName")) == "opaque":
                raise ValueError("Assignment of value to opaque types is invalid!")

            spec.write_field(Token("default"), attribute_value)

        if isinstance(attribute_metadata_block, list):
            attribute_metadata_block = attribute_metadata_block[0]
            for metadata_item in attribute_metadata_block:
                if isinstance(metadata_item, tuple):
                    # this was key / value metadata
                    self._add_metadata(spec, metadata_item[0], metadata_item[1])
                else:
                    # has to be a string
                    self._add_metadata(spec, Token("comment"), metadata_item)

        return spec

    def visit_attributetype(self, node, visited_children):
        """
        Processes an attribute type.
        """
        # attributetype = (attributevariability (inlinepadding)+)? identifier ((inlinepadding)* arraytype)?
        variability_statement, identifier, array_type = visited_children
        if isinstance(variability_statement, list):
            variability, _ = variability_statement[0]
            variability = Variability(variability.text)
        else:
            variability = Variability.Varying

        type_name = identifier
        if isinstance(array_type, list):
            type_name += "[]"

        if variability == Variability.Uniform:
            logging.getLogger("usdavisitor").info(f"ATTRIBUTE TYPE {variability} {type_name}")
        else:
            logging.getLogger("usdavisitor").info(f"ATTRIBUTE TYPE {type_name}")

        return (variability, type_name)

    def visit_attributemetadatablock(self, node, visited_children):
        """
        Processes an attribute metadata block.
        """
        # attributemetadatablock = attributemetadata (inlinepadding)*
        attribute_metadata, _ = visited_children
        return attribute_metadata

    def visit_attributemetadata(self, node, visited_children):
        """
        Processes attribute metadata.
        """
        # attributemetadata = leftparen (multilinepadding)* (attributemetadatacontents (multilinepadding)*)? rightparen
        metadata_content = []
        _, _, metadata_contents, _ = visited_children
        if isinstance(metadata_contents, list):
            metadata_content, _ = metadata_contents[0]

        return metadata_content

    def visit_attributemetadataitem(self, node, visited_children):
        """
        Processes an attribute metadata item.
        """
        # attributemetadataitem = sharedmetadata / listopmetadata
        return visited_children[0]

    def visit_attributemetadatacontents(self, node, visited_children):
        """
        Processes attribute metadata contents.
        """
        # attributemetadatacontents = attributemetadataitem ((singlelinepadding)* statementseparator (multilinepadding)* attributemetadataitem)* (singlelinepadding)* (statementseparator (multilinepadding)*)?
        first_item, next_items, _, _ = visited_children
        metadata_items = [first_item]
        for next_item in next_items:
            _, _, _, metadata_item = next_item
            metadata_items.append(metadata_item)

        return metadata_items

    # --------------------------------------------------
    # RELATIONS
    # -------------------------------------------------
    def visit_relationshipspec(self, node, visited_children):
        """
        Processes a relationship spec.
        """
        # relationshipspec = relationshipstandard / relationshippathref / listoprelationship
        return visited_children[0]

    def visit_relationshippathref(self, node, visited_children):
        """
        Processes a relationship that assignes a single path ref.
        """
        # relationshippathref = relationshiptype (inlinepadding)+ namespacedname (inlinepadding)? leftbracket (inlinepadding)* pathref (inlinepadding)* rightbracket
        relationship_type, _, namespaced_name, _, _, _, pathref, _, _ = visited_children
        spec = SpecData(namespaced_name, SpecFormFlags.Relationship | SpecFormFlags.Property)
        if relationship_type:
            spec.write_field(Token("custom"), True)

        listop_instance = listop.ListOp(explicit_items=pathref)
        spec.write_field(Token("targetPaths"), listop_instance)

        return spec

    def visit_relationshipstandard(self, node, visited_children):
        """
        Processes a standard relationship declaration.
        """
        # relationshipstandard = relationshiptype (inlinepadding)+ namespacedname (relationshipassignment)? (inlinepadding)* (relationshipmetadata)?
        relationship_type, _, namespaced_name, relationship_value, _, relationship_metadata = visited_children
        spec = SpecData(namespaced_name, SpecFormFlags.Relationship | SpecFormFlags.Property)
        if relationship_type:
            spec.write_field(Token("custom"), True)

        if isinstance(relationship_value, list):
            relationship_value = relationship_value[0]
            if relationship_value is not None:
                targets = []
                for val in relationship_value:
                    if val is not None:
                        targets.append(val)
            else:
                targets = None

            listop_instance = listop.ListOp(explicit_items=targets)

            spec.write_field(Token("targetPaths"), listop_instance)

        if isinstance(relationship_metadata, list):
            relationship_metadata = relationship_metadata[0]
            for metadata_item in relationship_metadata:
                if isinstance(metadata_item, tuple):
                    # this was key / value metadata
                    self._add_metadata(spec, metadata_item[0], metadata_item[1])
                else:
                    # has to be a string
                    self._add_metadata(spec, Token("comment"), metadata_item)

        return spec

    def visit_listoprelationship(self, node, visited_children):
        """
        Processes a list op relationship.
        """
        # listoprelationship = listop (inlinepadding)+ relationshiptype (inlinepadding)+ namespacedname (relationshipassignment)?
        listoptype, _, relationship_type, _, namespaced_name, relationship_value = visited_children
        spec = SpecData(namespaced_name, SpecFormFlags.Relationship | SpecFormFlags.Property)
        if relationship_type:
            spec.write_field(Token("custom"), True)

        if isinstance(relationship_value, list):
            relationship_value = relationship_value[0]
            targets = []
            if relationship_value is not None:
                for val in relationship_value:
                    if val is not None:
                        targets.append(val)
            listop_type = ListOpType[listoptype]
            if listop_type == ListOpType.explicit:
                listop_instance = listop.ListOp(explicit_items=targets)
            elif listop_type == ListOpType.append:
                listop_instance = listop.ListOp(appended_items=targets)
            elif listop_type == ListOpType.delete:
                listop_instance = listop.ListOp(deleted_items=targets)
            elif listop_type == ListOpType.prepend:
                listop_instance = listop.ListOp(prepended_items=targets)

            spec.write_field(Token("targetPaths"), listop_instance)

        return PartialSpec(spec)

    def visit_relationshipassignment(self, node, visited_children):
        """
        Processes a relationship assignment statement.
        """
        # relationshipassignment = (assignment keywordbignone) / (assignment pathref) / (assignment leftbracket (multilinepadding)* (pathreflistcontents (multilinepadding)*)? rightbracket)
        _, second_token, *_ = visited_children[0]

        # which one are we dealing with?
        if second_token is None:
            return None

        if isinstance(second_token, ObjectPath):
            # single path ref
            return [second_token]

        # it's a list of path refs
        _, _, _, pathref_list, _ = visited_children[0]
        if isinstance(pathref_list, list):
            pathref_list, _ = pathref_list[0]
            return pathref_list
        else:
            # it was optional and nothing was provided, treat as empty
            return []

    def visit_relationshiptype(self, node, visited_children):
        """
        Processes a relationship type declaration.
        """
        # relationshiptype = keywordrel / (keywordcustom (inlinepadding)+ keywordrel)
        # the only thing we need to pull from this is whether it is a custom rel or not
        is_custom = False
        if isinstance(visited_children[0], list):
            is_custom = True

        return is_custom

    def visit_pathreflistcontents(self, node, visited_children):
        """
        Processes a list of path refs.
        """
        # pathreflistcontents = pathref ((inlinepadding)* listseparator (multilinepadding)* pathref)* (inlinepadding)* (listseparator (multilinepadding)*)?
        first_pathref, additional_pathrefs, _, _ = visited_children
        pathrefs = [first_pathref]
        if isinstance(additional_pathrefs, list):
            for additional_pathref in additional_pathrefs:
                _, _, _, pathref = additional_pathref
                pathrefs.append(pathref)

        return pathrefs

    def visit_relationshipmetadataitem(self, node, visited_children):
        """
        Processes a relationship metadata item.
        """
        # relationshipmetadataitem = sharedmetadata / listopmetadata
        return visited_children[0]

    def visit_relationshipmetadatacontents(self, node, visited_children):
        """
        Processes relationship metadata content.
        """
        # relationshipmetadatacontents = relationshipmetadataitem ((singlelinepadding)* statementseparator (multilinepadding)* relationshipmetadataitem)* (singlelinepadding)* (statementseparator (multilinepadding)*)?
        first_item, additional_items, _, _ = visited_children
        metadata_items = [first_item]
        if isinstance(additional_items, list):
            for additional_item in additional_items:
                _, _, _, next_item = additional_item
                metadata_items.append(next_item)

        return metadata_items

    def visit_relationshipmetadata(self, node, visited_children):
        """
        Processes relationship metadata.
        """
        # relationshipmetadata = leftparen (multilinepadding)* (relationshipmetadatacontents (multilinepadding)*)? rightparen
        _, _, metadata_content, _ = visited_children
        metadata_items = []
        if isinstance(metadata_content, list):
            metadata_items, _ = metadata_content[0]

        return metadata_items

    # --------------------------------------------------
    # TUPLES AND LISTS
    # -------------------------------------------------
    def visit_tuplecontents(self, node, visited_children):
        """
        Processes tuple contents.
        """
        # tuplecontents = tupleitem ((inlinepadding)* listseparator (multilinepadding)* tupleitem)* (inlinepadding)* (listseparator (multilinepadding)*)?
        first_tuple_value, remaining_tuple_list, _, _ = visited_children
        tuple_values = [first_tuple_value]
        for tuple_item in remaining_tuple_list:
            _, _, _, tuple_value = tuple_item
            tuple_values.append(tuple_value)

        tuple_value = tuple(tuple_values)
        logging.getLogger("usdavisitor").info(f"TUPLE {tuple_value}")
        return tuple_value

    def visit_tupleitem(self, node, visited_children):
        """
        Processes a tuple item.
        """
        # tupleitem = atomicvalue / tuplevalue
        logging.getLogger("usdavisitor").info(f"TUPLE ITEM {visited_children[0]}")
        return visited_children[0]

    def visit_listcontents(self, node, visited_children):
        """
        Processes list contents.
        """
        # listcontents = listitem ((singlelinepadding)* statementseparator (multilinepadding)* listitem)* (singlelinepadding)* (statementseparator (multilinepadding)*)?
        first_list_value, remaining_list, _, _ = visited_children
        list_values = [first_list_value]
        for list_item in remaining_list:
            _, _, _, list_value = list_item
            list_values.append(list_value)

        logging.getLogger("usdavisitor").info(f"LIST {list_values}")
        return list_values

    def visit_listitem(self, node, visited_children):
        """
        Processes a list item.
        """
        # listitem = atomicvalue / listvalue / tuplevalue
        logging.getLogger("usdavisitor").info(f"LIST ITEM {visited_children[0]}")
        return visited_children[0]

    # --------------------------------------------------
    # VALUES
    # -------------------------------------------------
    def visit_number(self, node, visited_children):
        """
        Process a number.
        """
        # we return as text here, later it will get processed
        # into something matching the type of identifier it was
        # assigned to
        logging.getLogger("usdavisitor").info(f"NUMBER {node.text}")

        if (
            node.text == "inf"
            or node.text == "-inf"
            or node.text == "nan"
            or "." in node.text
            or "e" in node.text
            or "E" in node.text
        ):
            return float(node.text)

        # try to parse an integer
        try:
            return int(node.text)
        except:
            return float(node.text)

    def visit_baseidentifier(self, node, visited_children):
        """
        Processes a base identifier (one that can be a keyword).
        """
        logging.getLogger("usdavisitor").info(f"BASE IDENTIFIER {node.text}")
        return node.text

    def visit_keywordlessidentifier(self, node, visited_children):
        """
        Process an identifier that isn't a keyword.
        """
        logging.getLogger("usdavisitor").info(f"IDENTIFIER {node.text}")
        if node.text == "true":
            return True
        elif node.text == "false":
            return False

        return node.text

    def visit_string(self, node, visited_children):
        """
        Processes a string value.
        """
        # we want the interior of the string, not the quotes
        text = node.text
        if text.startswith('"""') or text.startswith("'''"):
            text = text[3 : len(text) - 3]
        else:
            text = text[1 : len(text) - 1]

        logging.getLogger("usdavisitor").info(f"STRING {text}")
        return text

    def visit_assetref(self, node, visited_children):
        """
        Processes an asset reference.
        """
        if node.text.startswith("@@@"):
            logging.getLogger("usdavisitor").info(f"ASSET REF {node.text[3 : len(node.text) - 3]}")
            return Asset(node.text[3 : len(node.text) - 3])
        else:
            logging.getLogger("usdavisitor").info(f"ASSET REF {node.text[1 : len(node.text) - 1]}")
            return Asset(node.text[1 : len(node.text) - 1])

    def visit_pathref(self, node, visited_children):
        """
        Processes a path reference.
        """
        path_ref = node.text[1 : len(node.text) - 1]
        if path_ref == "":
            return None

        if not path_ref.startswith("/"):
            # it's a relative path and needs to be converted
            base_path = ObjectPath.from_str(self._prim_paths[-1])
            return base_path.join(path_ref)

        return ObjectPath.from_str(path_ref)

    def visit_keywordbignone(self, node, visited_children):
        """
        Processes the None keyword.
        """
        logging.getLogger("usdavisitor").info("NONE")
        return None

    def visit_keywordcustomdata(self, node, visited_children):
        """
        Processes the customData keyword.
        """
        return node.text

    def visit_atomicvalue(self, node, visited_children):
        """
        Processes an atomic value.
        """
        # atomicvalue = number / identifier / string / assetref
        logging.getLogger("usdavisitor").info(f"ATOMIC VALUE {visited_children[0]}")
        return visited_children[0]

    def visit_tuplevalue(self, node, visisted_children):
        """
        Processes a tuple value.
        """
        # tuplevalue = leftparen (multilinepadding)* tuplecontents (multilinepadding)* rightparen
        _, _, tuple_value, _, _ = visisted_children
        logging.getLogger("usdavisitor").info(f"TUPLE VALUE {tuple_value}")
        return tuple_value

    def visit_listvalue(self, node, visited_children):
        """
        Processes a list value.
        """
        # listvalue = leftbracket (multilinepadding)* listcontents (multilinepadding)* rightbracket
        _, _, list_value, _, _ = visited_children
        logging.getLogger("usdavisitor").info(f"LIST VALUE {list_value}")
        return list_value

    def visit_arraytypevalue(self, node, visisted_children):
        """
        Processes an array type value.
        """
        return []

    def visit_typedvalue(self, node, visited_children):
        """
        Processes a typed value.
        """
        # the value has already been processed in the corresponding
        # child node, so we can just return that value
        # typedvalue = atomicvalue / tuplevalue / arraytype / listvalue / pathref
        logging.getLogger("usdavisitor").info(f"TYPED VALUE {visited_children[0]}")
        return visited_children[0]

    # --------------------------------------------------
    # DICTIONARIES
    # -------------------------------------------------
    def visit_dictionaryvalue(self, node, visited_children):
        """
        Processes a dictionary value.
        """
        # dictionaryvalue = leftcurlybrace (multilinepadding)* (dictionarycontents (multilinepadding)*)? rightcurlybrace
        _, _, dictionary_content, _ = visited_children
        if isinstance(dictionary_content, list):
            dictionary_content, _ = dictionary_content[0]
            return dictionary_content

        return {}

    def visit_dictionarycontents(self, node, visited_children):
        """
        Processes the contents of a dictionary.
        """
        # dictionarycontents = dictionaryvalueitem ((singlelinepadding)* statementseparator (multilinepadding)* dictionaryvalueitem)* (singlelinepadding)* (statementseparator (multilinepadding)*)?
        first_item, additional_items, _, _ = visited_children
        content = {first_item[0]: first_item[1]}
        if isinstance(additional_items, list):
            for additional_item in additional_items:
                _, _, _, next_item = additional_item
                content.update({next_item[0]: next_item[1]})

        return content

    def visit_dictionaryvalueitem(self, node, visited_children):
        """
        Processes a dictionary item.
        """
        # dictionaryvalueitem = (keyworddictionary (inlinepadding)+ dictionarykey assignment dictionaryvalue) / (dictionarytype (inlinepadding)+ dictionarykey assignment typedvalue)
        dictionary_type, _, key, _, value = visited_children[0]
        if isinstance(dictionary_type, Node):
            dictionary_type = dictionary_type.text

        if dictionary_type == "dictionary":
            if not isinstance(value, dict):
                raise ValueError(f"dictionary specified but value is of type {type(value).__name__}")
        elif dictionary_type.endswith("[]"):
            if not isinstance(value, list):
                raise ValueError(f"An array type was specified but value is of type {type(value).__name__}")
        elif dictionary_type == "string" or dictionary_type == "token":
            if type(value).__name__ != "str":
                raise ValueError(
                    f"The type {dictionary_type} was specified but value is of type {type(value).__name__}"
                )
        elif dictionary_type == "bool":
            if value == 0 or value == 1 or value == "true" or value == "false" or value == "True" or value == "False":
                if value == "false" or value == "False":
                    value = False
                else:
                    value = bool(value)
            else:
                raise ValueError(f"The type bool was specified but the value is of type {type(value).__name__}")
        else:
            if not (type(value).__name__ == dictionary_type):
                raise ValueError(
                    f"The type {dictionary_type} was specified but value is of type {type(value).__name__}"
                )

        return (key, value)

    def visit_dictionarykey(self, node, visited_children):
        """
        Processes a dictionary key.
        """
        # dictionarykey = string / baseidentifier
        return visited_children[0]

    def visit_dictionarytype(self, node, visited_children):
        """
        Processes a dictionary type.
        """
        # dictionarytype = identifier ((inlinepadding)* arraytype)?
        identifier, array_type = visited_children
        if isinstance(array_type, list):
            return identifier + "[]"
        else:
            return identifier

    # --------------------------------------------------
    # SPLINES
    # -------------------------------------------------
    def visit_splinemap(self, node, visited_children):
        """
        Processes a spline map.
        """
        # splinemap = leftcurlybrace (multilinepadding)* (splinemapcontents (multilinepadding)*)? rightcurlybrace
        spline_items = []
        _, _, spline_map_contents, _ = visited_children
        if isinstance(spline_map_contents, list):
            spline_items, _ = spline_map_contents[0]

        spline_curve_type = SplineCurveType.Bezier
        spline_loop_parameters = None
        spline_knots = []
        spline_knot_custom_data = {}
        spline_pre_extrapolation = None
        spline_post_extrapolation = None

        for spline_item in spline_items:
            if isinstance(spline_item, SplineCurveType):
                spline_curve_type = spline_item
            elif isinstance(spline_item, SplineLoopParameters):
                spline_loop_parameters = spline_item
            else:
                # it's a tuple - either an extrapolation or a knot item
                if isinstance(spline_item[0], SplineKnot):
                    # knot item
                    spline_knots.append(spline_item[0])
                    if spline_item[1] is not None:
                        spline_knot_custom_data.update({spline_item[0].time: spline_item[1]})
                else:
                    if spline_item[0] == "pre":
                        spline_pre_extrapolation = spline_item[1]
                    else:
                        spline_post_extrapolation = spline_item[1]

        return Spline(
            curve_type=spline_curve_type,
            pre_extrapolation=spline_pre_extrapolation,
            post_extrapolation=spline_post_extrapolation,
            loop_parameters=spline_loop_parameters,
            knots=spline_knots,
            knot_custom_data=spline_knot_custom_data,
        )

    def visit_splinemapcontents(self, node, visited_children):
        """
        Processes the content of a spline map.
        """
        # splinemapcontents = splineitem ((inlinepadding)* listseparator (multilinepadding)* splineitem)* (inlinepadding)* (listseparator (multilinepadding)*)?
        first_spline_item, other_spline_items, _, _ = visited_children
        spline_items = [first_spline_item]
        if isinstance(other_spline_items, list):
            for other_spline_item in other_spline_items:
                _, _, _, spline_item = other_spline_item
                spline_items.append(spline_item)

        return spline_items

    def visit_splineitem(self, node, visited_children):
        """
        Processes a spline item.
        """
        # splineitem = splinecurvetypeitem / splineextrapolationitem / splineloopitem / splineknotitem
        return visited_children[0]

    def visit_splinecurvetypeitem(self, node, visited_children):
        """
        Processes a spline curve.
        """
        # splinecurvetypeitem = keywordbezier / keywordhermite
        curve_type_value = visited_children[0].text
        return SplineCurveType[curve_type_value[0].upper() + curve_type_value[1:]]

    def visit_splineextrapolationitem(self, node, visited_children):
        """
        Processes a spline extrapolation item.
        """
        # splineextrapolationitem = (keywordpre (inlinepadding)* colon (inlinepadding)* splineextrapolation) / (keywordpost (inlinepadding)* colon (inlinepadding)* splineextrapolation)
        pre_post, _, _, _, extrapolation = visited_children[0]
        pre_post = pre_post.text

        return (pre_post, extrapolation)

    def visit_splineextrapolation(self, node, visited_children):
        """
        Processes a spline extrapolation.
        """
        # splineextrapolation = keywordnone / keywordheld / keywordlinear / (keywordsloped (inlinepadding)* leftparen (inlinepadding)* number (inlinepadding)* rightparen) / (keywordloop (inlinepadding)* loopoption)
        extrapolation = None
        option = visited_children[0]
        if isinstance(option, list):
            if len(option) == 1:
                if option[0].text == "none":
                    extrapolation_type = SplineExtrapolationMode.NoneMode
                else:
                    extrapolation_type = SplineExtrapolationMode[option[0].text[0].upper() + option[0].text[1:]]
                extrapolation = SplineExtrapolation(extrapolation_type)
            elif len(option) == 3:
                # loop type
                _, _, text_node = option
                loop_option = "loop" + text_node.text
                extrapolation_type = SplineExtrapolationMode[loop_option[0].upper() + loop_option[1:]]
                extrapolation = SplineExtrapolation(extrapolation_type)
            else:
                # sloped type
                _, _, _, _, slope_value, _, _ = option
                extrapolation = SplineExtrapolation(SplineExtrapolationMode.Sloped, slope_value)
        else:
            if option.text == "none":
                extrapolation = SplineExtrapolation(SplineExtrapolationMode.NoneMode)
            else:
                extrapolation = SplineExtrapolation(SplineExtrapolationMode[option.text[0].upper + option.text[1:]])

        return extrapolation

    def visit_loopoption(self, node, visited_children):
        """
        Processes a loop option.
        """
        # loopoption = keywordrepeat / keywordreset / keywordoscillate
        return visited_children[0].text

    def visit_splineloopitem(self, node, visited_children):
        """
        Processes a spline loop.
        """
        # splineloopitem = keywordloop (inlinepadding)* colon (inlinepadding)* leftparen (inlinepadding)* number (inlinepadding)* comma (inlinepadding)* number (inlinepadding)* comma (inlinepadding)* number (inlinepadding)* comma (inlinepadding)* number (inlinepadding)* comma (inlinepadding)* number (inlinepadding)* rightparen
        (
            _,
            _,
            _,
            _,
            _,
            _,
            proto_start,
            _,
            _,
            _,
            proto_end,
            _,
            _,
            _,
            num_pre_loops,
            _,
            _,
            _,
            num_post_loops,
            _,
            _,
            _,
            value_offset,
            _,
            _,
        ) = visited_children

        # perform basic validation on the values
        if type(num_pre_loops) is not int or type(num_post_loops) is not int:
            raise ValueError("Specified number of pre or post loops not an integer!")

        if num_pre_loops < 0:
            num_pre_loops = 0

        if num_post_loops < 0:
            num_post_loops = 0

        return SplineLoopParameters(proto_start, proto_end, num_pre_loops, num_post_loops, value_offset)

    def visit_splineknotitem(self, node, visited_children):
        """
        Processes a spline knot.
        """
        # splineknotitem = number (inlinepadding)* colon (inlinepadding)* splineknotvalues (inlinepadding)* (splineknotparameters)*
        knot_time, _, _, _, knot_values, _, parameters = visited_children
        pre_value = 0.0
        if knot_values[0] is not None:
            pre_value = knot_values[0]

        value = knot_values[1]
        pre_tan_slope = 0.0
        post_tan_slope = 0.0
        time = knot_time
        pre_tan_width = 0.0
        post_tan_width = 0.0
        next_interp_mode = SplineInterpMode.Held
        knot_custom_data = None
        if isinstance(parameters, list):
            for parameter in parameters[0]:
                if parameter[0] == "pre":
                    pre_tan_slope = parameter[1][0]
                    pre_tan_width = parameter[1][1]
                elif parameter[0] == "post":
                    next_interp_mode = parameter[1]
                    post_tan_slope = parameter[2][0]
                    post_tan_width = parameter[2][1]
                elif parameter[0] == "customData":
                    knot_custom_data = parameter[1]
                else:
                    raise ValueError(f"Unexpected knot parameter with key {parameter[0]}!")

        return (
            SplineKnot(
                time, pre_tan_width, post_tan_width, value, pre_value, pre_tan_slope, post_tan_slope, next_interp_mode
            ),
            knot_custom_data,
        )

    def visit_splineknotvalues(self, node, visited_children):
        """
        Processes spline knot values.
        """
        # splineknotvalues = (number (inlinepadding)* ampersand (inlinepadding)* number) / number
        pre_value = 0.0
        value = 0.0
        knot_values = visited_children[0]
        if isinstance(knot_values, list):
            pre_value, _, _, _, value = knot_values
        else:
            value = knot_values

        return (pre_value, value)

    def visit_splineknotparameters(self, node, visited_children):
        """
        Processes spline knot parameters.
        """
        # splineknotparameters = semicolon (inlinepadding)* splineknotparameterlist
        _, _, parameters = visited_children
        return parameters

    def visit_splineknotparameterlist(self, node, visited_children):
        """
        Processes a spline knot parameter list.
        """
        # splineknotparameterlist = splineknotparameter ((inlinepadding)* semicolon (inlinepadding)* splineknotparameter)*
        first_parameter, other_parameters = visited_children
        knot_parameters = [first_parameter]
        if isinstance(other_parameters, list):
            for other_parameter in other_parameters:
                _, _, _, next_parameter = other_parameter
                knot_parameters.append(next_parameter)

        return knot_parameters

    def visit_splineknotparameter(self, node, visited_children):
        """
        Processes a spline knot parameter.
        """
        # splineknotparameter = (keywordpre (inlinepadding)+ splinetangent) / (keywordpost (inlinepadding)+ splineinterpmode ((inlinepadding)+ splinetangent)?) / dictionaryvalue
        content = visited_children[0]
        if isinstance(content, list):
            pre_post, *_ = content
            pre_post = pre_post.text
            if pre_post == "pre":
                _, _, tangent = content
                return ("pre", tangent)
            else:
                _, _, interp_mode, tangent = content
                if isinstance(tangent, list):
                    _, tangent = tangent[0]
                else:
                    tangent = (0.0, 0.0)

                if interp_mode == "none":
                    return ("post", SplineInterpMode.NoneMode, tangent)
                else:
                    return ("post", SplineInterpMode[interp_mode[0].upper() + interp_mode[1:]], tangent)
        else:
            # it's a dictionary of custom data
            return ("customData", content)

    def visit_splineinterpmode(self, node, visited_children):
        """
        Processes a spline interp mode.
        """
        # splineinterpmode = keywordnone / keywordheld / keywordlinear / keywordcurve
        return visited_children[0].text

    def visit_splinetangent(self, node, visited_children):
        """
        Processes a spline tangent.
        """
        # splinetangent = leftparen (inlinepadding)* splinetangentcontent (inlinepadding)* rightparen
        _, _, tangent_content, _, _ = visited_children
        return tangent_content

    def visit_splinetangentcontent(self, node, visited_children):
        """
        Processes spline tangent content.
        """
        # splinetangentcontent = (number (inlinepadding)* comma (inlinepadding)* number) / number
        slope = 0.0
        width = 0.0
        tangent_content = visited_children[0]
        if isinstance(tangent_content, list):
            slope, _, _, _, width = tangent_content
        else:
            slope = tangent_content

        return (slope, width)

    # --------------------------------------------------
    # DEFAULT NODE VISITOR
    # -------------------------------------------------
    def generic_visit(self, node, visited_children):
        """
        Generic visitor node for those that don't have specific rules.
        """
        return visited_children or node
