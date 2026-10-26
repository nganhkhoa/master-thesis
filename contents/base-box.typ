#import "/setup.typ": setupdoc
#show: setupdoc

#import "/models/language.typ": *

== #langb Language

We define #langb language and its syntax in @base-box-syntax. The language extends the PCF language with tuples and mutable cells (boxes). This will be the base language for both #langc and #lange.

#v(1em)
#include "/models/base-box.typ"
#v(1em)

#v(1em)
#include "/models/base-box-type-rules.typ"
#v(1em)

#v(1em)
#include "/models/base-box-reduction-rules.typ"
#v(1em)
