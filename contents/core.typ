#import "/models/language.typ": *

== #langb Language

We define #langb language and its syntax in @core-syntax. The language extends the PCF language with tuples and mutable cells. This will be the base language for both #langc and #lange.

#v(1em)
#include "/models/core.typ"
#v(1em)

#v(1em)
#include "/models/core-type-rules.typ"
#v(1em)

#v(1em)
#include "/models/core-reduction-rules.typ"
#v(1em)
