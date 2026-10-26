#import "/setup.typ": setupdoc
#show: setupdoc

#import "/models/language.typ": *

== #langb Language

We define #langb language and its syntax in @base-syntax. The language extends the PCF language with tuples. It has no mutable cells. This will be the base language for both #langc and #lange.

#v(1em)
#include "/models/base.typ"
#v(1em)

#v(1em)
#include "/models/base-type-rules.typ"
#v(1em)

#v(1em)
#include "/models/base-reduction-rules.typ"
#v(1em)
