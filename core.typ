#import "models/language.typ": *

== Core Language

We define *Core* language and its syntax in @core-syntax. The language extends the PCF language with tuples and mutable cells. This will be the base language for both #langc and #lange.

#include "models/core.typ"
