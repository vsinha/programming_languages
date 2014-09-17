;;;usm.nw:4200
(class True Boolean ()
  (method ifTrue:ifFalse: (trueBlock falseValue) (value trueBlock))
  (method ifTrue:  (trueBlock) (value trueBlock))
  (method ifFalse: (falseBlock) nil)

  (method & (aBoolean) aBoolean)
  (method | (aBoolean) self)
  (method not () false)
  (method eqv: (aBoolean) aBoolean)
  (method xor: (aBoolean) (not aBoolean))
)
;;;usm.nw:4212
(class False Boolean ()
  (method ifTrue:ifFalse: (trueBlock falseBlock) (value falseBlock))
  (method ifTrue:  (trueBlock) nil)
  (method ifFalse: (falseBlock) (value falseBlock))

  (method & (aBoolean) self)
  (method | (aBoolean) aBoolean)
  (method not () true)
  (method xor: (aBoolean) aBoolean)
  (method eqv: (aBoolean) (not aBoolean))
)
