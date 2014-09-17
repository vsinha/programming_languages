;;;usm.nw:10284
(class LargeInteger Integer
  (magnitude)
  (class-method withMagnitude: (aNatural) 
      (magnitude: (new self) aNatural))
  (method magnitude () magnitude)
  (method magnitude: (aNatural) 
      (set magnitude aNatural)
      self)
  (class-method new: (anInteger)
     (if (negative anInteger) 
        [(magnitude: (new LargeNegativeInteger) (new: Natural (negated anInteger)))]
        [(magnitude: (new LargePositiveInteger) (new: Natural anInteger))]))
  (method asLargeInteger () self)
  (method isZero () (isZero magnitude))
  (method = (anInteger) (isZero   (- self anInteger)))
  (method < (anInteger) (negative (- self anInteger)))
)
