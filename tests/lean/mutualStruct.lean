mutual

-- | allow structures in mutual inductive blocks.
structure Foo where
  int: Int
  bar: Bar

inductive Bar where
| mk: Bar
| foo: Foo -> Bar
end


#print Foo
#print Bar
def fooBar : Foo := { int := 0, bar := (Bar.mk) }
#check fooBar
