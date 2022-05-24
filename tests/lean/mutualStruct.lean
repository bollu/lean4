mutual

-- | allow structures in mutual inductive blocks.
structure Foo where
  fooint: Int
  bar: Bar

inductive Bar where
| bar1: Bar
| bar2: Bar
end


#print Foo
#print Bar
def fooBar : Foo := { fooint := 0, bar := (Bar.bar1) }
#check fooBar
