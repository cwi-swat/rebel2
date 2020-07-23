module ropebridge

open util/ordering[State] as ord

sig State {
  far: set Object,
  near: set Object,
  totalTime: one Int
}

abstract sig Object {}

abstract sig Adventurer extends Object {
	timeToCross: one Int
}

one sig A1,A2,A3,A4 extends Adventurer {} 

one sig Torch extends Object {}

fact travelTimes {
  A1.timeToCross = 1
  A2.timeToCross = 2
  A3.timeToCross = 5
  A4.timeToCross = 10
}

fact NoQuantumAdventurers {
  all s: State | no s.(far & near)
}

fact EverybodyHasAPlace {
  all s:State | Object = s.(far+near)
} 

pred cross[from, from', to, to': Object, s,s':State] {
  some a,b: from-Torch | {
    from' = from - Torch - (a+b) 
    to'= to + Torch + a + b 
    a.timeToCross.gt[b.timeToCross] implies
      s'.totalTime = s.totalTime.plus[a.timeToCross] else 
      s'.totalTime = s.totalTime.plus[b.timeToCross] 
  }
}

fact SomebodyCrossesEachTime {
  all s: State, s': ord/next[s] | {
    Torch in s.near implies
      cross[s.near,s'.near,s.far,s'.far,s,s'] else
      cross[s.far,s'.far,s.near, s'.near,s,s']   
  }
}

fact Initial {
  ord/first.near = Object
  ord/first.totalTime = 0
}

fact goal {
  Object = ord/last.far && ord/last.totalTime = 17
}

pred show {}
run show for 6 State, 6 Int

run show for 6 State, 10 Int
