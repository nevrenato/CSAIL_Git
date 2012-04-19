abstract sig WDObject{
	wdparent: lone Dir
}

sig File, Dir extends WDObject{}

one sig Root extends Dir{}

pred inv[]{
	//objects from parent on a state s, belongs to that state
	wdparent  in WDObject -> Dir
	//a Object cannot ascend from itself
	no ^wdparent & iden
	//all Objects desdends from a root
  	//wdobjects.s in *(wdparent.s).(Root & wdobjects.s)
 	WDObject in ^wdparent.WDObject + Root
}

fact{
	 inv[]
	// debug purposes
}


run{
} for 3
