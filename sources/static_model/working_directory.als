abstract sig WDObject{
	
	wdparent: lone Dir
}

sig File, Dir extends WDObject{}

one sig Root extends Dir{}

pred inv[]{

	//a Object cannot ascend from itself
	no ^wdparent & iden

	//all Objects descend from a root
 	WDObject in *wdparent.Root
}

fact{
	 inv[]

}

run{
} for 5
