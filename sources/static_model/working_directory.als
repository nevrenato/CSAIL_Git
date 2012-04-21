open sha

abstract sig WDObject{
	wdparent: lone Dir
}

sig File extends WDObject{
	content: Sha 
}

sig Dir extends WDObject{}

one sig Root extends Dir{}

pred invWD[]{

	//a Object cannot ascend from itself
	no ^wdparent & iden

	//all Objects descend from a root
 	WDObject in *wdparent.Root
}

fact{
	 invWD[]

}

run{
} for 5
