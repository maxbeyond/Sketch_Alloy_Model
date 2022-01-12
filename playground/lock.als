sig Key {}

sig Lock {
	key: set Key
}

pred NoKey[l: Lock] {
	no l.key
}

one sig LockA, LockB extends Lock {}

fact {
//	NoKey[LockA]
	NoKey[LockB]
}

assert checkNoKey {
	no LockA.key
}

check checkNoKey for 5