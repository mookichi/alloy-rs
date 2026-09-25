one sig x, xx, v2 extends EReal
fact {
	erealMul[x, x, xx]
	setEReal[v2, 2.0]
	xx.erealCovers[v2]
	
}
run for 0, 16 int
