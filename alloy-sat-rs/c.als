one sig x, xx, d, dd, p extends Real
check {
	{
		realGT[x, 0.0]
		realGT[d, 0.0]
		realMul[x, x, xx]
		realMul[d, d, dd]
		realLTE[xx, (2.0)]
		realGT[dd, (2.0)]  
	} implies {
		realLT[x, p]
		realLT[p, d]
	}
}
check for 10 int

