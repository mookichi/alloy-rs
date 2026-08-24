module m15
sig Book { addr: Book -> Book }
check { all b, b", b"", n, t: Book |
	not some n.(b.addr)
	and b".addr = b.addr + n->t
	and b"".addr = b.addr - n->t
	implies b.addr = b"".addr } for 2
