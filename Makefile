.PHONY: fstar
fstar:
	fstar.exe fstar/difc.fst

.PHONY: stats
stats:
	fstar.exe fstar/difc.fst --query_stats
