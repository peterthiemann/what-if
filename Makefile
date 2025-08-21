.PHONY: final

final:
	rm -f tex.zip 
	zip -r tex tex -x \*/auto/\* -x \*.json -x \*.md -x \*.txt -x \*.cut -x \*.gz
