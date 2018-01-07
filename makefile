all: $(patsubst %.org,docs/%.html,$(wildcard *.org))

docs/%.html: %.org
	emacs $< --batch -u `id -un` --eval '(load user-init-file)' -f org-html-export-to-html
	mv *.html docs/

clean:
	rm *.bbl *.pdf
