# latexmkrc — Configuration for latexmk
# Usage: cd docs/thesis && latexmk -pdf main.tex
# Clean: latexmk -C

$pdf_mode = 1;            # Generate PDF via pdflatex
$out_dir  = 'build';      # All generated files go into build/
$bibtex_use = 2;          # Run biber when needed
$biber = 'biber %O %S';   # Use biber (not bibtex) for biblatex
$pdflatex = 'pdflatex -interaction=nonstopmode -halt-on-error %O %S';
$clean_ext = 'bbl blg run.xml bcf fdb_latexmk fls synctex.gz';
$success_cmd = "cp $out_dir/main.pdf .";  # Copy PDF to thesis root after build
