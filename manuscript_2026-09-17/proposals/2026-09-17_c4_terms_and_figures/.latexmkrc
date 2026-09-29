# Project-local build configuration.  The stock ICLR source loads the legacy
# PSNFSS `times` package, whose intended engine is pdfLaTeX.
$pdf_mode   = 1;
$pdflatex   = 'pdflatex -synctex=1 -file-line-error -interaction=nonstopmode %O %S';
$bibtex     = 'bibtex %O %B';
$max_repeat = 5;

# Please keep the red and black wrappers' auxiliary files in separate folders.
# Ordinary builds retain the historical build/ directory.
my $build_dir = $ENV{'MANUSCRIPT_BUILD_DIR'} // 'build';

use File::Path qw(make_path);
make_path($build_dir) unless -d $build_dir;

$out_dir = $build_dir;
$aux_dir = $build_dir;
