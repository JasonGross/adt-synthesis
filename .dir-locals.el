((nil . ((eval . (let ((default-directory (locate-dominating-file
						buffer-file-name ".dir-locals.el")))
			(make-local-variable 'compile-command)
			(setq compile-command (format "make -k --directory=\"%s\""
						      (expand-file-name ".")))))))
 (coq-mode . ((eval . (let ((default-directory (locate-dominating-file
						buffer-file-name ".dir-locals.el")))
			(make-local-variable 'coq-prog-args)
			(setq coq-prog-args `("-emacs" "-R" ,(expand-file-name "src") "ADTSynthesis" "-R" ,(expand-file-name "examples") "ADTExamples")))))))
