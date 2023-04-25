;;(require 'compile)

;; based on: http://ergoemacs.org/emacs/elisp_syntax_coloring.html

;; syntax table
;;(defvar hacky-syntax-table (make-syntax-table))

(defface labrat-directive
  '((t :foreground "dim gray"
       :background "pale turquoise"
       :weight bold
       :underline t
       ))
  "Face for directives."
  :group 'labrat )

(defface labrat-response-error
  '((t :foreground "dim gray"
       :background "light salmon"
       :weight bold
       :underline t
       ))
  "Face for error directive responses."
  :group 'labrat )

(defface labrat-response-success
  '((t :foreground "dark gray"
       :background "pale green"
       :weight bold
       :underline t
       ))
  "Face for successful directive responses."
  :group 'labrat )

;; define the mode
(define-derived-mode labrat-mode octave-mode
  "LabRat mode"
  ;; handling comments
  :syntax-table (make-syntax-table)
  ;; code for syntax highlighting
  (font-lock-add-keywords nil '(("^\s*%>[^%|^\n]+" . 'labrat-directive)))
  (font-lock-add-keywords nil '(("^\s*%<.+" . 'labrat-response-error)))
  (font-lock-add-keywords nil '(("^\s*%<\s*renamed[^%|^\n]+" . 'labrat-response-success)))
  (setq mode-name "labrat")
  ;; clear memory
  ;;(setq typos-keywords-regexp nil)
  ;;(setq typos-operators-regexp nil)
)

;; Customisation options

(defgroup labrat nil
  "A Matlab helper."
  :group 'languages)

(defcustom labrat-command "labrat"
  "The path to the LabRat command to run."
  :type 'string
  :group 'labrat)

(defface labrat-highlight-error-face
  '((t (:underline (:color "red" :style wave))))
  "The face used for errors.")

(defun labrat-run-on-file (labrat-file)
  "Run LabRat on the current buffer and replace the buffer contents with the LabRat output."

  (save-some-buffers compilation-ask-about-save
                     (when (boundp 'compilation-save-buffers-predicate)
                       compilation-save-buffers-predicate))

  (let ((labrat-command-to-run (concat labrat-command " " labrat-file)))
    (with-current-buffer (current-buffer)
     (let ((old-point (point)))
          (erase-buffer)
          (insert (shell-command-to-string labrat-command-to-run))
          (goto-char old-point)))))

;;;###autoload
(defun labrat-run (override-options)
  "Run LabRat on the current file."
  (interactive "P")
    (labrat-run-on-file (shell-quote-argument (buffer-file-name))))

(define-key labrat-mode-map (kbd "C-c C-l") 'labrat-run)

(provide 'labrat-mode)
