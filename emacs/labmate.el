;;(require 'compile)

;; based on: http://ergoemacs.org/emacs/elisp_syntax_coloring.html

;; syntax table
;;(defvar hacky-syntax-table (make-syntax-table))

(defface labmate-directive
  '((t :foreground "black"
       :background "pale turquoise"
       :weight bold
       ))
  "Face for directives."
  :group 'labmate )

(defface labmate-response-delimiter
  '((t :foreground "black"
       :background "pale green"
       ))
  "Face for response delimiters."
  :group 'labmate )


(defface labmate-response-error
  '((t :foreground "black"
       :background "light salmon"
       :weight bold
       ))
  "Face for errorneous directive responses."
  :group 'labmate )

(defface labmate-response-success
  '((t :foreground "black"
       :background "pale green"
       :weight bold
       ))
  "Face for successful directive responses."
  :group 'labmate )

;; define the mode
(define-derived-mode labmate-mode octave-mode
  "LabMate mode"
  ;; handling comments
  :syntax-table (make-syntax-table)
  ;; code for syntax highlighting
  (font-lock-add-keywords nil '(("^\s*%>[^%\n]+" 0 'labmate-directive t)))
  (font-lock-add-keywords nil '(("^\s*%<.+" . 'labmate-response-error)))
  (font-lock-add-keywords nil '(("^\s*%<[{}]$" . 'labmate-response-delimiter)))
  (font-lock-add-keywords nil '(("^\s*%<\s*renamed[^%\n]+" . 'labmate-response-success)))
  (font-lock-add-keywords nil '(("^\s*%<\s*.*::[^%\n]+" . 'labmate-response-success)))
  (font-lock-add-keywords nil '(("^\s*%<\s*LabMate[^%\n]+" . 'labmate-response-success)))
  ;; Fold generated code
  (hs-minor-mode)

  (setq mode-name "labmate")
)



;; Customisation options

(defgroup labmate nil
  "A Matlab helper."
  :group 'languages)

(defcustom labmate-command "labmate"
  "The path to the LabMate command to run."
  :type 'string
  :group 'labmate)

(defcustom labmate-hide-generated-code nil
  "Determine if generated code should be hidden after running LabMate."
  :type 'boolean
  :group 'labmate)


(defface labmate-highlight-error-face
  '((t (:underline (:color "red" :style wave))))
  "The face used for errors.")

(defun labmate-run-on-file (labmate-file)
  "Run LabMate on the current buffer and replace the buffer contents with the LabMate output."

  (save-some-buffers compilation-ask-about-save
                     (when (boundp 'compilation-save-buffers-predicate)
                       compilation-save-buffers-predicate))

  (let* ((res (with-temp-buffer
               (list (call-process labmate-command nil
                                   (current-buffer) nil labmate-file)
                     (buffer-string))))
         (exitcode (car res))
         (output (cadr res)))
    (if (< exitcode 10)
        (with-current-buffer (current-buffer)
          (let ((old-point (point)))
          (erase-buffer)
          (insert output)
          (goto-char old-point)))
        (message "%s" output))))

;;;###autoload
(defun labmate-run (override-options)
  "Run LabMate on the current file."
  (interactive "P")
  (labmate-run-on-file (shell-quote-argument (buffer-file-name)))
  (when labmate-hide-generated-code (hs-hide-all))
)

(define-key labmate-mode-map (kbd "C-c C-l") 'labmate-run)

(provide 'labmate-mode)
