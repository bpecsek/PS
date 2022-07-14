(eval-when (:compile-toplevel :load-toplevel :execute)
  (unless (find-package :ps-system)
    (defpackage "PS-SYSTEM"
      (:use "COMMON-LISP" "ASDF"))))

(in-package :ps-system)

(defsystem "ps"
  :description "A trivial production system"
  :version "0.1"
  :license "LLGPL"
  :author "Bela Pecsek"
  :mailto "bela.pecsek@gmail.com"
  :source-control "https://github.com/bpecsek/PS"
  :depends-on ("kr")
  :serial t
  :components ((:file "packages")
               ;(:file "reader-macros")
               (:file "utils")
               (:file "for")
               (:file "unifier")
               (:file "ps")))
