#lang racket/base

(require scriblib/autobib)

(provide comp/classical
         bidi-system-l
         basics-bidirectional
         bidirectional-typing
         quantitative)


(define comp/classical
  (make-bib
   #:title "Compiling with Classical Connectives"
   #:author (authors "Paul Downen" "Zena M. Ariola")
   #:date 2020
   #:location (journal-location "Logical Methods in Computer Science"
                                #:volume 16
                                #:number 3
                                #:pages '("13:1" "13:57"))
   #:url "https://arxiv.org/pdf/1907.13227"))

(define bidi-system-l
  (make-bib
   #:title "Canonical Bidirectional Typing via Polarised System L"
   #:author (authors "Zanzi Mihejevs")
   #:date 2025
   #:location (webpage-location "https://www.youtube.com/watch?v=0Qg_RnSHyhU"
                                #:accessed "2025-06-11")
   #:url "https://glaive-research.org/Resources/PolarisedSystemL.pdf"))

(define basics-bidirectional
  (make-bib
   #:title "basics of bidirectionalism"
   #:author (authors "Conor McBride")
   #:date 2018
   #:location (webpage-location "https://pigworker.wordpress.com/2018/08/06/basics-of-bidirectionalism/"
                                #:accessed "2025-06-11")))

(define bidirectional-typing
  (make-bib
   #:title "Bidirectional Typing"
   #:author (authors "Jana Dunfield" "Neel Krishnaswami")
   #:date 2021
   #:location (journal-location "ACM Computing Surveys"
                                #:volume 54
                                #:number 5)
   #:doi "https://doi.org/10.1145/3450952"))

(define quantitative
  (make-bib
   #:title "The Syntax and Semantics of Quantitative Type Theory"
   #:author (authors "Bob Atkey")
   #:date 2018
   #:location (proceedings-location "LICS '18: 33rd Anual ACM/IEEE Symposium on Logic in Computer Science"
                                    #:pages '(56 65))
   #:doi "https://doi.org/10.1145/3209108.3209189"))
