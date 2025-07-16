#lang racket/base

(require redex/reduction-semantics)

(provide BS-raw
         BS-exec
         BS-elab
         kind-type
         kind-=
         type-≼
         bindings-snoc
         var-check
         var-synth
         discharge-▽binding
         discharge-△binding
         requirements-+
         requirements-⊔
         requirements-⊓
         modes-+
         modes-⊔
         modes-⊓
         modes-≼
         modes-=
         usage-≼
         usage-+
         usage-×
         cut
         △consumer
         focused-△consumer
         ▽producer
         focused-▽producer
         △producer
         focused-△producer
         ▽consumer
         focused-▽consumer
         maybe-substitute
         maybe-substitute2
         red/BS)
  

(define-language BS-raw
  [p producer ::= w {let/C ▽χ κ ↦ k} {let/C △χ ↦ k}]
  [w weak-head ::=
     x
     () (pair w w) (ιl w) (ιr w)
     (pack f) (dn v-) (UP w)
     {⊤} {[] ↦ k} {[duo ▽χ ▽χ] ↦ k} {[πl ▽χ] ↦ k \| [πr ▽χ] ↦ k}
     {[throw ▽χ] ↦ k} {[up △χ] ↦ k} {[DN ▽χ] ↦ k}]
  [v+ positive-value ::= w]
  [v- negative-value ::= p]
  [c consumer ::= f {let/P ▽χ κ ↦ k} {let/P △χ ↦ k}]
  [f forcing ::=
     x
     [] [duo f f] [πl f] [πr f]
     [throw w] [up q+] [DN f]
     {𝟘} {() ↦ k} {(pair ▽χ ▽χ) ↦ k} {(ιl ▽χ) ↦ k \| (ιr ▽χ) ↦ k}
     {(pack ▽χ) ↦ k} {(dn △χ) ↦ k} {(UP ▽χ) ↦ k}]
  [q+ positive-question ::= c]
  [q- negative-question ::= f]
  [k command ::= [cmd p ⇒ c]]
  [x ::= variable-not-otherwise-mentioned]
  [▽χ checked-bind ::= x (nope τ~ κ)]
  [△χ synthesizing-bind ::= (△var x (τ κ) α) (nope (τ~ κ))]
  [α mode-vector ::= (modes) (modes ρ)]
  [ρ usage ::= 1 ω]
  [κ kind ::= + -]
  [τ~ pretype ::=
     𝟘 𝟙 (τ ⊗ τ) (τ ⊕ τ)
     (⊖ τ) (↓ τ) (⇓ τ)
     ⊤ ⊥ (τ ⅋ τ) (τ & τ)
     (¬ τ) (↑ τ) (⇑ τ)]
  [τ type ::= τ~ (@ τ~ α)]
  #:binding-forms
  (nope τ~ κ) #:exports nothing
  (nope (τ~ κ)) #:exports nothing
  (△var x (τ κ) α) #:exports x
  {let/P ▽χ ↦ k #:refers-to ▽χ}
  {let/P △χ ↦ k #:refers-to △χ}
  {let/C ▽χ ↦ k #:refers-to ▽χ}
  {let/C △χ ↦ k #:refers-to △χ}
  {(pair ▽χ_0 ▽χ_1) ↦ k #:refers-to (shadow ▽χ_0 ▽χ_1)}
  {(ιl ▽χ_0) ↦ k_0 #:refers-to ▽χ_0 \| (ιr ▽χ_1)v ↦ k_1 #:refers-to ▽χ_1}
  {[duo ▽χ_0 ▽χ_1] ↦ k #:refers-to (shadow ▽χ_0 ▽χ_1)}
  {[πl ▽χ_0] ↦ k_0 #:refers-to ▽χ_0 \| [πl ▽χ_1] ↦ k_1 #:refers-to ▽χ_1}
  {(pack ▽χ) ↦ k #:refers-to ▽χ}
  {[up △χ] ↦ k #:refers-to △χ}
  {(UP ▽χ) ↦ k #:refers-to ▽χ}
  {[throw ▽χ] ↦ k #:refers-to ▽χ}
  {(dn △χ) ↦ k #:refers-to △χ}
  {[DN ▽χ] ↦ k #:refers-to ▽χ})



(define-extended-language BS-exec BS-raw
  [P ::= W {let/C X ↦ K}]
  [W ::=
     x () (pair W W) (ιl W) (ιr W)
     (pack F) (dn V-) (UP W)
     {⊤} {[] ↦ K} {[duo X X] ↦ K} {[πl X] ↦ K \| [πr X] ↦ K}
     {[throw X] ↦ k} {[up X] ↦ k} {[DN X] ↦ k}]
  [V+ ::= W]
  [V- ::= P]
  [C ::= F {let/P X ↦ K}]
  [F ::=
     x [] [duo F F] [πl F] [πr F]
     [throw W] [up Q+] [DN F]
     {𝟘} {() ↦ K} {(pair X X) ↦ K} {(ιl X) ↦ K \| (ιr X) ↦ K}
     {(pack X) ↦ k} {(dn X) ↦ k} {(UP X) ↦ k}]
  [Q+ ::= C]
  [Q- ::= F]
  [K ::= [CMD P ⇒ C]]
  [X ::= x none]
  #:binding-forms
  none #:exports nothing
  {[duo X_0 X_1] ↦ K #:refers-to (shadow X_0 X_1)}
  {[πl X_0] ↦ K_0 #:refers-to X_0 \| [πr X_1] ↦ K_1 #:refers-to X_1}
  {(pair X_0 X_1) ↦ K #:refers-to (shadow X_0 X_1)}
  {(ιl X_0) ↦ K_0 #:refers-to X_0 \| (ιr X_1) ↦ K_1 #:refers-to X_1}
  {let/P X ↦ K #:refers-to X}
  {let/C X ↦ K #:refers-to X}
  {(throw X) ↦ k #:refers-to X}
  {(up X) ↦ k #:refers-to X}
  {(DN X) ↦ k #:refers-to X}
  {(pack X) ↦ k #:refers-to X}
  {(dn X) ↦ k #:refers-to X}
  {(UP X) ↦ k #:refers-to X})



(define-extended-language BS-elab BS-exec
  [χ ::= ▽χ △χ]
  [Γ binding-context ::= (γ ...)]
  [γ variable-binding ::= (▽bound x o) (△bound x o (τ κ) α)]
  [o orientation ::= prod con]
  [Ξ requirements ::= ∅ (ξ ...)]
  [ξ variable-requirement ::= (req x o τ κ) (req x o (τ κ) α)])




(define-judgment-form BS-elab
  #:mode (var-check I I I)
  #:contract (var-check x o Γ)

  [(var-check x o (_ ... (▽bound x o) _ ...))])

(define-judgment-form BS-elab
  #:mode (var-synth I I O O O I)
  #:contract (var-synth x o τ κ α Γ)

  [(var-synth x o τ κ α (_ ... (△bound x o (τ κ) α) _ ...))])




(define-metafunction BS-elab
  bindings-snoc : Γ χ o -> Γ

  [(bindings-snoc (γ ...) x o) (γ ... (▽bound x o))]
  [(bindings-snoc Γ (nope τ κ) o) Γ]
  [(bindings-snoc (γ ...) (△var x (τ κ) α) o) (γ ... (△bound x o (τ κ) α))]
  [(bindings-snoc Γ (nope τ κ α) o) Γ])





(define-judgment-form BS-elab
  #:mode (usage-≼ I I)
  #:contract (usage-≼ ρ ρ)

  [--------
   (usage-≼ 1 1)]

  [--------
   (usage-≼ ω ω)]

  [--------
   (usage-≼ ω 1)])


(define-metafunction BS-elab
  usage-+ : ρ ρ -> ρ

  [(usage-+ 1 1) ω]
  [(usage-+ ω 1) ω]
  [(usage-+ 1 ω) ω]
  [(usage-+ ω ω) ω])

(define-metafunction BS-elab
  usage-× : ρ ρ -> ρ

  [(usage-× 1 ρ) ρ]
  [(usage-× ρ 1) ρ]
  [(usage-× ω ω) ω])




(define-metafunction BS-elab
  modes-+ : α α -> α

  [(modes-+ (modes) α) α]
  [(modes-+ α (modes)) α]
  [(modes-+ (modes ρ) (modes ρ_′)) (modes (usage-+ ρ ρ_′))])


(define-metafunction BS-elab
  modes-× : α α -> α

  [(modes-× (modes) α) (modes)]
  [(modes-× α (modes)) (modes)]
  [(modes-× (modes ρ) (modes ρ_′)) (modes (usage-× ρ ρ_′))])


(define-judgment-form BS-elab
  #:mode (modes-≼ I I)
  #:contract (modes-≼ α α)

  [--------
   (modes-≼ α (modes))]

  [(usage-≼ ρ ρ_′)
   --------
   (modes-≼ (modes ρ) (modes ρ_′))]

  [--------
   (modes-≼ (modes) α)])


(define-judgment-form BS-elab
  #:mode (modes-= I I)
  #:contract (modes-= α α)

  [(modes-≼ α α_′)
   (modes-≼ α_′ α)
   --------
   (modes-= α α_′)])


(define-metafunction BS-elab
  modes-⊔ : α α -> α

  [(modes-⊔ α α_′) α
                   (judgment-holds (modes-≼ α_′ α))]
  [(modes-⊔ α α_′) α_′
                   (judgment-holds (modes-≼ α α_′))])

(define-metafunction BS-elab
  modes-⊓ : α α -> α

  [(modes-⊓ α α_′) α
                   (judgment-holds (modes-≼ α α_′))]
  [(modes-⊓ α α_′) α_′
                   (judgment-holds (modes-≼ α_′ α))])



(define-metafunction BS-elab
  requirements-+ : Ξ Ξ -> Ξ

  [(requirements-+ ∅ Ξ) ∅]
  [(requirements-+ Ξ ∅) ∅]
  [(requirements-+ (ξ_l1 ... ξ_l ξ_l2 ...) (ξ_r1 ... ξ_r ξ_r2 ...))
   (requirements-+ (ξ_l1 ... ξ_l2 ...) (ξ_r1 ... ξ ξ_r2 ...))
   (where (req x o τ_l κ_l α_l) ξ_l)
   (where (req x o τ_r κ_r α_r) ξ_r)
   (judgment-holds (kind-= κ_l κ_r))
   (judgment-holds (type-≼ τ_l τ_r κ_l))
   (where ξ (req x o τ_l κ_l (modes-+ α_l α_r)))]
  [(requirements-+ (ξ_l ...) (ξ_r ...)) (ξ_l ... ξ_r ...)])


(define-metafunction BS-elab
  requirements-⊔ : Ξ Ξ -> Ξ

  [(requirements-⊔ ∅ Ξ) Ξ]
  [(requirements-⊔ Ξ ∅) Ξ]
  [(requirements-⊔ (ξ_l1 ... ξ_l ξ_l2 ...) (ξ_r1 ... ξ_r ξ_r2 ...))
   (requirements-⊔ (ξ_l1 ... ξ_l2 ...) (ξ_r1 ... ξ ξ_r2 ...))
   (where (req x o τ_l κ_l α_l) ξ_l)
   (where (req x o τ_r κ_r α_r) ξ_r)
   (judgment-holds (kind-= κ_l κ_r))
   (judgment-holds (type-≼ τ_l τ_r κ_l))
   (where ξ (req x o τ_l κ_l (modes-⊔ α_l α_r)))]
  [(requirements-⊔ (ξ_l ...) (ξ_r ...)) (ξ_l ... ξ_r ...)])


(define-metafunction BS-elab
  requirements-⊓ : Ξ Ξ -> Ξ

  [(requirements-⊓ ∅ Ξ) Ξ]
  [(requirements-⊓ Ξ ∅) Ξ]
  [(requirements-⊓ (ξ_l1 ... ξ_l ξ_l2 ...) (ξ_r1 ... ξ_r ξ_r2 ...))
   (requirements-⊓ (ξ_l1 ... ξ_l2 ...) (ξ_r1 ... ξ ξ_r2 ...))
   (where (req x o τ_l κ_l α_l) ξ_l)
   (where (req x o τ_r κ_r α_r) ξ_r)
   (judgment-holds (kind-= κ_l κ_r))
   (judgment-holds (type-≼ τ_l τ_r κ_l))
   (where ξ (req x o τ_l κ_l (modes-⊓ α_l α_r)))]
  [(requirements-⊓ (ξ_l ...) (ξ_r ...)) (ξ_l ... ξ_r ...)])





(define-judgment-form BS-elab
  #:mode (kind-type I I)
  #:contract (kind-type τ κ)

  [---------- "𝟘"
   (kind-type (@ 𝟘 α) +)]

  [---------- "𝟙"
   (kind-type (@ 𝟙 α) +)]

  [(modes-≼ (modes-⊔ α_1 α_2) α) (kind-type (@ τ~_1 α_1) +) (kind-type (@ τ~_2 α_2) +)
   ---------- "⊗"
   (kind-type (@ ((@ τ~_1 α_1) ⊗ (@ τ~_2 α_2)) α) +)]

  [(modes-≼ (modes-⊓ α_l α_r) α) (kind-type (@ τ~_l α_l) +) (kind-type (@ τ~_r α_r) +)
   ---------- "⊕"
   (kind-type (@ ((@ τ~_l α_l) ⊕ (@ τ~_r α_r)) α) +)]

  [---------- "⊤"
   (kind-type (@ ⊤ α) -)]

  [---------- "⊥"
   (kind-type (@ ⊥ α) -)]

  [(modes-≼ (modes-⊔ α_1 α_2) α) (kind-type (@ τ~_1 α_1) -) (kind-type (@ τ~_2 α_2) -)
   ---------- "⅋"
   (kind-type (@ ((@ τ~_1 α_1) ⅋ (@ τ~_2 α_2)) α) -)]

  [(modes-≼ (modes-⊓ α_l α_r) α) (kind-type (@ τ~_l α_l) -) (kind-type (@ τ~_r α_r) -)
   ---------- "&"
   (kind-type (@ ((@ τ~_l α_l) & (@ τ~_r α_r)) α) -)]

  [(modes-≼ α_′ α) (kind-type (@ τ~ α_′) -)
   ---------- "⊖"
   (kind-type (@ (⊖ (@ τ~ α_′)) α) +)]

  [(kind-type τ -)
   ---------- "↓"
   (kind-type (@ (↓ τ) α) +)]

  [(modes-≼ α_′ α) (kind-type (@ τ~ α_′) +)
   ---------- "⇑"
   (kind-type (@ (⇑ (@ τ~ α_′)) α) -)]

  [(modes-≼ α_′ α) (kind-type (@ τ~ α_′) +)
   ---------- "¬"
   (kind-type (@ (¬ (@ τ~ α_′)) α) -)]

  [(kind-type τ +)
   ---------- "↑"
   (kind-type (@ (↑ τ) α) -)]

  [(modes-≼ α_′ α) (kind-type (@ τ~ α_′) -)
   ---------- "⇓"
   (kind-type (@ (⇓ (@ τ~ α_′)) α) +)])


(module+ test
  
  (test-judgment-holds (kind-type (@ ((@ 𝟙 (modes 1)) ⊗ (@ 𝟙 (modes))) (modes 1)) +))

  (test-judgment-holds (kind-type (@ ((@ ((@ 𝟙 (modes ω)) ⊗ (@ 𝟙 (modes 1))) (modes 1)) ⊗ (@ 𝟙 (modes ω))) (modes 1)) +))

  (test-judgment-holds (kind-type (@ ((@ 𝟘 (modes)) ⊕ (@ 𝟘 (modes))) (modes)) +))

  (test-judgment-holds (kind-type (@ ((@ ⊥ (modes ω)) ⅋ (@ ⊥ (modes ω))) (modes ω)) -))

  (test-judgment-holds (kind-type (@ ((@ ⊤ (modes 1)) & (@ ⊤ (modes ω))) (modes)) -))

  (test-judgment-holds (kind-type (@ ((@ ⊤ (modes ω)) & (@ ((@ ⊤ (modes ω)) & (@ ⊤ (modes ω))) (modes ω))) (modes ω)) -))
  )


(define-judgment-form BS-elab
  #:mode (kind-= I I)
  #:contract (kind-= κ κ)

  [-------
   (kind-= + +)]

  [-------
   (kind-= - -)])


(define-judgment-form BS-elab
  #:mode (type-≼ I I I)
  #:contract (type-≼ τ τ κ)

  [(modes-≼ α α_′)
   ------- "𝟘_="
   (type-≼ (@ 𝟘 α) (@ 𝟘 α_′) +)]

  [(modes-≼ α α_′)
   ------- "𝟙_="
   (type-≼ (@ 𝟙 α) (@ 𝟙 α_′) +)]

  [(modes-≼ α α_′) (type-≼ τ_1 τ_1′ +) (type-≼ τ_2 τ_2 +)
   ------- "⊗_="
   (type-≼ (@ (τ_1 ⊗ τ_2) α) (@ (τ_1′ ⊗ τ_2′) α_′) +)]

  [(modes-≼ α α_′) (type-≼ τ_l τ_l′ +) (type-≼ τ_r τ_r′ +)
   ------- "⊕_="
   (type-≼ (@ (τ_l ⊕ τ_r) α) (@ (τ_l′ ⊕ τ_r′) α_′) +)]

  [(modes-≼ α α_′) (type-≼ τ τ_′ -)
   ------- "⊖_="
   (type-≼ (@ (⊖ τ) α) (@ (⊖ τ_′) α_′) +)]

  [(modes-≼ α α_′) (type-≼ τ τ_′ -)
   ------- "↓_="
   (type-≼ (@ (↓ τ) α) (@ (↓ τ_′) α_′) +)]

  [(modes-≼ α α_′) (type-≼ τ τ_′ +)
   ------- "⇑_="
   (type-≼ (@ (⇑ τ) α) (@ (⇑ τ_′) α_′) -)]

  [(modes-≼ α α_′)
   ------- "⊥_="
   (type-≼ (@ ⊤ α) (@ ⊤ α_′) -)]

  [(modes-≼ α α_′)
   ------- "⊤_="
   (type-≼ (@ ⊥ α) (@ ⊥ α_′) -)]

  [(modes-≼ α α_′) (type-≼ τ_1 τ_1′ -) (type-≼ τ_2 τ_2′ -)
   ------- "⅋_="
   (type-≼ (@ (τ_1 ⅋ τ_2) α) (@ (τ_1′ ⅋ τ_2′) α_′) -)]

  [(modes-≼ α α_′) (type-≼ τ_l τ_l′ -) (type-≼ τ_r τ_r′ -)
   ------- "&_="
   (type-≼ (@ (τ_l & τ_r) α) (@ (τ_l′ & τ_r′) α_′) -)]

  [(modes-≼ α α_′) (type-≼ τ τ_′ +)
   ------- "¬_="
   (type-≼ (@ (¬ τ) α) (@ (¬ τ_′) α_′) -)]

  [(type-≼ τ τ_′ +) (modes-= α α_′)
   ------- "↑_="
   (type-≼ (↑ τ α) (↑ τ_′ α_′) -)]

  [(modes-≼ α α_′) (type-≼ τ τ_′ -)
   ------- "⇓_="
   (type-≼ (@ (⇓ τ) α) (@ (⇓ τ_′) α_′) +)])


(define-judgment-form BS-elab
  #:mode (type-~ I I I)
  #:contract (type-~ τ τ κ)

  [(type-≼ τ τ_′ κ) (type-≼ τ_′ τ κ)
   -------
   (type-~ τ τ_′ κ)])




(define-judgment-form BS-elab
  #:mode (discharge-▽binding I I O O O O)
  #:contract (discharge-▽binding Ξ ▽χ Ξ X τ κ)

  [-------------------
   (discharge-▽binding (ξ_1 ... (req x o τ κ) ξ_2 ...) x (ξ_1 ... ξ_2 ...) x τ κ)]

  [-------------------
   (discharge-▽binding Ξ (nope τ~ κ) Ξ none (@ τ~ (modes)) κ)])


(define-judgment-form BS-elab
  #:mode (discharge-△binding I I O O O O O)
  #:contract (discharge-△binding Ξ △χ Ξ X τ κ α)

  [-------------------
   (discharge-△binding Ξ (nope τ~ κ) Ξ none (@ τ~ (modes)) κ (modes))]

  [-------------------
   (discharge-△binding (ξ_1 ... (req x o (τ κ) α) ξ_n ...) (△var x (τ κ) α) (ξ_1 ... ξ_n ...) x τ κ α)])



(define-judgment-form BS-elab
  #:mode (cut I I O O)
  #:contract (cut Γ k Ξ K)

  [(△consumer Γ c Ξ_1 C τ κ) (▽producer Γ p Ξ_2 κ τ P)
   ----
   (cut Γ [cmd p ⇒ c] (requirements-+ Ξ_1 Ξ_2) [CMD P ⇒ C])]

  [(△producer Γ p Ξ_1 P τ κ) (▽consumer Γ c Ξ_2 κ τ C)
   ----
   (cut Γ [cmd p ⇒ c] (requirements-+ Ξ_1 Ξ_2) [CMD P ⇒ C])])

  

(define-judgment-form BS-elab
  #:mode (△consumer I I O O O O)
  #:contract (△consumer Γ c Ξ C τ κ)

  [(cut (bindings-snoc Γ ▽χ prod) k Ξ K) (discharge-▽binding Ξ ▽χ Ξ_′ X τ κ)
   ----------"△let_P"
   (△consumer Γ {let/P ▽χ κ ↦ k} Ξ_′ {let/P X ↦ K} τ κ)]

  [(focused-△consumer Γ f Ξ F τ κ)
   ---------- "F_△C"
   (△consumer Γ f Ξ F τ κ)])




(define-judgment-form BS-elab
  #:mode (focused-△consumer I I O O O O)
  #:contract (focused-△consumer Γ f Ξ F τ κ)

  [(var-synth x con τ κ α Γ)
   ------------------ "△Var_C"
   (focused-△consumer Γ x ((req x con (τ κ) α)) x τ κ)]
  
  [------------------ "𝟘_C"
   (focused-△consumer Γ {𝟘} ∅ {𝟘} (@ 𝟘 (modes)) +)]
  
  [(cut Γ k Ξ K)
   ------------------ "𝟙_C"
   (focused-△consumer Γ {() ↦ k} Ξ {() ↦ K} (@ 𝟙 (modes 1)) +)]

  [(cut (bindings-snoc (bindings-snoc Γ ▽χ_1 prod) ▽χ_2 prod) k Ξ K)
   (discharge-▽binding Ξ ▽χ_1 Ξ_′ X_1 (@ τ~_1 α_1) +) (discharge-▽binding Ξ_′ ▽χ_2 Ξ_′′ X_2 (@ τ~_2 α_2) +)
   ------------------ "⊗_C"
   (focused-△consumer Γ {(pair ▽χ_1 ▽χ_2) ↦ k} Ξ_′′ {(pair X_1 X_2) ↦ K} (@ ((@ τ~_1 α_1) ⊗ (@ τ~_2 α_2)) (modes-⊔ α_1 α_2)) +)]

  [(cut (bindings-snoc Γ ▽χ_l prod) k_l Ξ_l K_l) (discharge-▽binding Ξ_l ▽χ_l Ξ_l′ X_l (@ τ~_l α_l) +)
   (cut (bindings-snoc Γ ▽χ_r prod) k_r Ξ_r K_r) (discharge-▽binding Ξ_r ▽χ_r Ξ_r′ X_r (@ τ~_r α_r) +)
   ------------------ "⊕_C"
   (focused-△consumer Γ {(ιl ▽χ_l) ↦ k_l \| (ιr ▽χ_r) ↦ k_r}
    (requirements-⊓ Ξ_l′ Ξ_r′) {(ιl X_l) ↦ K_l \| (ιr X_r) ↦ K_r} (@ ((@ τ~_l α_l) ⊕ (@ τ~_r α_r)) (modes-⊓ α_l α_r)) +)]

  [(cut (bindings-snoc Γ ▽χ con) k Ξ K) (discharge-▽binding Ξ ▽χ Ξ_′ X (@ τ~ α) -)
   ------------------ "⊖_C"
   (focused-△consumer Γ {(pack ▽χ) ↦ k} Ξ_′ {(pack X) ↦ K} (@ (⊖ (@ τ~ α)) α) +)]

  [(cut (bindings-snoc Γ △χ prod) k Ξ K) (discharge-△binding Ξ △χ Ξ_′ X τ - α)
   ------------------ "↓_C"
   (focused-△consumer Γ {(dn △χ) ↦ k} Ξ_′ {(dn X) ↦ K} (@ (↓ τ) α) +)]

  [(cut (bindings-snoc Γ ▽χ prod) k Ξ K) (discharge-▽binding Ξ ▽χ Ξ_′ X (@ τ~ α) +)
   ------------------ "⇑_C"
   (focused-△consumer Γ {(⇑ ▽χ) ↦ k} Ξ_′ {(⇑ X) ↦ K} (@ (⇑ (@ τ~ α)) α) -)])




(define-judgment-form BS-elab
  #:mode (▽producer I I O I I O)
  #:contract (▽producer Γ p Ξ κ τ P)

  #;[(cut (bindings-snoc Γ △χ con) k Ξ K) (discharge-△binding Ξ △χ Ξ_′ X τ κ α) (type-= τ τ_′ κ)
   ---------- "▽let_C"
   (▽producer Γ {let/C △χ ↦ k} Ξ_′ κ τ_′ {let/C X ↦ K} α)]

  [(focused-▽producer Γ w Ξ κ τ W)
   ---------- "F_▽P"
   (▽producer Γ w Ξ κ τ W)])



(define-judgment-form BS-elab
  #:mode (focused-▽producer I I O I I O)
  #:contract (focused-▽producer Γ w Ξ κ τ W)

  [(var-check x prod Γ)
   ------------------ "▽Var_P"
   (focused-▽producer Γ x ((req x prod τ κ)) κ τ x)]
  
  [------------------ "𝟙_P"
   (focused-▽producer Γ () () + (@ 𝟙 α) ())]
  
  [(focused-▽producer Γ w_1 Ξ_1 + τ_1 W_1) (focused-▽producer Γ w_2 Ξ_2 + τ_2 W_2)
   ------------------ "⊗_P"
   (focused-▽producer Γ (pair w_1 w_2) (requirements-+ Ξ_1 Ξ_2) + (@ (τ_1 ⊗ τ_2) α) (pair W_1 W_2))]

  [(focused-▽producer Γ w Ξ + τ_l W)
   ------------------ "⊕_Pl"
   (focused-▽producer Γ (ιl w) Ξ + (@ (τ_l ⊕ τ_r) α) (ιl W))]

  [(focused-▽producer Γ w Ξ + τ_r W)
   ------------------ "⊕_Pr"
   (focused-▽producer Γ (ιr w) Ξ + (@ (τ_l ⊕ τ_r) α) (ιr W))]

  [(focused-▽consumer Γ f Ξ - τ F)
   ------------------ "⊖_P"
   (focused-▽producer Γ (pack f) Ξ + (@ (⊖ τ) α) (⊖ F))]

  [(△producer Γ v- Ξ V- τ_′ -) (type-≼ τ τ_′ -)
   ------------------ "↓_P"
   (focused-▽producer Γ (dn v-) Ξ + (@ (↓ τ) α) (dn V-))]

  [(focused-▽producer Γ w Ξ + τ W)
   ------------------ "⇑_P"
   (focused-▽producer Γ (UP w) Ξ - (@ (⇑ τ) α) (UP W))])




(define-judgment-form BS-elab
  #:mode (△producer I I O O O O)
  #:contract (△producer Γ p Ξ P τ~ κ)

  #;[(cut (bindings-snoc Γ ▽χ con) k Ξ K) (discharge-▽binding Ξ ▽χ Ξ_′ X τ κ)
   ---------- "△let_C"
   (△producer Γ {let/C ▽χ κ ↦ k} Ξ_′ {let/C X ↦ K} τ~ κ)]

  [(focused-△producer Γ w Ξ W τ~ κ)
   ---------- "F_△P"
   (△producer Γ w Ξ W τ~ κ)])



(define-judgment-form BS-elab
  #:mode (focused-△producer I I O O O O)
  #:contract (focused-△producer Γ w Ξ W τ~ κ)

  #;[(var-synth x prod τ κ α α_1 Γ)
   ------------------ "△Var_P"
   (focused-△producer Γ x ((req x prod (τ κ α) α_1)) x τ κ)]

  [------------------ "⊤_P"
   (focused-△producer Γ {⊤} ∅ {⊤} (@ ⊤ (modes)) -)]

  [(cut Γ k Ξ K)
   ------------------ "⊥_P"
   (focused-△producer Γ {[] ↦ k} Ξ {[] ↦ K} (@ ⊥ (modes 1)) -)]

  [(cut (bindings-snoc (bindings-snoc Γ ▽χ_1 con) ▽χ_2 con) k Ξ K)
   (discharge-▽binding Ξ ▽χ_1 Ξ_′ X_1 (@ τ~_1 α_1) -) (discharge-▽binding Ξ_′ ▽χ_2 Ξ_′′ X_2 (@ τ~_2 α_2) -)
   ------------------ "⅋_P"
   (focused-△producer Γ {[duo ▽χ_1 ▽χ_2] ↦ k} Ξ_′′ {[duo X_1 X_2] ↦ K} (@ ((@ τ~_1 α_1) ⅋ (@ τ~_2 α_2)) (modes-⊔ α_1 α_2)) -)]

  [(cut (bindings-snoc Γ ▽χ_l con) k_l Ξ_l K_l) (discharge-▽binding Ξ_l ▽χ_l Ξ_l′ X_l (@ τ~_l α_1) -)
   (cut (bindings-snoc Γ ▽χ_r con) k_r Ξ_r K_r) (discharge-▽binding Ξ_r ▽χ_r Ξ_r′ X_r (@ τ~_r α_2) -)
   ------------------ "&_P"
   (focused-△producer Γ {[πl ▽χ_l] ↦ k_l \| [πr ▽χ_r] ↦ k_r}
    (requirements-⊓ Ξ_l′ Ξ_r′) {[πl X_l] ↦ K_l \| [πr X_r] ↦ K_r} (@ ((@ τ~_l α_1) & (@ τ~_r α_2)) (modes-⊓ α_1 α_2)) -)]

  [(cut (bindings-snoc Γ ▽χ prod) k Ξ K) (discharge-▽binding Ξ ▽χ Ξ_′ X (@ τ~ α) +)
   ------------------ "¬_P"
   (focused-△producer Γ {[throw ▽χ] ↦ k} Ξ_′ {[throw X] ↦ K} (@ (¬ (@ τ~ α)) α) -)]

  [(cut (bindings-snoc Γ △χ con) k Ξ K) (discharge-△binding Ξ △χ Ξ_′ X τ + α)
   ------------------ "↑_P"
   (focused-△producer Γ {[up △χ] ↦ k} Ξ_′ {[up X] ↦ K} (@ (↑ τ) α) -)]

  [(cut (bindings-snoc Γ ▽χ con) k Ξ K) (discharge-▽binding Ξ ▽χ Ξ_′ X (@ τ~ α) -)
   ------------------ "⇓_P"
   (focused-△producer Γ {[DN ▽χ] ↦ k} Ξ_′ {[DN X] ↦ K} (@ (⇓ (@ τ~ α)) α) +)])




(define-judgment-form BS-elab
  #:mode (▽consumer I I O I I O)
  #:contract (▽consumer Γ c Ξ κ τ C)

  #;[(valid-△bind △χ) (cut (bindings-snoc Γ △χ prod) k Ξ K) (discharge-△binding Ξ △χ Ξ_′ X τ κ α) (type-= τ τ_′ κ)
   ---------- "▽let_P"
   (▽consumer Γ {let/P △χ ↦ k} Ξ_′ κ τ_′ {let/P X ↦ K} α)]

  [(focused-▽consumer Γ f Ξ κ τ F)
   ---------- "F_▽C"
   (▽consumer Γ f Ξ κ τ F)])

  

(define-judgment-form BS-elab
  #:mode (focused-▽consumer I I O I I O)
  #:contract (focused-▽consumer Γ f Ξ κ τ F)

  [(var-check x con Γ)
   ------------------ "▽Var_C"
   (focused-▽consumer Γ x ((req x con τ κ)) κ τ x)]

  [------------------ "⊥_C"
   (focused-▽consumer Γ [] () - (@ ⊥ α) [])]

  [(focused-▽consumer Γ f_1 Ξ_1 - τ_1 F_1) (focused-▽consumer Γ f_2 Ξ_2 - τ_2 F_2)
   ------------------ "⅋_C"
   (focused-▽consumer Γ [duo f_1 f_2] (requirements-+ Ξ_1 Ξ_2) - (@ (τ_1 ⅋ τ_2) α) [duo F_1 F_2])]

  [(focused-▽consumer Γ f Ξ - τ_l F)
   ------------------ "&_Cl"
   (focused-▽consumer Γ [πl f] Ξ - (@ (τ_l & τ_r) α) [πl F])]

  [(focused-▽consumer Γ f Ξ - τ_r F)
   ------------------ "&_Cr"
   (focused-▽consumer Γ [πr f] Ξ - (@ (τ_l & τ_r) α) [πr F])]

  [(focused-▽producer Γ w Ξ + τ~ W)
   ------------------ "¬_C"
   (focused-▽consumer Γ [throw w] Ξ - (¬ (@ τ~ α)) [throw W])]

  [(△consumer Γ q+ Ξ Q+ τ_′ +) (type-≼ τ τ_′ +)
   ------------------ "↑_C"
   (focused-▽consumer Γ [up q+] Ξ - (@ (↑ τ) α) [up Q+])]

  [(focused-▽consumer Γ f Ξ - τ F)
   ------------------ "⇓_C"
   (focused-▽consumer Γ [DN f] Ξ + (@ (⇓ τ) α) [DN F])])




(define-metafunction BS-elab
  maybe-substitute : K X any -> K

  [(maybe-substitute K x any) (substitute K x any)]
  [(maybe-substitute K none any) K])

(define-metafunction BS-elab
  maybe-substitute2 : K X any X any -> K

  [(maybe-substitute2 K X_1 any_1 X_2 any_2) (substitute K [X_1 any_1] [X_2 any_2])]
  [(maybe-substitute2 K none any_1 X_2 any_2) (substitute K X_2 any_2)]
  [(maybe-substitute2 K X_1 any_1 none any_2) (substitute K X_1 any_1)])



(define red/BS
  (reduction-relation
   BS-elab
   #:domain K
   #:codomain K

   [--> [CMD V+ ⇒ {let/P X ↦ K}]
        (maybe-substitute K X V+)
        "let V+_β"]

   [--> [CMD {let/C X ↦ K} ⇒ Q+]
        (maybe-substitute K X Q+)
        "let Q+_β"]

   [--> [CMD () ⇒ {() ↦ K}]
        K
        "𝟙_β"]

   [--> [CMD (pair W_1 W_2) ⇒ {(pair X_1 X_2) ↦ K}]
        (maybe-substitute2 K X_1 W_1 X_2 W_2)
        "⊗_β"]

   [--> [CMD (ιl W) ⇒ {(ιl X_l) ↦ K_l \| (ιr X_r) ↦ K_r}]
        (maybe-substitute K_l X_l W)
        "⊕l_β"]

   [--> [CMD (ιr W) ⇒ {(ιl X_l) ↦ K_l \| (ιr X_r) ↦ K_r}]
        (maybe-substitute K_r X_r W)
        "⊕r_β"]

   [--> [CMD (pack F) ⇒ {(pack X) ↦ K}]
        (maybe-substitute K X F)
        "⊖_β"]

   [--> [CMD (dn V-) ⇒ {(dn X) ↦ K}]
        (maybe-substitute K X V-)
        "↓_β"]

   [--> [CMD (UP W) ⇒ {(UP X) ↦ K}]
        (maybe-substitute K X W)
        "⇑_β"]

   [--> [CMD {let/C X ↦ K} ⇒ Q-]
        (maybe-substitute K X Q-)
        "let Q−_β"]

   [--> [CMD V- ⇒ {let/P X ↦ K}]
        (maybe-substitute K X V-)
        "let V−_β"]

   [--> [CMD {[] ↦ K} ⇒ []]
        K
        "⊥_β"]

   [--> [CMD {[duo X_1 X_2] ↦ K} ⇒ [duo F_1 F_2]]
        (maybe-substitute2 K X_1 F_1 X_2 F_2)
        "⅋_β"]

   [--> [CMD {[πl X_l] ↦ K_l \| [πr X_r] ↦ K_r} ⇒ [πl F]]
        (maybe-substitute K_l X_l F)
        "&l_β"]

   [--> [CMD {[πl X_l] ↦ K_l \| [πr X_r] ↦ K_r} ⇒ [πr F]]
        (maybe-substitute K_r X_r F)
        "&r_β"]

   [--> [CMD {(throw X) ↦ K} ⇒ (throw W)]
        (maybe-substitute K X W)
        "¬_β"]

   [--> [CMD {(up X) ↦ K} ⇒ (up Q+)]
        (maybe-substitute K X Q+)
        "↑_β"]

   [--> [CMD {(DN X) ↦ K} ⇒ (DN F)]
        (maybe-substitute K X F)
        "⇓_β"]))


(module+ test

  (define-syntax-rule (mk-CMD prod con)
    (term [CMD prod ⇒ con]))

  (define-syntax match+
    (syntax-rules ()
      [(match+ () body) (term (() ↦ body))]
      [(match+ b1 b2 body) (term ((pair b1 b2) ↦ body))]
      [(match+ (bl bodyl) (br bodyr)) (term ((ιl bl) ↦ bodyl \| (ιr br) ↦ bodyr))]))

  (define-syntax match-
    (syntax-rules ()
      [(match- () body) (term ([] ↦ body))]
      [(match- b1 b2 body) (term ([duo b1 b2] ↦ body))]
      [(match- (bl bodyl) (br bodyr)) (term ([πl bl] ↦ bodyl \| [πr br] ↦ bodyr))]))

  (define-syntax-rule (test-->/BS start step)
    (test--> red/BS (term start) (term step)))

  (define-syntax-rule (test-->>/BS start step)
    (test-->> red/BS (term start) (term step)))

  (define-term dummy-end [CMD x_end-prod ⇒ x_end-con])


  (test-->/BS
   ,(mk-CMD () ,(match+ () dummy-end))
   dummy-end)

  (test-->/BS
   ,(mk-CMD ,(match- [] dummy-end) [])
   dummy-end)

  (test-->>/BS
   ,(mk-CMD {let/C x ↦ ,(mk-CMD () x)}  ,(match+ () dummy-end))
   dummy-end)

  (test-->>/BS
   ,(mk-CMD ,(match- [] dummy-end) {let/P x ↦ ,(mk-CMD x [])})
   dummy-end)

  (test-->>/BS
   ,(mk-CMD
     (pair () ())
     ,(match+ x_0 x_1
              ,(mk-CMD x_0 ,(match+ () ,(mk-CMD x_1 ,(match+ () dummy-end))))))
   dummy-end)

  (test-->>/BS
   ,(mk-CMD
     (ιl (ιr ()))
     ,(match+
       (x_1l ,(mk-CMD
               x_1l
               ,(match+
                 (x_2l ,(mk-CMD x_y x_z))
                 (x_2r ,(mk-CMD x_2r ,(match+ () dummy-end))))))
       (x_1r ,(mk-CMD x_a x_b))))
   dummy-end)

  (test-->>/BS
   ,(mk-CMD
     ,(match-
       x_0 x_1
       ,(mk-CMD
         ,(match- [] ,(mk-CMD ,(match- [] dummy-end) x_1))
         x_0))
     [duo [] []])
   dummy-end)
  )




(module* typeset #f

  (require racket/match
           (only-in racket/list flatten)
           redex/pict
           pict)

    
  (provide make-literal-pict
           make-active-nonterminal
           with-my-rewriters
           pretty-term
           pretty-metafunction-sig)

  (define (make-literal-pict base
                             #:pre-sub [pre-sub #false]
                             #:pre-sup [pre-sup #false]
                             #:post-sub [post-sub #false]
                             #:post-sup [post-sup #false])
    (define base* (text base (literal-style)))
    (define pre-sub* (and pre-sub (text pre-sub (cons 'subscript (literal-style)))))
    (define pre-sup* (and pre-sup (text pre-sup (cons 'superscript (literal-style)))))
    (define post-sub* (and post-sub (text post-sub (cons 'subscript (literal-style)))))
    (define post-sup* (and post-sup (text post-sup (cons 'superscript (literal-style)))))
    (define pre
      (match* (pre-sub* pre-sup*)
        [(#false #false) #false]
        [(pre-sub #false) pre-sub]
        [(#false pre-sub) pre-sub]
        [(pre-sub pre-sup) (vr-append pre-sub pre-sup)]))
    (define post
      (match* (post-sub* post-sup*)
        [(#false #false) #false]
        [(post-sub #false) post-sub]
        [(#false post-sub) post-sub]
        [(post-sub post-sup) (vl-append post-sub post-sup)]))
    (match* (pre post)
      [(#false #false) base*]
      [(pre #false) (hb-append 1 pre base*)]
      [(#false post) (hb-append 1 base* post)]
      [(pre post) (hb-append 1 pre base* post)]))


  (define (make-active-nonterminal base kind)
    (hb-append 1
               (text base (non-terminal-style))
               (text kind (non-terminal-superscript-style))))


  (define (prettify . stuff)
    (flatten (list "" stuff "")))

  (define (prettify/elab-term ξ t Ξ T #:ty [ty #false] #:focused? [focused? #false])
    (define syntactic-turnstile (text (if focused? " ⊩ " " ⊢ ") (literal-style)))
    (define semantic-turnstile (text (if focused? " ⊫" " ⊨") (literal-style)))
    (define syntactic-fence (if ty
                                (list (hb-append syntactic-turnstile (orientation-script ty #true)) " ")
                                (list syntactic-turnstile " ")))
    (define semantic-fence (if ty
                               (list (hb-append semantic-turnstile (orientation-script ty #true)) " ")
                               (list semantic-turnstile " ")))
    (prettify "⟦" (list ξ syntactic-fence t) "⟧ ↝ " (list Ξ semantic-fence T)))

  (define (orientation-script type sub?)
    (define script (if sub? 'subscript 'superscript))
    (match type
      ['o (text "o" (cons script (non-terminal-style)))]
      ['prod (text "P" (cons script (literal-style)))]
      ['con (text "C" (cons script (literal-style)))]))


  (define (bind-or-var x o)
    (list x (orientation-script o #false)))

  
  (define (prettify/elab-synth ξ t Ξ T τ κ #:ty ty #:focused? [focused? #false])
    (prettify/elab-term ξ t Ξ (list T " ∈ " τ " ∈ " κ) #:ty ty #:focused? focused?))

  (define (prettify/elab-check ξ t Ξ κ τ T #:ty ty #:focused? [focused? #false])
    (prettify/elab-term ξ t Ξ (list κ " ∋ " τ " ∋ " T) #:ty ty #:focused? focused?))

  
  (define (with-my-rewriters proc)
    (with-compound-rewriters
        (['pair (match-λ [(list _ _ p_1 p_2 _)
                          (prettify "(" p_1 ", " p_2 ")")])]
         ['duo (match-λ [(list _ _ c_1 c_2 _)
                         (prettify "[" c_1 ", " c_2 "]")])]
         ['cmd (match-λ [(list _ _ p ⇒ c _)
                         (prettify p ⇒ c)])]
         ['CMD (match-λ [(list _ _ P ⇒ C _)
                         (prettify P ⇒ C)])]
         ['▽var (match-λ [(list _ _ x τ _)
                         (prettify x " : " τ)])]
         ['△var (match-λ [(list _ _ x τ κ _)
                          (prettify x " : " τ ": " κ)]
                         [(list _ _ x τ κ α _)
                          (prettify x " : " τ " : " κ " @ " α)])]
         ['modes (match-λ [(list _ _ ρ _)
                           (prettify "⟨" ρ "⟩")])]
         ['▽bound (match-λ [(list _ _ x o _)
                                 (prettify x (orientation-script (lw-e o) #false))])]
         ['△bound (match-λ [(list _ _ x o τ κ _)
                                 (prettify (list x (orientation-script (lw-e o) #false) " : " τ " : " κ))])]
         ['nope (match-λ [(list _ _ τ _)
                          (prettify "_ : " τ)]
                         [(list _ _ τ κ _)
                          (prettify "_ : " τ " : " κ)])]
         ['req (match-λ [(list _ _ x o τ κ _)
                         (prettify (bind-or-var x (lw-e o)) " : " τ " : " κ)])]
         ['var-check (match-λ [(list _ _ x o Γ _)
                               (prettify x (orientation-script (lw-e o) #false) " ∈ " Γ)])]
         ['var-synth (match-λ [(list _ _ x o τ κ Γ _)
                               (prettify x " : " τ " : " κ " ∈ " Γ)])]
         ['valid-▽bind (match-λ [(list _ _ χ κ _)
                                 (prettify χ " : " κ " ok")])]
         ['valid-△bind (match-λ [(list _ _ χ _)
                                 (prettify χ " ok")])]
         ['bindings-snoc (match-λ [(list _ _  ξ χ o _)
                                   (prettify ξ ", " (bind-or-var χ (lw-e o)))])]
         ['discharge-▽binding (match-λ [(list _ _ Ξ χ Ξ_′ X τ κ _)
                                        (prettify  Ξ "⟦" χ "⟧ ↝ " Ξ_′ "; " X " : " τ " : " κ)])]
         ['discharge-△binding (match-λ [(list _ _ Ξ χ Ξ_′ X τ κ _)
                                        (prettify  Ξ "⟦" χ "⟧ ↝ " Ξ_′ "; " X " : " τ " : " κ)])]
         ['kind-type (match-λ [(list _ _ τ κ _)
                               (prettify τ " : " κ)])]
         ['kind-= (match-λ [(list _ _ κ_1 κ_2 _)
                            (prettify κ_1 " = " κ_2)])]
         ['type-= (match-λ [(list _ _ τ_1 τ_2 κ _)
                            (prettify τ_1 " = " τ_2 " : " κ)])]
         ['modes-= (match-λ [(list _ _ α?_1 α?_2 _)
                             (prettify α?_1 " = " α?_2)])]
         ['modes-≼ (match-λ [(list _ _ α?_1 α?_2 _)
                             (prettify α?_1 " ≼ " α?_2)])]
         ['modes-+ (match-λ [(list _ _ α?_1 α?_2 _)
                             (prettify α?_1 " + " α?_2)])]
         ['modes-⊔ (match-λ [(list _ _ α?_1 α?_2 _)
                             (prettify α?_1 " ⊔ " α?_2)])]
         ['modes-⊓ (match-λ [(list _ _ α?_1 α?_2 _)
                             (prettify α?_1 " ⊓ " α?_2)])]
         ['requirements-+ (match-λ [(list _ _ Ξ_1 Ξ_2 _)
                                    (prettify Ξ_1 " + " Ξ_2)])]
         ['requirements-⊔ (match-λ [(list _ _ Ξ_1 Ξ_2 _)
                                    (prettify Ξ_1 " ⊔ " Ξ_2)])]
         ['requirements-⊓ (match-λ [(list _ _ Ξ_1 Ξ_2 _)
                                    (prettify Ξ_1 " ⊓ " Ξ_2)])]
         ['usage-≼ (match-λ [(list _ _ ρ_1 ρ_2 _)
                             (prettify ρ_1 " ≼ " ρ_2)])]
         ['usage-+ (match-λ [(list _ _ ρ_0 ρ_1 _)
                             (prettify ρ_0 " + " ρ_1)])]
         ['usage-× (match-λ [(list _ _ ρ_0 ρ_1 _)
                             (prettify ρ_0 " × " ρ_1)])]
         ['cut (match-λ [(list _ _ ξ k Ξ K _)
                         (prettify/elab-term ξ k Ξ K)])]
         ['△consumer (match-λ [(list _ _ ξ c Ξ C τ κ _)
                               (prettify/elab-synth ξ c Ξ C τ κ #:ty 'con)])]
         ['focused-△consumer (match-λ [(list _ _ ξ c Ξ C τ κ _)
                                       (prettify/elab-synth ξ c Ξ C τ κ #:ty 'con #:focused? #true)])]
         ['▽producer (match-λ [(list _ _ ξ p τ κ Ξ P _)
                               (prettify/elab-check ξ p τ κ Ξ P #:ty 'prod)])]
         ['focused-▽producer (match-λ [(list _ _ ξ p τ κ Ξ P _)
                                       (prettify/elab-check ξ p τ κ Ξ P #:ty 'prod #:focused? #true)])]
         ['△producer (match-λ [(list _ _ ξ p Ξ P τ κ _)
                               (prettify/elab-synth ξ p Ξ P τ κ #:ty 'prod)])]
         ['focused-△producer (match-λ [(list _ _ ξ p Ξ P τ κ _)
                                       (prettify/elab-synth ξ p Ξ P τ κ #:ty 'prod #:focused? #true)])]
         ['▽consumer (match-λ [(list _ _ ξ c τ κ Ξ C _)
                               (prettify/elab-check ξ c τ κ Ξ C #:ty 'con)])]
         ['focused-▽consumer (match-λ [(list _ _ ξ c τ κ Ξ C _)
                                       (prettify/elab-check ξ c τ κ Ξ C #:ty 'con #:focused? #true)])]
         ['substitute (match-λ [(list _ _ t (lw (list _ v_1 e_1 _) _ _ _ _ _ _) (lw (list _ v_2 e_2 _) _ _ _ _ _ _) _)
                                (prettify t "[" v_1 " := " e_1 ", " v_2 " := " e_2 "]")]
                               [(list _ _ t v e _)
                                (prettify t "[" v " := " e "]")])]
         ['maybe-substitute (match-λ [(list _ _ K X T _)
                                      (prettify K "[" X " := " T "]")])]
         ['maybe-substitute2 (match-λ [(list _ _ K X_1 T_1 X_2 T_2 _)
                                       (prettify K "[" X_1 " := " T_1 ", " X_2 " := " T_2 "]")])])
      (with-atomic-rewriters
          (['- "−"]
           ['none "_"]
           ['prod "P"]
           ['con "C"]
           ['ιl (λ () (make-literal-pict "ι" #:post-sub "l"))]
           ['ιr (λ () (make-literal-pict "ι" #:post-sub "r"))]
           ['πl (λ () (make-literal-pict "π" #:post-sub "l"))]
           ['πr (λ () (make-literal-pict "π" #:post-sub "r"))]
           ['let/P (λ () (make-literal-pict "let" #:post-sub "P"))]
           ['let/C (λ () (make-literal-pict "let" #:post-sub "C"))]
           ['v+ (λ () (make-active-nonterminal "v" "+"))]
           ['v- (λ () (make-active-nonterminal "v" "−"))]
           ['V+ (λ () (make-active-nonterminal "V" "+"))]
           ['V- (λ () (make-active-nonterminal "V" "−"))]
           ['q+ (λ () (make-active-nonterminal "q" "+"))]
           ['q- (λ () (make-active-nonterminal "q" "−"))]
           ['Q+ (λ () (make-active-nonterminal "Q" "+"))]
           ['Q- (λ () (make-active-nonterminal "Q" "−"))])
        (proc))))


  (define-syntax-rule (pretty-term tm)
    (with-my-rewriters (λ () (term->pict BS-elab tm))))

  (define-syntax-rule (pretty-metafunction-sig fun result)
    (hb-append (/ (default-font-size) 3)
               (pretty-term fun)
               (arrow->pict '->)
               (pretty-term result)))
  )
