#lang racket/base

(require redex/reduction-semantics)

(provide BS-raw
         BS-elab
         kind-type
         type-equal
         extend-bindings/check
         extend-bindings/synth
         var-check
         var-synth
         elaborate-binding
         requirements-mul
         requirements-add
         usage-equal
         usage-add
         usage-max
         cut
         synth-consumer
         focused-synth-consumer
         check-producer
         focused-check-producer
         synth-producer
         focused-synth-producer
         check-consumer
         focused-check-consumer
         maybe-substitute
         maybe-substitute2
         red/BS)
  

(define-language BS-raw
  [p producer ::= w {let/C χ ↦ k}]
  [w weak-head ::=
     x
     () (pair w w) (ιl w) (ιr w)
     (pack f) (dn v-) (UP w)
     {⊤} {[] ↦ k} {[duo χ χ] ↦ k} {[πl χ] ↦ k \| [πr χ] ↦ k}
     {[throw χ] ↦ k} {[up χ!] ↦ k} {[DN χ] ↦ k}]
  [v+ positive-value ::= w]
  [v- negative-value ::= p]
  [c consumer ::= f {let/P χ ↦ k}]
  [f forcing ::=
     x
     [] [duo f f] [πl f] [πr f]
     [throw w] [up q+] [DN f]
     {𝟘} {() ↦ k} {(pair χ χ) ↦ k} {(ιl χ) ↦ k \| (ιr χ) ↦ k}
     {(pack χ) ↦ k} {(dn χ!) ↦ k} {(UP χ) ↦ k}]
  [q+ positive-question ::= c]
  [q- negative-question ::= f]
  [k command ::= [cmd p ⇒ c]]
  [x ::= variable-not-otherwise-mentioned]
  [χ bind ::= x χ!]
  [χ! annotated-bind ::= (var x τ κ) (var x τ κ ρ) (nope τ κ)]
  [ρ usage ::= 1 ω]
  [κ kind ::= + -]
  [τ type ::=
     𝟘 𝟙 (τ ⊗ τ) (τ ⊕ τ)
     (⊖ τ) (↓ τ) (⇓ τ)
     ⊤ ⊥ (τ ⅋ τ) (τ & τ)
     (¬ τ) (↑ τ) (⇑ τ)]
  #:binding-forms
  (nope τ κ) #:exports nothing
  (var x τ κ) #:exports x
  (var x τ κ ρ) #:exports x
  {let/P χ ↦ k #:refers-to χ}
  {let/C χ ↦ k #:refers-to χ}
  {(pair χ_0 χ_1) ↦ k #:refers-to (shadow χ_0 χ_1)}
  {(ιl χ_0) ↦ k_0 #:refers-to χ_0 \| (ιr χ_1) ↦ k_1 #:refers-to χ_1}
  {[duo χ_0 χ_1] ↦ k #:refers-to (shadow χ_0 χ_1)}
  {[πl χ_0] ↦ k_0 #:refers-to χ_0 \| [πl χ_1] ↦ k_1 #:refers-to χ_1}
  {(pack χ) ↦ k #:refers-to χ}
  {[up χ!] ↦ k #:refers-to χ!}
  {(UP χ) ↦ k #:refers-to χ}
  {[throw χ] ↦ k #:refers-to χ}
  {(dn χ!) ↦ k #:refers-to χ!}
  {[DN χ] ↦ k #:refers-to χ})



(define-extended-language BS-elab BS-raw
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
  [K ::= [CMD P ⇒ κ C]]
  [X ::= x none]
  [ξ binding-context ::= (ψ ...)]
  [ψ variable-binding ::= (bound/check x o) (bound/synth x o τ κ)]
  [o orientation ::= prod con]
  [Ξ requirements ::= ∅ (Ψ ...)]
  [Ψ variable-requirement ::= (req x o τ κ ρ)]
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




(define-judgment-form BS-elab
  #:mode (var-check I I I)
  #:contract (var-check x o ξ)

  [(var-check x o (_ ... (bound/check x o) _ ...))])

(define-judgment-form BS-elab
  #:mode (var-synth I I O O I)
  #:contract (var-synth x o τ κ ξ)

  [(var-synth x o τ κ (_ ... (bound/synth x o τ κ) _ ...))])


(define-judgment-form BS-elab
  #:mode (valid-bind I)
  #:contract (valid-bind χ)

  [-----------
   (valid-bind x)]

  [(kind-type τ κ)
   -----------
   (valid-bind (var x τ κ))]

  [(kind-type τ κ)
   -----------
   (valid-bind (var x τ κ ρ))]

  [(kind-type τ κ)
   -----------
   (valid-bind (nope τ κ))])


(define-metafunction BS-elab
  extend-bindings/check : ξ χ o -> ξ
  [(extend-bindings/check (ψ ...) x o) (ψ ... (bound/check x o))]
  [(extend-bindings/check (ψ ...) (var x τ κ) o) (ψ ... (bound/check x o))]
  [(extend-bindings/check (ψ ...) (var x τ κ ρ) o) (ψ ... (bound/check x o))]
  [(extend-bindings/check ξ (nope τ κ) o) ξ])

(define-metafunction BS-elab
  extend-bindings/synth : ξ χ o -> ξ
  [(extend-bindings/synth (ψ ...) (var x τ κ) o) (ψ ... (bound/synth x o τ κ))]
  [(extend-bindings/synth (ψ ...) (var x τ κ ρ) o) (ψ ... (bound/synth x o τ κ))]
  [(extend-bindings/synth ξ (nope τ κ) o) ξ])



(define-judgment-form BS-elab
  #:mode (usage-equal I I)
  #:contract (usage-equal ρ ρ)

  [------------
   (usage-equal 1 1)]

  [------------
   (usage-equal ω ω)])


(define-metafunction BS-elab
  usage-add : ρ ρ -> ρ
  [(usage-add 1 1) ω]
  [(usage-add ω 1) ω]
  [(usage-add 1 ω) ω]
  [(usage-add ω ω) ω])
  

(define-metafunction BS-elab
  usage-max : ρ ρ -> ρ
  [(usage-max 1 1) 1]
  [(usage-max 1 ω) ω]
  [(usage-max ω 1) ω]
  [(usage-max ω ω) ω])


(define-metafunction BS-elab
  requirements-mul : Ξ Ξ -> Ξ
  [(requirements-mul ∅ Ξ) ∅]
  [(requirements-mul Ξ ∅) ∅]
  [(requirements-mul (Ψ_l1 ... (req x o τ_l κ_l ρ_l) Ψ_l2 ...) (Ψ_r1 ... (req x o τ_r κ_r ρ_r) Ψ_r2 ...))
   (requirements-mul (Ψ_l1 ... Ψ_l2 ...) (Ψ_r1 ... (req x o τ_l κ_l (usage-add ρ_l ρ_r)) Ψ_r2 ...))
   (judgment-holds (type-equal τ_l τ_r))]
  [(requirements-mul (Ψ_l ...) (Ψ_r ...)) (Ψ_l ... Ψ_r ...)])


(define-metafunction BS-elab
  requirements-add : Ξ Ξ -> Ξ
  [(requirements-add ∅ Ξ) Ξ]
  [(requirements-add Ξ ∅) Ξ]
  [(requirements-add (Ψ_l1 ... (req x o τ_l κ_l ρ_l) Ψ_l2 ...) (Ψ_r1 ... (req x o τ_r κ_r ρ_r) Ψ_r2 ...))
   (requirements-add (Ψ_l1 ... Ψ_l2 ...) (Ψ_r1 ... (req x o τ_l κ_l (usage-max ρ_l ρ_r)) Ψ_r2 ...))
   (judgment-holds (type-equal τ_l τ_r))]
  [(requirements-add (Ψ_l ...) (Ψ_r ...)) (Ψ_l ... Ψ_r ...)])


(define-metafunction BS-elab
  requirement-lookup : Ξ x -> (τ κ ρ)
  [(requirement-lookup (_ ... (req x o τ κ ρ) _ ...) x) (τ κ ρ)])



(define-judgment-form BS-elab
  #:mode (kind-type I I)
  #:contract (kind-type τ κ)

  [---------- "𝟘"
   (kind-type 𝟘 +)]

  [---------- "𝟙"
   (kind-type 𝟙 +)]

  [(kind-type τ_1 +) (kind-type τ_2 +)
   ---------- "⊗"
   (kind-type (τ_1 ⊗ τ_2) +)]

  [(kind-type τ_l +) (kind-type τ_r +)
   ---------- "⊕"
   (kind-type (τ_l ⊕ τ_r) +)]

  [---------- "⊤"
   (kind-type ⊤ -)]

  [---------- "⊥"
   (kind-type ⊥ -)]

  [(kind-type τ_1 -) (kind-type τ_2 -)
   ---------- "⅋"
   (kind-type (τ_1 ⅋ τ_2) -)]

  [(kind-type τ_l -) (kind-type τ_r -)
   ---------- "&"
   (kind-type (τ_l & τ_r) -)]

  [(kind-type τ -)
   ---------- "⊖"
   (kind-type (⊖ τ) +)]

  [(kind-type τ -)
   ---------- "↓"
   (kind-type (↓ τ) +)]

  [(kind-type τ +)
   ---------- "⇑"
   (kind-type (⇑ τ) -)]

  [(kind-type τ +)
   ---------- "¬"
   (kind-type (¬ τ) -)]

  [(kind-type τ +)
   ---------- "↑"
   (kind-type (↑ τ) -)]

  [(kind-type τ -)
   ---------- "⇓"
   (kind-type (⇓ τ) +)])


(module+ test
  
  (test-judgment-holds (kind-type (𝟙 ⊗ 𝟙) +))

  (test-equal (judgment-holds (kind-type (⊥ ⊗ 𝟙) +)) #false)

  (test-judgment-holds (kind-type ((𝟙 ⊗ 𝟙) ⊗ 𝟙) +))

  (test-judgment-holds (kind-type (𝟘 ⊕ 𝟘) +))

  (test-judgment-holds (kind-type (⊥ ⅋ ⊥) -))

  (test-judgment-holds (kind-type (⊤ & ⊤) -))

  (test-equal (judgment-holds (kind-type (⊥ & 𝟘) -)) #false)

  (test-judgment-holds (kind-type (⊤ & (⊤ & ⊤)) -))
  )


(define-judgment-form BS-elab
  #:mode (type-equal I I)
  #:contract (type-equal τ τ)

  [(side-condition (alpha-equivalent? τ_1 τ_2))
   ----------- "≡_τ"
   (type-equal τ_1 τ_2)])

  

(define-judgment-form BS-elab
  #:mode (elaborate-binding I I O O O)
  #:contract (elaborate-binding Ξ χ X τ κ)

  [------------------ "elab-[]"
   (elaborate-binding Ξ (nope τ κ) none τ κ)]

  [(where (τ κ ρ) (requirement-lookup Ξ x))
   ------------------ "elab-ρτ"
   (elaborate-binding Ξ x x τ κ)]

  [(where (τ_′ κ ρ) (requirement-lookup Ξ x)) (type-equal τ_′ τ)
   ------------------ "elab-ρ"
   (elaborate-binding Ξ (var x τ κ) x τ κ)]

  [(where (τ_′ κ ρ_′) (requirement-lookup Ξ x)) (type-equal τ_′ τ) (usage-equal ρ_′ ρ)
   ------------------ "elab"
   (elaborate-binding Ξ (var x τ ρ) x τ κ)])



(define-judgment-form BS-elab
  #:mode (cut I I O O)
  #:contract (cut ξ k Ξ K)

  [(synth-consumer ξ c Ξ_1 C τ κ) (check-producer ξ p τ κ Ξ_2 P)
   ---- "△C"
   (cut ξ [cmd p ⇒ c] (requirements-mul Ξ_1 Ξ_2) [CMD P ⇒ κ C])]

  [(synth-producer ξ p Ξ_1 P τ κ) (check-consumer ξ c τ κ Ξ_2 C)
   ---- "△P"
   (cut ξ [cmd p ⇒ c] (requirements-mul Ξ_1 Ξ_2) [CMD P ⇒ κ C])])

  

(define-judgment-form BS-elab
  #:mode (synth-consumer I I O O O O)
  #:contract (synth-consumer ξ c Ξ C τ κ)

  [(cut (extend-bindings/synth ξ χ! prod) k Ξ K) (elaborate-binding Ξ χ! X τ κ)
   --------------- "△let_P"
   (synth-consumer ξ {let/P χ! ↦ k} Ξ {let/P X ↦ K} τ κ)]

  [(focused-synth-consumer ξ c Ξ C τ κ)
   --------------- "F_△C"
   (synth-consumer ξ c Ξ C τ κ)])


(define-judgment-form BS-elab
  #:mode (blur-consumer I I O O O O)
  #:contract (blur-consumer ξ c Ξ C τ κ)

  [(synth-consumer ξ q+ Ξ Q+ τ κ)
   -------------- "B+_C"
   (blur-consumer ξ q+ Ξ Q+ τ κ)])


(define-judgment-form BS-elab
  #:mode (focused-synth-consumer I I O O O O)
  #:contract (focused-synth-consumer ξ c Ξ C τ κ)

  [(var-synth x con τ κ ξ)
   ----------------------- "△Var_C"
   (focused-synth-consumer ξ x ((req x con τ κ 1)) x τ κ)]
  
  [----------------------- "𝟘_C"
   (focused-synth-consumer ξ {𝟘} ∅ {𝟘} 𝟘 +)]
  
  [(cut ξ k Ξ K)
   ----------------------- "𝟙_C"
   (focused-synth-consumer ξ {() ↦ k} Ξ {() ↦ K} 𝟙 +)]

  [(valid-bind χ_1) (valid-bind χ_2) (cut (extend-bindings/check (extend-bindings/check ξ χ_1 prod) χ_2 prod) k Ξ K)
   (elaborate-binding Ξ χ_1 X_1 τ_1 +) (elaborate-binding Ξ χ_2 X_2 τ_2 +)
   ----------------------- "⊗_C"
   (focused-synth-consumer ξ {(pair χ_1 χ_2) ↦ k} Ξ {(pair X_1 X_2) ↦ K} (τ_1 ⊗ τ_2) +)]

  [(valid-bind χ_l) (cut (extend-bindings/check ξ χ_l prod) k_l Ξ_l K_l) (elaborate-binding Ξ_l χ_l X_l τ_l +)
   (valid-bind χ_r) (cut (extend-bindings/check ξ χ_r prod) k_r Ξ_r K_r) (elaborate-binding Ξ_r χ_r X_r τ_r +)
   ----------------------- "⊕_C"
   (focused-synth-consumer ξ {(ιl χ_l) ↦ k_l \| (ιr χ_r) ↦ k_r} (requirements-add Ξ_l Ξ_r) {(ιl X_l) ↦ K_l \| (ιr X_r) ↦ K_r} (τ_l ⊕ τ_r) +)]

  [(valid-bind χ) (cut (extend-bindings/check ξ χ con) k Ξ K) (elaborate-binding Ξ χ X τ +)
   ----------------------- "⊖_C"
   (focused-synth-consumer ξ {(pack χ) ↦ k} Ξ {(pack X) ↦ K} (⊖ τ) +)]

  [(valid-bind χ!) (cut (extend-bindings/synth ξ χ! prod) k Ξ K) (elaborate-binding Ξ χ! X τ -)
   ----------------------- "↓_C"
   (focused-synth-consumer ξ {(dn χ!) ↦ k} Ξ {(dn X) ↦ K} (↓ τ) +)]

  [(valid-bind χ) (cut (extend-bindings/check ξ χ prod) k Ξ K) (elaborate-binding Ξ χ X τ +)
   ----------------------- "⇑_C"
   (focused-synth-consumer ξ {(⇑ χ) ↦ k} Ξ {(⇑ X) ↦ K} (⇑ τ) -)])

(module+ test
  (test-judgment-holds
   (focused-synth-consumer
    () {𝟘}
    ∅ {𝟘} 𝟘 +))
  )



(define-judgment-form BS-elab
  #:mode (check-producer I I I I O O)
  #:contract (check-producer ξ p τ κ Ξ P)

  [(valid-bind χ!) (cut (extend-bindings/check ξ χ! con) k Ξ K) (elaborate-binding Ξ χ! X τ κ) (type-equal τ τ_′)
   --------------- "▽let_C"
   (check-producer ξ {let/C χ! ↦ k} τ_′ κ Ξ {let/C X ↦ K})]

  [(focused-check-producer ξ p τ κ Ξ P)
   --------------- "F_▽P"
   (check-producer ξ p τ κ Ξ P)])


(define-judgment-form BS-elab
  #:mode (focused-check-producer I I I I O O)
  #:contract (focused-check-producer ξ p τ κ Ξ P)

  [(var-check x prod ξ)
   ----------------------- "▽Var_P"
   (focused-check-producer ξ x τ κ ((req x prod τ κ 1)) x)]
  
  [----------------------- "𝟙_P"
   (focused-check-producer ξ () 𝟙 + () ())]
  
  [(focused-check-producer ξ w_1 τ_1 + Ξ_1 W_1) (focused-check-producer ξ w_2 τ_2 + Ξ_2 W_2)
   ----------------------- "⊗_P"
   (focused-check-producer ξ (pair w_1 w_2) (τ_1 ⊗ τ_2) + (requirements-mul Ξ_1 Ξ_2) (pair W_1 W_2))]

  [(focused-check-producer ξ w τ_l + Ξ W)
   ----------------------- "⊕_Pl"
   (focused-check-producer ξ (ιl w) (τ_l ⊕ τ_r) + Ξ (ιl W))]

  [(focused-check-producer ξ w τ_r + Ξ W)
   ----------------------- "⊕_Pr"
   (focused-check-producer ξ (ιr w) (τ_l ⊕ τ_r) + Ξ (ιr W))]

  [(focused-check-consumer ξ f τ - Ξ F)
   ----------------------- "⊖_P"
   (focused-check-producer ξ (pack f) (⊖ τ) + Ξ (⊖ F))]

  [(focused-synth-producer ξ v- τ - Ξ V-)
   ----------------------- "↓_P"
   (focused-check-producer ξ (dn v-) (↓ τ) + Ξ (dn V-))]

  [(focused-check-producer ξ w τ + Ξ W)
   ----------------------- "⇑_P"
   (focused-check-producer ξ (UP w) (⇑ τ) - Ξ (UP W))])

(module+ test

  (test-judgment-holds
   (focused-check-producer
    ((bound/check x prod)) x 𝟙 +
    ((req x prod 𝟙 + 1)) x))

  (test-judgment-holds
   (focused-check-producer
    ((bound/check x_1 prod) (bound/check x_2 prod)) x_2 (𝟙 ⊗ 𝟙) +
    ((req x_2 prod (𝟙 ⊗ 𝟙) + 1)) x_2))

  (test-judgment-holds
   (focused-check-producer
    () (pair () ()) (𝟙 ⊗ 𝟙) +
    () (pair () ())))
  
  (test-judgment-holds
   (focused-check-producer
    ((bound/check x prod)) (pair (ιr x) ()) ((𝟘 ⊕ 𝟙) ⊗ 𝟙) +
    ((req x prod 𝟙 + 1)) (pair (ιr x) ())))

  (test-judgment-holds
   (focused-check-producer
    ((bound/check x_1 prod) (bound/check x_2 prod)) (pair x_1 x_2) (𝟙 ⊗ 𝟙) +
    ((req x_1 prod 𝟙 + 1) (req x_2 prod 𝟙 + 1)) (pair x_1 x_2)))

  (test-judgment-holds
   (focused-check-producer
    ((bound/check x_1 prod) (bound/check x_2 prod)) (pair x_1 x_1) (𝟙 ⊗ 𝟙) +
    ((req x_1 prod 𝟙 + ω)) (pair x_1 x_1)))
  )



(define-judgment-form BS-elab
  #:mode (synth-producer I I O O O O)
  #:contract (synth-producer ξ p Ξ P τ κ)

  [(valid-bind χ) (cut (extend-bindings/synth ξ χ con) k Ξ K) (elaborate-binding Ξ χ X τ κ)
   --------------- "△let_C"
   (synth-producer ξ {let/C χ ↦ k} Ξ {let/C X ↦ K} τ κ)]

  [(focused-synth-producer ξ p Ξ P τ κ)
   --------------- "F_△P"
   (synth-producer ξ p Ξ P τ κ)])


(define-judgment-form BS-elab
  #:mode (blur-producer I I O O O O)
  #:contract (blur-producer ξ p Ξ P τ κ)

  [(synth-producer ξ v- Ξ V- τ κ)
   -------------- "B-_P"
   (blur-producer ξ v- Ξ V- τ κ)])


(define-judgment-form BS-elab
  #:mode (focused-synth-producer I I O O O O)
  #:contract (focused-synth-producer ξ p Ξ P τ κ)

  [(var-synth x prod τ κ ξ)
   ----------------------- "△Var_P"
   (focused-synth-producer ξ x ((req x prod τ κ 1)) x τ κ)]

  [----------------------- "⊤_P"
   (focused-synth-producer ξ {⊤} ∅ {⊤} ⊤ -)]

  [(cut ξ k Ξ K)
   ----------------------- "⊥_P"
   (focused-synth-producer ξ {[] ↦ k} Ξ {[] ↦ K} ⊥ -)]

  [(valid-bind χ_1) (valid-bind χ_2) (cut (extend-bindings/check (extend-bindings/check ξ χ_1 con) χ_2 con) k Ξ K)
   (elaborate-binding Ξ χ_1 X_1 τ_1 -) (elaborate-binding Ξ χ_2 X_2 τ_2 -)
   ----------------------- "⅋_P"
   (focused-synth-producer ξ {[duo χ_1 χ_2] ↦ k} Ξ {[duo X_1 X_2] ↦ K} (τ_1 ⅋ τ_2) -)]

  [(valid-bind χ_l) (cut (extend-bindings/check ξ χ_l con) k_l Ξ_l K_l) (elaborate-binding Ξ_l χ_l X_l τ_l -)
   (valid-bind χ_r) (cut (extend-bindings/check ξ χ_r con) k_r Ξ_r K_r) (elaborate-binding Ξ_r χ_r X_r τ_r -)
   ----------------------- "&_P"
   (focused-synth-producer ξ {[πl χ_l] ↦ k_l \| [πr χ_r] ↦ k_r} (requirements-add Ξ_l Ξ_r) {[πl X_l] ↦ K_l \| [πr X_r] ↦ K_r} (τ_l & τ_r) -)]

  [(valid-bind χ) (cut (extend-bindings/check ξ χ prod) k Ξ K) (elaborate-binding Ξ χ X τ +)
   ----------------------- "¬_P"
   (focused-synth-producer ξ {[throw χ] ↦ k} Ξ {[throw X] ↦ K} (¬ τ) -)]

  [(valid-bind χ!) (cut (extend-bindings/synth ξ χ! con) k Ξ K) (elaborate-binding Ξ χ! X τ +)
   ----------------------- "↑_P"
   (focused-synth-producer ξ {[up χ!] ↦ k} Ξ {[up X] ↦ K} (↑ τ) -)]

  [(valid-bind χ) (cut (extend-bindings/check ξ χ con) k Ξ K) (elaborate-binding Ξ χ X τ -)
   ----------------------- "⇓_P"
   (focused-synth-producer ξ {[DN χ] ↦ k} Ξ {[DN X] ↦ K} (⇓ τ) +)])



(define-judgment-form BS-elab
  #:mode (check-consumer I I I I O O)
  #:contract (check-consumer ξ c τ κ Ξ C)

  [(valid-bind χ!) (cut (extend-bindings/check ξ χ! prod) k Ξ K) (elaborate-binding Ξ χ! X τ κ) (type-equal τ τ_′)
   --------------- "▽let_P"
   (check-consumer ξ {let/P χ! ↦ k} τ_′ κ Ξ {let/P X ↦ K})]

  [(focused-check-consumer ξ c τ κ Ξ C)
   --------------- "F_▽C"
   (check-consumer ξ c τ κ Ξ C)])
  

(define-judgment-form BS-elab
  #:mode (focused-check-consumer I I I I O O)
  #:contract (focused-check-consumer ξ c τ κ Ξ C)

  [(var-check x con ξ)
   ----------------------- "▽Var_C"
   (focused-check-consumer ξ x τ κ ((req x con τ κ 1)) x)]

  [----------------------- "⊥_C"
   (focused-check-consumer ξ [] ⊥ - () [])]

  [(focused-check-consumer ξ f_1 τ_1 - Ξ_1 F_1) (focused-check-consumer ξ f_2 τ_2 - Ξ_2 F_2)
   ----------------------- "⅋_C"
   (focused-check-consumer ξ [duo f_1 f_2] (τ_1 ⅋ τ_2) - (requirements-mul Ξ_1 Ξ_2) [duo F_1 F_2])]

  [(focused-check-consumer ξ f τ_l - Ξ F)
   ----------------------- "&_Cl"
   (focused-check-consumer ξ [πl f] (τ_l & τ_r) - Ξ [πl F])]

  [(focused-check-consumer ξ f τ_r - Ξ F)
   ----------------------- "&_Cr"
   (focused-check-consumer ξ [πr f] (τ_l & τ_r) - Ξ [πr F])]

  [(focused-check-producer ξ w τ + Ξ W)
   ----------------------- "¬_C"
   (focused-check-consumer ξ [throw w] (¬ τ) - Ξ [throw W])]

  [(focused-synth-consumer ξ q+ Ξ Q+ τ +)
   ----------------------- "↑_C"
   (focused-check-consumer ξ [up q+] (↑ τ) - Ξ [up Q+])]

  [(focused-check-consumer ξ f τ - Ξ F)
   ----------------------- "⇓_C"
   (focused-check-consumer ξ [DN f] (⇓ τ) + Ξ [DN F])])

(module+ test

  (test-judgment-holds
   (focused-check-consumer
    () [] ⊥ -
    () []))

  (test-judgment-holds
   (focused-check-consumer
    ((bound/check x_1 prod)) [] ⊥ -
    () []))

  (test-judgment-holds
   (focused-check-consumer
    () [duo [] []] (⊥ ⅋ ⊥) -
    () [duo [] []]))

  (test-judgment-holds
   (focused-check-consumer
    ((bound/check x_1 con) (bound/check x_2 con)) [duo x_1 x_2] (⊥ ⅋ ⊥) -
    ((req x_1 con ⊥ - 1) (req x_2 con ⊥ - 1)) [duo x_1 x_2]))

  (test-judgment-holds
   (focused-check-consumer
    ((bound/check x_1 prod) (bound/check x_2 con) (bound/check x_3 con)) [πl [πl x_2]] ((⊥ & ⊤) & ⊤) -
    ((req x_2 con ⊥ - 1)) [πl [πl x_2]]))

  (test-judgment-holds
   (focused-check-consumer
    ((bound/check x_1 con) (bound/check x_2 con)) [πr [duo x_2 x_2]] (⊥ & (⊥ ⅋ ⊥)) -
    ((req x_2 con ⊥ - ω)) [πr [duo x_2 x_2]]))

  (test-judgment-holds
   (focused-check-consumer
    () [πl [πr [πl []]]] ((⊥ & (⊥ & ⊤)) & ⊤) -
    () [πl [πr [πl []]]]))

  (test-judgment-holds
   (focused-check-consumer
    ((bound/check x_1 con) (bound/check x_2 con)) [duo x_2 [duo x_1 x_2]] (⊥ ⅋ (⊥ ⅋ ⊥)) -
    ((req x_1 con ⊥ - 1) (req x_2 con ⊥ - ω)) [duo x_2 [duo x_1 x_2]]))
  )



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

   [--> [CMD V+ ⇒ + {let/P X ↦ K}]
        (maybe-substitute K X V+)
        "let V+_β"]

   [--> [CMD {let/C X ↦ K} ⇒ + Q+]
        (maybe-substitute K X Q+)
        "let Q+_β"]

   [--> [CMD () ⇒ + {() ↦ K}]
        K
        "𝟙_β"]

   [--> [CMD (pair W_1 W_2) ⇒ + {(pair X_1 X_2) ↦ K}]
        (maybe-substitute2 K X_1 W_1 X_2 W_2)
        "⊗_β"]

   [--> [CMD (ιl W) ⇒ + {(ιl X_l) ↦ K_l \| (ιr X_r) ↦ K_r}]
        (maybe-substitute K_l X_l W)
        "⊕l_β"]

   [--> [CMD (ιr W) ⇒ + {(ιl X_l) ↦ K_l \| (ιr X_r) ↦ K_r}]
        (maybe-substitute K_r X_r W)
        "⊕r_β"]

   [--> [(pack F) ⇒ + {(pack X) ↦ K}]
        (maybe-substitute K X F)
        "⊖_β"]

   [--> [(dn V-) ⇒ + {(dn X) ↦ K}]
        (maybe-substitute K X V-)
        "↓_β"]

   [--> [(UP W) ⇒ - {(UP X) ↦ K}]
        (maybe-substitute K X W)
        "⇑_β"]

   [--> [CMD {let/C X ↦ K} ⇒ - Q-]
        (maybe-substitute K X Q-)
        "let Q−_β"]

   [--> [CMD V- ⇒ - {let/P X ↦ K}]
        (maybe-substitute K X V-)
        "let V−_β"]

   [--> [CMD {[] ↦ K} ⇒ - []]
        K
        "⊥_β"]

   [--> [CMD {[duo X_1 X_2] ↦ K} ⇒ - [duo F_1 F_2]]
        (maybe-substitute2 K X_1 F_1 X_2 F_2)
        "⅋_β"]

   [--> [CMD {[πl X_l] ↦ K_l \| [πr X_r] ↦ K_r} ⇒ - [πl F]]
        (maybe-substitute K_l X_l F)
        "&l_β"]

   [--> [CMD {[πl X_l] ↦ K_l \| [πr X_r] ↦ K_r} ⇒ - [πr F]]
        (maybe-substitute K_r X_r F)
        "&r_β"]

   [--> [{(throw X) ↦ K} ⇒ - (throw W)]
        (maybe-substitute K X W)
        "¬_β"]

   [--> [{(up X) ↦ K} ⇒ - (up Q+)]
        (maybe-substitute K X Q+)
        "↑_β"]

   [--> [{(DN X) ↦ K} ⇒ + (DN F)]
        (maybe-substitute K X F)
        "⇓_β"]))


(module+ test

  (define-syntax-rule (test-->/BS start step)
    (test--> red/BS (term start) (term step)))

  (define-syntax-rule (test-->>/BS start step)
    (test-->> red/BS (term start) (term step)))

  (define-term dummy-end [CMD x_end-prod ⇒ + x_end-con])

  (test-->/BS [CMD () ⇒ + {() ↦ dummy-end}]
              dummy-end)

  (test-->/BS [CMD {[] ↦ dummy-end} ⇒ - []]
              dummy-end)

  (test-->>/BS [CMD {let/C x ↦ [CMD () ⇒ + x]} ⇒ + {() ↦ dummy-end}]
              dummy-end)

  (test-->>/BS [CMD {[] ↦ dummy-end} ⇒ - {let/P x ↦ [CMD x ⇒ - []]}]
               dummy-end)

  (test-->>/BS [CMD (pair () ()) ⇒ +
                    {(pair x_0 x_1) ↦ [CMD x_0 ⇒ +
                                           {() ↦ [CMD x_1 ⇒ + {() ↦ dummy-end}]}]}]
               dummy-end)

  (test-->>/BS [CMD {[duo x_0 x_1] ↦
                                   [CMD {[] ↦
                                            [CMD {[] ↦ dummy-end} ⇒ - x_1]} ⇒ - x_0]}
                    ⇒ - [duo [] []]]
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
    
  (define (prettify/elab l r)
    (prettify "⟦" l "⟧ ↝ (" r ")"))

  (define (prettify/elab-term ξ t Ξ T #:ty [ty #false] #:focused? [focused? #false])
    (define turnstile (text (if focused? " ⊩" " ⊢") (literal-style)))
    (define fence (if ty
                      (list (hb-append turnstile (orientation-script ty #true)) " ")
                      (list turnstile " ")))
    (prettify/elab (list ξ fence t) (list Ξ fence T)))

  (define (orientation-script type sub?)
    (define script (if sub? 'subscript 'superscript))
    (match type
      ['o (text "o" (cons script (non-terminal-style)))]
      ['prod (text "P" (cons script (literal-style)))]
      ['con (text "C" (cons script (literal-style)))]))


  (define (bind-or-var x o)
    (list x (orientation-script o #false)))

  (define (type-term t τ κ)
    (list t " : " τ " : " κ))
  
  (define (prettify/elab-synth ξ t Ξ T τ κ #:ty ty #:focused? [focused? #false])
    (prettify/elab-term ξ t Ξ (type-term T τ κ) #:ty ty #:focused? focused?))

  (define (prettify/elab-check ξ t τ κ Ξ T #:ty ty #:focused? [focused? #false])
    (prettify/elab-term ξ (type-term t τ κ) Ξ T #:ty ty #:focused? focused?))

  
  (define (with-my-rewriters proc)
    (with-compound-rewriters
        (['pair (match-λ [(list _ _ p_1 p_2 _)
                          (prettify "(" p_1 ", " p_2 ")")])]
         ['duo (match-λ [(list _ _ c_1 c_2 _)
                         (prettify "[" c_1 ", " c_2 "]")])]
         ['cmd (match-λ [(list _ _ p ⇒ c _)
                         (prettify p ⇒ c)])]
         ['CMD (match-λ [(list _ _ P ⇒ κ C _)
                         (prettify P ⇒ (text (symbol->string (lw-e κ)) (cons 'superscript (default-style))) " " C)])]
         ['var (match-λ [(list _ _ x τ κ _)
                         (prettify (type-term x τ κ))]
                        [(list _ _ x τ κ ρ _)
                         (prettify x " : " τ " : " κ "; " ρ)])]
         ['bound/check (match-λ [(list _ _ x o _)
                                 (prettify x (orientation-script (lw-e o) #true))])]
         ['bound/synth (match-λ [(list _ _ x o τ κ _)
                                 (prettify (type-term (list x (orientation-script (lw-e o) #true)) τ κ))])]
         ['nope (match-λ [(list _ _ τ κ _)
                          (prettify "_ : " τ " : " κ)])]
         ['req (match-λ [(list _ _ x o τ κ ρ _)
                         (prettify (type-term (bind-or-var x (lw-e o)) τ κ) "; " ρ)])]
         ['var-check (match-λ [(list _ _ x o ξ _)
                               (prettify x (orientation-script (lw-e o) #true) " ∈ " ξ)])]
         ['var-synth (match-λ [(list _ _ x o τ κ ξ _)
                               (prettify (type-term x τ κ) " ∈ " ξ)])]
         ['valid-bind (match-λ [(list _ _ χ _)
                                (prettify χ " ok")])]
         ['extend-bindings/check (match-λ [(list _ _  ξ χ o _)
                                           (prettify ξ ", " (bind-or-var χ (lw-e o)))])]
         ['extend-bindings/synth (match-λ [(list _ _ ξ χ o _)
                                         (prettify ξ ", " (bind-or-var χ (lw-e o)))])]
         ['requirement-lookup (match-λ [(list _ _ Ξ x _)
                                        (prettify Ξ "{" x "}")])]
         ['elaborate-binding (match-λ [(list _ _ Ξ χ X τ κ _)
                                       (prettify  Ξ "⟦" χ "⟧ ↝ (" (type-term X τ κ) ")")])]
         ['kind-type (match-λ [(list _ _ τ κ _)
                               (prettify τ " : " κ)])]
         ['type-equal (match-λ [(list _ _ τ_1 τ_2 _)
                                (prettify τ_1 " ≡ " τ_2)])]
         ['requirements-mul (match-λ [(list _ _ Ξ_1 Ξ_2 _)
                                      (prettify Ξ_1 " × " Ξ_2)])]
         ['requirements-add (match-λ [(list _ _ Ξ_1 Ξ_2 _)
                                      (prettify Ξ_1 " + " Ξ_2)])]
         ['usage-equal (match-λ [(list _ _ ρ_1 ρ_2 _)
                                 (prettify ρ_1 " ≡ " ρ_2)])]
         ['usage-add (match-λ [(list _ _ ρ_0 ρ_1 _)
                               (prettify ρ_0 " + " ρ_1)])]
         ['usage-max (match-λ [(list _ _ ρ_0 ρ_1 _)
                               (prettify ρ_0 " ⊔ " ρ_1)])]
         ['cut (match-λ [(list _ _ ξ k Ξ K _)
                         (prettify/elab-term ξ k Ξ K)])]
         ['synth-consumer (match-λ [(list _ _ ξ c Ξ C τ κ _)
                                    (prettify/elab-synth ξ c Ξ C τ κ #:ty 'con)])]
         ['focused-synth-consumer (match-λ [(list _ _ ξ c Ξ C τ κ _)
                                            (prettify/elab-synth ξ c Ξ C τ κ #:ty 'con #:focused? #true)])]
         ['check-producer (match-λ [(list _ _ ξ p τ κ Ξ P _)
                                    (prettify/elab-check ξ p τ κ Ξ P #:ty 'prod)])]
         ['focused-check-producer (match-λ [(list _ _ ξ p τ κ Ξ P _)
                                            (prettify/elab-check ξ p τ κ Ξ P #:ty 'prod #:focused? #true)])]
         ['synth-producer (match-λ [(list _ _ ξ p Ξ P τ κ _)
                                    (prettify/elab-synth ξ p Ξ P τ κ #:ty 'prod)])]
         ['focused-synth-producer (match-λ [(list _ _ ξ p Ξ P τ κ _)
                                            (prettify/elab-synth ξ p Ξ P τ κ #:ty 'prod #:focused? #true)])]
         ['check-consumer (match-λ [(list _ _ ξ c τ κ Ξ C _)
                                    (prettify/elab-check ξ c τ κ Ξ C #:ty 'con)])]
         ['focused-check-consumer (match-λ [(list _ _ ξ c τ κ Ξ C _)
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
    (hb-append (/ (default-font-size) 2)
               (pretty-term fun)
               (arrow->pict '->)
               (pretty-term result)))
  )
