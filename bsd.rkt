#lang racket/base

(require redex/reduction-semantics)

(provide BS-raw
         BS-exec
         BS-elab
         bindings-snoc
         var-check
         var-synth
         discharge-▽binding
         discharge-△binding
         requirements-⊔
         requirements-⊓
         cut
         △consumer
         pattern->bindtree/~p
         expand-pattern/~p
         ▽producer
         △producer
         pattern->bindtree/~c
         expand-pattern/~c
         ▽consumer
         red/BS)
  

(define-language BS-raw
  [p producer ::=
     x {let/C ~c ↦ k}
     () (pair p p) (ιl p) (ιr p) (pack c)
     {~c ↦ k} {↦} {[πl ~c] ↦ k} {[πr ~c] ↦ k} {[πl ~c] ↦ k \| [πr ~c] ↦ k}]
  [~c ::= ▽χ △χ [] [duo ~c ~c] [throw ~p]]
  [c consumer ::=
     x {let/P ~p ↦ k}
     [] [duo c c] [πl c] [πr c] [throw p]
     {~p ↦ k} {↦} {(ιl ~p) ↦ k} {(ιr ~p) ↦ k} {(ιl ~p) ↦ k \| (ιr ~p) ↦ k}]
  [~p ::= ▽χ △χ () (pair ~p ~p) (pack ~c)]
  [k command ::= [cmd p ◊ c]]
  [x ::= variable-not-otherwise-mentioned]
  [▽χ checked-bind ::= x (nope τ)]
  [△χ synthesizing-bind ::= (△var x τ) (nope τ)]
  [τ type ::=
     𝟘 𝟙 (τ ⊗ τ) (τ ⊕ τ) (⊖ τ)
     ⊤ ⊥ (τ ⅋ τ) (τ & τ) (¬ τ)]
  [κ kind ::= + -]
  #:binding-forms
  (nope τ) #:exports nothing
  (△var x τ) #:exports x
  {let/C ~p ↦ k #:refers-to ~p}
  {~p ↦ k #:refers-to ~p}
  {(ιl ~p_l) ↦ k_0 #:refers-to ~p_l \| (ιr ~p_r) ↦ k_1 #:refers-to ~p_r}
  {(ιl ~p) ↦ k #:refers-to ~p}
  {(ιr ~p) ↦ k #:refers-to ~p}
  () #:exports nothing
  (pair ~p_1 ~p_2) #:exports (shadow ~p_1 ~p_2)
  (pack ~c) #:exports ~c
  {let/P ~c ↦ k #:refers-to ~c}
  {[πl ~c_l] ↦ k_0 #:refers-to ~c_l \| [πl ~c_r] ↦ k_1 #:refers-to ~c_r}
  {[πl ~c] ↦ k #:refers-to ~c}
  {[πr ~c] ↦ k #:refers-to ~c}
  [duo ~c_1 ~c_2] #:exports (shadow ~c_1 ~c_2)
  [throw ~p] #:exports ~p)





(define-extended-language BS-exec BS-raw
  [P ::= W {let/C x ↦ K}]
  [W weak-head ::=
     x () (pair W W) (ιl W) (ιr W)
     (pack F) (dn P) (UP W)
     {↦} {[] ↦ K} {[duo x x] ↦ K} {[πl x] ↦ K \| [πr x] ↦ K}
     {[throw x] ↦ K} {[up x] ↦ K} {[DN x] ↦ K}]
  [C ::= F {let/P x ↦ K}]
  [F forcing ::=
     x [] [duo F F] [πl F] [πr F]
     [throw W] [up C] [DN F]
     {↦} {() ↦ K} {(pair x x) ↦ K} {(ιl x) ↦ K \| (ιr x) ↦ K}
     {(pack x) ↦ K} {(dn x) ↦ K} {(UP x) ↦ K}]
  [K ::= [CMD P κ C]]
  #:binding-forms
  {[duo x_0 x_1] ↦ K #:refers-to (shadow x_0 x_1)}
  {[πl x_0] ↦ K_0 #:refers-to x_0 \| [πr x_1] ↦ K_1 #:refers-to x_1}
  {(pair x_0 x_1) ↦ K #:refers-to (shadow x_0 x_1)}
  {(ιl x_0) ↦ K_0 #:refers-to x_0 \| (ιr x_1) ↦ K_1 #:refers-to x_1}
  {let/P x ↦ K #:refers-to x}
  {let/C x ↦ K #:refers-to x}
  {(throw x) ↦ k #:refers-to x}
  {(up x) ↦ K #:refers-to x}
  {(DN x) ↦ K #:refers-to x}
  {(pack x) ↦ K #:refers-to x}
  {(dn x) ↦ K #:refers-to x}
  {(UP x) ↦ K #:refers-to x})



(define-extended-language BS-elab BS-exec
  [χ ::= ▽χ △χ]
  [Γ binding-context ::= (γ ...)]
  [γ variable-binding ::= (▽bound x) (△bound x τ)]
  [o orientation ::= prod con]
  [Ξ requirements ::= ∅ (ξ ...)]
  [ξ variable-requirement ::= (req x o τ)]
  [ζ binding-tree ::=
     τ
     (X : ζ ⊗ X : ζ) (⊖ X : ζ) (↓ X : τ) (⇑ X : ζ)
     (X : ζ ⅋ X : ζ) (¬ X : ζ) (↑ X : τ) (⇓ X : ζ)]
  [X ::= ~X new]
  [~X ::= x none])



(define-judgment-form BS-elab
  #:mode (kind-= I I)
  #:contract (kind-= κ κ)

  [(kind-= + +)]

  [(kind-= - -)])


(define-judgment-form BS-elab
  #:mode (△type I O)
  #:contract (△type τ κ)

  [------
   (△type 𝟘 +)]

  [------
   (△type 𝟙 +)]

  [------
   (△type (τ_1 ⊗ τ_2) +)]

  [------
   (△type (τ_l ⊕ τ_r) +)]

  [------
   (△type (⊖ τ) +)]

  [------
   (△type ⊤ -)]
  
  [------
   (△type ⊥ -)]

  [------
   (△type (τ_1 ⅋ τ_2) -)]

  [------
   (△type (τ_l & τ_r) -)]
  
  [------
   (△type (¬ τ) -)])


(define-judgment-form BS-elab
  #:mode (type-= I I)
  #:contract (type-= τ τ)

  [-------
   (type-= 𝟘 𝟘)]

  [-------
   (type-= 𝟙 𝟙)]

  [(type-= τ_1 τ_1′) (type-= τ_2 τ_2′)
   -------
   (type-= (τ_1 ⊗ τ_2) (τ_1′ ⊗ τ_2′))]

  [(type-= τ_l τ_l′) (type-= τ_r τ_r′)
   -------
   (type-= (τ_l ⊕ τ_r) (τ_l′ ⊕ τ_r′))]

  [(type-= τ τ_′)
   -------
   (type-= (⊖ τ) (⊖ τ_′))]

  [-------
   (type-= ⊤ ⊤)]

  (-------
   (type-= ⊥ ⊥))

  [(type-= τ_1 τ_1′) (type-= τ_2 τ_2′)
   -------
   (type-= (τ_1 ⅋ τ_2) (τ_1′ ⅋ τ_2′))]

  [(type-= τ_l τ_l′) (type-= τ_r τ_r′)
   -------
   (type-= (τ_l & τ_r) (τ_l′ & τ_r′))]

  [(type-= τ τ_′)
   -------
   (type-= (¬ τ) (¬ τ_′))])




(define-metafunction BS-elab
  bindings-snoc : Γ any -> Γ

  [(bindings-snoc (γ ...) x) (γ ... (▽bound x))]
  [(bindings-snoc Γ (nope τ)) Γ]
  [(bindings-snoc Γ ()) Γ]
  [(bindings-snoc Γ (pair ~p_1 ~p_2)) (bindings-snoc (bindings-snoc Γ ~p_1) ~p_2)]
  [(bindings-snoc Γ (pack ~c)) (bindings-snoc Γ ~c)]
  [(bindings-snoc Γ (UP ~p)) (bindings-snoc Γ ~p)]
  [(bindings-snoc Γ [duo ~c_1 ~c_2]) (bindings-snoc (bindings-snoc Γ ~c_1) ~c_2)]
  [(bindings-snoc Γ [throw ~p]) (bindings-snoc Γ ~p)]
  [(bindings-snoc Γ [DN ~c]) (bindings-snoc Γ ~c)]
  [(bindings-snoc (γ ...) (△var x τ)) (γ ... (△bound x τ))]
  [(bindings-snoc Γ (nope τ)) Γ])


(define-judgment-form BS-elab
  #:mode (var-check I I)
  #:contract (var-check x Γ)

  [(var-check x (_ ... (▽bound x) _ ...))])

(define-judgment-form BS-elab
  #:mode (var-synth I O I)
  #:contract (var-synth x τ Γ)

  [(var-synth x τ (_ ... (△bound x τ) _ ...))])



(define-metafunction BS-elab
  requirements-⊔ : Ξ Ξ -> Ξ

  [(requirements-⊔ ∅ Ξ) ∅]
  [(requirements-⊔ Ξ ∅) ∅]
  [(requirements-⊔ (ξ_l1 ... ξ_l ξ_l2 ...) (ξ_r1 ... ξ_r ξ_r2 ...))
   (requirements-⊔ (ξ_l1 ... ξ_l2 ...) (ξ_r1 ... ξ ξ_r2 ...))
   (where (req x o τ_l) ξ_l)
   (where (req x o τ_r) ξ_r)
   (judgment-holds (△type τ_l κ_l))
   (judgment-holds (△type τ_r κ_r))
   (judgment-holds (kind-= κ_l κ_r))
   (judgment-holds (type-= τ_l τ_r))
   (where ξ (req x o τ_r))]
  [(requirements-⊔ (ξ_l ...) (ξ_r ...)) (ξ_l ... ξ_r ...)])


(define-metafunction BS-elab
  requirements-⊓ : Ξ Ξ -> Ξ

  [(requirements-⊓ ∅ Ξ) Ξ]
  [(requirements-⊓ Ξ ∅) Ξ]
  [(requirements-⊓ (ξ_l1 ... ξ_l ξ_l2 ...) (ξ_r1 ... ξ_r ξ_r2 ...))
   (requirements-⊓ (ξ_l1 ... ξ_l2 ...) (ξ_r1 ... ξ ξ_r2 ...))
   (where (req x o τ_l) ξ_l)
   (where (req x o τ_r) ξ_r)
   (judgment-holds (△type τ_l κ_l))
   (judgment-holds (△type τ_r κ_r))
   (judgment-holds (kind-= κ_l κ_r))
   (judgment-holds (type-= τ_l τ_r))
   (where ξ (req x o τ_r))]
  [(requirements-⊓ (ξ_l ...) (ξ_r ...)) (ξ_l ... ξ_r ...)])


(define-judgment-form BS-elab
  #:mode (discharge-▽binding I I O O O)
  #:contract (discharge-▽binding Ξ ▽χ Ξ X τ)

  [-------------------
   (discharge-▽binding (ξ_1 ... (req x o τ) ξ_2 ...) x (ξ_1 ... ξ_2 ...) x τ)]

  [-------------------
   (discharge-▽binding Ξ (nope τ) Ξ none τ)])


(define-judgment-form BS-elab
  #:mode (discharge-△binding I I O O O)
  #:contract (discharge-△binding Ξ △χ Ξ X τ)

  [-------------------
   (discharge-△binding Ξ (nope τ) Ξ none τ)]

  [-------------------
   (discharge-△binding (ξ_1 ... (req x o τ) ξ_n ...) (△var x τ) (ξ_1 ... ξ_n ...) x τ)])


(define-judgment-form BS-elab
  #:mode (extract-type I O)
  #:contract (extract-type ζ τ)

  [-------------
   (extract-type τ τ)]

  [-------------
   (extract-type (X : τ) τ)]

  [(extract-type ζ_1 τ_1) (extract-type ζ_2 τ_2)
   -------------
   (extract-type (X_1 : ζ_1 ⊗ X_2 : ζ_2) (τ_1 ⊗ τ_2))]

  [(extract-type ζ τ)
   -------------
   (extract-type (⊖ X : ζ) (⊖ τ))]

  [-------------
   (extract-type (↓ X : τ) τ)]

  [(extract-type ζ τ)
   -------------
   (extract-type (⇑ X : ζ) (⇑ τ))]

  [(extract-type ζ_1 τ_1) (extract-type ζ_2 τ_2)
   -------------
   (extract-type (X_1 : ζ_1 ⅋ X_2 : ζ_2) (τ_1 ⅋ τ_2))]

  [(extract-type ζ τ)
   -------------
   (extract-type (¬ X : ζ) (¬ τ))]

  [-------------
   (extract-type (↑ X : τ) τ)]

  [(extract-type ζ τ)
   -------------
   (extract-type (⇓ X : ζ) (⇓ τ))])


(define-judgment-form BS-elab
  #:mode (bind-type I O)
  #:contract (bind-type ~p X)

  [(bind-type x x)]

  [(bind-type (nope τ) none)]

  [(bind-type ~p new)])



(define-metafunction BS-elab
  maybe-fresh : ~X any -> x

  [(maybe-fresh none any) x
                          (where x ,(variable-not-in (term any) 'unused))]
  [(maybe-fresh x any) x])


(define-metafunction BS-elab
  fresh-immediate : any -> x

  [(fresh-immediate any) x
                         (where x ,(variable-not-in (term any) 'immediate))])



(define-judgment-form BS-elab
  #:mode (cut I O I O)
  #:contract (cut Γ Ξ k K)

  [(△consumer Γ Ξ_1 c τ κ C) (▽producer Γ Ξ_2 τ p P)
   ----
   (cut Γ (requirements-⊓ Ξ_1 Ξ_2) [cmd p ◊ c] [CMD P κ C])]

  [(△producer Γ Ξ_1 p τ κ P) (▽consumer Γ Ξ_2 τ c C)
   ----
   (cut Γ (requirements-⊓ Ξ_1 Ξ_2) [cmd p ◊ c] [CMD P κ C])])



(define-judgment-form BS-elab
  #:mode (△consumer I O I O O O)
  #:contract (△consumer Γ Ξ c τ κ C)

  [(cut (bindings-snoc Γ ~p) Ξ k K) (pattern->bindtree/~p Ξ ~p Ξ_′ ζ) (where F (expand-pattern/~p Γ ζ K)) (extract-type ζ τ) (△type τ +) (where x (fresh-immediate F))
   ----------
   (△consumer Γ Ξ_′ {let/P ~p ↦ k} τ + {let/P x ↦ [CMD x + F]})]

  [(var-synth x τ Γ) (△type τ κ)
   ----------
   (△consumer Γ ((req x con τ)) x τ κ x)]
  
  [----------
   (△consumer Γ ∅ {↦} 𝟘 + {↦})]
  
  [(cut Γ Ξ k K)
   ----------
   (△consumer Γ Ξ {() ↦ k} 𝟙 + {() ↦ K})]

  [(cut (bindings-snoc Γ ~p) Ξ k K) (pattern->bindtree/~p Ξ ~p Ξ_′ ζ) (where F (expand-pattern/~p Γ ζ K)) (extract-type ζ τ) (△type τ κ)
   ----------
   (△consumer Γ Ξ {~p ↦ k} τ κ F)]

  [(cut (bindings-snoc Γ ~p_l) Ξ_l k_l K_l) (pattern->bindtree/~p Ξ_l ~p_l Ξ_l′ ζ_l) (where F_l (expand-pattern/~p Γ ζ_l K_l)) (extract-type ζ_l τ_l) (△type τ_l +) (where x_l (fresh-immediate (Γ F_l)))
   (cut (bindings-snoc Γ ~p_r) Ξ_r k_r K_r) (pattern->bindtree/~p Ξ_r ~p_r Ξ_r′ ζ_r) (where F_r (expand-pattern/~p Γ ζ_r K_r)) (extract-type ζ_r τ_r) (△type τ_r +) (where x_r (fresh-immediate (Γ F_r)))
   ----------
   (△consumer Γ (requirements-⊓ Ξ_l′ Ξ_r′) {(ιl ~p_l) ↦ k_l \| (ιr ~p_r) ↦ k_r} (τ_l ⊕ τ_r) +
      {(ιl x_l) ↦ [CMD x_l + K_l] \| (ιr x_r) ↦ [CMD x_r + K_r]})]

  [(cut (bindings-snoc Γ ~p_l) Ξ_l k_l K_l) (pattern->bindtree/~p Ξ_l ~p_l Ξ_l′ ζ_l) (where F_l (expand-pattern/~p Γ ζ_l K_l)) (extract-type ζ_l τ_l) (△type τ_l +)
   (where x_l (fresh-immediate (Γ F_l))) (where x_r (fresh-immediate Γ))
   ----------
   (△consumer Γ (requirements-⊓ Ξ_l′ ∅) {(ιl ~p_l) ↦ k_l} (τ_l ⊕ 𝟘) +
     {(ιl x_l) ↦ [CMD x_l + K_l] \| (ιr x_r) ↦ [CMD x_r + {↦}]})]

  [(cut (bindings-snoc Γ ~p_r) Ξ_r k_r K_r) (pattern->bindtree/~p Ξ_r ~p_r Ξ_r′ ζ_r) (where F_r (expand-pattern/~p Γ ζ_r K_r)) (extract-type ζ_r τ_r) (△type τ_r +)
   (where x_r (fresh-immediate (Γ F_r))) (where x_l (fresh-immediate Γ))
   ----------
   (△consumer Γ (requirements-⊓ ∅ Ξ_r′) {(ιr ~p_r) ↦ k_r} (𝟘 ⊕ τ_r) +
     {(ιl x_l) ↦ [CMD x_l + {↦}] \| (ιr x_r) ↦ [CMD x_r + K_r]})])



(define-judgment-form BS-elab
  #:mode (pattern->bindtree/~p I I O O)
  #:contract (pattern->bindtree/~p Ξ ~p Ξ ζ)

  [(discharge-▽binding Ξ x Ξ_′ x τ)
   --------------
   (pattern->bindtree/~p Ξ x Ξ_′ τ)]

  [-----------
   (pattern->bindtree/~p Ξ (nope τ) Ξ τ)]

  [----------------
   (pattern->bindtree/~p Ξ () Ξ 𝟙)]

  [(bind-type ~p_1 X_1) (pattern->bindtree/~p Ξ ~p_1 Ξ_′ ζ_1)
   (bind-type ~p_2 X_2) (pattern->bindtree/~p Ξ_′ ~p_2 Ξ_′′ ζ_2)
   ----------------
   (pattern->bindtree/~p Ξ (pair ~p_1 ~p_2) Ξ_′′ (X_1 : ζ_1 ⊗ X_2 : ζ_2))]

  [(bind-type ~c X) (pattern->bindtree/~c Ξ ~c Ξ_′ ζ)
   ----------------
   (pattern->bindtree/~p Ξ (pack ~c) Ξ_′ (⊖ X : ζ))]

  [(discharge-△binding Ξ △χ Ξ_′ X τ)
   ----------------
   (pattern->bindtree/~p Ξ △χ Ξ_′ (↓ X : τ))])



(define-metafunction BS-elab
  expand-pattern/~p : Γ ζ K -> F

  [(expand-pattern/~p Γ 𝟙 K)
   {() ↦ K}]

  [(expand-pattern/~p Γ (~X_1 : τ_1 ⊗ ~X_2 : τ_2) K)
   {(pair x_1 x_2) ↦ K}
   (where x_2 (maybe-fresh ~X_2 (Γ K)))
   (where x_1 (maybe-fresh ~X_1 (Γ x_2 K)))]

  [(expand-pattern/~p Γ (~X : τ_1 ⊗ new : ζ_2) K)
   {(pair x_1 x_2) ↦ [CMD x_2 + F]}
   (where F (expand-pattern/~p Γ ζ_2 K))
   (where x_2 (fresh-immediate (Γ F)))
   (where x_1 (maybe-fresh ~X (Γ x_2 F)))]

  [(expand-pattern/~p Γ (new : ζ_1 ⊗ ~X : τ_2) K)
   {(pair x_1 x_2) ↦ [CMD x_1 + F]}
   (where x_2 (maybe-fresh ~X (Γ K)))
   (where F (expand-pattern/~p Γ ζ_1 K))
   (where x_1 (fresh-immediate (Γ x_2 F)))]

  [(expand-pattern/~p Γ (new : ζ_1 ⊗ new : ζ_2) K)
   {(pair x_1 x_2) ↦ [CMD x_1 + F_′]}
   (where F (expand-pattern/~p Γ ζ_2 K))
   (where x_2 (fresh-immediate (Γ F)))
   (where F_′ (expand-pattern/~p Γ ζ_1 [CMD x_2 + F]))
   (where x_1 (fresh-immediate (Γ F_′)))]

  [(expand-pattern/~p Γ (⊖ ~X : τ) K)
   {(pack x) ↦ K}
   (where x (maybe-fresh ~X (Γ K)))]

  [(expand-pattern/~p Γ (⊖ new : ζ) K)
   {(pack x) ↦ [CMD W - x]}
   (where W (expand-pattern/~c Γ ζ K))
   (where x (fresh-immediate (Γ W)))]

  [(expand-pattern/~p Γ (↓ ~X : τ) K)
   {(dn x) ↦ K}
   (where x (maybe-fresh ~X (Γ K)))]

  [(expand-pattern/~p Γ (⇑ ~X : τ) K)
   {(UP x) ↦ K}
   (where x (maybe-fresh ~X (Γ K)))]

  [(expand-pattern/~p Γ (⇑ new : ζ) K)
   {(UP x) ↦ [CMD x + F]}
   (where F (expand-pattern/~p Γ ζ (Γ K)))
   (where x (fresh-immediate F))])





(define-judgment-form BS-elab
  #:mode (▽producer I O I I O)
  #:contract (▽producer Γ Ξ τ p P)

  [(cut (bindings-snoc Γ △χ) Ξ k K) (discharge-△binding Ξ △χ Ξ_′ X τ_′) (type-= τ_′ τ)
   (where x (maybe-fresh X (Γ K)))
   ----------
   (▽producer Γ Ξ_′ τ {let/C △χ ↦ k} {let/C x ↦ K})]

  [(var-check x Γ)
   ---------- "▽Var_P"
   (▽producer Γ ((req x prod τ)) τ x x)]
  
  [---------- "𝟙_P"
   (▽producer Γ () 𝟙 () ())]
  
  [(▽producer Γ Ξ_1 τ_1 p_1 W_1) (▽producer Γ Ξ_2 τ_2 p_2 W_2)
   ---------- "⊗_P"
   (▽producer Γ (requirements-⊔ Ξ_1 Ξ_2) (τ_1 ⊗ τ_2) (pair p_1 p_2) (pair W_1 W_2))]

  [(▽producer Γ Ξ τ_l p W)
   ---------- "⊕_Pl"
   (▽producer Γ Ξ (τ_l ⊕ τ_r) (ιl p) (ιl W))]

  [(▽producer Γ Ξ τ_r p W)
   ---------- "⊕_Pr"
   (▽producer Γ Ξ (τ_l ⊕ τ_r) (ιr p) (ιr W))]

  [(▽consumer Γ Ξ τ c F)
   ---------- "⊖_P"
   (▽producer Γ Ξ (⊖ τ) (pack c) (⊖ F))]

  [(△producer Γ Ξ p τ_′ κ P) (kind-= κ -) (type-= τ_′ τ)
   ---------- "↓_P"
   (▽producer Γ Ξ τ p (dn P))]

  [(▽producer Γ Ξ τ p W)
   ---------- "⇑_P"
   (▽producer Γ Ξ (⇑ τ) (UP p) (UP W))])




(define-judgment-form BS-elab
  #:mode (△producer I O I O O O)
  #:contract (△producer Γ Ξ p τ κ P)

  [(cut (bindings-snoc Γ ~c) Ξ k K) (pattern->bindtree/~c Ξ ~c Ξ_′ ζ) (where W (expand-pattern/~c Γ ζ K)) (extract-type ζ τ) (△type τ -) (where x (fresh-immediate (Γ W)))
   ----------
   (△producer Γ Ξ_′ {let/C ~c κ ↦ k} τ - {let/C x ↦ [CMD W - x]})]

  [(var-synth x τ Γ) (△type τ κ)
   ----------
   (△producer Γ ((req x prod τ)) x τ κ x)]

  [----------
   (△producer Γ ∅ {↦} ⊤ - {↦})]

  [(cut Γ Ξ k K)
   ----------
   (△producer Γ Ξ {[] ↦ k} ⊥ - {[] ↦ K})]

  [(cut (bindings-snoc Γ ~c) Ξ k K) (pattern->bindtree/~c Ξ ~c Ξ_′ ζ) (where W (expand-pattern/~c Γ ζ K)) (extract-type ζ τ) (△type τ κ)
   ----------
   (△producer Γ Ξ_′ {~c ↦ k} τ κ W)]

  [(cut (bindings-snoc Γ ~c_l) Ξ_l k_l K_l) (pattern->bindtree/~c Ξ_l ~c_l Ξ_l′ ζ_l) (where W_l (expand-pattern/~c Γ ζ_l K_l)) (extract-type ζ_l τ_l) (△type τ_l -) (where x_l (fresh-immediate (Γ W_l)))
   (cut (bindings-snoc Γ ~c_r) Ξ_r k_r K_r) (pattern->bindtree/~c Ξ_r ~c_r Ξ_r′ ζ_r) (where W_r (expand-pattern/~c Γ ζ_r K_r)) (extract-type ζ_r τ_r) (△type τ_r -) (where x_r (fresh-immediate (Γ W_r)))
   ----------
   (△producer Γ (requirements-⊓ Ξ_l′ Ξ_r′) {[πl ~c_l] ↦ k_l \| [πr ~c_r] ↦ k_r} (τ_l & τ_r) -
     {[πl x_l] ↦ [CMD W_l - x_l] \| [πr x_r] ↦ [CMD W_r - x_r]})]

  [(cut (bindings-snoc Γ ~c_l) Ξ_l k_l K_l) (pattern->bindtree/~c Ξ_l ~c_l Ξ_l′ ζ_l) (where W_l (expand-pattern/~c Γ ζ_l K_l)) (extract-type ζ_l τ_l) (△type τ_l -)
   (where x_l (fresh-immediate (Γ W_l))) (where x_r (fresh-immediate (Γ)))
   ----------
   (△producer Γ (requirements-⊓ Ξ_l′ ∅) {[πl ~c_l] ↦ k_l} (τ_l & 𝟘) -
     {[πl x_l] ↦ [CMD W_l - x_l] \| [πr x_r] ↦ [CMD {↦} - x_r]})]

 [(cut (bindings-snoc Γ ~c_r) Ξ_r k_r K_r) (pattern->bindtree/~c Ξ_r ~c_r Ξ_r′ ζ_r) (where W_r (expand-pattern/~c Γ ζ_r K_r)) (extract-type ζ_r τ_r) (△type τ_r -)
   (where x_r (fresh-immediate (Γ W_r))) (where x_l (fresh-immediate (Γ)))
   ----------
   (△producer Γ (requirements-⊓ ∅ Ξ_r′) {[πl ~c_l] ↦ k_l \| [πr ~c_r] ↦ k_r} (𝟘 & τ_r) -
     {[πl x_l] ↦ [CMD {↦} - x_l] \| [πr x_r] ↦ [CMD W_r - x_r]})])




(define-judgment-form BS-elab
  #:mode (pattern->bindtree/~c I I O O)
  #:contract (pattern->bindtree/~c Ξ ~c Ξ ζ)

  [(discharge-▽binding Ξ x Ξ_′ x τ)
   ------------------
   (pattern->bindtree/~c Ξ x Ξ_′ τ)]

  [----------------
   (pattern->bindtree/~c Ξ [] Ξ ⊥)]

  [(bind-type ~c_1 X_1) (bind-type ~c_2 X_2)
   (pattern->bindtree/~c Ξ ~c_1 Ξ_′ ζ_1) (pattern->bindtree/~c Ξ_′ ~c_2 Ξ_′′ ζ_2)
   ----------------
   (pattern->bindtree/~c Ξ [duo ~c_1 ~c_2] Ξ_′′ (X_1 : ζ_1 ⅋ X_2 : ζ_2))]

  [(bind-type ~p X) (pattern->bindtree/~p Ξ ~p Ξ_′ ζ)
   ----------------
   (pattern->bindtree/~c Ξ [throw ~p] Ξ_′ (¬ X : ζ))]

  [(discharge-△binding Ξ △χ Ξ_′ X τ)
   ----------------
   (pattern->bindtree/~c Ξ △χ Ξ_′ (↑ X : τ))])


(define-metafunction BS-elab
  expand-pattern/~c : Γ ζ K -> W

  [(expand-pattern/~c Γ ⊥ K)
   {[] ↦ K}]

  [(expand-pattern/~c Γ (~X_1 : τ_1 ⅋ ~X_2 : τ_2) K)
   {[duo x_1 x_2] ↦ K}
   (where x_2 (maybe-fresh ~X_2 (Γ K)))
   (where x_1 (maybe-fresh ~X_1 (Γ x_2 K)))]

  [(expand-pattern/~c Γ (new : ζ_1 ⅋ ~X : τ_2) K)
   {[duo x_1 x_2] ↦ [CMD W - x_1]}
   (where W (expand-pattern/~c Γ ζ_1 K))
   (where x_2 (maybe-fresh ~X (Γ W)))
   (where x_1 (fresh-immediate (Γ x_2 W)))]

  [(expand-pattern/~c Γ (~X : τ_1 ⅋ new : ζ_2) K)
   {[duo x_1 x_2] ↦ [CMD W - x_2]}
   (where W (expand-pattern/~c Γ ζ_2 K))
   (where x_2 (fresh-immediate (Γ W)))
   (where x_1 (maybe-fresh (Γ x_2 W)))]

  [(expand-pattern/~c Γ (new : ζ_1 ⅋ new : ζ_2) K)
   {[duo x_1 x_2] ↦ [CMD W_′ - x_1]}
   (where W (expand-pattern Γ ζ_2 K))
   (where x_2 (fresh-immediate (Γ W)))
   (where W_′ (expand-pattern Γ ζ_1 [CMD W - x_2]))
   (where x_1 (fresh-immediate (Γ W_′)))]

  [(expand-pattern/~c Γ (¬ ~X : τ) K)
   {[pack x] ↦ K}
   (where x (maybe-fresh ~X (Γ K)))]

  [(expand-pattern/~c Γ (¬ new : ζ) K)
   {[pack x] ↦ [CMD x + F]}
   (where F (expand-pattern/~p Γ ζ K))
   (where x (fresh-immediate x (Γ F)))]

  [(expand-pattern/~c Γ (↑ ~X : τ) K)
   {[up x] ↦ K}
   (where x (maybe-fresh ~X (Γ K)))]

  [(expand-pattern/~c Γ (⇓ ~X : τ) K)
   {[DN x] ↦ K}
   (where x (maybe-fresh ~X (Γ K)))]

  [(expand-pattern/~c Γ (⇓ new : ζ) K)
   {[DN x] ↦ [CMD W - x]}
   (where W (expand-pattern/~c Γ ζ K))
   (where x (fresh-immediate (Γ W)))])



(define-judgment-form BS-elab
  #:mode (▽consumer I O I I O)
  #:contract (▽consumer Γ Ξ τ c C)
  
  [(cut (bindings-snoc Γ △χ) Ξ k K) (discharge-△binding Ξ △χ Ξ_′ X τ_′) (type-= τ_′ τ)
   (where x (maybe-fresh X (Γ K)))
   ----------
   (▽consumer Γ Ξ_′ τ {let/P △χ ↦ k} {let/P x ↦ K})]

  [(var-check x Γ)
   ----------
   (▽consumer Γ ((req x con τ)) x τ x)]

  [----------
   (▽consumer Γ () ⊥ [] [])]

  [(▽consumer Γ Ξ_1 τ_1 c_1 F_1) (▽consumer Γ Ξ_2 τ_2 c_2 F_2)
   ----------
   (▽consumer Γ (requirements-⊔ Ξ_1 Ξ_2) (τ_1 ⅋ τ_2) [duo c_1 c_2] [duo F_1 F_2])]

  [(▽consumer Γ Ξ τ_l c F)
   ----------
   (▽consumer Γ Ξ (τ_l & τ_r) [πl c] [πl F])]

  [(▽consumer Γ Ξ τ_r c F)
   ----------
   (▽consumer Γ Ξ (τ_l & τ_r) [πr c] [πr F])]

  [(▽producer Γ Ξ τ p W)
   ----------
   (▽consumer Γ Ξ (¬ τ) [throw p] [throw W])]

  [(△consumer Γ Ξ c τ_′ κ C) (kind-= κ +) (type-= τ_′ τ)
   ----------
   (▽consumer Γ Ξ τ c [up C])]

  [(▽consumer Γ Ξ τ c F)
   ----------
   (▽consumer Γ Ξ (⇓ τ) [DN c] [DN F])])





(define red/BS
  (reduction-relation
   BS-elab
   #:domain K
   #:codomain K

   [--> [CMD W + {let/P X ↦ K}]
        (substitute K X W)
        "let W_β"]

   [--> [CMD {let/C X ↦ K} + C]
        (substitute K X C)
        "let C_β"]

   [--> [CMD () + {() ↦ K}]
        K
        "𝟙_β"]

   [--> [CMD (pair W_1 W_2) + {(pair X_1 X_2) ↦ K}]
        (substitute K [X_1 W_1]  [X_2 W_2])
        "⊗_β"]

   [--> [CMD (ιl W) + {(ιl X_l) ↦ K_l \| (ιr X_r) ↦ K_r}]
        (substitute K_l X_l W)
        "⊕l_β"]

   [--> [CMD (ιr W) + {(ιl X_l) ↦ K_l \| (ιr X_r) ↦ K_r}]
        (substitute K_r X_r W)
        "⊕r_β"]

   [--> [CMD (pack F) + {(pack X) ↦ K}]
        (substitute K X F)
        "⊖_β"]

   [--> [CMD (dn V-) + {(dn X) ↦ K}]
        (substitute K X V-)
        "↓_β"]

   [--> [CMD (UP W) - {(UP X) ↦ K}]
        (substitute K X W)
        "⇑_β"]

   [--> [CMD {let/C X ↦ K} - F]
        (substitute K X F)
        "let F_β"]

   [--> [CMD P - {let/P X ↦ K}]
        (substitute K X P)
        "let P_β"]

   [--> [CMD {[] ↦ K} - []]
        K
        "⊥_β"]

   [--> [CMD {[duo X_1 X_2] ↦ K} - [duo F_1 F_2]]
        (substitute2 K [X_1 F_1] [X_2 F_2])
        "⅋_β"]

   [--> [CMD {[πl X_l] ↦ K_l \| [πr X_r] ↦ K_r} - [πl F]]
        (substitute K_l X_l F)
        "&l_β"]

   [--> [CMD {[πl X_l] ↦ K_l \| [πr X_r] ↦ K_r} - [πr F]]
        (substitute K_r X_r F)
        "&r_β"]

   [--> [CMD {(throw X) ↦ K} - (throw W)]
        (substitute K X W)
        "¬_β"]

   [--> [CMD {(up X) ↦ K} - (up Q+)]
        (substitute K X Q+)
        "↑_β"]

   [--> [CMD {(DN X) ↦ K} + (DN F)]
        (substitute K X F)
        "⇓_β"]))




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

  (define (prettify/elab-term Γ Ξ t T #:ty [ty #false])
    (define turnstile (if ty
                          (list (hb-append (text " ⊢" (literal-style)) (orientation-script ty #true)) " ")
                          (list " ⊢ ")))
    (prettify "⟦" (list Γ "; " Ξ turnstile t) "⟧ ↝ " (list T)))

  (define (orientation-script type sub?)
    (define script (if sub? 'subscript 'superscript))
    (match type
      ['o (text "o" (cons script (non-terminal-style)))]
      ['prod (text "P" (cons script (literal-style)))]
      ['con (text "C" (cons script (literal-style)))]))


  (define (bind-or-var x o)
    (list x (orientation-script o #false)))

  
  (define (prettify/elab-synth ξ Ξ t τ κ T #:ty ty)
    (prettify/elab-term ξ Ξ (list t " ∈ " τ " ∈ " κ) T #:ty ty))

  (define (prettify/elab-check ξ Ξ τ t T #:ty ty)
    (prettify/elab-term ξ Ξ (list τ " ∋ " t) T #:ty ty))

  
  (define (with-my-rewriters proc)
    (with-compound-rewriters
        (['pair (match-λ [(list _ _ p_1 p_2 _)
                          (prettify "(" p_1 ", " p_2 ")")])]
         ['duo (match-λ [(list _ _ c_1 c_2 _)
                         (prettify "[" c_1 ", " c_2 "]")])]
         ['cmd (match-λ [(list _ _ p ◊ c _)
                         (prettify p ◊ c)])]
         ['CMD (match-λ [(list _ _ P κ C _)
                         (prettify P κ C)])]
         ['△var (match-λ [(list _ _ x τ _)
                          (prettify x " : " τ)])]
         ['▽bound (match-λ [(list _ _ x _)
                            (prettify x)])]
         ['△bound (match-λ [(list _ _ x τ _)
                            (prettify x " : " τ)])]
         ['nope (match-λ [(list _ _ τ _)
                          (prettify "_ : " τ)])]
         ['req (match-λ [(list _ _ x o τ _)
                         (prettify (bind-or-var x (lw-e o)) " : " τ)])]
         ['var-check (match-λ [(list _ _ x Γ _)
                               (prettify x " ∈ " Γ)])]
         ['var-synth (match-λ [(list _ _ x τ Γ _)
                               (prettify x " : " τ " ∈ " Γ)])]
         ['bindings-snoc (match-λ [(list _ _  Γ ~~ _)
                                   (prettify Γ ", " ~~)])]
         ['discharge-▽binding (match-λ [(list _ _ Ξ χ Ξ_′ X τ _)
                                        (prettify  Ξ "⟦" χ "⟧ ↝ " Ξ_′ "; " X " : " τ)])]
         ['discharge-△binding (match-λ [(list _ _ Ξ χ Ξ_′ X τ _)
                                        (prettify  Ξ "⟦" χ "⟧ ↝ " Ξ_′ "; " X " : " τ)])]
         ['maybe-fresh (match-λ [(list _ _ ~X stuff _)
                                 (prettify ~X ".?fresh(" stuff ")")])]
         ['fresh-immediate (match-λ [(list _ _ stuff _)
                                     (prettify "fresh(" stuff ")")])]
         ['pattern->bindtree/~p (match-λ [(list _ _ Ξ ~p Ξ_′ ζ _)
                                          (prettify Ξ "[" ~p "] → " Ξ_′ "; " ζ)])]
         ['pattern->bindtree/~c (match-λ [(list _ _ Ξ ~c Ξ_′ ζ _)
                                          (prettify Ξ "[" ~c "] → " Ξ_′ "; " ζ)])]
         ['expand-pattern/~p (match-λ [(list _ _ Γ ζ K _)
                                       (prettify "expand(" Γ ", " ζ ", " K ")" )])]
         ['expand-pattern/~c (match-λ [(list _ _ Γ ζ K _)
                                       (prettify "expand(" Γ ", " ζ ", " K ")" )])]
         ['extract-type (match-λ [(list _ _ ζ τ _)
                                  (prettify ζ " ⇒ " τ)])]
         ['△type (match-λ [(list _ _ τ κ _)
                           (prettify τ " ∈ " κ)])]
         ['kind-= (match-λ [(list _ _ κ κ_′ _)
                            (prettify κ " = " κ_′)])]
         ['type-= (match-λ [(list _ _ τ τ_′ _)
                            (prettify τ " = " τ_′)])]
         ['requirements-⊔ (match-λ [(list _ _ Ξ_1 Ξ_2 _)
                                    (prettify Ξ_1 " ⊔ " Ξ_2)])]
         ['requirements-⊓ (match-λ [(list _ _ Ξ_1 Ξ_2 _)
                                    (prettify Ξ_1 " ⊓ " Ξ_2)])]
         ['cut (match-λ [(list _ _ ξ Ξ k K _)
                         (prettify/elab-term ξ Ξ k K)])]
         ['△consumer (match-λ [(list _ _ ξ Ξ c τ κ C _)
                               (prettify/elab-synth ξ Ξ c τ κ C #:ty 'con)])]
         ['▽producer (match-λ [(list _ _ ξ Ξ τ p P _)
                               (prettify/elab-check ξ Ξ τ p P #:ty 'prod)])]
         ['△producer (match-λ [(list _ _ ξ Ξ p τ κ P _)
                               (prettify/elab-synth ξ Ξ p τ κ P #:ty 'prod)])]
         ['▽consumer (match-λ [(list _ _ ξ Ξ τ c C _)
                               (prettify/elab-check ξ Ξ τ c C #:ty 'con)])]
         ['substitute (match-λ [(list _ _ t (lw (list _ v_1 e_1 _) _ _ _ _ _ _) (lw (list _ v_2 e_2 _) _ _ _ _ _ _) _)
                                (prettify t "[" v_1 " := " e_1 ", " v_2 " := " e_2 "]")]
                               [(list _ _ t v e _)
                                (prettify t "[" v " := " e "]")])])
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
           ['let/C (λ () (make-literal-pict "let" #:post-sub "C"))])
        (proc))))


  (define-syntax-rule (pretty-term tm)
    (with-my-rewriters (λ () (term->pict BS-elab tm))))

  (define-syntax-rule (pretty-metafunction-sig fun result)
    (hb-append (/ (default-font-size) 3)
               (pretty-term fun)
               (arrow->pict '->)
               (pretty-term result)))
  )
