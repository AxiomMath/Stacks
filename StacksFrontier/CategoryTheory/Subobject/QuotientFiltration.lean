module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksCore.CategoryTheory.Abelian.Subobject
public import StacksFrontier.CategoryTheory.Subobject.CokernelOfLE

/-!
# Filtrations, their quotient filtrations, and multiplicative invariants

Let `E` be an object of an abelian category with a finite filtration by subobjects

  `0 = E_0 ⊂ E_1 ⊂ … ⊂ E_r = E`,   `E_i / E_{i-1} ≅ L_i`.

The image of the filtration in the quotient `q : E ⟶ E / E_1` is a filtration

  `0 = E_1 / E_1 ⊂ E_2 / E_1 ⊂ … ⊂ E_r / E_1 = E / E_1`

with the same subquotients `L_2, …, L_r` (the third isomorphism theorem), and `E` itself is an
extension `0 ⟶ L_1 ⟶ E ⟶ E / E_1 ⟶ 0`. Peeling off the bottom step in this way, an invariant
`c` of objects which is multiplicative on extensions `0 ⟶ L ⟶ E ⟶ F ⟶ 0` whose sub `L` belongs
to a given class takes the value

  `c(E) = c(L_1) c(L_2) ⋯ c(L_r)`

on `E`. This is the shape of the computation of a total Chern class from a filtration with
invertible subquotients, where `c` is multiplicative on extensions by an invertible sub, and
the general form of it is recorded here.

Conversely, filtrations can be concatenated along a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`: the images in `X₂` of the steps of a filtration of `X₁`, followed by the
preimages in `X₂` of the steps of a filtration of `X₃`, form a filtration of `X₂` whose
subquotients are those of the first filtration followed by those of the second.

## Main definitions

* `CategoryTheory.Abelian.Subobject.cokernelOfLEExistsCokernelπIso` — for subobjects
  `A ≤ X' ≤ Y'` of `E`, the identification of the subquotient `(Y'/A)/(X'/A)` of `E/A` with
  `Y'/X'`.
* `CategoryTheory.Abelian.Subobject.concatFiltration` — the filtration of the middle term of a
  short exact sequence built from filtrations of the outer terms, and
  `CategoryTheory.Abelian.Subobject.concatFiltrationSubquotientIso` the identification of its
  subquotients.

## Main results

* `CategoryTheory.Abelian.Subobject.kernelSubobject_cokernel_π_arrow` — the kernel of
  `E ⟶ E/A` is `A`.
* `CategoryTheory.Abelian.Subobject.pullback_exists_cokernel_π` — a subobject containing `A` is
  the preimage of its image in `E/A`.
* `CategoryTheory.Abelian.Subobject.exists_and_eq_prod_of_filtration` — the product formula for
  a rank-graded invariant which is multiplicative on extensions with sub in a given class, and
  `CategoryTheory.Abelian.Subobject.prop_of_filtration` the rank of a filtered object.
* `CategoryTheory.Abelian.Subobject.monotone_concatFiltration`,
  `CategoryTheory.Abelian.Subobject.concatFiltration_zero` and
  `CategoryTheory.Abelian.Subobject.concatFiltration_last` — the concatenation is a filtration
  from `⊥` to `⊤`.
-/

@[expose] public section

universe v u w

namespace CategoryTheory.Abelian.Subobject

open CategoryTheory.Subobject Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The kernel of the quotient map `E ⟶ E/A` is the subobject `A`. -/
lemma kernelSubobject_cokernel_π_arrow {E : C} (A : Subobject E) :
    kernelSubobject (cokernel.π A.arrow) = A := by
  rw [← imageSubobject_eq_kernelSubobject, imageSubobject_mono, mk_arrow]

/-- The image of `A` in `E/A` is zero. -/
lemma exists_cokernel_π_self {E : C} (A : Subobject E) :
    («exists» (cokernel.π A.arrow)).obj A = ⊥ := by
  rw [exists_eq_imageSubobject, cokernel.condition, imageSubobject_zero]

/-- The image of `E` in a quotient of `E` is everything. -/
lemma exists_top_of_epi {E Q : C} (q : E ⟶ Q) [Epi q] : («exists» q).obj ⊤ = ⊤ := by
  rw [← exists_pullback_eq_self_of_epi q ⊤, pullback_top]

/-- A subobject `B` of `E` containing `A` is the preimage of its image in `E/A`. -/
lemma pullback_exists_cokernel_π {E : C} {A B : Subobject E} (h : A ≤ B) :
    (Subobject.pullback (cokernel.π A.arrow)).obj ((«exists» (cokernel.π A.arrow)).obj B) = B :=
  pullback_exists_eq_self_of_epi _ B (by rwa [kernelSubobject_cokernel_π_arrow])

/-- **The third isomorphism theorem for subquotients.** For subobjects `A ≤ X' ≤ Y'` of `E`,
the subquotient of `E/A` cut out by the images of `X'` and `Y'` is `Y'/X'`. -/
noncomputable def cokernelOfLEExistsCokernelπIso {E : C} {A X' Y' : Subobject E} (hX : A ≤ X')
    (h : X' ≤ Y') :
    cokernel (ofLE ((«exists» (cokernel.π A.arrow)).obj X')
        ((«exists» (cokernel.π A.arrow)).obj Y') ((«exists» _).monotone h)) ≅
      cokernel (ofLE X' Y' h) :=
  (cokernelOfLEPullbackIso (cokernel.π A.arrow) ((«exists» _).monotone h)).symm ≪≫
    cokernelOfLEIsoOfEq _ _ (pullback_exists_cokernel_π hX)
      (pullback_exists_cokernel_π (hX.trans h))

/-- The bottom step of a filtration starting at `⊥` is the subobject itself: for `A = ⊥`, the
quotient `B / A` is `B`. -/
noncomputable def cokernelOfLEBotIso {E : C} {A B : Subobject E} (h : A ≤ B) (hA : A = ⊥) :
    cokernel (ofLE A B h) ≅ (B : C) :=
  cokernelIsoOfEq (f := ofLE A B h) (g := 0)
      (((isZero_zero C).of_iso (isoOfEq _ _ hA ≪≫ botCoeIsoZero)).eq_of_src _ _) ≪≫
    cokernelZeroIsoTarget

/-- **A multiplicative invariant along a filtration.** Let `P r` be a class of objects
("of rank `r`"), `I` a class of objects, `c r X` an invariant of objects `X` of rank `r` and
`y L` an element attached to each `L` in `I`, such that zero objects have rank `0` and invariant
`1`, and such that for every short exact sequence `0 ⟶ L ⟶ X ⟶ F ⟶ 0` with `L` in `I` and `F` of
rank `r`, the object `X` has rank `r + 1` and `c (r + 1) X = y L * c r F`. Then an object `E`
with a filtration `0 = E_0 ⊂ E_1 ⊂ … ⊂ E_r = E` by subobjects with `E_{i+1}/E_i ≅ L_i` in `I`
has rank `r`, and

  `c r E = y L_0 * y L_1 * ⋯ * y L_{r-1}`.

The filtration is indexed by `Fin (r + 1)` and the subquotients by `Fin r`. -/
theorem exists_and_eq_prod_of_filtration {M : Type w} [Monoid M]
    (P : ℕ → C → Prop) (I : C → Prop) (c : ∀ (r : ℕ) (X : C), P r X → M) (y : ∀ X, I X → M)
    (hP₀ : ∀ X : C, IsZero X → P 0 X) (hc₀ : ∀ (X : C) (hX : P 0 X), c 0 X hX = 1)
    (hP : ∀ (r : ℕ) (S : ShortComplex C), S.ShortExact → I S.X₁ → P r S.X₃ → P (r + 1) S.X₂)
    (hc : ∀ (r : ℕ) (S : ShortComplex C) (_ : S.ShortExact) (h₁ : I S.X₁) (h₂ : P (r + 1) S.X₂)
      (h₃ : P r S.X₃), c (r + 1) S.X₂ h₂ = y S.X₁ h₁ * c r S.X₃ h₃) :
    ∀ (r : ℕ) (E : C) (L : Fin r → C) (hL : ∀ i, I (L i)) (F : Fin (r + 1) → Subobject E)
      (hF : Monotone F) (_ : F 0 = ⊥) (_ : F (Fin.last r) = ⊤)
      (_ : ∀ i : Fin r,
        cokernel (ofLE (F i.castSucc) (F i.succ) (hF i.castSucc_le_succ)) ≅ L i),
      ∃ hE : P r E, c r E hE = (List.ofFn fun i ↦ y (L i) (hL i)).prod
  | 0, E, L, hL, F, hF, h0, hr, e => by
      have hz : IsZero E := (isZero_zero C).of_iso
        ((asIso (⊤ : Subobject E).arrow).symm ≪≫ isoOfEq _ _ (hr.symm.trans h0) ≪≫ botCoeIsoZero)
      exact ⟨hP₀ E hz, by rw [hc₀, List.ofFn_zero, List.prod_nil]⟩
  | r + 1, E, L, hL, F, hF, h0, hr, e => by
      set A : Subobject E := F 1
      let q := cokernel.π A.arrow
      let G : Fin (r + 1) → Subobject (cokernel A.arrow) := fun j ↦ («exists» q).obj (F j.succ)
      have hFs := hF.comp Fin.strictMono_succ.monotone
      have hG : Monotone G := («exists» q).monotone.comp hFs
      have hAF : ∀ j : Fin (r + 1), A ≤ F j.succ := fun j ↦ hFs (Fin.zero_le j)
      have hG0 : G 0 = ⊥ := exists_cokernel_π_self A
      have hGr : G (Fin.last r) = ⊤ := by
        change («exists» q).obj (F (Fin.last (r + 1))) = ⊤
        rw [hr, exists_top_of_epi]
      let eG : ∀ i : Fin r,
          cokernel (ofLE (G i.castSucc) (G i.succ) (hG i.castSucc_le_succ)) ≅ L i.succ :=
        fun i ↦
          have hi : F i.castSucc.succ ≤ F i.succ.succ := hFs i.castSucc_le_succ
          cokernelOfLEExistsCokernelπIso (hAF i.castSucc) hi ≪≫
            cokernelOfLEIsoOfEq hi (hF i.succ.castSucc_le_succ) (by rw [Fin.succ_castSucc]) rfl ≪≫
              e i.succ
      obtain ⟨hQ, hcQ⟩ := exists_and_eq_prod_of_filtration P I c y hP₀ hc₀ hP hc r
        (cokernel A.arrow) (fun i ↦ L i.succ) (fun i ↦ hL i.succ) G hG hG0 hGr eG
      -- the bottom step `0 ⟶ L_0 ⟶ E ⟶ E/E_1 ⟶ 0`
      let φ : L 0 ≅ (A : C) := (e 0).symm ≪≫ cokernelOfLEBotIso _ h0
      let S : ShortComplex C := ShortComplex.mk (φ.hom ≫ A.arrow) q
        (by rw [Category.assoc, cokernel.condition, comp_zero])
      have hS : S.ShortExact :=
        ShortComplex.shortExact_of_iso (S₁ := ShortComplex.mk A.arrow q (cokernel.condition _))
          (ShortComplex.isoMk φ.symm (Iso.refl _) (Iso.refl _) (by simp [S]) (by simp [S]))
          { exact := ShortComplex.exact_cokernel A.arrow }
      have hE : P (r + 1) E := hP r S hS (hL 0) hQ
      refine ⟨hE, ?_⟩
      rw [hc r S hS (hL 0) hE hQ, List.ofFn_succ, List.prod_cons]
      exact congrArg _ hcQ

/-- **The rank of an object with a filtration.** Let `P r` be a class of objects ("of rank `r`")
and `I` a class of objects such that zero objects have rank `0` and an extension of an object of
rank `r` by an object of `I` has rank `r + 1`. Then an object with a filtration of length `r`
whose subquotients lie in `I` has rank `r`. -/
theorem prop_of_filtration (P : ℕ → C → Prop) (I : C → Prop) (hP₀ : ∀ X : C, IsZero X → P 0 X)
    (hP : ∀ (r : ℕ) (S : ShortComplex C), S.ShortExact → I S.X₁ → P r S.X₃ → P (r + 1) S.X₂)
    {r : ℕ} {E : C} (L : Fin r → C) (hL : ∀ i, I (L i)) (F : Fin (r + 1) → Subobject E)
    (hF : Monotone F) (h0 : F 0 = ⊥) (hr : F (Fin.last r) = ⊤)
    (e : ∀ i : Fin r, cokernel (ofLE (F i.castSucc) (F i.succ) (hF i.castSucc_le_succ)) ≅ L i) :
    P r E :=
  (exists_and_eq_prod_of_filtration (M := ℕ) P I (fun _ _ _ ↦ 1) (fun _ _ ↦ 1) hP₀
    (fun _ _ ↦ rfl) hP (fun _ _ _ _ _ _ ↦ rfl) r E L hL F hF h0 hr e).1

/-- **The product formula along a filtration.** Under the hypotheses of
`CategoryTheory.Abelian.Subobject.exists_and_eq_prod_of_filtration`, for an object `E` of rank
`r` with a filtration `0 = E_0 ⊂ E_1 ⊂ … ⊂ E_r = E` with `E_{i+1}/E_i ≅ L_i` in `I`,

  `c r E = y L_0 * y L_1 * ⋯ * y L_{r-1}`. -/
theorem eq_prod_of_filtration {M : Type w} [Monoid M]
    (P : ℕ → C → Prop) (I : C → Prop) (c : ∀ (r : ℕ) (X : C), P r X → M) (y : ∀ X, I X → M)
    (hP₀ : ∀ X : C, IsZero X → P 0 X) (hc₀ : ∀ (X : C) (hX : P 0 X), c 0 X hX = 1)
    (hP : ∀ (r : ℕ) (S : ShortComplex C), S.ShortExact → I S.X₁ → P r S.X₃ → P (r + 1) S.X₂)
    (hc : ∀ (r : ℕ) (S : ShortComplex C) (_ : S.ShortExact) (h₁ : I S.X₁) (h₂ : P (r + 1) S.X₂)
      (h₃ : P r S.X₃), c (r + 1) S.X₂ h₂ = y S.X₁ h₁ * c r S.X₃ h₃)
    {r : ℕ} {E : C} (hE : P r E) (L : Fin r → C) (hL : ∀ i, I (L i))
    (F : Fin (r + 1) → Subobject E) (hF : Monotone F) (h0 : F 0 = ⊥) (hr : F (Fin.last r) = ⊤)
    (e : ∀ i : Fin r, cokernel (ofLE (F i.castSucc) (F i.succ) (hF i.castSucc_le_succ)) ≅ L i) :
    c r E hE = (List.ofFn fun i ↦ y (L i) (hL i)).prod :=
  (exists_and_eq_prod_of_filtration P I c y hP₀ hc₀ hP hc r E L hL F hF h0 hr e).2

/-! ### Concatenating filtrations along a short exact sequence -/

section Concat

variable {S : ShortComplex C}

/-- The preimage of `0` under the quotient map of an exact sequence `X₁ ⟶ X₂ ⟶ X₃` with
monomorphic first map is the image of `X₁`. -/
lemma pullback_bot_eq_map_top (hS : S.Exact) [Mono S.f] :
    (Subobject.pullback S.g).obj ⊥ = (map S.f).obj ⊤ := by
  have := cokernel.π_of_zero (Subobject.bot_arrow : (⊥ : Subobject S.X₃).arrow = 0)
  rw [pullback_eq_kernelSubobject, kernelSubobject_comp_mono, Subobject.map_top,
    ← imageSubobject_mono, (ShortComplex.exact_iff_image_eq_kernel S).mp hS]

/-- The filtration of the middle term `X₂` of a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`
obtained from filtrations `F₁` of `X₁` (of length `a`) and `F₃` of `X₃` (of length `b`): its
first `a` steps are the images of the steps of `F₁`, and the remaining ones the preimages of the
steps of `F₃`. -/
noncomputable def concatFiltration [Mono S.f] {a b : ℕ} (F₁ : Fin (a + 1) → Subobject S.X₁)
    (F₃ : Fin (b + 1) → Subobject S.X₃) (k : Fin (a + b + 1)) : Subobject S.X₂ :=
  if h : (k : ℕ) < a then (map S.f).obj (F₁ ⟨k, by omega⟩)
  else (Subobject.pullback S.g).obj (F₃ ⟨k - a, by omega⟩)

variable [Mono S.f] (hS : S.ShortExact) {a b : ℕ} {F₁ : Fin (a + 1) → Subobject S.X₁}
  {F₃ : Fin (b + 1) → Subobject S.X₃} (hF₁ : Monotone F₁) (hF₃ : Monotone F₃)
  (h₁0 : F₁ 0 = ⊥) (h₁a : F₁ (Fin.last a) = ⊤) (h₃0 : F₃ 0 = ⊥) (h₃b : F₃ (Fin.last b) = ⊤)
include hS

omit hS in
/-- Below `a`, the concatenated filtration is the image of the corresponding step of `F₁`. -/
lemma concatFiltration_of_lt {k : Fin (a + b + 1)} (hk : (k : ℕ) < a) :
    concatFiltration F₁ F₃ k = (map S.f).obj (F₁ ⟨k, by omega⟩) := dite_eq_left hk

omit hS in
/-- From `a` on, the concatenated filtration is the preimage of the corresponding step of
`F₃`. -/
lemma concatFiltration_of_le {k : Fin (a + b + 1)} (hk : a ≤ (k : ℕ)) :
    concatFiltration F₁ F₃ k = (Subobject.pullback S.g).obj (F₃ ⟨k - a, by omega⟩) :=
  dite_eq_right (by omega)

include h₁a h₃0 in
/-- The images of the steps of `F₁` and the preimages of the steps of `F₃` agree at the junction:
both describe the image of `X₁`. -/
lemma concatFiltration_eq_map {k : Fin (a + b + 1)} (hk : (k : ℕ) ≤ a) :
    concatFiltration F₁ F₃ k = (map S.f).obj (F₁ ⟨k, by omega⟩) := by
  rcases lt_or_eq_of_le hk with hk | hk
  · exact concatFiltration_of_lt hk
  · rw [concatFiltration_of_le hk.ge]
    have e₃ : (⟨k - a, by omega⟩ : Fin (b + 1)) = 0 := Fin.ext (by simp; omega)
    have e₁ : (⟨k, by omega⟩ : Fin (a + 1)) = Fin.last a := Fin.ext (by simp [hk])
    rw [e₃, e₁, h₃0, h₁a, pullback_bot_eq_map_top hS.exact]

include hF₁ hF₃ h₁a h₃0 in
/-- The concatenation of two monotone filtrations is monotone. -/
lemma monotone_concatFiltration : Monotone (concatFiltration F₁ F₃) := by
  intro i j hij
  have hij' : (i : ℕ) ≤ j := hij
  by_cases hj : (j : ℕ) ≤ a
  · rw [concatFiltration_eq_map hS h₁a h₃0 (hij'.trans hj), concatFiltration_eq_map hS h₁a h₃0 hj]
    exact (map S.f).monotone (hF₁ (show (⟨i, _⟩ : Fin (a + 1)) ≤ ⟨j, _⟩ from hij'))
  · rw [concatFiltration_of_le (k := j) (by omega)]
    by_cases hi : a ≤ (i : ℕ)
    · rw [concatFiltration_of_le hi]
      exact (Subobject.pullback S.g).monotone
        (hF₃ (show (⟨i - a, _⟩ : Fin (b + 1)) ≤ ⟨j - a, _⟩ from Fin.mk_le_mk.mpr (by omega)))
    · rw [concatFiltration_eq_map hS h₁a h₃0 (by omega)]
      calc (map S.f).obj (F₁ ⟨i, _⟩) ≤ (map S.f).obj ⊤ := (map S.f).monotone le_top
        _ = (Subobject.pullback S.g).obj (F₃ 0) := by
            rw [h₃0, pullback_bot_eq_map_top hS.exact]
        _ ≤ _ := (Subobject.pullback S.g).monotone (hF₃ (Fin.zero_le _))

include h₁0 h₁a h₃0 in
/-- The concatenated filtration starts at `⊥`. -/
lemma concatFiltration_zero : concatFiltration F₁ F₃ 0 = ⊥ := by
  rw [concatFiltration_eq_map hS h₁a h₃0 (by simp)]
  exact (congrArg _ h₁0).trans (Subobject.map_bot _)

omit hS in
include h₃b in
/-- The concatenated filtration ends at `⊤`. -/
lemma concatFiltration_last : concatFiltration F₁ F₃ (Fin.last (a + b)) = ⊤ := by
  rw [concatFiltration_of_le (by simp)]
  have e : (⟨(Fin.last (a + b) : ℕ) - a, by simp⟩ : Fin (b + 1)) = Fin.last b :=
    Fin.ext (by simp)
  rw [e, h₃b, pullback_top]

/-- **The subquotients of a concatenated filtration** are those of `F₁` followed by those of
`F₃`. -/
noncomputable def concatFiltrationSubquotientIso (L : Fin a → C) (M : Fin b → C)
    (e₁ : ∀ i : Fin a, cokernel (ofLE (F₁ i.castSucc) (F₁ i.succ) (hF₁ i.castSucc_le_succ)) ≅ L i)
    (e₃ : ∀ j : Fin b, cokernel (ofLE (F₃ j.castSucc) (F₃ j.succ) (hF₃ j.castSucc_le_succ)) ≅ M j)
    (i : Fin (a + b)) :
    cokernel (ofLE (concatFiltration F₁ F₃ i.castSucc) (concatFiltration F₁ F₃ i.succ)
        (monotone_concatFiltration hS hF₁ hF₃ h₁a h₃0 i.castSucc_le_succ)) ≅
      Fin.addCases (motive := fun _ ↦ C) L M i := by
  have := hS.epi_g
  refine Fin.addCases (motive := fun i ↦ cokernel (ofLE (concatFiltration F₁ F₃ i.castSucc)
      (concatFiltration F₁ F₃ i.succ)
      (monotone_concatFiltration hS hF₁ hF₃ h₁a h₃0 i.castSucc_le_succ)) ≅
      Fin.addCases (motive := fun _ ↦ C) L M i) (fun i ↦ ?_) (fun j ↦ ?_) i
  · rw [Fin.addCases_left]
    have hle : (map S.f).obj (F₁ i.castSucc) ≤ (map S.f).obj (F₁ i.succ) :=
      (map S.f).monotone (hF₁ i.castSucc_le_succ)
    refine cokernelOfLEIsoOfEq _ hle ?_ ?_ ≪≫ cokernelOfLEMapIso S.f _ ≪≫ e₁ i
    · rw [concatFiltration_eq_map hS h₁a h₃0 (by simp)]
      rfl
    · rw [concatFiltration_eq_map hS h₁a h₃0 (by simp; omega)]
      rfl
  · rw [Fin.addCases_right]
    have hle : (Subobject.pullback S.g).obj (F₃ j.castSucc) ≤
        (Subobject.pullback S.g).obj (F₃ j.succ) :=
      (Subobject.pullback S.g).monotone (hF₃ j.castSucc_le_succ)
    refine cokernelOfLEIsoOfEq _ hle ?_ ?_ ≪≫ cokernelOfLEPullbackIso S.g _ ≪≫ e₃ j
    · rw [concatFiltration_of_le (by simp)]
      congr 2
      exact Fin.ext (by simp)
    · rw [concatFiltration_of_le (by simp; omega)]
      congr 2
      exact Fin.ext (by simp; omega)

end Concat

end CategoryTheory.Abelian.Subobject

end
