module

public import StacksFrontier.CategoryTheory.Monoidal.InternalHomTransfer

/-!
# Biduality morphisms are carried along a functor with a fully faithful left adjoint

Let `C` and `D` be categories with tensor bifunctors `⊗_C`, `⊗_D` and commutativity isomorphisms
`σ : A ⊗ B ≅ B ⊗ A`. For objects `L`, `K` of `C` let `e₁ : H₁ ⊗ L ⟶ K` exhibit `H₁` as an internal
hom from `L` to `K`, and `e₂ : H₂ ⊗ H₁ ⟶ K` exhibit `H₂` as one from `H₁` to `K`. The **biduality
morphism** `β : L ⟶ H₂` is the morphism with `(β ⊗ 1) ≫ e₂ = σ ≫ e₁`, the transpose of evaluation
after commutativity: with `H₁ = R𝓗om(L, K)` and `H₂ = R𝓗om(R𝓗om(L, K), K)` it is the canonical
map `L ⟶ R𝓗om(R𝓗om(L, K), K)` of [Stacks, Tag 0A89].

Let `R : C ⥤ D` have a left adjoint whose unit is an isomorphism (for instance an equivalence, or
restriction to an open with extension by zero as left adjoint), and let `c : R(A ⊗ B) ≅ RA ⊗ RB`
be natural in **both** variables. Then `R β` is an isomorphism exactly when the biduality
morphism formed in `D` at `R L`, `R K` is one.

No compatibility of `c` with the commutativity isomorphisms is asked for. The inner internal hom
is compared through its *right-handed* universal property, `g ↦ (1 ⊗ g) ≫ σ ≫ e₁`, by
`CategoryTheory.InternalHomTransfer.isIso_of_tensorHomBijective` applied to the flipped tensor
bifunctors; the outer one through the usual left-handed property. Both comparisons are
isomorphisms, and the identity `R β ≫ s = β'` is checked by transposing once.

## Main results

* `CategoryTheory.BidualityTransfer.isIso_map_iff`: `R β` is an isomorphism iff the biduality
  morphism of the images is, for internal homs from `R L` to `R K` in `D`.
* `CategoryTheory.BidualityTransfer.isIso_map_iff_of_iso`: the same for internal homs from `L'`
  to `K'` in `D`, given `R L ≅ L'` and `R K ≅ K'`.
* `CategoryTheory.BidualityTransfer.isIso_iff_of_equivalence`: along an equivalence, `β` is an
  isomorphism iff the biduality morphism of the images is.

## References

* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.BidualityTransfer

open InternalHomTransfer

variable {C D : Type*} [Category C] [Category D]

section Right

variable (T : C ⥤ C ⥤ C) (σ : ∀ A B, (T.obj A).obj B ≅ (T.obj B).obj A)

/-- A left internal hom becomes a right internal hom after composing its evaluation with the
commutativity isomorphism: `g ↦ (1 ⊗ g) ≫ σ ≫ e` is bijective when `g ↦ (g ⊗ 1) ≫ e` is. -/
lemma rightBijective
    (hσ : ∀ (L : C) {Z Z' : C} (g : Z ⟶ Z'),
      (T.obj L).map g ≫ (σ L Z').hom = (σ L Z).hom ≫ (T.map g).app L)
    {L M H : C} (e : (T.obj H).obj L ⟶ M)
    (he : ∀ Z, Function.Bijective (fun g : Z ⟶ H => (T.map g).app L ≫ e)) (Z : C) :
    Function.Bijective (fun g : Z ⟶ H => (T.obj L).map g ≫ (σ L H).hom ≫ e) := by
  have h : (fun g : Z ⟶ H => (T.obj L).map g ≫ (σ L H).hom ≫ e) =
      (fun y => (σ L Z).hom ≫ y) ∘ (fun g : Z ⟶ H => (T.map g).app L ≫ e) := by
    funext g
    simp only [Function.comp_apply, ← Category.assoc, hσ]
  rw [h]
  exact (bijective_comp_left _).comp (he Z)

end Right

variable (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
  (σC : ∀ A B, (TC.obj A).obj B ≅ (TC.obj B).obj A)
  (σD : ∀ A B, (TD.obj A).obj B ≅ (TD.obj B).obj A)

/-- Postcomposing an evaluation with an isomorphism preserves the universal property. -/
private lemma bijective_comp_inv_of_bijective {X K K' H : D} (b : K ≅ K')
    (e : (TD.obj H).obj X ⟶ K')
    (he : ∀ Z, Function.Bijective (fun g : Z ⟶ H => (TD.map g).app X ≫ e)) (Z : D) :
    Function.Bijective (fun g : Z ⟶ H => (TD.map g).app X ≫ e ≫ b.inv) := by
  have h : (fun g : Z ⟶ H => (TD.map g).app X ≫ e ≫ b.inv) =
      (fun y => y ≫ b.inv) ∘ (fun g : Z ⟶ H => (TD.map g).app X ≫ e) := by
    funext g
    simp only [Function.comp_apply, Category.assoc]
  rw [h]
  exact (Function.bijective_iff_has_inverse.2
    ⟨fun y => y ≫ b.hom, fun y => by simp, fun y => by simp⟩).comp (he Z)

/-- Transporting an evaluation along isomorphisms `a : L ≅ L'` and `b : K ≅ K'` preserves the
universal property. -/
private lemma bijective_map_comp_iso {L L' K K' H : D} (a : L ≅ L') (b : K ≅ K')
    (e : (TD.obj H).obj L' ⟶ K')
    (he : ∀ Z, Function.Bijective (fun g : Z ⟶ H => (TD.map g).app L' ≫ e)) (Z : D) :
    Function.Bijective (fun g : Z ⟶ H => (TD.map g).app L ≫ (TD.obj H).map a.hom ≫ e ≫ b.inv) := by
  have h : (fun g : Z ⟶ H => (TD.map g).app L ≫ (TD.obj H).map a.hom ≫ e ≫ b.inv) =
      (fun y => (TD.obj Z).map a.hom ≫ y) ∘
        (fun g : Z ⟶ H => (TD.map g).app L' ≫ e ≫ b.inv) := by
    funext g
    simp only [Function.comp_apply]
    rw [← NatTrans.naturality_assoc]
  rw [h]
  exact (bijective_comp_left _).comp (bijective_comp_inv_of_bijective TD b e he Z)

/-- If `e` exhibits `H` as an internal hom out of `Y`, it does so out of `X` after precomposing
with `(TD.obj H).map t` for an isomorphism `t : X ⟶ Y`. -/
private lemma bijective_map_comp_of_isIso {X Y K H : D} (t : X ⟶ Y) [IsIso t]
    (e : (TD.obj H).obj Y ⟶ K)
    (he : ∀ Z, Function.Bijective (fun g : Z ⟶ H => (TD.map g).app Y ≫ e)) (Z : D) :
    Function.Bijective (fun g : Z ⟶ H => (TD.map g).app X ≫ (TD.obj H).map t ≫ e) := by
  have h : (fun g : Z ⟶ H => (TD.map g).app X ≫ (TD.obj H).map t ≫ e) =
      (fun y => (TD.obj Z).map t ≫ y) ∘ (fun g : Z ⟶ H => (TD.map g).app Y ≫ e) := by
    funext g
    simp only [Function.comp_apply]
    rw [← Category.assoc, ← Category.assoc, NatTrans.naturality]
  rw [h]
  exact (bijective_comp_left _).comp (he Z)

/-- The comparison `s` of outer internal homs, given the one `t` of inner ones, is compatible with
`β` and `β'`: `R β ≫ s = β'` when both sides have the same transpose. -/
private lemma map_comp_eq_of_transpose {R : C ⥤ D} (c : ∀ A B, R.obj ((TC.obj A).obj B) ≅
      (TD.obj (R.obj A)).obj (R.obj B))
    (hc₁ : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      R.map ((TC.map f).app B) ≫ (c A' B).hom = (c A B).hom ≫ (TD.map (R.map f)).app (R.obj B))
    {L K H₁ H₂ : C} (e₁ : (TC.obj H₁).obj L ⟶ K) (e₂ : (TC.obj H₂).obj H₁ ⟶ K) (β : L ⟶ H₂)
    (hβ : (TC.map β).app H₁ ≫ e₂ = (σC L H₁).hom ≫ e₁) {H₁' H₂' : D} (t : R.obj H₁ ⟶ H₁')
    (f₁ : (TD.obj H₁').obj (R.obj L) ⟶ R.obj K) (e₂' : (TD.obj H₂').obj H₁' ⟶ R.obj K)
    (ht : (TD.obj (R.obj L)).map t ≫ (σD (R.obj L) H₁').hom ≫ f₁ =
      (c L H₁).inv ≫ R.map ((σC L H₁).hom ≫ e₁))
    (hinj : Function.Injective
      (fun g : R.obj L ⟶ H₂' => (TD.map g).app (R.obj H₁) ≫ (TD.obj H₂').map t ≫ e₂'))
    (s : R.obj H₂ ⟶ H₂')
    (hs : (TD.map s).app (R.obj H₁) ≫ (TD.obj H₂').map t ≫ e₂' = (c H₂ H₁).inv ≫ R.map e₂)
    (γ : R.obj L ⟶ H₂') (hγ : (TD.map γ).app H₁' ≫ e₂' = (σD (R.obj L) H₁').hom ≫ f₁) :
    R.map β ≫ s = γ := by
  apply hinj
  simp only
  have h1 : (TD.map (R.map β ≫ s)).app (R.obj H₁) ≫ (TD.obj H₂').map t ≫ e₂' =
      (c L H₁).inv ≫ R.map ((σC L H₁).hom ≫ e₁) := by
    rw [Functor.map_comp, NatTrans.comp_app, Category.assoc, hs, ← hβ, Functor.map_comp,
      Iso.eq_inv_comp, ← Category.assoc, ← hc₁, Category.assoc, Iso.hom_inv_id_assoc]
  have h2 : (TD.map γ).app (R.obj H₁) ≫ (TD.obj H₂').map t ≫ e₂' =
      (c L H₁).inv ≫ R.map ((σC L H₁).hom ≫ e₁) := by
    rw [← ht, ← Category.assoc, ← NatTrans.naturality]
    simp only [Category.assoc]
    rw [hγ]
  rw [h1, h2]

/-- **Biduality morphisms along `R`.** With the hypotheses of the module documentation and
internal homs `H₁' = [R L, R K]`, `H₂' = [H₁', R K]` in `D`, `R β` is an isomorphism exactly when
the biduality morphism `β'` of `D` at `R L` is one. -/
theorem isIso_map_iff {R : C ⥤ D} {E : D ⥤ C} (adj : E ⊣ R) [IsIso adj.unit]
    (c : ∀ A B, R.obj ((TC.obj A).obj B) ≅ (TD.obj (R.obj A)).obj (R.obj B))
    (hc₁ : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      R.map ((TC.map f).app B) ≫ (c A' B).hom = (c A B).hom ≫ (TD.map (R.map f)).app (R.obj B))
    (hc₂ : ∀ (A : C) {B B' : C} (g : B ⟶ B'),
      R.map ((TC.obj A).map g) ≫ (c A B').hom = (c A B).hom ≫ (TD.obj (R.obj A)).map (R.map g))
    (ρ : ∀ (Z : D) (L : C), (TC.obj (E.obj Z)).obj L ≅ E.obj ((TD.obj Z).obj (R.obj L)))
    (ρ' : ∀ (Z : D) (L : C), (TC.obj L).obj (E.obj Z) ≅ E.obj ((TD.obj (R.obj L)).obj Z))
    (hσC : ∀ (L : C) {Z Z' : C} (g : Z ⟶ Z'),
      (TC.obj L).map g ≫ (σC L Z').hom = (σC L Z).hom ≫ (TC.map g).app L)
    (hσD : ∀ (L : D) {Z Z' : D} (g : Z ⟶ Z'),
      (TD.obj L).map g ≫ (σD L Z').hom = (σD L Z).hom ≫ (TD.map g).app L)
    {L K H₁ H₂ : C} (e₁ : (TC.obj H₁).obj L ⟶ K)
    (he₁ : ∀ Z, Function.Bijective (fun g : Z ⟶ H₁ => (TC.map g).app L ≫ e₁))
    (e₂ : (TC.obj H₂).obj H₁ ⟶ K)
    (he₂ : ∀ Z, Function.Bijective (fun g : Z ⟶ H₂ => (TC.map g).app H₁ ≫ e₂))
    (β : L ⟶ H₂) (hβ : (TC.map β).app H₁ ≫ e₂ = (σC L H₁).hom ≫ e₁)
    {H₁' H₂' : D} (e₁' : (TD.obj H₁').obj (R.obj L) ⟶ R.obj K)
    (he₁' : ∀ Z, Function.Bijective (fun g : Z ⟶ H₁' => (TD.map g).app (R.obj L) ≫ e₁'))
    (e₂' : (TD.obj H₂').obj H₁' ⟶ R.obj K)
    (he₂' : ∀ Z, Function.Bijective (fun g : Z ⟶ H₂' => (TD.map g).app H₁' ≫ e₂'))
    (β' : R.obj L ⟶ H₂') (hβ' : (TD.map β').app H₁' ≫ e₂' = (σD (R.obj L) H₁').hom ≫ e₁') :
    IsIso (R.map β) ↔ IsIso β' := by
  -- the inner comparison, through the right-handed universal property
  obtain ⟨t, ht⟩ := (rightBijective TD σD hσD e₁' he₁' (R.obj H₁)).surjective
    ((c L H₁).inv ≫ R.map ((σC L H₁).hom ≫ e₁))
  dsimp only at ht
  have htiso : IsIso t := isIso_of_tensorHomBijective TC.flip TD.flip adj (fun A B => c B A)
    (fun f B => hc₂ B f) ρ' ((σC L H₁).hom ≫ e₁) (rightBijective TC σC hσC e₁ he₁)
    ((σD (R.obj L) H₁').hom ≫ e₁') (rightBijective TD σD hσD e₁' he₁') t ht
  -- `H₂'` is an internal hom from `R H₁` to `R K`, through `t`
  have he₂t := bijective_map_comp_of_isIso TD t e₂' he₂'
  -- the outer comparison
  obtain ⟨s, hs⟩ := (he₂t (R.obj H₂)).surjective ((c H₂ H₁).inv ≫ R.map e₂)
  dsimp only at hs
  have hsiso : IsIso s := isIso_of_tensorHomBijective TC TD adj c hc₁ ρ e₂ he₂
    ((TD.obj H₂').map t ≫ e₂') he₂t s hs
  -- `R β ≫ s = β'`
  have hkey : R.map β ≫ s = β' := map_comp_eq_of_transpose TC TD σC σD c hc₁ e₁ e₂ β hβ t _ e₂' ht
    (he₂t _).injective s hs β' hβ'
  rw [← hkey]
  exact ⟨fun _ => inferInstance, fun _ => IsIso.of_isIso_comp_right (R.map β) s⟩

/-- **Biduality morphisms along `R`, for isomorphic objects of `D`.** As
`CategoryTheory.BidualityTransfer.isIso_map_iff`, with the internal homs in `D` taken from `L'` to
`K'` for given isomorphisms `R L ≅ L'` and `R K ≅ K'`. -/
theorem isIso_map_iff_of_iso {R : C ⥤ D} {E : D ⥤ C} (adj : E ⊣ R) [IsIso adj.unit]
    (c : ∀ A B, R.obj ((TC.obj A).obj B) ≅ (TD.obj (R.obj A)).obj (R.obj B))
    (hc₁ : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      R.map ((TC.map f).app B) ≫ (c A' B).hom = (c A B).hom ≫ (TD.map (R.map f)).app (R.obj B))
    (hc₂ : ∀ (A : C) {B B' : C} (g : B ⟶ B'),
      R.map ((TC.obj A).map g) ≫ (c A B').hom = (c A B).hom ≫ (TD.obj (R.obj A)).map (R.map g))
    (ρ : ∀ (Z : D) (L : C), (TC.obj (E.obj Z)).obj L ≅ E.obj ((TD.obj Z).obj (R.obj L)))
    (ρ' : ∀ (Z : D) (L : C), (TC.obj L).obj (E.obj Z) ≅ E.obj ((TD.obj (R.obj L)).obj Z))
    (hσC : ∀ (L : C) {Z Z' : C} (g : Z ⟶ Z'),
      (TC.obj L).map g ≫ (σC L Z').hom = (σC L Z).hom ≫ (TC.map g).app L)
    (hσD : ∀ (L : D) {Z Z' : D} (g : Z ⟶ Z'),
      (TD.obj L).map g ≫ (σD L Z').hom = (σD L Z).hom ≫ (TD.map g).app L)
    (hσD' : ∀ {Z Z' : D} (g : Z ⟶ Z') (L : D),
      (TD.map g).app L ≫ (σD Z' L).hom = (σD Z L).hom ≫ (TD.obj L).map g)
    {L K H₁ H₂ : C} (e₁ : (TC.obj H₁).obj L ⟶ K)
    (he₁ : ∀ Z, Function.Bijective (fun g : Z ⟶ H₁ => (TC.map g).app L ≫ e₁))
    (e₂ : (TC.obj H₂).obj H₁ ⟶ K)
    (he₂ : ∀ Z, Function.Bijective (fun g : Z ⟶ H₂ => (TC.map g).app H₁ ≫ e₂))
    (β : L ⟶ H₂) (hβ : (TC.map β).app H₁ ≫ e₂ = (σC L H₁).hom ≫ e₁)
    {L' K' H₁' H₂' : D} (a : R.obj L ≅ L') (b : R.obj K ≅ K')
    (e₁' : (TD.obj H₁').obj L' ⟶ K')
    (he₁' : ∀ Z, Function.Bijective (fun g : Z ⟶ H₁' => (TD.map g).app L' ≫ e₁'))
    (e₂' : (TD.obj H₂').obj H₁' ⟶ K')
    (he₂' : ∀ Z, Function.Bijective (fun g : Z ⟶ H₂' => (TD.map g).app H₁' ≫ e₂'))
    (β' : L' ⟶ H₂') (hβ' : (TD.map β').app H₁' ≫ e₂' = (σD L' H₁').hom ≫ e₁') :
    IsIso (R.map β) ↔ IsIso β' := by
  have he₁'' := bijective_map_comp_iso TD a b e₁' he₁'
  have he₂'' := bijective_comp_inv_of_bijective TD b e₂' he₂'
  have hβ'' : (TD.map (a.hom ≫ β')).app H₁' ≫ e₂' ≫ b.inv =
      (σD (R.obj L) H₁').hom ≫ (TD.obj H₁').map a.hom ≫ e₁' ≫ b.inv := by
    rw [Functor.map_comp, NatTrans.comp_app, Category.assoc, reassoc_of% hβ',
      ← reassoc_of% (hσD' a.hom H₁')]
  rw [isIso_map_iff TC TD σC σD adj c hc₁ hc₂ ρ ρ' hσC hσD e₁ he₁ e₂ he₂ β hβ
    ((TD.obj H₁').map a.hom ≫ e₁' ≫ b.inv) he₁'' (e₂' ≫ b.inv) he₂'' (a.hom ≫ β') hβ'']
  exact ⟨fun _ => IsIso.of_isIso_comp_left a.hom β', fun _ => inferInstance⟩

/-- **Biduality morphisms along an equivalence.** If `eq : C ≌ D` carries tensor products to tensor
products naturally in both variables, a biduality morphism of `C` is an isomorphism exactly when
the biduality morphism of `D` at the images (for any internal homs there, from objects isomorphic
to the images) is one. -/
theorem isIso_iff_of_equivalence (eq : C ≌ D)
    (c : ∀ A B, eq.functor.obj ((TC.obj A).obj B) ≅
      (TD.obj (eq.functor.obj A)).obj (eq.functor.obj B))
    (hc₁ : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      eq.functor.map ((TC.map f).app B) ≫ (c A' B).hom =
        (c A B).hom ≫ (TD.map (eq.functor.map f)).app (eq.functor.obj B))
    (hc₂ : ∀ (A : C) {B B' : C} (g : B ⟶ B'),
      eq.functor.map ((TC.obj A).map g) ≫ (c A B').hom =
        (c A B).hom ≫ (TD.obj (eq.functor.obj A)).map (eq.functor.map g))
    (hσC : ∀ (L : C) {Z Z' : C} (g : Z ⟶ Z'),
      (TC.obj L).map g ≫ (σC L Z').hom = (σC L Z).hom ≫ (TC.map g).app L)
    (hσD : ∀ (L : D) {Z Z' : D} (g : Z ⟶ Z'),
      (TD.obj L).map g ≫ (σD L Z').hom = (σD L Z).hom ≫ (TD.map g).app L)
    (hσD' : ∀ {Z Z' : D} (g : Z ⟶ Z') (L : D),
      (TD.map g).app L ≫ (σD Z' L).hom = (σD Z L).hom ≫ (TD.obj L).map g)
    {L K H₁ H₂ : C} (e₁ : (TC.obj H₁).obj L ⟶ K)
    (he₁ : ∀ Z, Function.Bijective (fun g : Z ⟶ H₁ => (TC.map g).app L ≫ e₁))
    (e₂ : (TC.obj H₂).obj H₁ ⟶ K)
    (he₂ : ∀ Z, Function.Bijective (fun g : Z ⟶ H₂ => (TC.map g).app H₁ ≫ e₂))
    (β : L ⟶ H₂) (hβ : (TC.map β).app H₁ ≫ e₂ = (σC L H₁).hom ≫ e₁)
    {L' K' H₁' H₂' : D} (a : eq.functor.obj L ≅ L') (b : eq.functor.obj K ≅ K')
    (e₁' : (TD.obj H₁').obj L' ⟶ K')
    (he₁' : ∀ Z, Function.Bijective (fun g : Z ⟶ H₁' => (TD.map g).app L' ≫ e₁'))
    (e₂' : (TD.obj H₂').obj H₁' ⟶ K')
    (he₂' : ∀ Z, Function.Bijective (fun g : Z ⟶ H₂' => (TD.map g).app H₁' ≫ e₂'))
    (β' : L' ⟶ H₂') (hβ' : (TD.map β').app H₁' ≫ e₂' = (σD L' H₁').hom ≫ e₁') :
    IsIso β ↔ IsIso β' := by
  let adj : eq.inverse ⊣ eq.functor := eq.symm.toAdjunction
  have : IsIso adj.unit := inferInstanceAs (IsIso eq.counitIso.inv)
  let ρ : ∀ (Z : D) (L : C), (TC.obj (eq.inverse.obj Z)).obj L ≅
      eq.inverse.obj ((TD.obj Z).obj (eq.functor.obj L)) := fun Z L =>
    eq.unitIso.app _ ≪≫ eq.inverse.mapIso
      (c (eq.inverse.obj Z) L ≪≫ (TD.mapIso (eq.counitIso.app Z)).app (eq.functor.obj L))
  let ρ' : ∀ (Z : D) (L : C), (TC.obj L).obj (eq.inverse.obj Z) ≅
      eq.inverse.obj ((TD.obj (eq.functor.obj L)).obj Z) := fun Z L =>
    eq.unitIso.app _ ≪≫ eq.inverse.mapIso
      (c L (eq.inverse.obj Z) ≪≫ (TD.obj (eq.functor.obj L)).mapIso (eq.counitIso.app Z))
  rw [← isIso_map_iff_of_iso TC TD σC σD adj c hc₁ hc₂ ρ ρ' hσC hσD hσD' e₁ he₁ e₂ he₂ β hβ
    a b e₁' he₁' e₂' he₂' β' hβ']
  exact ⟨fun _ => inferInstance, fun _ => isIso_of_fully_faithful eq.functor β⟩

section FullyFaithful

/-- **The comparison of internal homs along a fully faithful functor.** Let `R : C ⥤ D` be fully
faithful and carry tensor products to tensor products naturally in the first variable. If
`e : H ⊗ L ⟶ M` exhibits `H` as an internal hom in `C` and `e' : H' ⊗ R L ⟶ R M` exhibits `H'` as
one in `D`, with `H'` in the essential image of `R`, then the morphism `t : R H ⟶ H'` whose
transpose is `c⁻¹ ≫ R e` is an isomorphism. No adjoint of `R` is needed. -/
theorem isIso_of_tensorHomBijective_of_fullyFaithful {R : C ⥤ D} (hR : R.FullyFaithful)
    (c : ∀ A B, R.obj ((TC.obj A).obj B) ≅ (TD.obj (R.obj A)).obj (R.obj B))
    (hc : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      R.map ((TC.map f).app B) ≫ (c A' B).hom = (c A B).hom ≫ (TD.map (R.map f)).app (R.obj B))
    {L M H : C} (e : (TC.obj H).obj L ⟶ M)
    (he : ∀ Z, Function.Bijective (fun g : Z ⟶ H => (TC.map g).app L ≫ e))
    {H' : D} (e' : (TD.obj H').obj (R.obj L) ⟶ R.obj M)
    (he' : ∀ Z, Function.Bijective (fun g : Z ⟶ H' => (TD.map g).app (R.obj L) ≫ e'))
    (hH' : R.essImage H') (t : R.obj H ⟶ H')
    (ht : (TD.map t).app (R.obj L) ≫ e' = (c H L).inv ≫ R.map e) :
    IsIso t := by
  obtain ⟨H₀, ⟨i⟩⟩ := hH'
  let t₀ : H ⟶ H₀ := hR.preimage (t ≫ i.inv)
  have hRt₀ : R.map t₀ = t ≫ i.inv := hR.map_preimage _
  have ht₀ : IsIso t₀ := by
    rw [isIso_iff_yoneda_map_bijective]
    intro Z
    -- `k ↦ R k ≫ i.hom`, then the bijection of `H'`
    let φ : (Z ⟶ H₀) → ((TD.obj (R.obj Z)).obj (R.obj L) ⟶ R.obj M) :=
      fun k => (TD.map (R.map k ≫ i.hom)).app (R.obj L) ≫ e'
    have hφ : Function.Bijective φ := by
      have h : φ = (fun g : R.obj Z ⟶ H' => (TD.map g).app (R.obj L) ≫ e') ∘
          (fun y => y ≫ i.hom) ∘ (fun k : Z ⟶ H₀ => R.map k) := rfl
      rw [h]
      exact (he' (R.obj Z)).comp ((Function.bijective_iff_has_inverse.2
        ⟨fun y => y ≫ i.inv, fun y => by simp, fun y => by simp⟩).comp (hR.map_bijective _ _))
    rw [← Function.Bijective.of_comp_iff' hφ]
    have h1 : (φ ∘ fun g : Z ⟶ H => g ≫ t₀) =
        (fun y => (c Z L).inv ≫ y) ∘ (fun h => R.map h) ∘
          (fun g : Z ⟶ H => (TC.map g).app L ≫ e) := by
      funext g
      have e1 : R.map (g ≫ t₀) ≫ i.hom = R.map g ≫ t := by
        rw [R.map_comp, hRt₀]; simp
      have hcg : (TD.map (R.map g)).app (R.obj L) ≫ (c H L).inv =
          (c Z L).inv ≫ R.map ((TC.map g).app L) := by
        rw [Iso.comp_inv_eq, Category.assoc, hc g L, Iso.inv_hom_id_assoc]
      simp only [Function.comp_apply, φ]
      rw [e1, Functor.map_comp, NatTrans.comp_app, Category.assoc, ht, reassoc_of% hcg,
        R.map_comp]
    rw [h1]
    exact (bijective_comp_left _).comp ((hR.map_bijective _ _).comp (he Z))
  have : IsIso (t ≫ i.inv) := by rw [← hRt₀]; infer_instance
  exact IsIso.of_isIso_comp_right t i.inv

/-- **Biduality morphisms along a fully faithful functor.** As
`CategoryTheory.BidualityTransfer.isIso_map_iff_of_iso`, for a fully faithful `R` with no adjoint,
provided the two internal homs `H₁'`, `H₂'` of `D` lie in the essential image of `R`. Then `β` is
an isomorphism exactly when `β'` is. -/
theorem isIso_iff_of_fullyFaithful {R : C ⥤ D} (hR : R.FullyFaithful)
    (c : ∀ A B, R.obj ((TC.obj A).obj B) ≅ (TD.obj (R.obj A)).obj (R.obj B))
    (hc₁ : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      R.map ((TC.map f).app B) ≫ (c A' B).hom = (c A B).hom ≫ (TD.map (R.map f)).app (R.obj B))
    (hc₂ : ∀ (A : C) {B B' : C} (g : B ⟶ B'),
      R.map ((TC.obj A).map g) ≫ (c A B').hom = (c A B).hom ≫ (TD.obj (R.obj A)).map (R.map g))
    (hσC : ∀ (L : C) {Z Z' : C} (g : Z ⟶ Z'),
      (TC.obj L).map g ≫ (σC L Z').hom = (σC L Z).hom ≫ (TC.map g).app L)
    (hσD : ∀ (L : D) {Z Z' : D} (g : Z ⟶ Z'),
      (TD.obj L).map g ≫ (σD L Z').hom = (σD L Z).hom ≫ (TD.map g).app L)
    (hσD' : ∀ {Z Z' : D} (g : Z ⟶ Z') (L : D),
      (TD.map g).app L ≫ (σD Z' L).hom = (σD Z L).hom ≫ (TD.obj L).map g)
    {L K H₁ H₂ : C} (e₁ : (TC.obj H₁).obj L ⟶ K)
    (he₁ : ∀ Z, Function.Bijective (fun g : Z ⟶ H₁ => (TC.map g).app L ≫ e₁))
    (e₂ : (TC.obj H₂).obj H₁ ⟶ K)
    (he₂ : ∀ Z, Function.Bijective (fun g : Z ⟶ H₂ => (TC.map g).app H₁ ≫ e₂))
    (β : L ⟶ H₂) (hβ : (TC.map β).app H₁ ≫ e₂ = (σC L H₁).hom ≫ e₁)
    {L' K' H₁' H₂' : D} (a : R.obj L ≅ L') (b : R.obj K ≅ K')
    (e₁' : (TD.obj H₁').obj L' ⟶ K')
    (he₁' : ∀ Z, Function.Bijective (fun g : Z ⟶ H₁' => (TD.map g).app L' ≫ e₁'))
    (e₂' : (TD.obj H₂').obj H₁' ⟶ K')
    (he₂' : ∀ Z, Function.Bijective (fun g : Z ⟶ H₂' => (TD.map g).app H₁' ≫ e₂'))
    (β' : L' ⟶ H₂') (hβ' : (TD.map β').app H₁' ≫ e₂' = (σD L' H₁').hom ≫ e₁')
    (hH₁' : R.essImage H₁') (hH₂' : R.essImage H₂') :
    IsIso β ↔ IsIso β' := by
  -- move the `D`-side data to `R L`, `R K`
  let f₁ : (TD.obj H₁').obj (R.obj L) ⟶ R.obj K := (TD.obj H₁').map a.hom ≫ e₁' ≫ b.inv
  have hf₁ := bijective_map_comp_iso TD a b e₁' he₁'
  let f₂ : (TD.obj H₂').obj H₁' ⟶ R.obj K := e₂' ≫ b.inv
  have hf₂ := bijective_comp_inv_of_bijective TD b e₂' he₂'
  let γ : R.obj L ⟶ H₂' := a.hom ≫ β'
  have hγ : (TD.map γ).app H₁' ≫ f₂ = (σD (R.obj L) H₁').hom ≫ f₁ := by
    simp only [γ, f₁, f₂, Functor.map_comp, NatTrans.comp_app, Category.assoc]
    rw [reassoc_of% hβ', ← reassoc_of% (hσD' a.hom H₁')]
  -- the inner comparison, through the right-handed universal property
  obtain ⟨t, ht⟩ := (rightBijective TD σD hσD f₁ hf₁ (R.obj H₁)).surjective
    ((c L H₁).inv ≫ R.map ((σC L H₁).hom ≫ e₁))
  dsimp only at ht
  have htiso : IsIso t := isIso_of_tensorHomBijective_of_fullyFaithful TC.flip TD.flip hR
    (fun A B => c B A) (fun f B => hc₂ B f) ((σC L H₁).hom ≫ e₁)
    (rightBijective TC σC hσC e₁ he₁) ((σD (R.obj L) H₁').hom ≫ f₁)
    (rightBijective TD σD hσD f₁ hf₁) hH₁' t ht
  have he₂t := bijective_map_comp_of_isIso TD t f₂ hf₂
  -- the outer comparison
  obtain ⟨s, hs⟩ := (he₂t (R.obj H₂)).surjective ((c H₂ H₁).inv ≫ R.map e₂)
  dsimp only at hs
  have hsiso : IsIso s := isIso_of_tensorHomBijective_of_fullyFaithful TC TD hR c hc₁ e₂ he₂
    ((TD.obj H₂').map t ≫ f₂) he₂t hH₂' s hs
  have hkey : R.map β ≫ s = γ := map_comp_eq_of_transpose TC TD σC σD c hc₁ e₁ e₂ β hβ t f₁ f₂ ht
    (he₂t _).injective s hs γ hγ
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · have : IsIso γ := by rw [← hkey]; infer_instance
    exact IsIso.of_isIso_comp_left a.hom β'
  · have : IsIso (R.map β ≫ s) := by rw [hkey]; infer_instance
    have := IsIso.of_isIso_comp_right (R.map β) s
    exact hR.isIso_of_isIso_map β

end FullyFaithful

section Yoneda

variable (T : C ⥤ C ⥤ C) (σ : ∀ A B, (T.obj A).obj B ≅ (T.obj B).obj A)

/-- **Postcomposition with the biduality morphism is the dual on morphisms.** Let `β : L ⟶ H₂`
be a biduality morphism into an internal hom `H₂ = [H_L, K]` from `H_L = [L, K]`, and let
`D g : H_L ⟶ H_Z` be the morphism induced on internal homs into `K` by `g : Z ⟶ L`. Then, up to
the bijection `Hom(Z, [H_L, K]) ≃ Hom(H_L, [Z, K])` given by the commutativity constraint,
`g ↦ g ≫ β` is `g ↦ D g`; in particular one is bijective exactly when the other is. -/
theorem bijective_comp_iff_bijective
    (hσ : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      (T.map f).app B ≫ (σ A' B).hom = (σ A B).hom ≫ (T.obj B).map f)
    {Z L K H_L H_Z H₂ : C} (eL : (T.obj H_L).obj L ⟶ K) (eZ : (T.obj H_Z).obj Z ⟶ K)
    (heZ : ∀ W, Function.Bijective (fun g : W ⟶ H_Z => (T.map g).app Z ≫ eZ))
    (e₂ : (T.obj H₂).obj H_L ⟶ K)
    (he₂ : ∀ W, Function.Bijective (fun g : W ⟶ H₂ => (T.map g).app H_L ≫ e₂))
    (β : L ⟶ H₂) (hβ : (T.map β).app H_L ≫ e₂ = (σ L H_L).hom ≫ eL)
    (D : (Z ⟶ L) → (H_L ⟶ H_Z))
    (hD : ∀ g, (T.map (D g)).app Z ≫ eZ = (T.obj H_L).map g ≫ eL) :
    Function.Bijective (fun g : Z ⟶ L => g ≫ β) ↔ Function.Bijective D := by
  let b₂ := Equiv.ofBijective _ (he₂ Z)
  let bZ := Equiv.ofBijective _ (heZ H_L)
  let ψ : (Z ⟶ H₂) → (H_L ⟶ H_Z) := fun x => bZ.symm ((σ Z H_L).inv ≫ b₂ x)
  have hψ : Function.Bijective ψ :=
    bZ.symm.bijective.comp ((bijective_comp_left _).comp b₂.bijective)
  have hcomp : ψ ∘ (fun g : Z ⟶ L => g ≫ β) = D := by
    funext g
    apply bZ.injective
    simp only [Function.comp_apply, ψ, Equiv.apply_symm_apply, b₂, bZ, Equiv.ofBijective_apply]
    rw [hD, Functor.map_comp, NatTrans.comp_app, Category.assoc, hβ, reassoc_of% (hσ g H_L),
      Iso.inv_hom_id_assoc]
  rw [← hcomp]
  exact (Function.Bijective.of_comp_iff' hψ _).symm

/-- **Biduality morphisms are natural.** Let `g : L ⟶ L'`, let `D g : H_{L'} ⟶ H_L` be the morphism
it induces on internal homs into `K` and `DD g : H₂ ⟶ H₂'` the morphism `D g` induces on the outer
internal homs. Then `g ≫ β' = β ≫ DD g`. -/
theorem comp_biduality_eq
    (hσl : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      (T.map f).app B ≫ (σ A' B).hom = (σ A B).hom ≫ (T.obj B).map f)
    (hσr : ∀ (A : C) {B B' : C} (f : B ⟶ B'),
      (T.obj A).map f ≫ (σ A B').hom = (σ A B).hom ≫ (T.map f).app A)
    {L L' K H_L H_L' H₂ H₂' : C} (g : L ⟶ L')
    (eL : (T.obj H_L).obj L ⟶ K) (eL' : (T.obj H_L').obj L' ⟶ K)
    (e₂ : (T.obj H₂).obj H_L ⟶ K) (e₂' : (T.obj H₂').obj H_L' ⟶ K)
    (he₂' : ∀ W, Function.Injective (fun h : W ⟶ H₂' => (T.map h).app H_L' ≫ e₂'))
    (β : L ⟶ H₂) (hβ : (T.map β).app H_L ≫ e₂ = (σ L H_L).hom ≫ eL)
    (β' : L' ⟶ H₂') (hβ' : (T.map β').app H_L' ≫ e₂' = (σ L' H_L').hom ≫ eL')
    (Dg : H_L' ⟶ H_L) (hD : (T.map Dg).app L ≫ eL = (T.obj H_L').map g ≫ eL')
    (DDg : H₂ ⟶ H₂') (hDD : (T.map DDg).app H_L' ≫ e₂' = (T.obj H₂).map Dg ≫ e₂) :
    g ≫ β' = β ≫ DDg := by
  apply he₂' L
  simp only
  rw [Functor.map_comp, NatTrans.comp_app, Category.assoc, hβ', reassoc_of% (hσl g H_L'),
    Functor.map_comp, NatTrans.comp_app, Category.assoc, hDD,
    ← reassoc_of% ((T.map β).naturality Dg), hβ, reassoc_of% (hσr L Dg), hD]

end Yoneda

end CategoryTheory.BidualityTransfer
