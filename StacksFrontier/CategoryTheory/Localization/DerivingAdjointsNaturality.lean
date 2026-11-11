module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import StacksFrontier.CategoryTheory.Functor.Derived.Morphisms
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints

/-!
# Functoriality of the derived adjunction bijection

Let `F : 𝒜 ⥤ ℬ` be right adjoint to `G : ℬ ⥤ 𝒜`, functors of abelian categories, and write `RF`,
resp. `LG`, for the partially defined right, resp. left, derived functor of
`K(F) ⋙ Qh : K(𝒜) ⥤ D(ℬ)`, resp. `K(G) ⋙ Qh : K(ℬ) ⥤ D(𝒜)`, with respect to the
quasi-isomorphisms. If `RF` is defined at a complex `K` and `LG` at a complex `M`, then
`CategoryTheory.Adjunction.existsUnique_homEquiv_derivedCategory_of_isRightDerivedValueAt`
provides a unique bijection
$$ \operatorname{Hom}_{D(\mathcal{B})}(M, RF(K)) =
   \operatorname{Hom}_{D(\mathcal{A})}(LG(M), K) $$
compatible with the fractions computing the two sides. This file names that bijection,
`CategoryTheory.Adjunction.derivedCategoryHomEquiv`, and proves the remaining assertion of
[Stacks, Tag 0DVC]: the bijection is functorial in both variables on the subcategories where `RF`
and `LG` are defined.

Over arbitrary categories (the situation of [Stacks, Tag 0FND]), with `S` admitting left and
`S'` right fractions, the bijection of
`CategoryTheory.Adjunction.existsUnique_homEquiv_of_isRightDerivedValueAt` is named
`CategoryTheory.Adjunction.derivedHomEquiv`, and its functoriality in both variables on the
subcategories where `RF` and `LG` are defined is proved, for morphisms of `𝒟` and `𝒟'` and for
morphisms of the localized categories `S⁻¹𝒟` and `(S')⁻¹𝒟'`.

## Main results

* `CategoryTheory.Adjunction.derivedHomEquiv`: the canonical bijection of [Stacks 0FND], with its
  characterisation `derivedHomEquiv_spec`.
* `CategoryTheory.Adjunction.derivedHomEquiv_naturality`: for `κ : K ⟶ K'` in `𝒟` and
  `γ : M' ⟶ M` in `𝒟'`, `φ_{K',M'}(Q'(γ) ≫ ψ ≫ RF(κ)) = LG(γ) ≫ φ_{K,M}(ψ) ≫ Q(κ)`, from the
  two one-variable statements `derivedHomEquiv_comp_rightDerivedMap` and
  `derivedHomEquiv_map_comp`. Here `LG(γ)` is the opposite of the morphism induced by `γ.op`
  between the values of the opposite ind-objects, the form in which the left derived value is
  taken in Tag 0FND's statement.
* `CategoryTheory.Adjunction.derivedHomEquiv_comp_eq_comp` and
  `CategoryTheory.Adjunction.derivedHomEquiv_comp_eq_comp_left`: the same for a morphism
  `g = Q(κ) ≫ Q(σ)⁻¹` of `S⁻¹𝒟`, resp. `γ = Q'(τ)⁻¹ ≫ Q'(ν)` of `(S')⁻¹𝒟'`, acting on the values
  through `RF(κ) ≫ RF(σ)⁻¹`, resp. `LG(τ)⁻¹ ≫ LG(ν)` (every morphism of the localized categories
  is such a fraction).
* `CategoryTheory.Adjunction.derivedCategoryHomEquiv`: the canonical bijection of [Stacks 0DVC],
  with its characterisation `derivedCategoryHomEquiv_spec` and `derivedCategoryHomEquiv_unique`.
* `CategoryTheory.Adjunction.derivedCategoryHomEquiv_comp_rightDerivedMap`: naturality in `K`.
  For a morphism `κ : K ⟶ K'` between complexes at which `RF` is defined, with induced morphism
  `RF(κ) : RF(K) ⟶ RF(K')` of [Stacks, Tag 05SA] (`StacksDerivedFunctor.rightDerivedMap`),
  `φ_{K',M}(ψ ≫ RF(κ)) = φ_{K,M}(ψ) ≫ κ`.
* `CategoryTheory.Adjunction.derivedCategoryHomEquiv_map_comp`: naturality in `M`. For a morphism
  `γ : M' ⟶ M` between complexes at which `LG` is defined, with induced morphism
  `LG(γ) : LG(M') ⟶ LG(M)` (`StacksDerivedFunctor.leftDerivedMap`),
  `φ_{K,M'}(γ ≫ ψ) = LG(γ) ≫ φ_{K,M}(ψ)`.

## Implementation notes

*Morphisms of the derived category.* The source's subcategories are full subcategories of
`D(𝒜)` and `D(ℬ)`, and every morphism of `D(𝒜)` between objects `K`, `K'` is a fraction
`Qh(κ) ≫ Qh(s)⁻¹` with `κ : K ⟶ L` a morphism of `K(𝒜)` and `s : K' ⟶ L` a quasi-isomorphism;
`RF` is then defined at `L`, `RF(s)` is invertible ([Stacks, Tag 05SB]) and `RF` of the fraction
is `RF(κ) ≫ RF(s)⁻¹`; dually for `D(ℬ)`. Naturality with respect to `Qh(s)⁻¹` is a formal
consequence of naturality with respect to `s` (compose with `RF(s)` and with `Qh(s)`), so the
content of the functoriality is naturality with respect to the morphisms of `K(𝒜)` and of
`K(ℬ)`, which is what is proved here, in both variables. No functor on the subcategories is
assembled, since neither derived functor is assumed to be defined everywhere.

*Proof.* Naturality in `K` is checked on one fraction representing `ψ`: by essential constancy
`RF(K)` is a retract of a term `Qh(F(I₀))` of its ind-object, and the calculus of right fractions
writes `ψ` followed by the retraction as a fraction `Qh(t)⁻¹ ≫ Qh(f)`. A square
`κ ≫ s' = s₀ ≫ f'` (calculus of left fractions) then represents `ψ ≫ RF(κ)` by
`f ≫ F(f')`, whose transpose is `f^♯ ≫ f'`, and the characterisations of `φ_{K,M}` and
`φ_{K',M}` give the claim after cancelling the isomorphism `Qh(s')`. Naturality in `M` is dual.

## References

* [Stacks, Tag 0DVC](https://stacks.math.columbia.edu/tag/0DVC)
* [Stacks, Tag 0FND](https://stacks.math.columbia.edu/tag/0FND)
* [Stacks, Tag 05SA](https://stacks.math.columbia.edu/tag/05SA)
* [Stacks, Tag 05SB](https://stacks.math.columbia.edu/tag/05SB)
-/

@[expose] public section

universe w₁ w₂ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Adjunction

open Limits StacksDerivedFunctor

/-! ### Functoriality of the pointwise bijection over arbitrary localizations -/

section General

open Opposite

variable {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']
  {SD : Type u₃} [Category.{v₃} SD] {SD' : Type u₄} [Category.{v₄} SD']
  {F : D ⥤ D'} {G : D' ⥤ D} (adj : G ⊣ F)
  {S : MorphismProperty D} {S' : MorphismProperty D'}
  [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
  {Q : D ⥤ SD} [Q.IsLocalization S] {Q' : D' ⥤ SD'} [Q'.IsLocalization S']
  {K K' L : D} {M M' N : D'}
  {c : Cocone (MorphismProperty.Under.forget S ⊤ K ⋙ Under.forget K ⋙ F ⋙ Q')}
  {c' : Cocone (MorphismProperty.Under.forget S ⊤ K' ⋙ Under.forget K' ⋙ F ⋙ Q')}
  {cL : Cocone (MorphismProperty.Under.forget S ⊤ L ⋙ Under.forget L ⋙ F ⋙ Q')}
  {d : Cocone (MorphismProperty.Under.forget S'.op ⊤ (op M) ⋙
    Under.forget (op M) ⋙ (G ⋙ Q).op)}
  {d' : Cocone (MorphismProperty.Under.forget S'.op ⊤ (op M') ⋙
    Under.forget (op M') ⋙ (G ⋙ Q).op)}
  {dN : Cocone (MorphismProperty.Under.forget S'.op ⊤ (op N) ⋙
    Under.forget (op N) ⋙ (G ⋙ Q).op)}

/-- The canonical bijection `Hom_{(S')⁻¹𝒟'}(M, RF(K)) ≃ Hom_{S⁻¹𝒟}(LG(M), K)` of Stacks 0FND,
for `F : 𝒟 ⥤ 𝒟'` right adjoint to `G : 𝒟' ⥤ 𝒟`, an object `K` of `𝒟` at which `RF` is defined,
with value `RF(K) = c.pt`, and an object `M` of `𝒟'` at which `LG` is defined, with value
`LG(M) = d.pt.unop`. It is the unique bijection compatible with the fractions computing the two
sides (`existsUnique_homEquiv_of_isRightDerivedValueAt`, `derivedHomEquiv_spec`), and it is
natural in both variables (`derivedHomEquiv_naturality`). -/
noncomputable def derivedHomEquiv
    (hc : (F ⋙ Q').IsRightDerivedValueAt S K c)
    (hd : (G ⋙ Q).op.IsRightDerivedValueAt S'.op (op M) d) :
    (Q'.obj M ⟶ c.pt) ≃ (d.pt.unop ⟶ Q.obj K) :=
  (existsUnique_homEquiv_of_isRightDerivedValueAt adj S S' Q Q' K M c hc d hd).exists.choose

/-- The bijection `derivedHomEquiv` is compatible with the fractions computing the two sides:
for an index `s : K ⟶ I` of the ind-object defining `RF(K)`, an index `t : P ⟶ M` of the
pro-object defining `LG(M)` and `f : P ⟶ F(I)`, `Q'(t) ≫ ψ = Q'(f) ≫ (coprojection at s)` exactly
when `φ(ψ) ≫ Q(s) = (projection at t) ≫ Q(f^♯)`. -/
lemma derivedHomEquiv_spec
    (hc : (F ⋙ Q').IsRightDerivedValueAt S K c)
    (hd : (G ⋙ Q).op.IsRightDerivedValueAt S'.op (op M) d)
    (s : S.Under ⊤ K) (t : S'.op.Under ⊤ (op M)) (f : t.right.unop ⟶ F.obj s.right)
    (ψ : Q'.obj M ⟶ c.pt) :
    Q'.map t.hom.unop ≫ ψ = Q'.map f ≫ c.ι.app s ↔
      adj.derivedHomEquiv hc hd ψ ≫ Q.map s.hom =
        (d.ι.app t).unop ≫ Q.map ((adj.homEquiv _ _).symm f) :=
  (existsUnique_homEquiv_of_isRightDerivedValueAt adj S S' Q Q' K M c hc d
    hd).exists.choose_spec s t f ψ

omit [S.HasLeftCalculusOfFractions] in
/-- A morphism `ψ : M ⟶ RF(K)` is represented by a fraction through a single index of the
ind-object: `Q'(t) ≫ ψ = Q'(f) ≫ (coprojection at s)` for some index `s : K ⟶ I`, some index
`t : P ⟶ M` of the pro-object and some `f : P ⟶ F(I)`. -/
private lemma exists_rep_of_isRightDerivedValueAt
    (hc : (F ⋙ Q').IsRightDerivedValueAt S K c) (ψ : Q'.obj M ⟶ c.pt) :
    ∃ (s : S.Under ⊤ K) (t : S'.op.Under ⊤ (op M)) (f : t.right.unop ⟶ F.obj s.right),
      Q'.map t.hom.unop ≫ ψ = Q'.map f ≫ c.ι.app s := by
  obtain ⟨s₀, r, hr, -⟩ := hc
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction Q' S' (Y := F.obj s₀.right) (ψ ≫ r)
  have h1 : Q'.map φ.s ≫ ψ ≫ r = Q'.map φ.f := by
    rw [hφ]; exact φ.map_s_comp_map Q' _
  refine ⟨s₀, MorphismProperty.Under.mk ⊤ φ.s.op φ.hs, φ.f, ?_⟩
  exact (Category.comp_id _).symm.trans <|
    (congrArg (fun z => (Q'.map φ.s ≫ ψ) ≫ z) hr.symm).trans <|
    (Category.assoc _ _ _).symm.trans <|
    congrArg (· ≫ c.ι.app s₀) ((Category.assoc _ _ _).trans h1)

/-- Naturality of the bijection of Stacks 0FND in `K`. Let `κ : K ⟶ K'` be a morphism of `𝒟`
such that `RF` is defined at `K` and at `K'`, and let `RF(κ) : RF(K) ⟶ RF(K')` be the induced
morphism between the values (Stacks 05SA). Then `φ_{K',M}(ψ ≫ RF(κ)) = φ_{K,M}(ψ) ≫ Q(κ)`. -/
theorem derivedHomEquiv_comp_rightDerivedMap
    (hc : (F ⋙ Q').IsRightDerivedValueAt S K c) (hc' : (F ⋙ Q').IsRightDerivedValueAt S K' c')
    (hd : (G ⋙ Q).op.IsRightDerivedValueAt S'.op (op M) d)
    (κ : K ⟶ K') (ψ : Q'.obj M ⟶ c.pt) :
    adj.derivedHomEquiv hc' hd (ψ ≫ rightDerivedMap S (F ⋙ Q') hc hc' κ) =
      adj.derivedHomEquiv hc hd ψ ≫ Q.map κ := by
  obtain ⟨s, t, f, hψ⟩ := exists_rep_of_isRightDerivedValueAt (S' := S') hc ψ
  obtain ⟨I', s', f', hs', hsq⟩ := exists_ore_square_left S κ s.hom s.prop
  have hspec : c.ι.app s ≫ rightDerivedMap S (F ⋙ Q') hc hc' κ =
      Q'.map (F.map f') ≫ c'.ι.app (MorphismProperty.Under.mk ⊤ s' hs') :=
    rightDerivedMap_spec S (F ⋙ Q') hc hc' κ s.right I' s.hom s' f' s.prop hs' hsq
  have h₁ := (adj.derivedHomEquiv_spec hc hd s t f ψ).1 hψ
  have h₂ := (adj.derivedHomEquiv_spec hc' hd (MorphismProperty.Under.mk ⊤ s' hs') t
    (f ≫ F.map f') (ψ ≫ rightDerivedMap S (F ⋙ Q') hc hc' κ)).1 <|
      (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ rightDerivedMap S (F ⋙ Q') hc hc' κ) hψ).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (Q'.map f ≫ ·) hspec).trans <|
      (Category.assoc _ _ _).symm.trans <|
      congrArg (· ≫ c'.ι.app (MorphismProperty.Under.mk ⊤ s' hs')) (Q'.map_comp _ _).symm
  have : IsIso (Q.map s') := Localization.inverts Q S s' hs'
  rw [← cancel_mono (Q.map s')]
  exact h₂.trans <| Eq.symm <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) ((Q.map_comp _ _).symm.trans
      ((congrArg Q.map hsq).trans (Q.map_comp _ _)))).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ Q.map f') h₁).trans <|
    (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) ((Q.map_comp _ _).symm.trans
      (congrArg Q.map (adj.homEquiv_naturality_right_symm f f').symm))

/-- Naturality of the bijection of Stacks 0FND in `M`. Let `γ : M' ⟶ M` be a morphism of `𝒟'`
such that `LG` is defined at `M'` and at `M`, and let `LG(γ) : LG(M') ⟶ LG(M)` be the induced
morphism between the values (Stacks 05SA, for the pro-objects, written as the opposite of the
induced morphism of the opposite ind-objects). Then
`φ_{K,M'}(Q'(γ) ≫ ψ) = LG(γ) ≫ φ_{K,M}(ψ)`. -/
theorem derivedHomEquiv_map_comp
    (hc : (F ⋙ Q').IsRightDerivedValueAt S K c)
    (hd : (G ⋙ Q).op.IsRightDerivedValueAt S'.op (op M) d)
    (hd' : (G ⋙ Q).op.IsRightDerivedValueAt S'.op (op M') d')
    (γ : M' ⟶ M) (ψ : Q'.obj M ⟶ c.pt) :
    adj.derivedHomEquiv hc hd' (Q'.map γ ≫ ψ) =
      (rightDerivedMap S'.op (G ⋙ Q).op hd hd' γ.op).unop ≫ adj.derivedHomEquiv hc hd ψ := by
  obtain ⟨s, t, f, hψ⟩ := exists_rep_of_isRightDerivedValueAt (S' := S') hc ψ
  obtain ⟨P', v, t', ht', hsq⟩ := exists_ore_square_right S' t.hom.unop γ t.prop
  have hspec : d.ι.app t ≫ rightDerivedMap S'.op (G ⋙ Q).op hd hd' γ.op =
      (G ⋙ Q).op.map v.op ≫ d'.ι.app (MorphismProperty.Under.mk ⊤ t'.op ht') :=
    rightDerivedMap_spec S'.op (G ⋙ Q).op hd hd' γ.op t.right (op P') t.hom t'.op v.op t.prop ht'
      (Quiver.Hom.unop_inj hsq.symm)
  have hspec' : (rightDerivedMap S'.op (G ⋙ Q).op hd hd' γ.op).unop ≫ (d.ι.app t).unop =
      (d'.ι.app (MorphismProperty.Under.mk ⊤ t'.op ht')).unop ≫ Q.map (G.map v) :=
    congrArg Quiver.Hom.unop hspec
  have h₁ := (adj.derivedHomEquiv_spec hc hd s t f ψ).1 hψ
  have h₂ := (adj.derivedHomEquiv_spec hc hd' s (MorphismProperty.Under.mk ⊤ t'.op ht')
    (v ≫ f) (Q'.map γ ≫ ψ)).1 <|
      (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ ψ) ((Q'.map_comp _ _).symm.trans
        ((congrArg Q'.map hsq.symm).trans (Q'.map_comp _ _)))).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) hψ).trans <|
      (Category.assoc _ _ _).symm.trans <|
      congrArg (· ≫ c.ι.app s) (Q'.map_comp _ _).symm
  have : IsIso (Q.map s.hom) := Localization.inverts Q S s.hom s.prop
  rw [← cancel_mono (Q.map s.hom)]
  exact h₂.trans <| Eq.symm <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) h₁).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ Q.map ((adj.homEquiv _ _).symm f)) hspec').trans <|
    (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) ((Q.map_comp _ _).symm.trans
      (congrArg Q.map (adj.homEquiv_naturality_left_symm v f).symm))

/-- **Stacks 0FND**, functoriality of the canonical bijection in both variables, with respect to
morphisms of `𝒟` and `𝒟'`. Let `κ : K ⟶ K'` be a morphism of `𝒟` with `RF` defined at `K` and
`K'`, and `γ : M' ⟶ M` a morphism of `𝒟'` with `LG` defined at `M'` and `M`, with induced
morphisms `RF(κ) : RF(K) ⟶ RF(K')` and `LG(γ) : LG(M') ⟶ LG(M)` between the values
(Stacks 05SA). Then for every `ψ : M ⟶ RF(K)`,
`φ_{K',M'}(Q'(γ) ≫ ψ ≫ RF(κ)) = LG(γ) ≫ φ_{K,M}(ψ) ≫ Q(κ)`. Morphisms of the localized categories
are `derivedHomEquiv_comp_eq_comp` and `derivedHomEquiv_comp_eq_comp_left`. -/
@[stacks 0FND "functoriality of the bijection in both variables, for morphisms of `𝒟` and `𝒟'`"]
theorem derivedHomEquiv_naturality
    (hc : (F ⋙ Q').IsRightDerivedValueAt S K c) (hc' : (F ⋙ Q').IsRightDerivedValueAt S K' c')
    (hd : (G ⋙ Q).op.IsRightDerivedValueAt S'.op (op M) d)
    (hd' : (G ⋙ Q).op.IsRightDerivedValueAt S'.op (op M') d')
    (κ : K ⟶ K') (γ : M' ⟶ M) (ψ : Q'.obj M ⟶ c.pt) :
    adj.derivedHomEquiv hc' hd' (Q'.map γ ≫ ψ ≫ rightDerivedMap S (F ⋙ Q') hc hc' κ) =
      (rightDerivedMap S'.op (G ⋙ Q).op hd hd' γ.op).unop ≫
        adj.derivedHomEquiv hc hd ψ ≫ Q.map κ := by
  rw [adj.derivedHomEquiv_map_comp hc' hd hd', adj.derivedHomEquiv_comp_rightDerivedMap hc hc' hd]

/-- The morphism `RF(σ) : RF(K) ⟶ RF(L)` induced by a morphism `σ ∈ S` between objects at which
`RF` is defined is an isomorphism (Stacks 05SB). -/
lemma isIso_rightDerivedMap_of_mem {E : Type*} [Category E] {W : MorphismProperty D}
    [W.HasLeftCalculusOfFractions] (Φ : D ⥤ E)
    {cX : Cocone (MorphismProperty.Under.forget W ⊤ K ⋙ Under.forget K ⋙ Φ)}
    {cY : Cocone (MorphismProperty.Under.forget W ⊤ L ⋙ Under.forget L ⋙ Φ)}
    (hX : Φ.IsRightDerivedValueAt W K cX) (hY : Φ.IsRightDerivedValueAt W L cY)
    {σ : K ⟶ L} (hσ : W σ) : IsIso (rightDerivedMap W Φ hX hY σ) := by
  obtain ⟨φ, hφ, hiso⟩ := (Φ.exists_isRightDerivedValueAt_iff_and_isIso_of_mem W hσ).2 hX hY
  have : φ = rightDerivedMap W Φ hX hY σ :=
    rightDerivedMap_unique W Φ hX hY σ φ fun _ _ s₁ s' f' hs₁ hs' hsq =>
      hφ (MorphismProperty.Under.mk ⊤ s₁ hs₁) (MorphismProperty.Under.mk ⊤ s' hs') f' hsq.symm
  rw [← this]
  exact hiso

/-- **Stacks 0FND**, functoriality of the canonical bijection in `K` with respect to a morphism
`g : Q(K) ⟶ Q(K')` of `S⁻¹𝒟`. Such a morphism is a left fraction `g = Q(κ) ≫ Q(σ)⁻¹` with
`κ : K ⟶ L` and `σ : K' ⟶ L` in `S`, that is `g ≫ Q(σ) = Q(κ)`; then `RF` is defined at `L`
(Stacks 05SB) and `RF(g) = RF(κ) ≫ RF(σ)⁻¹` is the morphism `ρ : RF(K) ⟶ RF(K')` with
`ρ ≫ RF(σ) = RF(κ)`. For every `ψ : M ⟶ RF(K)`, `φ_{K',M}(ψ ≫ ρ) = φ_{K,M}(ψ) ≫ g`. -/
@[stacks 0FND "functoriality of the bijection in `K`, for morphisms of `S⁻¹𝒟`"]
theorem derivedHomEquiv_comp_eq_comp
    (hc : (F ⋙ Q').IsRightDerivedValueAt S K c) (hc' : (F ⋙ Q').IsRightDerivedValueAt S K' c')
    (hL : (F ⋙ Q').IsRightDerivedValueAt S L cL)
    (hd : (G ⋙ Q).op.IsRightDerivedValueAt S'.op (op M) d)
    (κ : K ⟶ L) (σ : K' ⟶ L) (hσ : S σ) (g : Q.obj K ⟶ Q.obj K')
    (hg : g ≫ Q.map σ = Q.map κ) (ρ : c.pt ⟶ c'.pt)
    (hρ : ρ ≫ rightDerivedMap S (F ⋙ Q') hc' hL σ = rightDerivedMap S (F ⋙ Q') hc hL κ)
    (ψ : Q'.obj M ⟶ c.pt) :
    adj.derivedHomEquiv hc' hd (ψ ≫ ρ) = adj.derivedHomEquiv hc hd ψ ≫ g := by
  have : IsIso (Q.map σ) := Localization.inverts Q S σ hσ
  rw [← cancel_mono (Q.map σ), Category.assoc, hg,
    ← adj.derivedHomEquiv_comp_rightDerivedMap hc hL hd, ← hρ, ← Category.assoc,
    adj.derivedHomEquiv_comp_rightDerivedMap hc' hL hd]

/-- **Stacks 0FND**, functoriality of the canonical bijection in `M` with respect to a morphism
`γ : Q'(M') ⟶ Q'(M)` of `(S')⁻¹𝒟'`. Such a morphism is a right fraction
`γ = Q'(τ)⁻¹ ≫ Q'(ν)` with `τ : N ⟶ M'` in `S'` and `ν : N ⟶ M`, that is `Q'(τ) ≫ γ = Q'(ν)`;
then `LG` is defined at `N` (Stacks 05SB) and `LG(γ) = LG(τ)⁻¹ ≫ LG(ν)` is the morphism
`μ : LG(M') ⟶ LG(M)` with `LG(τ) ≫ μ = LG(ν)`. For every `ψ : M ⟶ RF(K)`,
`φ_{K,M'}(γ ≫ ψ) = μ ≫ φ_{K,M}(ψ)`. -/
@[stacks 0FND "functoriality of the bijection in `M`, for morphisms of `(S')⁻¹𝒟'`"]
theorem derivedHomEquiv_comp_eq_comp_left
    (hc : (F ⋙ Q').IsRightDerivedValueAt S K c)
    (hd : (G ⋙ Q).op.IsRightDerivedValueAt S'.op (op M) d)
    (hd' : (G ⋙ Q).op.IsRightDerivedValueAt S'.op (op M') d')
    (hN : (G ⋙ Q).op.IsRightDerivedValueAt S'.op (op N) dN)
    (ν : N ⟶ M) (τ : N ⟶ M') (hτ : S' τ) (γ : Q'.obj M' ⟶ Q'.obj M)
    (hγ : Q'.map τ ≫ γ = Q'.map ν) (μ : d'.pt.unop ⟶ d.pt.unop)
    (hμ : (rightDerivedMap S'.op (G ⋙ Q).op hd' hN τ.op).unop ≫ μ =
      (rightDerivedMap S'.op (G ⋙ Q).op hd hN ν.op).unop)
    (ψ : Q'.obj M ⟶ c.pt) :
    adj.derivedHomEquiv hc hd' (γ ≫ ψ) = μ ≫ adj.derivedHomEquiv hc hd ψ := by
  have := isIso_rightDerivedMap_of_mem (G ⋙ Q).op hd' hN (σ := τ.op) hτ
  rw [← cancel_epi (rightDerivedMap S'.op (G ⋙ Q).op hd' hN τ.op).unop,
    ← adj.derivedHomEquiv_map_comp hc hd' hN, ← Category.assoc (Q'.map τ), hγ,
    adj.derivedHomEquiv_map_comp hc hd hN, ← Category.assoc _ μ, hμ]

end General

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive] (adj : G ⊣ F)
  {K K' : HomotopyCategory A (ComplexShape.up ℤ)} {M M' : HomotopyCategory B (ComplexShape.up ℤ)}
  {c : Cocone (MorphismProperty.Under.forget
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ K ⋙
    Under.forget K ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)}
  {c' : Cocone (MorphismProperty.Under.forget
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ K' ⋙
    Under.forget K' ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)}
  {d : Cone (MorphismProperty.Over.forget
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) ⊤ M ⋙
    Over.forget M ⋙ G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)}
  {d' : Cone (MorphismProperty.Over.forget
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) ⊤ M' ⋙
    Over.forget M' ⋙ G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)}

/-- **Stacks 0DVC**: the canonical bijection `Hom_{D(ℬ)}(M, RF(K)) ≃ Hom_{D(𝒜)}(LG(M), K)` for
`F : 𝒜 ⥤ ℬ` right adjoint to `G : ℬ ⥤ 𝒜`, a complex `K` of `𝒜` at which `RF` is defined, with
value `RF(K) = c.pt`, and a complex `M` of `ℬ` at which `LG` is defined, with value
`LG(M) = d.pt`. It is the unique bijection compatible with the fractions computing the two sides
(`derivedCategoryHomEquiv_spec`, `derivedCategoryHomEquiv_unique`), and it is natural in `K`
(`derivedCategoryHomEquiv_comp_rightDerivedMap`) and in `M`
(`derivedCategoryHomEquiv_map_comp`). -/
@[stacks 0DVC "the canonical isomorphism; its functoriality in both variables is
`derivedCategoryHomEquiv_comp_rightDerivedMap` and `derivedCategoryHomEquiv_map_comp`"]
noncomputable def derivedCategoryHomEquiv
    (hc : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsRightDerivedValueAt
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) K c)
    (hd : (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsLeftDerivedValueAt
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) M d) :
    (DerivedCategory.Qh.obj M ⟶ c.pt) ≃ (d.pt ⟶ DerivedCategory.Qh.obj K) :=
  (existsUnique_homEquiv_derivedCategory_of_isRightDerivedValueAt adj K M c hc d hd).exists.choose

/-- The bijection `derivedCategoryHomEquiv` is compatible with the fractions computing the two
sides: for an index `s : K ⟶ I` of the ind-object defining `RF(K)`, an index `t : P ⟶ M` of the
pro-object defining `LG(M)` and chain maps `f : P ⟶ F(I)`, `g : G(P) ⟶ I` adjoint to one another
in each degree, `Qh(t) ≫ ψ = Qh(f) ≫ (coprojection at s)` if and only if
`φ(ψ) ≫ Qh(s) = (projection at t) ≫ Qh(g)`. -/
lemma derivedCategoryHomEquiv_spec
    (hc : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsRightDerivedValueAt
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) K c)
    (hd : (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsLeftDerivedValueAt
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) M d)
    (s : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ K)
    (t : (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)).Over ⊤ M)
    (f : t.left.as ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj s.right.as)
    (g : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj t.left.as ⟶ s.right.as)
    (hfg : ∀ n, f.f n = adj.homEquiv _ _ (g.f n)) (ψ : DerivedCategory.Qh.obj M ⟶ c.pt) :
    DerivedCategory.Qh.map t.hom ≫ ψ =
        DerivedCategory.Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map f) ≫
          c.ι.app s ↔
      adj.derivedCategoryHomEquiv hc hd ψ ≫ DerivedCategory.Qh.map s.hom =
        d.π.app t ≫ DerivedCategory.Qh.map
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g) :=
  (existsUnique_homEquiv_derivedCategory_of_isRightDerivedValueAt adj K M c hc d
    hd).exists.choose_spec s t f g hfg ψ

/-- `derivedCategoryHomEquiv` is the only bijection compatible with the fractions. -/
lemma derivedCategoryHomEquiv_unique
    (hc : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsRightDerivedValueAt
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) K c)
    (hd : (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsLeftDerivedValueAt
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) M d)
    (φ : (DerivedCategory.Qh.obj M ⟶ c.pt) ≃ (d.pt ⟶ DerivedCategory.Qh.obj K))
    (hφ : ∀ (s : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ K)
        (t : (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)).Over ⊤ M)
        (f : t.left.as ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj s.right.as)
        (g : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj t.left.as ⟶ s.right.as),
        (∀ n, f.f n = adj.homEquiv _ _ (g.f n)) →
        ∀ ψ : DerivedCategory.Qh.obj M ⟶ c.pt,
          DerivedCategory.Qh.map t.hom ≫ ψ =
              DerivedCategory.Qh.map
                ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map f) ≫ c.ι.app s ↔
            φ ψ ≫ DerivedCategory.Qh.map s.hom =
              d.π.app t ≫ DerivedCategory.Qh.map
                ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g)) :
    φ = adj.derivedCategoryHomEquiv hc hd :=
  (existsUnique_homEquiv_derivedCategory_of_isRightDerivedValueAt adj K M c hc d hd).unique hφ
    (fun s t f g hfg ψ => derivedCategoryHomEquiv_spec adj hc hd s t f g hfg ψ)

omit [HasDerivedCategory A] in
/-- A morphism `ψ : M ⟶ RF(K)` of `D(ℬ)` is represented by a fraction through a single index of
the ind-object: `Qh(t) ≫ ψ = Qh(f) ≫ (coprojection at s)` for some index `s : K ⟶ I`, some
quasi-isomorphism `t : P ⟶ M` and some morphism `f : P ⟶ F(I)` of `K(ℬ)`. -/
private lemma exists_fraction_rep
    (hc : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsRightDerivedValueAt
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) K c)
    (ψ : DerivedCategory.Qh.obj M ⟶ c.pt) :
    ∃ (s : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ K)
      (t : (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)).Over ⊤ M)
      (f : t.left ⟶ (F.mapHomotopyCategory (ComplexShape.up ℤ)).obj s.right),
      DerivedCategory.Qh.map t.hom ≫ ψ = DerivedCategory.Qh.map f ≫ c.ι.app s := by
  obtain ⟨s₀, r, hr, -⟩ := hc
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction DerivedCategory.Qh
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) (ψ ≫ r)
  refine ⟨s₀, MorphismProperty.Over.mk ⊤ φ.s φ.hs, φ.f, ?_⟩
  have key : DerivedCategory.Qh.map φ.s ≫ ψ ≫ r = DerivedCategory.Qh.map φ.f := by
    rw [hφ]
    exact MorphismProperty.RightFraction.map_s_comp_map _ _ _
  exact (Category.comp_id _).symm.trans <|
    (congrArg (fun z => (DerivedCategory.Qh.map φ.s ≫ ψ) ≫ z) hr.symm).trans <|
    (Category.assoc _ _ _).symm.trans <|
    congrArg (· ≫ c.ι.app s₀) ((Category.assoc _ _ _).trans key)

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- The degreewise transpose of a chain map `f : P ⟶ F(I)` across `adj`. -/
private lemma exists_degreewise_transpose {P : HomologicalComplex B (ComplexShape.up ℤ)}
    {I : HomologicalComplex A (ComplexShape.up ℤ)}
    (f : P ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :
    ∃ g : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶ I,
      ∀ n, f.f n = adj.homEquiv _ _ (g.f n) :=
  ⟨((mapHomologicalComplexAdjunction adj (ComplexShape.up ℤ)).homEquiv P I).symm f,
    fun n => ((adj.homEquiv _ _).apply_symm_apply (f.f n)).symm⟩

/-- **Stacks 0DVC**, functoriality in `K`. Let `κ : K ⟶ K'` be a morphism of complexes of `𝒜`
(in the homotopy category) such that `RF` is defined at `K` and at `K'`, and let
`RF(κ) : RF(K) ⟶ RF(K')` be the induced morphism between the values (Stacks 05SA). Then for every
`ψ : M ⟶ RF(K)` in `D(ℬ)`, `φ_{K',M}(ψ ≫ RF(κ)) = φ_{K,M}(ψ) ≫ κ` in `D(𝒜)`. -/
@[stacks 0DVC "functoriality in `K`, with respect to morphisms of `K(𝒜)`"]
theorem derivedCategoryHomEquiv_comp_rightDerivedMap
    (hc : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsRightDerivedValueAt
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) K c)
    (hc' : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsRightDerivedValueAt
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) K' c')
    (hd : (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsLeftDerivedValueAt
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) M d)
    (κ : K ⟶ K') (ψ : DerivedCategory.Qh.obj M ⟶ c.pt) :
    adj.derivedCategoryHomEquiv hc' hd
        (ψ ≫ rightDerivedMap (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
          (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hc hc' κ) =
      adj.derivedCategoryHomEquiv hc hd ψ ≫ DerivedCategory.Qh.map κ := by
  obtain ⟨s, t, f₀, hψ⟩ := exists_fraction_rep hc ψ
  obtain ⟨f, rfl⟩ : ∃ f : t.left.as ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj s.right.as,
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map f = f₀ :=
    ⟨f₀.out, HomotopyCategory.quotient_map_out f₀⟩
  obtain ⟨g, hfg⟩ := exists_degreewise_transpose adj f
  obtain ⟨I', s', f', hs', hsq⟩ : ∃ (I' : HomotopyCategory A (ComplexShape.up ℤ)) (s' : K' ⟶ I')
      (f' : s.right ⟶ I'), HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s' ∧
        κ ≫ s' = s.hom ≫ f' :=
    exists_ore_square_left (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) κ s.hom s.prop
  obtain ⟨u, hu⟩ : ∃ u : s.right.as ⟶ I'.as,
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map u = f' :=
    ⟨f'.out, HomotopyCategory.quotient_map_out f'⟩
  set ρ := rightDerivedMap (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hc hc' κ
  have hspec : c.ι.app s ≫ ρ = DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map f') ≫
        c'.ι.app (MorphismProperty.Under.mk ⊤ s' hs') :=
    rightDerivedMap_spec (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hc hc' κ s.right I' s.hom
      s' f' s.prop hs' hsq
  have hfg' : ∀ n, (f ≫ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map u).f n =
      adj.homEquiv _ _ ((g ≫ u).f n) := fun n => by
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, hfg n,
      Adjunction.homEquiv_naturality_right]
  have e₁ : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
      (f ≫ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map u) =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map f ≫
        (F.mapHomotopyCategory (ComplexShape.up ℤ)).map f' := by
    rw [Functor.map_comp, ← Functor.mapHomotopyCategory_map, hu]
    rfl
  have e₂ : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (g ≫ u) =
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g ≫ f' := by
    rw [Functor.map_comp, hu]
    rfl
  have h₁ := (derivedCategoryHomEquiv_spec adj hc hd s t f g hfg ψ).1 hψ
  have h₂ := (derivedCategoryHomEquiv_spec adj hc' hd (MorphismProperty.Under.mk ⊤ s' hs') t
    (f ≫ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map u) (g ≫ u) hfg' (ψ ≫ ρ)).1 <|
      (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ ρ) hψ).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) hspec).trans <|
      (Category.assoc _ _ _).symm.trans <|
      congrArg (· ≫ c'.ι.app (MorphismProperty.Under.mk ⊤ s' hs'))
        ((DerivedCategory.Qh.map_comp _ _).symm.trans (congrArg DerivedCategory.Qh.map e₁.symm))
  have : IsIso (DerivedCategory.Qh.map s') := Localization.inverts DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) s' hs'
  rw [← cancel_mono (DerivedCategory.Qh.map s')]
  exact h₂.trans <| Eq.symm <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) ((DerivedCategory.Qh.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Qh.map hsq).trans (DerivedCategory.Qh.map_comp _ _)))).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ DerivedCategory.Qh.map f') h₁).trans <|
    (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) ((DerivedCategory.Qh.map_comp _ _).symm.trans
      (congrArg DerivedCategory.Qh.map e₂.symm))

/-- **Stacks 0DVC**, functoriality in `M`. Let `γ : M' ⟶ M` be a morphism of complexes of `ℬ`
(in the homotopy category) such that `LG` is defined at `M'` and at `M`, and let
`LG(γ) : LG(M') ⟶ LG(M)` be the induced morphism between the values (Stacks 05SA). Then for every
`ψ : M ⟶ RF(K)` in `D(ℬ)`, `φ_{K,M'}(γ ≫ ψ) = LG(γ) ≫ φ_{K,M}(ψ)` in `D(𝒜)`. -/
@[stacks 0DVC "functoriality in `M`, with respect to morphisms of `K(ℬ)`"]
theorem derivedCategoryHomEquiv_map_comp
    (hc : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsRightDerivedValueAt
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) K c)
    (hd : (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsLeftDerivedValueAt
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) M d)
    (hd' : (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsLeftDerivedValueAt
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) M' d')
    (γ : M' ⟶ M) (ψ : DerivedCategory.Qh.obj M ⟶ c.pt) :
    adj.derivedCategoryHomEquiv hc hd' (DerivedCategory.Qh.map γ ≫ ψ) =
      leftDerivedMap (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
          (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hd' hd γ ≫
        adj.derivedCategoryHomEquiv hc hd ψ := by
  obtain ⟨s, t, f₀, hψ⟩ := exists_fraction_rep hc ψ
  obtain ⟨f, rfl⟩ : ∃ f : t.left.as ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj s.right.as,
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map f = f₀ :=
    ⟨f₀.out, HomotopyCategory.quotient_map_out f₀⟩
  obtain ⟨g, hfg⟩ := exists_degreewise_transpose adj f
  obtain ⟨P', v, t', ht', hsq⟩ : ∃ (P' : HomotopyCategory B (ComplexShape.up ℤ)) (v : P' ⟶ t.left)
      (t' : P' ⟶ M'), HomotopyCategory.quasiIso B (ComplexShape.up ℤ) t' ∧
        v ≫ t.hom = t' ≫ γ :=
    exists_ore_square_right (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) t.hom γ t.prop
  obtain ⟨w, hw⟩ : ∃ w : P'.as ⟶ t.left.as,
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map w = v :=
    ⟨v.out, HomotopyCategory.quotient_map_out v⟩
  set μ := leftDerivedMap (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
    (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hd' hd γ
  have hspec : μ ≫ d.π.app t = d'.π.app (MorphismProperty.Over.mk ⊤ t' ht') ≫
      DerivedCategory.Qh.map ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map v) :=
    leftDerivedMap_spec (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
      (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hd' hd γ P' t.left t'
      t.hom v ht' t.prop hsq.symm
  have hfg' : ∀ n, (w ≫ f).f n =
      adj.homEquiv _ _ (((G.mapHomologicalComplex (ComplexShape.up ℤ)).map w ≫ g).f n) :=
    fun n => by
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, hfg n,
        Adjunction.homEquiv_naturality_left]
  have e₁ : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map (w ≫ f) =
      v ≫ (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map f := by
    rw [Functor.map_comp, hw]
    rfl
  have e₂ : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map w ≫ g) =
      (G.mapHomotopyCategory (ComplexShape.up ℤ)).map v ≫
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g := by
    rw [Functor.map_comp, ← Functor.mapHomotopyCategory_map, hw]
    rfl
  have h₁ := (derivedCategoryHomEquiv_spec adj hc hd s t f g hfg ψ).1 hψ
  have h₂ := (derivedCategoryHomEquiv_spec adj hc hd' s (MorphismProperty.Over.mk ⊤ t' ht')
    (w ≫ f) ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map w ≫ g) hfg'
    (DerivedCategory.Qh.map γ ≫ ψ)).1 <|
      (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ ψ) ((DerivedCategory.Qh.map_comp _ _).symm.trans
        ((congrArg DerivedCategory.Qh.map hsq.symm).trans
          (DerivedCategory.Qh.map_comp _ _)))).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) hψ).trans <|
      (Category.assoc _ _ _).symm.trans <|
      congrArg (· ≫ c.ι.app s)
        ((DerivedCategory.Qh.map_comp _ _).symm.trans (congrArg DerivedCategory.Qh.map e₁.symm))
  have : IsIso (DerivedCategory.Qh.map s.hom) := Localization.inverts DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) s.hom s.prop
  rw [← cancel_mono (DerivedCategory.Qh.map s.hom)]
  exact h₂.trans <| Eq.symm <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) h₁).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ DerivedCategory.Qh.map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g)) hspec).trans <|
    (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) ((DerivedCategory.Qh.map_comp _ _).symm.trans
      (congrArg DerivedCategory.Qh.map e₂.symm))

end CategoryTheory.Adjunction

end
