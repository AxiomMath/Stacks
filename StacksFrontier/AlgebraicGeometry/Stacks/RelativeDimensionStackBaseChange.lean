module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionChartIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDecent
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedBicategory
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence

/-!
# Base change of the relative dimension of a 1-morphism of algebraic stacks

Stacks 0DRL defines the relative dimension `dim_t(𝒯_x)` of a locally-of-finite-type 1-morphism
`f : 𝒯 ⟶ 𝒳` of locally Noetherian algebraic stacks at a point `t ∈ |𝒯|`: it is the dimension of
the algebraic stack `𝒯 ×_𝒳 Spec k` at a point above `t`, for a field-valued point
`Spec k ⟶ 𝒳` representing the image `x` of `t`. This file computes that dimension on a smooth
chart of `𝒯`, and reads off the two consequences: the value does not depend on the two choices
(Stacks 0DRM), and it is unchanged by base change (**Stacks 0DRN**).

## Main results

* `AlgebraicGeometry.Stack.exists_isSmooth_algebraicSpaceStack_hom_pointsMap_eq`: every
  algebraic stack carries, above any point, a smooth 1-morphism from an algebraic space.
* `AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_of_isTwoFibreProduct_fieldFibre`:
  the chart formula. For *any* 2-fibre product of `f` with the 1-morphism of a field-valued
  point `p` of `𝒳`, the dimension of its apex at a point above `t` is
  `dim_t(T_x) - dim_t(T_t)`, the two relative dimensions of Stacks 0DRG of a smooth chart
  `T ⟶ 𝒯` of `𝒯` at a point above `t`, read over `𝒳` and over `𝒯` respectively. The right-hand
  side mentions neither `p` nor the point above `t` nor even the square.
* `AlgebraicGeometry.Stack.relativeStackDimensionAt_eq_dimensionSubNat_of_isSmooth`: the same
  formula for the relative dimension of Stacks 0DRL itself.
* `AlgebraicGeometry.Stack.relativeStackDimensionAt_eq_fieldFibreStackDimensionAt` is
  **Stacks 0DRM** in general: the infimum of Stacks 0DRL is attained at every admissible pair of
  choices, so the relative dimension depends on neither.
* `AlgebraicGeometry.Stack.relativeStackDimensionAt_fst_eq_relativeStackDimensionAt` is
  **Stacks 0DRN**: in a Cartesian square of locally Noetherian algebraic stacks whose vertical
  1-morphisms are locally of finite type, the relative dimension at a point of the upper-left
  stack is the relative dimension at its image in the upper-right stack.

## Implementation notes

The chart formula is the source's own computation of Stacks 0DRM, made available at a
*recognised* fibre rather than only at the canonical apex of Stacks 003Q. That generality is
what proves Stacks 0DRN: the fibre `𝒯' ×_{𝒳'} Spec k` of the base-changed 1-morphism over a
field-valued point `p'` of `𝒳'` is, pasted with the Cartesian square and reindexed along
`AlgebraicGeometry.Stack.fieldValuedPointMorphism_comp_iso`, a 2-fibre product of `f` with the
1-morphism of the image field-valued point of `𝒳`. So both sides of Stacks 0DRN are infima of
sets each of whose members the chart formula evaluates at one and the same chart of `𝒯` — and
no comparison of a field-valued point of `𝒳` with one of `𝒳'` is needed, which is what the
naive reading of the source's one-line proof would require.

The proof of the chart formula is the dimension formula of Stacks 0DRJ
(`AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_of_isSmooth`, which rests on the
chart-independence of Stacks 0AFM) applied to the apex `𝒵` of the given square along the base
change `𝒵 ×_𝒯 T` of the chart. Two things have to be arranged.

First, the formula of Stacks 0AFN quantifies over 1-morphisms whose source is *the* algebraic
stack of an algebraic space, while `𝒵 ×_𝒯 T` is the 2-fibre product of Stacks 04T2, merely
*representable* by an algebraic space `E`. The comparison `E ⟶ 𝒵 ×_𝒯 T` that Stacks 04SW
attaches to the identity of `E` repairs this: it is smooth, by the representable case of
Stacks 06FM, and it is an equivalence of the underlying categories, because Stacks 04SW is a
bijection on 2-isomorphism classes, so the square precomposed with it is again a 2-fibre
product by `CategoryTheory.Bicategory.isTwoFibreProduct_of_isEquivalence_to`.

Second, the subtrahend of Stacks 0AFN for that chart is the relative dimension of Stacks 0DRG of
`E ⟶ 𝒵`, and it has to be identified with the relative dimension of `T ⟶ 𝒯`. This is the
base-change invariance of Stacks 0DRG *along a 1-morphism of algebraic stacks*;
`AlgebraicGeometry.Stack.hasRelativeDimensionAt_representingMap_fst_of_fieldFibreDimensionAt`
is the case of a base representable by an algebraic space.
It is obtained here from Stacks 0DRH (1) at both ends: the fibre of `E ⟶ 𝒵` over a field-valued
point `τ` of `𝒵` is, pasted with the base-change square and reindexed, a 2-fibre product of
`T ⟶ 𝒯` with the 1-morphism of the image of `τ` in `𝒯`, and
`AlgebraicGeometry.Stack.representedDimensionAtPoint_eq_fieldFibreDimensionAt_of_fst` evaluates
the formula of Stacks 0DRG on it.

Local Noetherianity of the apex is an argument rather than a consequence: the statement is for
an arbitrary recognised 2-fibre product, so the projection to the field spectrum is not at hand
in the form Stacks 06R6 wants. At the canonical apex it is
`AlgebraicGeometry.Stack.isLocallyNoetherianStack_fieldFibreStackSquare`, which is what the
three results built on the chart formula pass.

The Cartesian hypothesis of Stacks 0DRN is terminality in the 2-category of algebraic stacks,
which is a priori weaker than terminality in the ambient 2-category of categories fibred in
groupoids; the two agree here because the cospan has a 2-fibre product whose apex is an
algebraic stack (Stacks 04T2), which is
`CategoryTheory.Bicategory.isTwoFibreProduct_underlying`.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06R6](https://stacks.math.columbia.edu/tag/06R6)
* [Stacks Project, Tag 075V](https://stacks.math.columbia.edu/tag/075V)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
* [Stacks Project, Tag 0AFM](https://stacks.math.columbia.edu/tag/0AFM)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRH](https://stacks.math.columbia.edu/tag/0DRH)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DRM](https://stacks.math.columbia.edu/tag/0DRM)
* [Stacks Project, Tag 0DRN](https://stacks.math.columbia.edu/tag/0DRN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

/-! ### Precomposing a 2-commutative square with a 1-morphism into its apex -/

section Precompose

variable {A : Type*} [Bicategory A] {x y z : A} {f : x ⟶ z} {g : y ⟶ z}

/-- **The cone obtained by precomposing the apex of a 2-commutative square of Stacks 003O with a
1-morphism.** Its two legs are those of the given square preceded by that 1-morphism, and its
filler is the given one whiskered by it. -/
private def precomposedSq (W : Bicategory.TwoCommSq f g) {a : A} (c : a ⟶ W.pt) :
    Bicategory.TwoCommSq f g where
  pt := a
  fst := c ≫ W.fst
  snd := c ≫ W.snd
  iso := α_ c W.fst f ≪≫ Bicategory.whiskerLeftIso c W.iso ≪≫ (α_ c W.snd g).symm

/-- **The comparison of Stacks 003O from a precomposed cone into the original one.** Its
1-morphism is the one precomposed with, and both of its comparison 2-cells are identities,
`AlgebraicGeometry.Stack.precomposedSq` having been given exactly the filler that makes the
compatibility square of Stacks 003O coherence. -/
private def precomposedPreHom (W : Bicategory.TwoCommSq f g) {a : A} (c : a ⟶ W.pt) :
    Bicategory.TwoCommSq.PreHom (precomposedSq W c) W where
  hom := c
  isoFst := Iso.refl _
  isoSnd := Iso.refl _
  compat := by
    dsimp only [precomposedSq]
    simp only [Iso.trans_hom, Iso.symm_hom, Bicategory.whiskerLeftIso_hom]
    bicategory

end Precompose

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A smooth chart by an algebraic space above a given point -/

/-- **Every algebraic stack over `S` carries, above any point of it, a smooth 1-morphism from an
algebraic space.** This is the nonemptiness of the set of choices the formula of Stacks 0AFN
takes its infimum over, and it is what makes the chart formula below unconditional.

Stacks 03YP gives a smooth surjective 1-morphism from the algebraic stack of a scheme of the
site, and that algebraic stack receives a smooth surjective 1-morphism from the algebraic stack
of the algebraic space the same scheme represents, both being representable by one presheaf; the
composite is smooth and surjective, and surjectivity is surjectivity on points
(Stacks 04ZS). -/
theorem exists_isSmooth_algebraicSpaceStack_hom_pointsMap_eq (𝒯 : AlgebraicStacks.{u, w} B S hS)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    ∃ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
      (a : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒯),
      AlgebraicStacks.IsSmooth B S hS a ∧
        ∃ u : Space.points B S hS U,
          pointsMap B S hS (fibredCategory B S hS U).val (fibredCategory B S hS U).property
            𝒯.val.property a.hom.hom (stackPointOfSpacePoint B S hS U u) = t := by
  obtain ⟨U₀, a, hasm, hasurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒯
  obtain ⟨e, hesm, hesurj⟩ := exists_smooth_surjective_algebraicSpaceStack_hom.{u, w} B S hS U₀
  refine ⟨yoneda.obj U₀, isAlgebraicSpace_yoneda B S hS U₀, e ≫ a,
    AlgebraicStacks.isSmooth_comp B S hS e a hesm hasm, ?_⟩
  obtain ⟨z, hz⟩ := isSurjective_comp B S hS e a hesurj hasurj t
  obtain ⟨u, hu⟩ := (spacePointMap_id_bijective B S hS (yoneda.obj U₀)).surjective z
  exact ⟨u, by rw [← hz, ← hu]⟩

/-! ### The chart formula at a recognised fibre over a field-valued point -/

section ChartFormula

variable {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **The chart formula for the dimension of a fibre of Stacks 0DRL.** Let `f : 𝒯 ⟶ 𝒳` be a
1-morphism of algebraic stacks over `S`, let `h : U ⟶ 𝒯` be a smooth, locally-of-finite-type
1-morphism from an algebraic space with `u ∈ |U|`, and let `R` be *any* 2-fibre product of `f`
with the 1-morphism of a field-valued point `p` of `𝒳` representing the image of `u` in `|𝒳|`.
If `y` is a point of the apex of `R` with the same image in `|𝒯|` as `u`, and if the relative
dimension of Stacks 0DRG of `h` at `u` is the natural number `d`, then
`dim_y(R) = dim_u(U_x) - d`,
the subtrahend being the relative dimension of Stacks 0DRG of `h ≫ f` at `u`.

The right-hand side is a function of `(h, u)` alone: it mentions neither `p`, nor `y`, nor `R`.
That is what makes this statement prove both Stacks 0DRM and Stacks 0DRN.

The proof is the dimension formula of Stacks 0DRJ on the apex of `R`, computed along the base
change `R ×_𝒯 U` of `h`; see the module's implementation notes for the two repairs that needs. -/
theorem dimensionAtPoint_eq_dimensionSubNat_of_isTwoFibreProduct_fieldFibre
    (f : 𝒯 ⟶ 𝒳)
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (h : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒯)
    (hsm : AlgebraicStacks.IsSmooth B S hS h)
    (hh : AlgebraicStacks.IsLocallyOfFiniteType B S hS h)
    (hhf : AlgebraicStacks.IsLocallyOfFiniteType B S hS (h ≫ f))
    (u : Space.points B S hS U)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    {R : Bicategory.TwoCommSq f.hom (fieldValuedPointMorphism B S hS 𝒳.val p)}
    (hR : Bicategory.IsTwoFibreProduct R)
    (hRalg : IsAlgebraicStack.{u, w} B S hS R.pt.val)
    (hRN : IsLocallyNoetherianStack.{u, w} B S hS ⟨R.pt, hRalg⟩)
    (y : points B S hS R.pt.val R.pt.property)
    (hy : pointsMap B S hS R.pt.val R.pt.property 𝒯.val.property R.fst.hom y =
      pointsMap B S hS (fibredCategory B S hS U).val (fibredCategory B S hS U).property
        𝒯.val.property h.hom.hom (stackPointOfSpacePoint B S hS U u))
    (hp : pointClass B S hS 𝒳.val.val 𝒳.val.property p =
      pointsMap B S hS (fibredCategory B S hS U).val (fibredCategory B S hS U).property
        𝒳.val.property (h ≫ f).hom.hom (stackPointOfSpacePoint B S hS U u))
    (d : ℕ) (hd : relativeDimensionAt.{u, w} B S hS U hU 𝒯 h hh u = (d : WithBot ℕ∞)) :
    dimensionAtPoint B S hS ⟨R.pt, hRalg⟩ hRN y =
      dimensionSubNat (relativeDimensionAt.{u, w} B S hS U hU 𝒳 (h ≫ f) hhf u) d := by
  classical
  have hUrep : IsRepresentableByAlgebraicSpace B S hS (fibredCategory B S hS U) :=
    isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU
  -- the apex of `R`, read as an algebraic stack, and its projection to `𝒯`
  set 𝒵 : AlgebraicStacks.{u, w} B S hS := ⟨R.pt, hRalg⟩ with h𝒵
  set ρ : 𝒵 ⟶ 𝒯 := Bicategory.InducedBicategory.mkHom R.fst with hρ
  -- the base change of the chart along `ρ`
  set W := twoFibreProductSquareAlgebraicStacks B S hS ρ h with hWdef
  have hW := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS ρ h
  have hWc : Bicategory.IsTwoFibreProduct
      (Bicategory.TwoCommSq.underlying (F := Subtype.val) W) :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      R.fst h.hom
  have hWfstsm : AlgebraicStacks.IsSmooth B S hS W.fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS h ρ W hW hsm
  have hWrep : IsRepresentableByAlgebraicSpace B S hS W.pt.val :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (fibredCategory B S hS U) 𝒳.val (schemeFibredCategory B S hS p.base)
      (h.hom ≫ f.hom) (fieldValuedPointMorphism B S hS 𝒳.val p)
      (R.swap.paste (Bicategory.TwoCommSq.underlying (F := Subtype.val) W))
      (Bicategory.isTwoFibreProduct_paste (Bicategory.isTwoFibreProduct_swap hR) hWc)
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property hUrep _)
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS p.base)
  obtain ⟨E, hE, ⟨eE⟩⟩ := id hWrep
  have hErep : IsRepresentableByAlgebraicSpace B S hS (fibredCategory B S hS E) :=
    isRepresentableByAlgebraicSpace_fibredCategory B S hS E hE
  obtain ⟨c, hc⟩ := exists_oneMorphism_representingMap_eq B S hS
    (𝒳 := algebraicSpaceStack.{u, w} B S hS E hE) (𝒴 := W.pt) E E
    (StacksRepresentableCFG.EquivalenceOver.refl _) eE (𝟙 E)
  obtain ⟨c', hc'⟩ := exists_oneMorphism_representingMap_eq B S hS
    (𝒳 := W.pt) (𝒴 := algebraicSpaceStack.{u, w} B S hS E hE) E E
    eE (StacksRepresentableCFG.EquivalenceOver.refl _) (𝟙 E)
  have hcsm : AlgebraicStacks.IsSmooth B S hS c :=
    isSmooth_of_isSmooth_representingMap B S hS E E hE hE
      (StacksRepresentableCFG.EquivalenceOver.refl _) eE c
      (by rw [hc]; exact Space.isSmooth_id B S hS hE)
  obtain ⟨e₁⟩ := nonempty_unique_twoIso_of_representingMap_eq B S hS
    (fibredCategory B S hS E) (fibredCategory B S hS E) E E
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (f := c.hom ≫ c'.hom) (g := 𝟙 _)
    (by rw [representingMap_comp B S hS E E E
        (StacksRepresentableCFG.EquivalenceOver.refl _) eE
        (StacksRepresentableCFG.EquivalenceOver.refl _) c.hom c'.hom, hc, hc',
      Category.comp_id, representingMap_id B S hS (fibredCategory B S hS E) E
        (StacksRepresentableCFG.EquivalenceOver.refl _)])
  obtain ⟨e₁'⟩ := nonempty_unique_twoIso_of_representingMap_eq B S hS
    W.pt.val W.pt.val E E eE eE
    (f := c'.hom ≫ c.hom) (g := 𝟙 _)
    (by rw [representingMap_comp B S hS E E E eE
        (StacksRepresentableCFG.EquivalenceOver.refl _) eE c'.hom c.hom, hc, hc',
      Category.comp_id, representingMap_id B S hS W.pt.val E eE])
  have hceq : (c.hom).hom.toFunctor.IsEquivalence :=
    (CategoryTheory.Equivalence.mk c.hom.hom.toFunctor c'.hom.hom.toFunctor
      (CatFiberedInGroupoids.underlyingIso e₁.default).symm
      (CatFiberedInGroupoids.underlyingIso e₁'.default)).isEquivalence_functor
  set Q := precomposedSq (Bicategory.TwoCommSq.underlying (F := Subtype.val) W) c.hom with hQdef
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    Bicategory.isTwoFibreProduct_of_isEquivalence_to hWc
      (precomposedPreHom (Bicategory.TwoCommSq.underlying (F := Subtype.val) W) c.hom) hceq
  set k : algebraicSpaceStack.{u, w} B S hS E hE ⟶ 𝒵 := c ≫ W.fst with hkdef
  have hksm : AlgebraicStacks.IsSmooth B S hS k :=
    AlgebraicStacks.isSmooth_comp B S hS c W.fst hcsm hWfstsm
  have hklft := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS k hksm
  obtain ⟨ζ, hz1, hz2⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS W hW
    y (stackPointOfSpacePoint B S hS U u) hy
  obtain ⟨w₀, hw₀⟩ := (bijective_spacePointMap_representing B S hS E W.pt.val eE).surjective ζ
  have hcw : pointsMap B S hS (fibredCategory B S hS E).val (fibredCategory B S hS E).property
      W.pt.val.property c.hom.hom (stackPointOfSpacePoint B S hS E w₀) = ζ := by
    have hnat := spacePointMap_representing_naturality B S hS E E
      (fibredCategory B S hS E) W.pt.val (StacksRepresentableCFG.EquivalenceOver.refl _) eE
      c.hom w₀
    rw [hc, Space.pointsMap_id, id_eq] at hnat
    rw [← hw₀]; exact hnat.symm
  have hky : pointsMap B S hS (fibredCategory B S hS E).val
      (fibredCategory B S hS E).property 𝒵.val.property k.hom.hom
      (stackPointOfSpacePoint B S hS E w₀) = y :=
    ((pointsMap_comp B S hS (fibredCategory B S hS E).val
      (fibredCategory B S hS E).property W.pt.val.property 𝒵.val.property
      c.hom.hom W.fst.hom.hom (stackPointOfSpacePoint B S hS E w₀)).symm.trans
      (congrArg _ hcw)).trans hz1
  have hQsnd : pointsMap B S hS (fibredCategory B S hS E).val
      (fibredCategory B S hS E).property (fibredCategory B S hS U).property Q.snd.hom
      (stackPointOfSpacePoint B S hS E w₀) = stackPointOfSpacePoint B S hS U u :=
    ((pointsMap_comp B S hS (fibredCategory B S hS E).val
      (fibredCategory B S hS E).property W.pt.val.property
      (fibredCategory B S hS U).property c.hom.hom W.snd.hom.hom
      (stackPointOfSpacePoint B S hS E w₀)).symm.trans (congrArg _ hcw)).trans hz2
  obtain ⟨d₂, hd₂⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS E hE 𝒵 k hklft w₀
  have hJ := dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒵 hRN y hE k hksm
    hklft w₀ hky d₂ hd₂
  obtain ⟨q₀, hq₀⟩ := exists_point_fieldFibreSquare B S hS (h ≫ f).hom
    (stackPointOfSpacePoint B S hS U u) p hp
  have hdimE : Space.dimensionAtPoint B S hS E hE w₀ =
      relativeDimensionAt.{u, w} B S hS U hU 𝒳 (h ≫ f) hhf u :=
    ((representedDimensionAtPoint_eq B S hS (fibredCategory B S hS E) hErep E hE
        (StacksRepresentableCFG.EquivalenceOver.refl _) w₀).symm.trans
      (representedDimensionAtPoint_eq_fieldFibreDimensionAt_of_fst.{u, w} B S hS (h ≫ f)
        hUrep hhf p (P := (R.swap.paste Q).swap)
        (Bicategory.isTwoFibreProduct_swap
          (Bicategory.isTwoFibreProduct_paste (Bicategory.isTwoFibreProduct_swap hR) hQ))
        hErep (stackPointOfSpacePoint B S hS E w₀) q₀ (hQsnd.trans hq₀.symm))).trans
      (relativeDimensionAt_eq_fieldFibreDimensionAt B S hS U hU 𝒳 (h ≫ f) hhf u p q₀
        hp hq₀).symm
  obtain ⟨τ, q₁, hτ, hq₁, hvalk⟩ := exists_eq_fieldFibreDimensionAt B S hS E hE 𝒵 k hklft w₀
  have hkrho : pointsMap B S hS (fibredCategory B S hS E).val
      (fibredCategory B S hS E).property 𝒯.val.property
      (Q.fst ≫ ρ.hom).hom (stackPointOfSpacePoint B S hS E w₀) =
      pointsMap B S hS (fibredCategory B S hS U).val (fibredCategory B S hS U).property
        𝒯.val.property h.hom.hom (stackPointOfSpacePoint B S hS U u) :=
    (congrFun (pointsMap_eq_of_basedNatTrans B S hS (fibredCategory B S hS E).val
      (fibredCategory B S hS E).property 𝒯.val.property Q.iso.hom.hom)
      (stackPointOfSpacePoint B S hS E w₀)).trans
      ((pointsMap_comp B S hS (fibredCategory B S hS E).val
        (fibredCategory B S hS E).property (fibredCategory B S hS U).property
        𝒯.val.property Q.snd.hom h.hom.hom
        (stackPointOfSpacePoint B S hS E w₀)).symm.trans (congrArg _ hQsnd))
  have hτ' : pointClass B S hS 𝒯.val.val 𝒯.val.property
      (fieldValuedPointMap B S hS 𝒵.val.val ρ.hom.hom τ) =
      pointsMap B S hS (fibredCategory B S hS U).val (fibredCategory B S hS U).property
        𝒯.val.property h.hom.hom (stackPointOfSpacePoint B S hS U u) := by
    rw [← pointsMap_class B S hS 𝒵.val.val 𝒵.val.property 𝒯.val.property ρ.hom.hom τ, hτ,
      pointsMap_comp B S hS (fibredCategory B S hS E).val (fibredCategory B S hS E).property
        𝒵.val.property 𝒯.val.property k.hom.hom ρ.hom.hom
        (stackPointOfSpacePoint B S hS E w₀)]
    exact hkrho
  obtain ⟨q₂, hq₂⟩ := exists_point_fieldFibreSquare B S hS h.hom
    (stackPointOfSpacePoint B S hS U u)
    (fieldValuedPointMap B S hS 𝒵.val.val ρ.hom.hom τ) hτ'
  have hRe := Bicategory.isTwoFibreProduct_reindexSnd
    (Bicategory.InducedBicategory.isoMk
      (fieldValuedPointMorphism_comp_iso B S hS ρ.hom.hom τ))
    (Bicategory.isTwoFibreProduct_paste (Bicategory.isTwoFibreProduct_swap hQ)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        k.hom (fieldValuedPointMorphism B S hS 𝒵.val τ)))
  have hPptrep : IsRepresentableByAlgebraicSpace B S hS (fieldFibreSquare B S hS k.hom τ).pt :=
    isRepresentableByAlgebraicSpace_fieldFibreSquare.{u, w} B S hS k.hom 𝒵.property hErep τ
  have hd2d : fieldFibreDimensionAt.{u, w} B S hS k.hom 𝒵.property hErep τ q₁ =
      relativeDimensionAt.{u, w} B S hS U hU 𝒯 h hh u :=
    (representedDimensionAtPoint_eq_fieldFibreDimensionAt_of_fst.{u, w} B S hS h hUrep hh
      (fieldValuedPointMap B S hS 𝒵.val.val ρ.hom.hom τ) hRe hPptrep q₁ q₂
      (((pointsMap_comp B S hS (fieldFibreSquare B S hS k.hom τ).pt.val
          (fieldFibreSquare B S hS k.hom τ).pt.property
          (fibredCategory B S hS E).property (fibredCategory B S hS U).property
          (fieldFibreSquare B S hS k.hom τ).fst.hom Q.snd.hom q₁).symm.trans
        (congrArg _ hq₁)).trans (hQsnd.trans hq₂.symm))).trans
      (relativeDimensionAt_eq_fieldFibreDimensionAt B S hS U hU 𝒯 h hh u _ q₂ hτ' hq₂).symm
  have hdd : d₂ = d := by
    have hcast : ((d₂ : ℕ∞) : WithBot ℕ∞) = ((d : ℕ∞) : WithBot ℕ∞) :=
      hd₂.symm.trans (hvalk.trans (hd2d.trans hd))
    exact_mod_cast hcast
  rw [hJ, hdd, hdimE]

/-- A value of the formula of Stacks 0DRL at every admissible pair of choices is the relative
dimension: such a pair exists by
`AlgebraicGeometry.Stack.exists_admissible_fieldFibreStackDimensionAt`, and the relative dimension
is the infimum of those values. -/
private theorem relativeStackDimension_eq_of_forall_fieldFibreStackDimensionAt_eq (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) {v : EInt}
    (hv : ∀ (p : FieldValuedPoint B S hS 𝒳.val.val)
      (q : points B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
        (fieldFibreStackSquare B S hS f p).pt.val.property),
      pointClass B S hS 𝒳.val.val 𝒳.val.property p =
          pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property f.hom.hom t →
        pointsMap B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
            (fieldFibreStackSquare B S hS f p).pt.val.property 𝒯.val.property
            (fieldFibreStackSquare B S hS f p).snd.hom.hom q = t →
          fieldFibreStackDimensionAt.{u, w} B S hS f hf p q = v) :
    relativeStackDimension.{u, w} B S hS f hf t = v := by
  refine le_antisymm ?_ (le_sInf ?_)
  · obtain ⟨p₀, q₀, hp₀, hq₀⟩ := exists_admissible_fieldFibreStackDimensionAt.{u, w} B S hS f t
    exact (relativeStackDimension_le.{u, w} B S hS f hf t p₀ hp₀ q₀ hq₀).trans_eq
      (hv p₀ q₀ hp₀ hq₀)
  · rintro z ⟨p, q, hp, hq, rfl⟩
    exact (hv p q hp hq).ge

/-- **The chart formula at an admissible pair of choices.** For a smooth, locally-of-finite-type
1-morphism `h : U ⟶ 𝒯` from an algebraic space with a point `u ∈ |U|` above `t`, the formula of
Stacks 0DRL takes the value `dim_u(U_x) - d` at every admissible pair of choices, where `d` is the
relative dimension of Stacks 0DRG of `h` at `u`: this is
`AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_of_isTwoFibreProduct_fieldFibre` at
the canonical apex. -/
private theorem fieldFibreStackDimensionAt_eq_dimensionSubNat_of_isSmooth
    (f : 𝒯 ⟶ 𝒳) (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (t : points B S hS 𝒯.val.val 𝒯.val.property)
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (h : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒯)
    (hsm : AlgebraicStacks.IsSmooth B S hS h)
    (hh : AlgebraicStacks.IsLocallyOfFiniteType B S hS h)
    (hhf : AlgebraicStacks.IsLocallyOfFiniteType B S hS (h ≫ f))
    (u : Space.points B S hS U)
    (hu : pointsMap B S hS (fibredCategory B S hS U).val (fibredCategory B S hS U).property
      𝒯.val.property h.hom.hom (stackPointOfSpacePoint B S hS U u) = t)
    (d : ℕ) (hd : relativeDimensionAt.{u, w} B S hS U hU 𝒯 h hh u = (d : WithBot ℕ∞))
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (q : points B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
      (fieldFibreStackSquare B S hS f p).pt.val.property)
    (hp : pointClass B S hS 𝒳.val.val 𝒳.val.property p =
      pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property f.hom.hom t)
    (hq : pointsMap B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
      (fieldFibreStackSquare B S hS f p).pt.val.property 𝒯.val.property
      (fieldFibreStackSquare B S hS f p).snd.hom.hom q = t) :
    fieldFibreStackDimensionAt.{u, w} B S hS f hf p q =
      dimensionSubNat (relativeDimensionAt.{u, w} B S hS U hU 𝒳 (h ≫ f) hhf u) d := by
  classical
  refine dimensionAtPoint_eq_dimensionSubNat_of_isTwoFibreProduct_fieldFibre.{u, w} B S hS f
    hU h hsm hh hhf u p
    (R := (Bicategory.TwoCommSq.underlying (F := Subtype.val)
      (fieldFibreStackSquare B S hS f p)).swap)
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        (fieldValuedPointMorphism B S hS 𝒳.val p) f.hom))
    (fieldFibreStackSquare B S hS f p).pt.property
    (isLocallyNoetherianStack_fieldFibreStackSquare.{u, w} B S hS f hf p) q
    (hq.trans hu.symm) ?_ d hd
  rw [hp, ← hu, pointsMap_comp B S hS (fibredCategory B S hS U).val
    (fibredCategory B S hS U).property 𝒯.val.property 𝒳.val.property h.hom.hom f.hom.hom
    (stackPointOfSpacePoint B S hS U u)]
  rfl

/-- **The chart formula for the relative dimension of Stacks 0DRL.** For a locally-of-finite-type
1-morphism `f : 𝒯 ⟶ 𝒳` of locally Noetherian algebraic stacks, a point `t ∈ |𝒯|`, and a smooth,
locally-of-finite-type 1-morphism `h : U ⟶ 𝒯` from an algebraic space with a point `u ∈ |U|`
above `t`, the relative dimension of Stacks 0DRL at `t` is `dim_u(U_x) - d`, where `d` is the
relative dimension of Stacks 0DRG of `h` at `u`.

The relative dimension of Stacks 0DRL is the infimum of the admissible values, and
`AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_of_isTwoFibreProduct_fieldFibre`
shows every one of them to be the right-hand side; the set of them is nonempty by
`AlgebraicGeometry.Stack.exists_admissible_fieldFibreStackDimensionAt`. -/
theorem relativeStackDimensionAt_eq_dimensionSubNat_of_isSmooth
    (f : 𝒯 ⟶ 𝒳) (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t : points B S hS 𝒯.val.val 𝒯.val.property)
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (h : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒯)
    (hsm : AlgebraicStacks.IsSmooth B S hS h)
    (hh : AlgebraicStacks.IsLocallyOfFiniteType B S hS h)
    (hhf : AlgebraicStacks.IsLocallyOfFiniteType B S hS (h ≫ f))
    (u : Space.points B S hS U)
    (hu : pointsMap B S hS (fibredCategory B S hS U).val (fibredCategory B S hS U).property
      𝒯.val.property h.hom.hom (stackPointOfSpacePoint B S hS U u) = t)
    (d : ℕ) (hd : relativeDimensionAt.{u, w} B S hS U hU 𝒯 h hh u = (d : WithBot ℕ∞)) :
    relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t =
      dimensionSubNat (relativeDimensionAt.{u, w} B S hS U hU 𝒳 (h ≫ f) hhf u) d :=
  relativeStackDimension_eq_of_forall_fieldFibreStackDimensionAt_eq B S hS f hf t
    fun p q hp hq => fieldFibreStackDimensionAt_eq_dimensionSubNat_of_isSmooth B S hS f hf t hU
      h hsm hh hhf u hu d hd p q hp hq

/-- **The chart formula for the relative dimension of Stacks 0DRL.** For a locally-of-finite-type
1-morphism `f : 𝒯 ⟶ 𝒳` of algebraic stacks, a point `t ∈ |𝒯|`, and a smooth,
locally-of-finite-type 1-morphism `h : U ⟶ 𝒯` from an algebraic space with a point `u ∈ |U|`
above `t`, the relative dimension of Stacks 0DRL at `t` is `dim_u(U_x) - d`, where `d` is the
relative dimension of Stacks 0DRG of `h` at `u`.

The relative dimension of Stacks 0DRL is the infimum of the admissible values, and
`AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_of_isTwoFibreProduct_fieldFibre`
shows every one of them to be the right-hand side; the set of them is nonempty by
`AlgebraicGeometry.Stack.exists_admissible_fieldFibreStackDimensionAt`. -/
theorem relativeStackDimension_eq_dimensionSubNat_of_isSmooth
    (f : 𝒯 ⟶ 𝒳) (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (t : points B S hS 𝒯.val.val 𝒯.val.property)
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (h : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒯)
    (hsm : AlgebraicStacks.IsSmooth B S hS h)
    (hh : AlgebraicStacks.IsLocallyOfFiniteType B S hS h)
    (hhf : AlgebraicStacks.IsLocallyOfFiniteType B S hS (h ≫ f))
    (u : Space.points B S hS U)
    (hu : pointsMap B S hS (fibredCategory B S hS U).val (fibredCategory B S hS U).property
      𝒯.val.property h.hom.hom (stackPointOfSpacePoint B S hS U u) = t)
    (d : ℕ) (hd : relativeDimensionAt.{u, w} B S hS U hU 𝒯 h hh u = (d : WithBot ℕ∞)) :
    relativeStackDimension.{u, w} B S hS f hf t =
      dimensionSubNat (relativeDimensionAt.{u, w} B S hS U hU 𝒳 (h ≫ f) hhf u) d :=
  relativeStackDimension_eq_of_forall_fieldFibreStackDimensionAt_eq B S hS f hf t
    fun p q hp hq => fieldFibreStackDimensionAt_eq_dimensionSubNat_of_isSmooth B S hS f hf t hU
      h hsm hh hhf u hu d hd p q hp hq

/-- A locally-of-finite-type 1-morphism `f : 𝒯 ⟶ 𝒳` has a smooth chart `h : U ⟶ 𝒯` from an
algebraic space above any point `t`, with `h` and `h ≫ f` locally of finite type and `h` of natural
number relative dimension `d` at a point `u` above `t`. -/
private theorem exists_chart_with_relativeDimension (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    ∃ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
      (h : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒯) (_ : AlgebraicStacks.IsSmooth B S hS h)
      (hh : AlgebraicStacks.IsLocallyOfFiniteType B S hS h)
      (_ : AlgebraicStacks.IsLocallyOfFiniteType B S hS (h ≫ f))
      (u : Space.points B S hS U),
      pointsMap B S hS (fibredCategory B S hS U).val (fibredCategory B S hS U).property
        𝒯.val.property h.hom.hom (stackPointOfSpacePoint B S hS U u) = t ∧
      ∃ d : ℕ, relativeDimensionAt.{u, w} B S hS U hU 𝒯 h hh u = (d : WithBot ℕ∞) := by
  obtain ⟨U, hU, h, hsm, u, hu⟩ :=
    exists_isSmooth_algebraicSpaceStack_hom_pointsMap_eq.{u, w} B S hS 𝒯 t
  have hh := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS h hsm
  exact ⟨U, hU, h, hsm, hh, AlgebraicStacks.isLocallyOfFiniteType_comp B S hS h f hh hf, u, hu,
    exists_relativeDimensionAt_eq_natCast.{u, w} B S hS U hU 𝒯 h hh u⟩

/-- **Stacks 0DRM.** The relative dimension `dim_t(𝒯_x)` of Stacks 0DRL is well defined: for a
locally-of-finite-type 1-morphism `f : 𝒯 ⟶ 𝒳` of locally Noetherian algebraic stacks and a
point `t ∈ |𝒯|`, it is the value of the formula of Stacks 0DRL at *every* admissible pair of
choices — a field-valued point `p` of `𝒳` representing the image of `t` and a point of
`𝒯 ×_𝒳 Spec κ(p)` above `t`. So the value depends on neither choice.

Both sides are computed on one smooth chart of `𝒯` above `t` by
`AlgebraicGeometry.Stack.relativeStackDimensionAt_eq_dimensionSubNat_of_isSmooth` and
`AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_of_isTwoFibreProduct_fieldFibre`,
and the chart exists by
`AlgebraicGeometry.Stack.exists_isSmooth_algebraicSpaceStack_hom_pointsMap_eq`. -/
@[stacks 0DRM]
theorem relativeStackDimensionAt_eq_fieldFibreStackDimensionAt
    (f : 𝒯 ⟶ 𝒳) (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t : points B S hS 𝒯.val.val 𝒯.val.property)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (q : points B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
      (fieldFibreStackSquare B S hS f p).pt.val.property)
    (hp : pointClass B S hS 𝒳.val.val 𝒳.val.property p =
      pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property f.hom.hom t)
    (hq : pointsMap B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
      (fieldFibreStackSquare B S hS f p).pt.val.property 𝒯.val.property
      (fieldFibreStackSquare B S hS f p).snd.hom.hom q = t) :
    relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t =
      fieldFibreStackDimensionAt.{u, w} B S hS f hf p q := by
  classical
  obtain ⟨U, hU, h, hsm, hh, hhf, u, hu, d, hd⟩ := exists_chart_with_relativeDimension B S hS f hf t
  rw [relativeStackDimensionAt_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS f hf h𝒯 h𝒳 t hU h
    hsm hh hhf u hu d hd]
  exact (fieldFibreStackDimensionAt_eq_dimensionSubNat_of_isSmooth B S hS f hf t hU h hsm
    hh hhf u hu d hd p q hp hq).symm

/-- **Stacks 0DRM.** The relative dimension `dim_t(𝒯_x)` of Stacks 0DRL is well defined: for a
locally-of-finite-type 1-morphism `f : 𝒯 ⟶ 𝒳` of algebraic stacks and a
point `t ∈ |𝒯|`, it is the value of the formula of Stacks 0DRL at *every* admissible pair of
choices — a field-valued point `p` of `𝒳` representing the image of `t` and a point of
`𝒯 ×_𝒳 Spec κ(p)` above `t`. So the value depends on neither choice.

Both sides are computed on one smooth chart of `𝒯` above `t` by
`AlgebraicGeometry.Stack.relativeStackDimension_eq_dimensionSubNat_of_isSmooth` and
`AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_of_isTwoFibreProduct_fieldFibre`,
and the chart exists by
`AlgebraicGeometry.Stack.exists_isSmooth_algebraicSpaceStack_hom_pointsMap_eq`. -/
theorem relativeStackDimension_eq_fieldFibreStackDimensionAt
    (f : 𝒯 ⟶ 𝒳) (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (t : points B S hS 𝒯.val.val 𝒯.val.property)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (q : points B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
      (fieldFibreStackSquare B S hS f p).pt.val.property)
    (hp : pointClass B S hS 𝒳.val.val 𝒳.val.property p =
      pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property f.hom.hom t)
    (hq : pointsMap B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
      (fieldFibreStackSquare B S hS f p).pt.val.property 𝒯.val.property
      (fieldFibreStackSquare B S hS f p).snd.hom.hom q = t) :
    relativeStackDimension.{u, w} B S hS f hf t =
      fieldFibreStackDimensionAt.{u, w} B S hS f hf p q := by
  classical
  obtain ⟨U, hU, h, hsm, hh, hhf, u, hu, d, hd⟩ := exists_chart_with_relativeDimension B S hS f hf t
  rw [relativeStackDimension_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS f hf t hU h
    hsm hh hhf u hu d hd]
  exact (fieldFibreStackDimensionAt_eq_dimensionSubNat_of_isSmooth B S hS f hf t hU h hsm
    hh hhf u hu d hd p q hp hq).symm

end ChartFormula

/-! ### Stacks 0DRN -/

section BaseChange

/-- **The chart formula at an admissible pair of choices for the base change.** In a Cartesian
square of algebraic stacks with vertical 1-morphisms `P.fst` and `f`, take a smooth chart
`h : U ⟶ 𝒯` with a point `u ∈ |U|` above the image of `t' ∈ |𝒯'|` in `|𝒯|`. Then the formula of
Stacks 0DRL for `P.fst` takes the value `dim_u(U_x) - d` at every admissible pair of choices at
`t'`, where `d` is the relative dimension of Stacks 0DRG of `h` at `u`: the fibre of `P.fst` over a
field-valued point of `𝒳'`, pasted with the square, is a 2-fibre product of `f` with the image
field-valued point of `𝒳`. -/
private theorem fieldFibreStackDimensionAt_fst_eq_dimensionSubNat_of_isSmooth
    {𝒳' 𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒳' ⟶ 𝒳) (f : 𝒯 ⟶ 𝒳)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hfst : AlgebraicStacks.IsLocallyOfFiniteType B S hS P.fst)
    (t' : points B S hS P.pt.val.val P.pt.val.property)
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (h : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒯)
    (hsm : AlgebraicStacks.IsSmooth B S hS h)
    (hh : AlgebraicStacks.IsLocallyOfFiniteType B S hS h)
    (hhf : AlgebraicStacks.IsLocallyOfFiniteType B S hS (h ≫ f))
    (u : Space.points B S hS U)
    (hu : pointsMap B S hS (fibredCategory B S hS U).val (fibredCategory B S hS U).property
      𝒯.val.property h.hom.hom (stackPointOfSpacePoint B S hS U u) =
        pointsMap B S hS P.pt.val.val P.pt.val.property 𝒯.val.property P.snd.hom.hom t')
    (d : ℕ) (hd : relativeDimensionAt.{u, w} B S hS U hU 𝒯 h hh u = (d : WithBot ℕ∞))
    (p' : FieldValuedPoint B S hS 𝒳'.val.val)
    (q' : points B S hS (fieldFibreStackSquare B S hS P.fst p').pt.val.val
      (fieldFibreStackSquare B S hS P.fst p').pt.val.property)
    (hp' : pointClass B S hS 𝒳'.val.val 𝒳'.val.property p' =
      pointsMap B S hS P.pt.val.val P.pt.val.property 𝒳'.val.property P.fst.hom.hom t')
    (hq' : pointsMap B S hS (fieldFibreStackSquare B S hS P.fst p').pt.val.val
      (fieldFibreStackSquare B S hS P.fst p').pt.val.property P.pt.val.property
      (fieldFibreStackSquare B S hS P.fst p').snd.hom.hom q' = t') :
    fieldFibreStackDimensionAt.{u, w} B S hS P.fst hfst p' q' =
      dimensionSubNat (relativeDimensionAt.{u, w} B S hS U hU 𝒳 (h ≫ f) hhf u) d := by
  classical
  have hPc : Bicategory.IsTwoFibreProduct
      (Bicategory.TwoCommSq.underlying P) :=
    Bicategory.isTwoFibreProduct_underlying
      (twoFibreProductSquareAlgebraicStacks B S hS g f) hP
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        g.hom f.hom)
  refine dimensionAtPoint_eq_dimensionSubNat_of_isTwoFibreProduct_fieldFibre.{u, w} B S hS f
    hU h hsm hh hhf u (fieldValuedPointMap B S hS 𝒳'.val.val g.hom.hom p')
    (R := (((Bicategory.TwoCommSq.underlying P).swap).paste
      (Bicategory.TwoCommSq.underlying (F := Subtype.val)
        (fieldFibreStackSquare B S hS P.fst p')).swap).reindexSnd
      (Bicategory.InducedBicategory.isoMk
        (fieldValuedPointMorphism_comp_iso B S hS g.hom.hom p')))
    (Bicategory.isTwoFibreProduct_reindexSnd _
      (Bicategory.isTwoFibreProduct_paste (Bicategory.isTwoFibreProduct_swap hPc)
        (Bicategory.isTwoFibreProduct_swap
          (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
            (fieldValuedPointMorphism B S hS 𝒳'.val p') P.fst.hom))))
    (fieldFibreStackSquare B S hS P.fst p').pt.property
    (isLocallyNoetherianStack_fieldFibreStackSquare.{u, w} B S hS P.fst hfst p') q' ?_ ?_ d hd
  · rw [hu]
    refine Eq.trans ?_ (congrArg (pointsMap B S hS P.pt.val.val P.pt.val.property
      𝒯.val.property P.snd.hom.hom) hq')
    exact (pointsMap_comp B S hS
      (fieldFibreStackSquare B S hS P.fst p').pt.val.val
      (fieldFibreStackSquare B S hS P.fst p').pt.val.property P.pt.val.property
      𝒯.val.property (fieldFibreStackSquare B S hS P.fst p').snd.hom.hom P.snd.hom.hom q').symm
  · rw [← pointsMap_class B S hS 𝒳'.val.val 𝒳'.val.property 𝒳.val.property g.hom.hom p', hp',
      pointsMap_comp B S hS P.pt.val.val P.pt.val.property 𝒳'.val.property 𝒳.val.property
        P.fst.hom.hom g.hom.hom t']
    refine Eq.trans (congrFun (pointsMap_eq_of_basedNatTrans B S hS P.pt.val.val
      P.pt.val.property 𝒳.val.property P.iso.hom.hom.hom) t') ?_
    exact ((pointsMap_comp B S hS P.pt.val.val P.pt.val.property 𝒯.val.property
        𝒳.val.property P.snd.hom.hom f.hom.hom t').symm.trans
      (congrArg (pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property f.hom.hom)
        hu.symm)).trans
      (pointsMap_comp B S hS (fibredCategory B S hS U).val
        (fibredCategory B S hS U).property 𝒯.val.property 𝒳.val.property h.hom.hom f.hom.hom
        (stackPointOfSpacePoint B S hS U u))

/-- **Stacks 0DRN.** Let
```text
  𝒯' ⟶ 𝒯
  |      |
  v      v
  𝒳' ⟶ 𝒳
```
be a Cartesian square of 1-morphisms of locally Noetherian algebraic stacks over `S` in which
the vertical 1-morphisms are locally of finite type. If `t' ∈ |𝒯'|` has images `t`, `x'` and `x`
in `|𝒯|`, `|𝒳'|` and `|𝒳|`, then `dim_{t'}(𝒯'_{x'}) = dim_t(𝒯_x)`.

Both sides are infima of sets of values of the formula of Stacks 0DRL, and the chart formula
`AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_of_isTwoFibreProduct_fieldFibre`
evaluates every member of either set at one and the same smooth chart `U ⟶ 𝒯` of `𝒯` above `t`:
the fibre `𝒯' ×_{𝒳'} Spec κ(p')` over a field-valued point `p'` of `𝒳'` is, pasted with the
Cartesian square and reindexed along
`AlgebraicGeometry.Stack.fieldValuedPointMorphism_comp_iso`, a 2-fibre product of the vertical
1-morphism `𝒯 ⟶ 𝒳` with the 1-morphism of the image field-valued point of `𝒳`. So no
field-valued point of `𝒳` has to be lifted to `𝒳'`, which is what the source's one-line proof
elides. -/
@[stacks 0DRN]
theorem relativeStackDimensionAt_fst_eq_relativeStackDimensionAt
    {𝒳' 𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒳' ⟶ 𝒳) (f : 𝒯 ⟶ 𝒳)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hfst : AlgebraicStacks.IsLocallyOfFiniteType B S hS P.fst)
    (h𝒯' : IsLocallyNoetherianStack.{u, w} B S hS P.pt)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳' : IsLocallyNoetherianStack.{u, w} B S hS 𝒳')
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t' : points B S hS P.pt.val.val P.pt.val.property) :
    relativeStackDimensionAt.{u, w} B S hS P.fst hfst h𝒯' h𝒳' t' =
      relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳
        (pointsMap B S hS P.pt.val.val P.pt.val.property 𝒯.val.property P.snd.hom.hom t') := by
  classical
  obtain ⟨U, hU, h, hsm, hh, hhf, u, hu, d, hd⟩ := exists_chart_with_relativeDimension B S hS f hf
    (pointsMap B S hS P.pt.val.val P.pt.val.property 𝒯.val.property P.snd.hom.hom t')
  rw [relativeStackDimensionAt_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS f hf h𝒯 h𝒳 _ hU h
    hsm hh hhf u hu d hd]
  exact relativeStackDimension_eq_of_forall_fieldFibreStackDimensionAt_eq B S hS P.fst hfst t'
    fun p' q' hp' hq' => fieldFibreStackDimensionAt_fst_eq_dimensionSubNat_of_isSmooth B S hS g f
      P hP hfst t' hU h hsm hh hhf u hu d hd p' q' hp' hq'

/-- **Stacks 0DRN.** Let
```text
  𝒯' ⟶ 𝒯
  |      |
  v      v
  𝒳' ⟶ 𝒳
```
be a Cartesian square of 1-morphisms of algebraic stacks over `S` in which
the vertical 1-morphisms are locally of finite type. If `t' ∈ |𝒯'|` has images `t`, `x'` and `x`
in `|𝒯|`, `|𝒳'|` and `|𝒳|`, then `dim_{t'}(𝒯'_{x'}) = dim_t(𝒯_x)`.

Both sides are infima of sets of values of the formula of Stacks 0DRL, and the chart formula
`AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_of_isTwoFibreProduct_fieldFibre`
evaluates every member of either set at one and the same smooth chart `U ⟶ 𝒯` of `𝒯` above `t`:
the fibre `𝒯' ×_{𝒳'} Spec κ(p')` over a field-valued point `p'` of `𝒳'` is, pasted with the
Cartesian square and reindexed along
`AlgebraicGeometry.Stack.fieldValuedPointMorphism_comp_iso`, a 2-fibre product of the vertical
1-morphism `𝒯 ⟶ 𝒳` with the 1-morphism of the image field-valued point of `𝒳`. So no
field-valued point of `𝒳` has to be lifted to `𝒳'`, which is what the source's one-line proof
elides. -/
theorem relativeStackDimension_fst_eq_relativeStackDimension
    {𝒳' 𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒳' ⟶ 𝒳) (f : 𝒯 ⟶ 𝒳)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hfst : AlgebraicStacks.IsLocallyOfFiniteType B S hS P.fst)
    (t' : points B S hS P.pt.val.val P.pt.val.property) :
    relativeStackDimension.{u, w} B S hS P.fst hfst t' =
      relativeStackDimension.{u, w} B S hS f hf
        (pointsMap B S hS P.pt.val.val P.pt.val.property 𝒯.val.property P.snd.hom.hom t') := by
  classical
  obtain ⟨U, hU, h, hsm, hh, hhf, u, hu, d, hd⟩ := exists_chart_with_relativeDimension B S hS f hf
    (pointsMap B S hS P.pt.val.val P.pt.val.property 𝒯.val.property P.snd.hom.hom t')
  rw [relativeStackDimension_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS f hf _ hU h
    hsm hh hhf u hu d hd]
  exact relativeStackDimension_eq_of_forall_fieldFibreStackDimensionAt_eq B S hS P.fst hfst t'
    fun p' q' hp' hq' => fieldFibreStackDimensionAt_fst_eq_dimensionSubNat_of_isSmooth B S hS g f
      P hP hfst t' hU h hsm hh hhf u hu d hd p' q' hp' hq'

end BaseChange

end AlgebraicGeometry.Stack

end
