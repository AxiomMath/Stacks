module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionSmoothStacks
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Additivity of the relative dimension along a composite with smooth first factor

Let `a : 𝒜 ⟶ ℬ` and `b : ℬ ⟶ 𝒞` be 1-morphisms, locally of finite type, of locally Noetherian
algebraic stacks over `S`, and suppose `a` is smooth. For `p ∈ |𝒜|` with image `q ∈ |ℬ|` the
relative dimension of Stacks 0DRL is additive along the composite:
`dim_p(𝒜_c) = dim_q(ℬ_c) + dim_p(𝒜_q)`,
where `c ∈ |𝒞|` is the common image.

## Main results

* `AlgebraicGeometry.Stack.dimensionAtPoint_eq_relativeStackDimensionAt_of_isTwoFibreProduct`:
  Stacks 0DRM read at an arbitrary *recognised* fibre. The dimension of the apex of any 2-fibre
  product of `f` with the 1-morphism of a field-valued point representing the image of `t` is the
  relative dimension of Stacks 0DRL of `f` at `t`.
* `AlgebraicGeometry.Stack.relativeStackDimensionAt_comp_of_isSmooth`: the additivity formula.

## Implementation notes

The sum is written with the relative dimension of `b` first because that is the order
Stacks 0DRP produces, and `EInt` is not a group: the two summands may be `⊤` or `-∞`, so no
rearrangement of the equation is available.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 06FU](https://stacks.math.columbia.edu/tag/06FU)
* [Stacks Project, Tag 06R6](https://stacks.math.columbia.edu/tag/06R6)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DRM](https://stacks.math.columbia.edu/tag/0DRM)
* [Stacks Project, Tag 0DRN](https://stacks.math.columbia.edu/tag/0DRN)
* [Stacks Project, Tag 0DRP](https://stacks.math.columbia.edu/tag/0DRP)
-/


@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Stacks 0DRM at a recognised fibre -/

/-- **Stacks 0DRM at a recognised fibre.** Let `f : 𝒯 ⟶ 𝒳` be a locally-of-finite-type
1-morphism of locally Noetherian algebraic stacks over `S`, let `t ∈ |𝒯|`, and let `p` be a
field-valued point of `𝒳` representing the image of `t`. If `R` is *any* 2-fibre product of `f`
with the 1-morphism of `p` whose apex is a locally Noetherian algebraic stack, then the dimension
of that apex at any point above `t` is the relative dimension of Stacks 0DRL of `f` at `t`. -/
theorem dimensionAtPoint_eq_relativeStackDimensionAt_of_isTwoFibreProduct
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t : points B S hS 𝒯.val.val 𝒯.val.property)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (hp : pointClass B S hS 𝒳.val.val 𝒳.val.property p =
      pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property f.hom.hom t)
    {R : Bicategory.TwoCommSq f.hom (fieldValuedPointMorphism B S hS 𝒳.val p)}
    (hR : Bicategory.IsTwoFibreProduct R)
    (hRalg : IsAlgebraicStack.{u, w} B S hS R.pt.val)
    (hRN : IsLocallyNoetherianStack.{u, w} B S hS ⟨R.pt, hRalg⟩)
    (y : points B S hS R.pt.val R.pt.property)
    (hy : pointsMap B S hS R.pt.val R.pt.property 𝒯.val.property R.fst.hom y = t) :
    dimensionAtPoint B S hS ⟨R.pt, hRalg⟩ hRN y =
      relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t := by
  classical
  obtain ⟨U, hU, h, hsm, u, hu⟩ :=
    exists_isSmooth_algebraicSpaceStack_hom_pointsMap_eq.{u, w} B S hS 𝒯 t
  have hh := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS h hsm
  have hhf := AlgebraicStacks.isLocallyOfFiniteType_comp B S hS h f hh hf
  obtain ⟨d, hd⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS U hU 𝒯 h hh u
  rw [relativeStackDimensionAt_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS f hf h𝒯 h𝒳 t hU h
    hsm hh hhf u hu d hd]
  refine dimensionAtPoint_eq_dimensionSubNat_of_isTwoFibreProduct_fieldFibre.{u, w} B S hS f
    hU h hsm hh hhf u p hR hRalg hRN y (hy.trans hu.symm) ?_ d hd
  rw [hp, ← hu, pointsMap_comp B S hS (fibredCategory B S hS U).val
    (fibredCategory B S hS U).property 𝒯.val.property 𝒳.val.property h.hom.hom f.hom.hom
    (stackPointOfSpacePoint B S hS U u)]
  rfl

/-! ### Additivity along a composite with smooth first factor -/

section Composition

/-- The fibre `𝒜 ×_ℬ ℬ_κ` of `a` over the fibre of `b` at a field-valued point `κ` of `𝒞`: the
canonical 2-fibre product square of the projection `ℬ_κ ⟶ ℬ` with `a`. Its apex is the fibre of
the composite `a ≫ b` at `κ`, by
`AlgebraicGeometry.Stack.isTwoFibreProduct_pastedFieldFibreStackSquare`. -/
private noncomputable abbrev pastedFieldFibreInner {𝒜 ℬ 𝒞 : AlgebraicStacks.{u, w} B S hS}
    (a : 𝒜 ⟶ ℬ) (b : ℬ ⟶ 𝒞)
    (κ : FieldValuedPoint B S hS 𝒞.val.val) :
    Bicategory.TwoCommSq (fieldFibreStackSquare B S hS b κ).snd a :=
  twoFibreProductSquareAlgebraicStacks B S hS (fieldFibreStackSquare B S hS b κ).snd a

/-- **The fibre of a composite, recognised one base change at a time.** Pasting the square
`AlgebraicGeometry.Stack.pastedFieldFibreInner` onto the fibre of `b` at `κ` gives a 2-fibre
product of the cospan `(Spec κ ⟶ 𝒞, a ≫ b)`, whose apex is `𝒜 ×_ℬ ℬ_κ`. -/
private noncomputable def isTwoFibreProduct_pastedFieldFibreStackSquare
    {𝒜 ℬ 𝒞 : AlgebraicStacks.{u, w} B S hS} (a : 𝒜 ⟶ ℬ) (b : ℬ ⟶ 𝒞)
    (κ : FieldValuedPoint B S hS 𝒞.val.val) :
    Bicategory.IsTwoFibreProduct (Bicategory.TwoCommSq.underlying (F := Subtype.val)
      ((fieldFibreStackSquare B S hS b κ).paste (pastedFieldFibreInner B S hS a b κ))) :=
  Bicategory.isTwoFibreProduct_underlying
    (twoFibreProductSquareAlgebraicStacks B S hS
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒞 κ) (a ≫ b))
    (Bicategory.isTwoFibreProduct_paste
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
        (fieldValuedPointStackMorphism.{u, w} B S hS 𝒞 κ) b)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
        (fieldFibreStackSquare B S hS b κ).snd a))
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒞 κ).hom (a ≫ b).hom)

/-- **Additivity of the relative dimension of Stacks 0DRL along a composite whose first factor is
smooth.** Let `a : 𝒜 ⟶ ℬ` and `b : ℬ ⟶ 𝒞` be 1-morphisms of locally Noetherian algebraic stacks
over `S`, all locally of finite type, with `a` smooth. If `p ∈ |𝒜|` has image `q ∈ |ℬ|`, then
`dim_p(𝒜_c) = dim_q(ℬ_c) + dim_p(𝒜_q)`,
where `c ∈ |𝒞|` is the image of `q`. -/
@[sga "1 II 1.5" "more general"]
theorem relativeStackDimensionAt_comp_of_isSmooth
    {𝒜 ℬ 𝒞 : AlgebraicStacks.{u, w} B S hS} (a : 𝒜 ⟶ ℬ) (b : ℬ ⟶ 𝒞)
    (hasm : AlgebraicStacks.IsSmooth B S hS a)
    (ha : AlgebraicStacks.IsLocallyOfFiniteType B S hS a)
    (hb : AlgebraicStacks.IsLocallyOfFiniteType B S hS b)
    (hab : AlgebraicStacks.IsLocallyOfFiniteType B S hS (a ≫ b))
    (h𝒜 : IsLocallyNoetherianStack.{u, w} B S hS 𝒜)
    (hℬ : IsLocallyNoetherianStack.{u, w} B S hS ℬ)
    (h𝒞 : IsLocallyNoetherianStack.{u, w} B S hS 𝒞)
    (p : points B S hS 𝒜.val.val 𝒜.val.property) :
    relativeStackDimensionAt.{u, w} B S hS (a ≫ b) hab h𝒜 h𝒞 p =
      relativeStackDimensionAt.{u, w} B S hS b hb hℬ h𝒞
          (pointsMap B S hS 𝒜.val.val 𝒜.val.property ℬ.val.property a.hom.hom p) +
        relativeStackDimensionAt.{u, w} B S hS a ha h𝒜 hℬ p := by
  classical
  set q := pointsMap B S hS 𝒜.val.val 𝒜.val.property ℬ.val.property a.hom.hom p with hqdef
  set κ := Quotient.out
    (pointsMap B S hS 𝒜.val.val 𝒜.val.property 𝒞.val.property (a ≫ b).hom.hom p) with hκdef
  have hκab : pointClass B S hS 𝒞.val.val 𝒞.val.property κ =
      pointsMap B S hS 𝒜.val.val 𝒜.val.property 𝒞.val.property (a ≫ b).hom.hom p :=
    Quotient.out_eq _
  have hκb : pointClass B S hS 𝒞.val.val 𝒞.val.property κ =
      pointsMap B S hS ℬ.val.val ℬ.val.property 𝒞.val.property b.hom.hom q := by
    rw [hκab, hqdef,
      pointsMap_comp B S hS 𝒜.val.val 𝒜.val.property ℬ.val.property 𝒞.val.property
        a.hom.hom b.hom.hom p]
    rfl
  have hℬκ := isLocallyNoetherianStack_fieldFibreStackSquare.{u, w} B S hS b hb κ
  obtain ⟨q', hq'⟩ := exists_point_fieldFibreStackSquare.{u, w} B S hS b q κ hκb
  set T := pastedFieldFibreInner B S hS a b κ with hTdef
  have hT := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
    (fieldFibreStackSquare B S hS b κ).snd a
  have hTsm : AlgebraicStacks.IsSmooth B S hS T.fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS a (fieldFibreStackSquare B S hS b κ).snd T hT hasm
  have hTft : AlgebraicStacks.IsLocallyOfFiniteType B S hS T.fst :=
    AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS a
      (fieldFibreStackSquare B S hS b κ).snd T hT ha
  have hTN : IsLocallyNoetherianStack.{u, w} B S hS T.pt :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS T.fst hTft hℬκ
  obtain ⟨t', ht'₁, ht'₂⟩ :=
    exists_point_of_isTwoFibreProduct_algebraicStacks.{u, w} B S hS T hT q' p hq'
  have h0DRP := dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isSmooth.{u, w} B S hS T.fst
    hTsm hTft hTN hℬκ t'
  have hsrc : dimensionAtPoint B S hS T.pt hTN t' =
      relativeStackDimensionAt.{u, w} B S hS (a ≫ b) hab h𝒜 h𝒞 p :=
    dimensionAtPoint_eq_relativeStackDimensionAt_of_isTwoFibreProduct.{u, w} B S hS (a ≫ b) hab
      h𝒜 h𝒞 p κ hκab
      (R := (Bicategory.TwoCommSq.underlying (F := Subtype.val)
        ((fieldFibreStackSquare B S hS b κ).paste T)).swap)
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_pastedFieldFibreStackSquare B S hS a b κ))
      T.pt.property hTN t' ht'₂
  have htgt : dimensionAtPoint B S hS (fieldFibreStackSquare B S hS b κ).pt hℬκ q' =
      relativeStackDimensionAt.{u, w} B S hS b hb hℬ h𝒞 q :=
    (relativeStackDimensionAt_eq_fieldFibreStackDimensionAt.{u, w} B S hS b hb hℬ h𝒞 q κ q'
      hκb hq').symm
  have h0DRN := relativeStackDimensionAt_fst_eq_relativeStackDimensionAt.{u, w} B S hS
    (fieldFibreStackSquare B S hS b κ).snd a T hT ha hTft hTN h𝒜 hℬκ hℬ t'
  rw [← hsrc, h0DRP, ht'₁, htgt, h0DRN, ht'₂]

end Composition

end AlgebraicGeometry.Stack

end
