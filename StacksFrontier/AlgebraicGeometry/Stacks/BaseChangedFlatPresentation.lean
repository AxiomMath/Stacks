module

public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallnessDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.StackInSetoidsRepresentableBySpace

/-!
# Representability of a stack in setoids over a stack with a flat presentation

Let `v : 𝒬 ⟶ 𝒳` be a presentation of a category fibred in groupoids over the big fppf site of `S`
by an algebraic space which is representable by algebraic spaces, surjective, flat and locally of
finite presentation, and let `q : 𝒲 ⟶ 𝒳` be any 1-morphism representable by algebraic spaces.
Base changing `v` along `q` gives a presentation of `𝒲` with all four properties: the apex of the
2-fibre product is representable by an algebraic space by **Stacks 0300**, its projection to `𝒲`
is representable by algebraic spaces by **Stacks 0302**, and the three relative properties are
stable under base change by **Stacks 045C**.

Two consequences follow for `𝒲` alone, both of which the hypotheses on `𝒳` are too weak to give
directly:

* the fibres of `𝒲` are essentially small, by the descent bound of
  `StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallnessDescent`;
* if `𝒲` is a stack in setoids, it is representable by an algebraic space, by the engine
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids_of_flatPresentation`
  (Stacks 04SZ), whose essential-smallness hypothesis the first consequence discharges.

## Main results

* `AlgebraicGeometry.Stack.exists_flatPresentation_baseChange`: the base-changed presentation.
* `AlgebraicGeometry.Stack.essentiallySmall_fiber_of_baseChangedFlatPresentation`: the fibres of
  `𝒲` are essentially small.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids_of_baseChange`:
  **a stack in setoids over a stack with a flat presentation is representable by an algebraic
  space**.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

attribute [local instance] Space.isFlat_isStableUnderBaseChange
  Space.isLocallyOfFinitePresentation_isStableUnderBaseChange

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒬 𝒳 𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **The base change of a flat presentation along a 1-morphism representable by algebraic
spaces.** If `v : 𝒬 ⟶ 𝒳` is representable by algebraic spaces, surjective, flat and locally of
finite presentation with `𝒬` representable by an algebraic space, and `q : 𝒲 ⟶ 𝒳` is
representable by algebraic spaces, then `𝒲` admits a 1-morphism with the same four properties out
of a category representable by an algebraic space. -/
theorem exists_flatPresentation_baseChange (v : 𝒬 ⟶ 𝒳) (q : 𝒲 ⟶ 𝒳)
    (h𝒬 : IsRepresentableByAlgebraicSpace B S hS 𝒬)
    (hv : IsRepresentableByAlgebraicSpaces B S hS v.hom)
    (hvsurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) v hv)
    (hvflat : @HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => Space.IsFlat B S hS k.hom)
      (Space.isFlat_isStableUnderBaseChange B S hS)
      ((Space.isFlat_isLocalAtTarget_fpqc B S hS).of_le
        (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS))
      𝒬 𝒳 v hv)
    (hvlfp : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS k.hom) v hv)
    (hq : IsRepresentableByAlgebraicSpaces B S hS q.hom) :
    ∃ (𝒩 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) (w : 𝒩 ⟶ 𝒲)
      (hw : IsRepresentableByAlgebraicSpaces B S hS w.hom),
      IsRepresentableByAlgebraicSpace B S hS 𝒩 ∧
        HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
          (Space.surjectiveMorphismProperty B S hS) w hw ∧
        @HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
          (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => Space.IsFlat B S hS k.hom)
          (Space.isFlat_isStableUnderBaseChange B S hS)
          ((Space.isFlat_isLocalAtTarget_fpqc B S hS).of_le
            (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS))
          𝒩 𝒲 w hw ∧
        HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
          (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
            Space.IsLocallyOfFinitePresentation B S hS k.hom) w hw := by
  classical
  have hflatloc : MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => Space.IsFlat B S hS k.hom)
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    (Space.isFlat_isLocalAtTarget_fpqc B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  set T := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} v q
  have hT : Bicategory.IsTwoFibreProduct T :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} v q
  have hTswap : Bicategory.IsTwoFibreProduct T.swap := Bicategory.isTwoFibreProduct_swap hT
  have hTpt : IsRepresentableByAlgebraicSpace B S hS T.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS _ _ _ q v T hT
      hq h𝒬
  have hw : IsRepresentableByAlgebraicSpaces B S hS T.swap.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ v q T.swap hTswap hv
  exact ⟨T.pt, T.swap.fst, hw, hTpt,
    hasRelativeProperty_baseChange.{u, u, u + 1, u + 1} B S hS _ _ _ _ v q T.swap hTswap hv
      hvsurj,
    hasRelativeProperty_baseChange.{u, u, u + 1, u + 1} B S hS _ _ _ _ v q T.swap hTswap hv
      hvflat,
    hasRelativeProperty_baseChange.{u, u, u + 1, u + 1} B S hS _ _ _ _ v q T.swap hTswap hv
      hvlfp⟩

/-- **The fibres of `𝒲` are essentially small** when `𝒲` is a stack receiving a 1-morphism
representable by algebraic spaces to a category carrying a flat presentation by an algebraic
space: the base-changed presentation of
`AlgebraicGeometry.Stack.exists_flatPresentation_baseChange` is locally essentially surjective
and its source has essentially small fibres. -/
theorem essentiallySmall_fiber_of_baseChangedFlatPresentation (v : 𝒬 ⟶ 𝒳) (q : 𝒲 ⟶ 𝒳)
    (h𝒲 : Functor.IsStack 𝒲.val.p (BigFppfOver.topology B S hS))
    (h𝒬 : IsRepresentableByAlgebraicSpace B S hS 𝒬)
    (hv : IsRepresentableByAlgebraicSpaces B S hS v.hom)
    (hvsurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) v hv)
    (hvflat : @HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => Space.IsFlat B S hS k.hom)
      (Space.isFlat_isStableUnderBaseChange B S hS)
      ((Space.isFlat_isLocalAtTarget_fpqc B S hS).of_le
        (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS))
      𝒬 𝒳 v hv)
    (hvlfp : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS k.hom) v hv)
    (hq : IsRepresentableByAlgebraicSpaces B S hS q.hom) (V : BigFppfOver B S hS) :
    EssentiallySmall.{u} (𝒲.val.p.Fiber V) := by
  obtain ⟨𝒩, w, hw, h𝒩, hwsurj, hwflat, hwlfp⟩ :=
    exists_flatPresentation_baseChange B S hS v q h𝒬 hv hvsurj hvflat hvlfp hq
  exact essentiallySmall_fiber_of_flatPresentation w h𝒲
    (fun W => essentiallySmall_fiber_of_isRepresentableByAlgebraicSpace B S hS 𝒩 h𝒩 W) hw
    (fun W y hy G hG h =>
      ⟨hwsurj W y hy G hG h, hwflat W y hy G hG h, hwlfp W y hy G hG h⟩) V

/-- **A stack in setoids over a category with a flat presentation is representable by an
algebraic space.**

Let `v : 𝒬 ⟶ 𝒳` be representable by algebraic spaces, surjective, flat and locally of finite
presentation with `𝒬` representable by an algebraic space, and let `q : 𝒲 ⟶ 𝒳` be representable
by algebraic spaces with `𝒲` a stack in setoids. Then `𝒲` is representable by an algebraic space:
the base change of `v` along `q` is a flat presentation of `𝒲`, and it makes the fibres of `𝒲`
essentially small, which is the remaining hypothesis of the engine of Stacks 04SZ. -/
theorem isRepresentableByAlgebraicSpace_of_isStackInSetoids_of_baseChange (v : 𝒬 ⟶ 𝒳)
    (q : 𝒲 ⟶ 𝒳) (h𝒲 : 𝒲.val.p.IsStackInSetoids (BigFppfOver.topology B S hS))
    (h𝒬 : IsRepresentableByAlgebraicSpace B S hS 𝒬)
    (hv : IsRepresentableByAlgebraicSpaces B S hS v.hom)
    (hvsurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) v hv)
    (hvflat : @HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => Space.IsFlat B S hS k.hom)
      (Space.isFlat_isStableUnderBaseChange B S hS)
      ((Space.isFlat_isLocalAtTarget_fpqc B S hS).of_le
        (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS))
      𝒬 𝒳 v hv)
    (hvlfp : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS k.hom) v hv)
    (hq : IsRepresentableByAlgebraicSpaces B S hS q.hom) :
    IsRepresentableByAlgebraicSpace B S hS 𝒲 := by
  obtain ⟨𝒩, w, hw, h𝒩, hwsurj, hwflat, hwlfp⟩ :=
    exists_flatPresentation_baseChange B S hS v q h𝒬 hv hvsurj hvflat hvlfp hq
  exact isRepresentableByAlgebraicSpace_of_isStackInSetoids_of_flatPresentation B S hS w h𝒲
    (fun V => essentiallySmall_fiber_of_baseChangedFlatPresentation B S hS v q h𝒲.isStack h𝒬
      hv hvsurj hvflat hvlfp hq V)
    h𝒩 hw hwsurj hwflat hwlfp

end AlgebraicGeometry.Stack

end
