module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningOfFormallyUnramified
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Thickenings.KernelGlobalSections

/-!
# The universal first order thickening is formally unramified over the base

Let `S` be a scheme and let `Z ⟶ X` be a formally unramified morphism of algebraic spaces over
`S`.  The ambient algebraic space `Z'` of the universal first order thickening `Z ⊂ Z'` of `Z`
over `X` is formally unramified over `X`.

## Main definitions

* `AlgebraicGeometry.Space.thickOrder`: being an `n`th-order thickening, as a property of
  morphisms of schemes.

## Main results

* `AlgebraicGeometry.Space.isNthOrderThickening_range_yoneda_map`: the range of a morphism of
  the big fppf site which is an `n`th-order thickening of schemes is an `n`th-order thickening
  of the algebraic space represented by its target.
* `AlgebraicGeometry.Space.isFirstOrderThickening_range_yoneda_map`: the case of a square-zero
  closed immersion of the site and first-order thickenings.
* `AlgebraicGeometry.Space.formallyUnramified_of_isUniversalFirstOrderThickening`: the
  structure morphism of a universal first order thickening is formally unramified.
* `AlgebraicGeometry.Space.UniversalFirstOrderThickening.formallyUnramified_toBase`: the same
  for the universal first order thickening of a formally unramified morphism.

## References

* [Stacks Project, Tag 0609](https://stacks.math.columbia.edu/tag/0609)
* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 09ZU](https://stacks.math.columbia.edu/tag/09ZU)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A square-zero closed immersion of the site as a thickening of algebraic spaces -/

/-- Being an `n`th-order thickening, read as a property of morphisms of schemes. -/
public def thickOrder (n : ℕ) : MorphismProperty Scheme.{u} :=
  fun _ _ f ↦ Stacks.Thickenings.IsNthOrderThickening n f

/-- Being an `n`th-order thickening of schemes is stable under base change. -/
public instance thickOrder_isStableUnderBaseChange (n : ℕ) :
    (thickOrder.{u} n).IsStableUnderBaseChange :=
  ⟨fun sq hf ↦ Stacks.Thickenings.isNthOrderThickening_of_isPullback sq.flip hf⟩

/-- A morphism of the big fppf category over `S` whose underlying morphism of schemes is a
closed immersion has monomorphic Yoneda image. -/
private theorem mono_yoneda_map_of_isClosedImmersion {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    (hi : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i)) :
    Mono (yoneda.map i) := by
  have hpClosed : IsClosedImmersion B S hS (yoneda.map i) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.IsClosedImmersion.{u}) i).2 hi
  have hPmono : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) ≤
      MorphismProperty.monomorphisms (BigFppfOver B S hS) := fun _ _ g hg =>
    have : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map g) := hg
    (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  exact MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
    (MorphismProperty.relative_monotone hPmono _ hpClosed)

/-- If `i : T ⟶ T'` is a morphism of the big fppf category over `S` whose underlying morphism of
schemes is a closed immersion with kernel ideal sheaf of vanishing `(n+1)`st power, then the
range of `yoneda.map i` is an `n`th-order thickening of the algebraic space represented by
`T'`. -/
theorem isNthOrderThickening_range_yoneda_map (n : ℕ) {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    (hi : Stacks.Thickenings.IsNthOrderThickening n ((BigFppfOver.toScheme B S hS).map i)) :
    IsNthOrderThickening B S hS n ((schemeSpaceFunctor B S hS).obj T')
      (Subfunctor.range (yoneda.map i)) := by
  classical
  have hG : IsClosedSubspace B S hS (Subfunctor.range (yoneda.map i)) :=
    isClosedSubspace_range_yoneda_map B S hS i hi.1
  have hmono : Mono (yoneda.map i) := mono_yoneda_map_of_isClosedImmersion B S hS i hi.1
  have hQ : (MorphismProperty.inverseImage (thickOrder.{u} n)
      (BigFppfOver.toScheme B S hS)).presheaf (Subfunctor.range (yoneda.map i)).ι := by
    have hstable : (MorphismProperty.inverseImage (thickOrder.{u} n)
        (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
      ⟨fun sq hq => MorphismProperty.of_isPullback (P := thickOrder.{u} n)
        (sq.map (BigFppfOver.toScheme B S hS)) hq⟩
    have hprop : (MorphismProperty.inverseImage (thickOrder.{u} n)
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map i) :=
      MorphismProperty.relative_map (show MorphismProperty.inverseImage (thickOrder.{u} n)
        (BigFppfOver.toScheme B S hS) i from hi)
    have heq : (asIso (Subfunctor.toRange (yoneda.map i))).inv ≫ yoneda.map i =
        (Subfunctor.range (yoneda.map i)).ι :=
      (asIso _).inv_comp_eq.2 (Subfunctor.toRange_ι _).symm
    exact heq ▸ MorphismProperty.RespectsIso.precomp _
      (asIso (Subfunctor.toRange (yoneda.map i))).inv (yoneda.map i) hprop
  have hsurj : Function.Surjective (pointsMap B S hS
      (Subfunctor.range (yoneda.map i)).toFunctor (Subfunctor.range (yoneda.map i)).ι) := by
    have hs0 : Function.Surjective (pointsMap B S hS (yoneda.obj T) (yoneda.map i)) :=
      (surjective_pointsMap_yoneda_iff B S hS i).2 hi.isThickening.2
    rw [← Subfunctor.toRange_ι (yoneda.map i), pointsMap_comp] at hs0
    exact hs0.of_comp
  refine ⟨⟨hG, hsurj⟩, fun W ↦ ?_⟩
  have hn : Stacks.Thickenings.IsNthOrderThickening n
      ((BigFppfOver.toScheme B S hS).map (hG.2.rep.snd
        (W.1.hom : yoneda.obj W.1.left ⟶ yoneda.obj T'))) :=
    hQ.property_snd _
  have hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map (hG.2.rep.snd
      (W.1.hom : yoneda.obj W.1.left ⟶ yoneda.obj T'))) := by
    have hci := hn.1
    infer_instance
  rw [definingIdealAt_eq_ker B S hS ((schemeSpaceFunctor B S hS).obj T')
    ⟨Subfunctor.range (yoneda.map i), hG⟩ W, Scheme.Γ_map_op]
  exact Scheme.ker_appTop_pow_eq_bot _ hqc hn.2

/-- If `i : T ⟶ T'` is a square-zero closed immersion of the site, then the range of
`yoneda.map i` is a first-order thickening of the algebraic space represented by `T'`. -/
theorem isFirstOrderThickening_range_yoneda_map {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) :
    IsFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).obj T')
      (Subfunctor.range (yoneda.map i)) :=
  isNthOrderThickening_range_yoneda_map B S hS 1 i ⟨hi.1, by simpa using hi.2⟩

/-! ### Formal unramifiedness from uniqueness of dotted arrows -/

/-- Formal unramifiedness, from uniqueness of dotted arrows read as transformations out of
representable presheaves, against square-zero closed immersions of the site that need not be
affine. -/
private theorem formallyUnramified_of_yoneda_hom_ext
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (h : ∀ {P Q : BigFppfOver B S hS} (i : P ⟶ Q), IsSquareZeroClosedImmersion B S hS i →
      ∀ z₁ z₂ : yoneda.obj Q ⟶ F, yoneda.map i ≫ z₁ = yoneda.map i ≫ z₂ →
        z₁ ≫ a = z₂ ≫ a → z₁ = z₂) :
    FormallyUnramified a := by
  intro P Q _ _ i hi x y _ z₁ z₂ hz₁ hz₂
  refine yonedaEquiv.symm.injective (h i hi _ _ ?_ ?_)
  · rw [yonedaEquiv_symm_naturality_left, yonedaEquiv_symm_naturality_left, hz₁.1, hz₂.1]
  · rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, hz₁.2, hz₂.2]

/-- For a first-order thickening `I ⊂ T'` of a representable algebraic space and a morphism
`z : T' ⟶ Z'` with `z⁻¹(Z) ⊂ T'` a first-order thickening, the inverse image of `I` in
`z⁻¹(Z)` is a first-order thickening of `z⁻¹(Z)`. -/
private theorem isFirstOrderThickening_preimage_preimage
    {Z' : AlgebraicSpaces B S hS} {Z : Subfunctor Z'.1} {Q : BigFppfOver B S hS}
    (I : Subfunctor (yoneda.obj Q)) (z : yoneda.obj Q ⟶ Z'.1)
    (hI : IsFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).obj Q) I)
    (hA : IsFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).obj Q) (Z.preimage z)) :
    IsFirstOrderThickening B S hS
      (⟨(Z.preimage z).toFunctor, (IsNthOrderThickening.isThickening B S hS hA).1.1⟩ :
        AlgebraicSpaces B S hS) (I.preimage (Z.preimage z).ι) :=
  isFirstOrderThickening_preimage B S hS I
    (ObjectProperty.homMk (Z.preimage z).ι :
      (⟨(Z.preimage z).toFunctor, (IsNthOrderThickening.isThickening B S hS hA).1.1⟩ :
        AlgebraicSpaces B S hS) ⟶ (schemeSpaceFunctor B S hS).obj Q) hI

/-! ### Stacks 0609 -/

/-- Let `Z ⊂ Z'` be a universal first order thickening of `Z` over an algebraic space `X`, with
structure morphism `p : Z' ⟶ X`.  Then `p` is formally unramified. -/
@[stacks 0609]
theorem formallyUnramified_of_isUniversalFirstOrderThickening
    {X Z' : AlgebraicSpaces B S hS} (Z : Subfunctor Z'.1) (p : Z' ⟶ X)
    (hZ : IsUniversalFirstOrderThickening B S hS Z p) :
    FormallyUnramified p.hom := by
  refine formallyUnramified_of_yoneda_hom_ext B S hS p.hom fun {P Q} i hi z₁ z₂ hres hover => ?_
  have hI : IsFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).obj Q)
      (Subfunctor.range (yoneda.map i)) :=
    isFirstOrderThickening_range_yoneda_map B S hS i hi
  have hA : IsFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).obj Q) (Z.preimage z₁) :=
    isFirstOrderThickening_preimage B S hS Z
      (ObjectProperty.homMk z₁ : (schemeSpaceFunctor B S hS).obj Q ⟶ Z') hZ.firstOrder
  have hK := isFirstOrderThickening_preimage_preimage B S hS
    (Subfunctor.range (yoneda.map i)) z₁ hI hA
  have hab : (Subfunctor.range (yoneda.map i)).ι ≫ z₁ =
      (Subfunctor.range (yoneda.map i)).ι ≫ z₂ :=
    (cancel_epi (Subfunctor.toRange (yoneda.map i))).1 (by
      rwa [← Category.assoc, ← Category.assoc, Subfunctor.toRange_ι])
  exact hZ.eq_of_isFirstOrderThickening_preimage (T' := (schemeSpaceFunctor B S hS).obj Q)
    (Subfunctor.range (yoneda.map i)) z₁ z₂ hab hover hA hK

/-- The ambient algebraic space `Z'` of a universal first order thickening of a formally
unramified morphism `h : Z ⟶ X` of algebraic spaces over `S` is formally unramified over `X`. -/
@[stacks 0609 "the universal first order thickening of a formally unramified morphism"]
theorem UniversalFirstOrderThickening.formallyUnramified_toBase
    {Z X : AlgebraicSpaces B S hS} {h : Z ⟶ X} (t : UniversalFirstOrderThickening B S hS h) :
    FormallyUnramified t.toBase.hom :=
  AlgebraicGeometry.Space.formallyUnramified_of_isUniversalFirstOrderThickening B S hS
    t.sub t.toBase t.isUniversal

end AlgebraicGeometry.Space

end
