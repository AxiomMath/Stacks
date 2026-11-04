module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcIntegral
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae

/-!
# Integral and finite morphisms are étale local on the base

A morphism of algebraic spaces over a scheme `S` is integral, respectively finite, as soon as
its base change along a single surjective étale morphism from a scheme is. This is condition
(3) of Stacks 03ZQ, the one condition of that tag which rests on effective descent rather than
on Zariski locality.

## Main results

* `AlgebraicGeometry.Space.isIntegralHom_of_surjectiveEtaleChart`: **Stacks 03ZQ**, condition
  (3) implies condition (2) for integral morphisms.
* `AlgebraicGeometry.Space.isFinite_of_surjectiveEtaleChart`: the same for finite morphisms.
* `AlgebraicGeometry.Space.isIntegralHom_iff_etaleLocal` and
  `AlgebraicGeometry.Space.isFinite_iff_etaleLocal`: **Stacks 03ZQ**, the equivalence of
  conditions (2) and (3) for the two properties, in the form of
  `AlgebraicGeometry.Space.holdsOnAffineBaseChange_iff_exists_etaleChart` instantiated at
  `AlgebraicGeometry.IsIntegralHom` and at `AlgebraicGeometry.IsFinite`.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isFinite`: effective descent
  for finite morphisms along a surjective étale morphism of the big fppf site of `S`, which is
  Stacks 03I2 at the class of finite morphisms of schemes.
* `AlgebraicGeometry.Space.isFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact`:
  **Stacks 02LA**, the descent step for finite morphisms; its fppf form is
  `AlgebraicGeometry.isFinite_descendsAlong_fppf`.

## Implementation notes

Both are the instance at `AlgebraicGeometry.IsIntegralHom`, respectively
`AlgebraicGeometry.IsFinite`, of
`AlgebraicGeometry.Space.presheaf_of_surjectiveEtaleChart_of_descent`, the form of Stacks 03I2
which carries the representability by an auxiliary property. The auxiliary property is
`AlgebraicGeometry.IsAffineHom`, for which effective descent along a surjective étale chart is
available outright as
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isAffineHom`; the tested
property then only has to descend along the surjective flat morphisms of finite presentation,
which is Stacks 02L9 and Stacks 02LA in the form
`AlgebraicGeometry.isIntegralHom_descendsAlong_fppf` and
`AlgebraicGeometry.isFinite_descendsAlong_fppf`.

The passage between the predicates of Stacks 03ZP and the relative property of
`AlgebraicGeometry.MorphismProperty.presheaf` is the equivalence of conditions (1) and (2) of
Stacks 03ZQ, which is
`AlgebraicGeometry.Space.isIntegralHom_iff_representable` and
`AlgebraicGeometry.Space.isFinite_iff_representable`; the representability half of condition
(1) is recovered from the descended relative property itself.

## References

* [Stacks Project, Tag 02L9](https://stacks.math.columbia.edu/tag/02L9)
* [Stacks Project, Tag 02LA](https://stacks.math.columbia.edu/tag/02LA)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- If a property of schemes `P` of affine morphisms descends along fppf morphisms, and the base
change of `f` along a surjective étale chart is representable with `P`, so is `f`. -/
private theorem presheaf_and_rep_of_surjectiveEtaleChart
    {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hle : P ≤ @_root_.AlgebraicGeometry.IsAffineHom.{u})
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {U : BigFppfOver B S hS} {q : yoneda.obj U ⟶ Y} (hqs : IsSurjective B S hS q)
    (hqe : IsEtale B S hS q)
    (hVQ : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f q)) :
    yoneda.relativelyRepresentable f ∧
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f := by
  have _hra : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h := presheaf_of_surjectiveEtaleChart_of_descent
    (isEffectiveDescentAlongSurjectiveEtale_isAffineHom B S hS) hX.isSheaf hY.isSheaf
    ((presheafSurjective_iff_isSurjective_yoneda B S hS Y hY U q).mpr hqs)
    (presheaf_etale_of_isEtale B S hS hqe)
    (MorphismProperty.relative_monotone
      (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS) hle) _ hVQ) hVQ
  exact ⟨h.rep, h⟩

/-- **Stacks 03ZQ for integral morphisms, condition (3) implies condition (2).** A morphism of
algebraic spaces over `S` whose base change along some surjective étale morphism from a scheme
is integral is itself integral. -/
@[stacks 03ZQ "integral: condition (3)"]
theorem isIntegralHom_of_surjectiveEtaleChart (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) {U : BigFppfOver B S hS}
    {q : yoneda.obj U ⟶ Y} (hqs : IsSurjective B S hS q) (hqe : IsEtale B S hS q)
    (hbase : IsIntegralHom B S hS (pullback.snd f q)) :
    IsIntegralHom B S hS f := by
  have _hri := Stacks.Descent.isIntegralHom_respectsIso.{u}
  have _hd := isIntegralHom_descendsAlong_fppf.{u}
  exact (isIntegralHom_iff_representable B S hS f hX hY).mpr
    (presheaf_and_rep_of_surjectiveEtaleChart B S hS isIntegralHom_le_isAffineHom.{u}
      hX hY f hqs hqe
      ((isIntegralHom_iff_representable B S hS (pullback.snd f q)
        (isAlgebraicSpace_pullback B S hS f q hX (isAlgebraicSpace_yoneda B S hS U) hY)
        (isAlgebraicSpace_yoneda B S hS U)).mp hbase).2)

/-- **Stacks 03ZQ for finite morphisms, condition (3) implies condition (2).** A morphism of
algebraic spaces over `S` whose base change along some surjective étale morphism from a scheme
is finite is itself finite. -/
@[stacks 03ZQ "finite: condition (3)"]
theorem isFinite_of_surjectiveEtaleChart (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) {U : BigFppfOver B S hS}
    {q : yoneda.obj U ⟶ Y} (hqs : IsSurjective B S hS q) (hqe : IsEtale B S hS q)
    (hbase : IsFinite B S hS (pullback.snd f q)) :
    IsFinite B S hS f := by
  have _hri := Stacks.Morphisms.isFinite_respectsIso.{u}
  have _hd := isFinite_descendsAlong_fppf.{u}
  exact (isFinite_iff_representable B S hS f hX hY).mpr
    (presheaf_and_rep_of_surjectiveEtaleChart B S hS isFinite_le_isAffineHom.{u}
      hX hY f hqs hqe
      ((isFinite_iff_representable B S hS (pullback.snd f q)
        (isAlgebraicSpace_pullback B S hS f q hX (isAlgebraicSpace_yoneda B S hS U) hY)
        (isAlgebraicSpace_yoneda B S hS U)).mp hbase).2)

/-! ### Two scheme-level facts about finite morphisms -/

/-- **Stacks 02LA, the descent step.** Finite morphisms satisfy fpqc descent: if the base
change of `g` along a surjective flat quasi-compact morphism is finite, then so is `g`.

Finiteness is integrality together with being locally of finite type
(`AlgebraicGeometry.IsFinite.eq_inf`), and both factors descend along surjective flat
quasi-compact morphisms, the first by Stacks 02L9. -/
@[sga "1 VIII 5.7" "detection (finite)"]
theorem isFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have _h :=
    Stacks.Descent.isIntegralHom_descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  rw [_root_.AlgebraicGeometry.IsFinite.eq_inf]
  exact MorphismProperty.DescendsAlong.inf

/-! ### Effective descent for finite morphisms -/

/-- **Effective descent for finite morphisms along a surjective étale morphism of the site.**
This is Stacks 03I2 at the class of finite morphisms of schemes. -/
theorem isEffectiveDescentAlongSurjectiveEtale_isFinite :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) :=
  have _hri := Stacks.Morphisms.isFinite_respectsIso.{u}
  have _hfppf := isFinite_descendsAlong_fppf.{u}
  isEffectiveDescentAlongSurjectiveEtale_of_le
    (isEffectiveDescentAlongSurjectiveEtale_isIntegralHom B S hS)
    fun _ _ f hf =>
      have : _root_.AlgebraicGeometry.IsFinite f := hf
      inferInstanceAs (_root_.AlgebraicGeometry.IsIntegralHom f)

/-! ### Stacks 03ZQ for integral and for finite morphisms -/

/-- **Stacks 03ZQ for integral morphisms, conditions (2) and (3).** A morphism of algebraic
spaces over `S` is integral in the sense of Stacks 03ZP exactly when there is one surjective
étale morphism from a representable presheaf onto its target along which its base change is
integral. -/
@[stacks 03ZQ "integral: conditions (2) and (3)"]
theorem isIntegralHom_iff_etaleLocal (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) :
    IsIntegralHom B S hS f ↔
      ∃ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ Y),
        (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        IsIntegralHom B S hS (pullback.snd f g) :=
  have _hri := Stacks.Descent.isIntegralHom_respectsIso.{u}
  have _hfppf := isIntegralHom_descendsAlong_fppf.{u}
  holdsOnAffineBaseChange_iff_exists_etaleChart B S hS isZariskiLocalAtTarget_isIntegralHom
    (fun p hp hZ => isAffine_of_isIntegralHom p hp hZ)
    (isEffectiveDescentAlongSurjectiveEtale_isIntegralHom B S hS) hX hY f

/-- **Stacks 03ZQ for finite morphisms, conditions (2) and (3).** A morphism of algebraic
spaces over `S` is finite in the sense of Stacks 03ZP exactly when there is one surjective
étale morphism from a representable presheaf onto its target along which its base change is
finite. -/
@[stacks 03ZQ "finite: conditions (2) and (3)"]
theorem isFinite_iff_etaleLocal (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) :
    IsFinite B S hS f ↔
      ∃ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ Y),
        (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        IsFinite B S hS (pullback.snd f g) := by
  have _hri := Stacks.Morphisms.isFinite_respectsIso.{u}
  have _hfppf := isFinite_descendsAlong_fppf.{u}
  rw [isFinite_iff_holdsOnAffineBaseChange,
    holdsOnAffineBaseChange_iff_exists_etaleChart B S hS isZariskiLocalAtTarget_isFinite
      (fun p hp hZ => isAffine_of_isFinite p hp hZ)
      (isEffectiveDescentAlongSurjectiveEtale_isFinite B S hS) hX hY f]
  exact ⟨fun ⟨U, g, hs, he, h⟩ =>
      ⟨U, g, hs, he, (isFinite_iff_holdsOnAffineBaseChange _).2 h⟩,
    fun ⟨U, g, hs, he, h⟩ =>
      ⟨U, g, hs, he, (isFinite_iff_holdsOnAffineBaseChange _).1 h⟩⟩

end AlgebraicGeometry.Space

end
