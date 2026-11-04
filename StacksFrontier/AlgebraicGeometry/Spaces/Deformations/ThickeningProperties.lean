module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleUniversallyInjectiveOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderMorphismMonomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderMorphismRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.MorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SeparatedAndClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SourceFiniteOrderMorphismImmersions

/-!
# Properties of a cartesian finite-order deformation which are not étale local

Let

```
(X ⊂ X') --(f, f')--> (Y ⊂ Y')
         ↘                ↙
            (B ⊂ B')
```

be a cartesian finite-order deformation of algebraic spaces over a scheme `S`: the base
thickening is of finite order, `X'` is flat over `B'`, and `X = B ×_{B'} X'`,
`Y = B ×_{B'} Y'`. Stacks 0CG6 lists the properties shared by `f` and `f'`. The properties
which are étale local on the source and target are in
`StacksFrontier/AlgebraicGeometry/Spaces/Deformations/Properties.lean`; this file proves the
remaining parts except finite local freeness, which is in
`StacksFrontier/AlgebraicGeometry/Spaces/Deformations/FiniteLocallyFreeProperty.lean`.

The two inputs are the comparisons for morphisms of thickenings of algebraic spaces.

* Stacks 09ZY applies to the morphism of thickenings `(f, f')` itself, with no hypothesis:
  representability, quasi-compactness, universal closedness, (quasi-)separatedness,
  universal injectivity, affineness, universal openness and integrality.
* Stacks 09ZZ applies once `(f, f')` is recognised as a *cartesian* morphism of thickenings
  whose target thickening `Y ⊂ Y'` is of finite order: `X = Y ×_{Y'} X'` is the pasting of the
  two cartesian squares over the base, and `Y ⊂ Y'` is the inverse image of the finite-order
  thickening `B ⊂ B'` along `Y' ⟶ B'`, hence of finite order by Stacks 09ZX. This gives the
  monomorphism, relative dimension, properness and finiteness parts.

The open immersion and isomorphism parts follow the source. If `f` is an open immersion it is
étale and universally injective, hence so is `f'` by the étale part of Stacks 0CG6 and by
Stacks 09ZY, and then `f'` is an open immersion by Stacks 05W5; conversely `f` is a base
change of `f'`. If `f` is an isomorphism it is an open immersion, so `f'` is a surjective open
immersion, hence an isomorphism; conversely `f` is a base change of `f'`.

## Main definitions

* `AlgebraicGeometry.Space.CartesianFiniteOrderDeformation.morphism`: the morphism of
  thickenings `(f, f')`, as a morphism in the arrow category.
* `CartesianFiniteOrderDeformation.toCartesianFiniteOrderMorphismOfThickenings`: the cartesian
  morphism of thickenings `(f, f')`, with target thickening of finite order.
* `AlgebraicGeometry.Space.CartesianFiniteOrderDeformation.smallHom` and
  `AlgebraicGeometry.Space.CartesianFiniteOrderDeformation.ambientHom`: `f` and `f'` as morphisms
  of algebraic spaces.

## Main results

The parts of **Stacks 0CG6** proved here, each as an equivalence between the property of `f`
and that of `f'`:

* `isRelativelyRepresentable_iff`: part 0CG7, representable;
* `isIso_iff`: part 0CG9, isomorphism;
* `isOpenImmersion_iff`: part 0CGA, open immersion;
* `isQuasiCompact_iff`: part 0CGB, quasi-compact;
* `universallyClosed_iff`: part 0CGC, universally closed;
* `isSeparated_iff_and_isQuasiSeparated_iff`: part 0CGD, separated and quasi-separated;
* `mono_iff`: part 0CGE, monomorphism;
* `universallyInjective_iff`: part 0CGG, universally injective;
* `isAffineHom_iff`: part 0CGH, affine;
* `isLocallyOfFiniteType_and_hasRelativeDimension_iff`: part 0CGL, locally of finite type of
  relative dimension `d`;
* `universallyOpen_iff`: part 0CGM, universally open;
* `isProper_iff`: part 0CGS, proper;
* `isIntegralHom_iff`: part 0CGT, integral;
* `isFinite_iff`: part 0CGU, finite.

## References

* [Stacks Project, Tag 0CG6](https://stacks.math.columbia.edu/tag/0CG6)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 09ZY](https://stacks.math.columbia.edu/tag/09ZY)
* [Stacks Project, Tag 09ZZ](https://stacks.math.columbia.edu/tag/09ZZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

namespace CartesianFiniteOrderDeformation

variable {T : BigFppfSite.{u}} {S : Scheme.{u}} {hS : T.Contains S}
    (D : CartesianFiniteOrderDeformation T S hS)

/-! ### The underlying morphism of thickenings -/

/-- The morphism of thickenings `(f, f') : (X ⊂ X') ⟶ (Y ⊂ Y')` of a cartesian finite-order
deformation, as a morphism in the arrow category. -/
abbrev morphism : Arrow.mk D.X.ι ⟶ Arrow.mk D.Y.ι :=
  Arrow.homMk D.f D.f' D.comm_f

/-- The source of a cartesian finite-order deformation is the base change of its ambient
source along the target thickening: the two cartesian squares over the base paste. -/
theorem isPullback_f : IsPullback D.f D.X.ι D.Y.ι D.f' :=
  IsPullback.of_right D.isPullback_X.flip D.comm_f D.isPullback_Y.flip

/-- The target thickening of a cartesian finite-order deformation is the inverse image of the
base thickening along the structure morphism of the ambient target. -/
theorem target_eq_preimage : D.Y = D.B.preimage D.g' := by
  have h : Subfunctor.range D.Y.ι = (Subfunctor.range D.B.ι).preimage D.g' := by
    ext U x
    exact Set.ext_iff.mp (Types.range_snd_of_isPullback (D.isPullback_Y.flip.app U)) x
  rwa [Subfunctor.range_ι, Subfunctor.range_ι] at h

/-- **Stacks 09ZX at the target.** The target thickening of a cartesian finite-order
deformation is of finite order, being the inverse image of the finite-order base thickening. -/
theorem target_finiteOrder : IsFiniteOrderThickening T S hS D.Y' D.Y :=
  D.target_eq_preimage ▸ isFiniteOrderThickening_preimage T S hS D.B
    (ObjectProperty.homMk D.g' : D.Y' ⟶ D.B') D.base_finiteOrder

/-- The morphism of thickenings `(f, f')` of a cartesian finite-order deformation is a
cartesian morphism of thickenings whose target thickening is of finite order: the situation of
Stacks 09ZZ. -/
def toCartesianFiniteOrderMorphismOfThickenings :
    CartesianFiniteOrderMorphismOfThickenings T S hS where
  X' := D.X'
  Y' := D.Y'
  X := D.X
  Y := D.Y
  sourceThickening := D.source_thickening
  targetFiniteOrder := D.target_finiteOrder
  morphism := D.morphism
  cartesian := D.isPullback_f

/-! ### Parts which hold for every morphism of thickenings (Stacks 09ZY) -/

/-- **Stacks 0CG6, part 0CG7.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is representable if and only if its ambient deformation is. -/
@[stacks 0CG6 "0CG7: representable"]
theorem isRelativelyRepresentable_iff :
    yoneda.relativelyRepresentable D.f ↔ yoneda.relativelyRepresentable D.f' :=
  relativelyRepresentable_iff_relativelyRepresentable_of_isThickening_unconditional T S hS
    D.source_thickening D.target_thickening D.morphism

/-- **Stacks 0CG6, part 0CGB.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is quasi-compact if and only if its ambient deformation is. -/
@[stacks 0CG6 "0CGB: quasi-compact"]
theorem isQuasiCompact_iff : IsQuasiCompact T S hS D.f ↔ IsQuasiCompact T S hS D.f' :=
  isQuasiCompact_iff_isQuasiCompact_of_isThickening T S hS D.source_thickening
    D.target_thickening D.morphism

/-- **Stacks 0CG6, part 0CGC.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is universally closed if and only if its ambient deformation is. -/
@[stacks 0CG6 "0CGC: universally closed"]
theorem universallyClosed_iff : UniversallyClosed T S hS D.f ↔ UniversallyClosed T S hS D.f' :=
  universallyClosed_iff_universallyClosed_of_isThickening T S hS D.source_thickening
    D.target_thickening D.morphism

/-- **Stacks 0CG6, part 0CGD.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is separated if and only if its ambient deformation is, and it is
quasi-separated if and only if its ambient deformation is. -/
@[stacks 0CG6 "0CGD: separated, and quasi-separated"]
theorem isSeparated_iff_and_isQuasiSeparated_iff :
    (IsSeparated T S hS D.f ↔ IsSeparated T S hS D.f') ∧
      (IsQuasiSeparated T S hS D.f ↔ IsQuasiSeparated T S hS D.f') :=
  isSeparated_iff_and_isQuasiSeparated_iff_of_isThickening T S hS D.source_thickening
    D.target_thickening D.morphism

/-- **Stacks 0CG6, part 0CGG.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is universally injective if and only if its ambient deformation
is. -/
@[stacks 0CG6 "0CGG: universally injective"]
theorem universallyInjective_iff :
    UniversallyInjective T S hS D.f ↔ UniversallyInjective T S hS D.f' :=
  universallyInjective_iff_universallyInjective_of_isThickening T S hS D.source_thickening
    D.target_thickening D.morphism

/-- **Stacks 0CG6, part 0CGH.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is affine if and only if its ambient deformation is. -/
@[stacks 0CG6 "0CGH: affine"]
theorem isAffineHom_iff : IsAffineHom T S hS D.f ↔ IsAffineHom T S hS D.f' :=
  isAffineHom_iff_isAffineHom_of_isThickening_unconditional T S hS D.source_thickening
    D.target_thickening D.morphism

/-- **Stacks 0CG6, part 0CGM.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is universally open if and only if its ambient deformation is. -/
@[stacks 0CG6 "0CGM: universally open"]
theorem universallyOpen_iff : UniversallyOpen T S hS D.f ↔ UniversallyOpen T S hS D.f' :=
  universallyOpen_iff_universallyOpen_of_isThickening T S hS D.source_thickening
    D.target_thickening D.morphism

/-- **Stacks 0CG6, part 0CGT.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is integral if and only if its ambient deformation is. -/
@[stacks 0CG6 "0CGT: integral"]
theorem isIntegralHom_iff : IsIntegralHom T S hS D.f ↔ IsIntegralHom T S hS D.f' :=
  isIntegralHom_iff_isIntegralHom_of_isThickening_unconditional T S hS D.source_thickening
    D.target_thickening D.morphism

/-! ### Parts which use the cartesian square (Stacks 09ZZ) -/

/-- **Stacks 0CG6, part 0CGE.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is a monomorphism if and only if its ambient deformation is. -/
@[stacks 0CG6 "0CGE: monomorphism"]
theorem mono_iff : Mono D.f ↔ Mono D.f' :=
  D.toCartesianFiniteOrderMorphismOfThickenings.mono_iff

/-- **Stacks 0CG6, part 0CGL.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is locally of finite type of relative dimension `d` if and only if
its ambient deformation is. -/
@[stacks 0CG6 "0CGL: locally of finite type of relative dimension d"]
theorem isLocallyOfFiniteType_and_hasRelativeDimension_iff (d : ℕ) :
    (IsLocallyOfFiniteType T S hS D.f ∧ HasRelativeDimension d T S hS D.f) ↔
      (IsLocallyOfFiniteType T S hS D.f' ∧ HasRelativeDimension d T S hS D.f') :=
  D.toCartesianFiniteOrderMorphismOfThickenings.isLocallyOfFiniteType_and_hasRelativeDimension_iff
    d

/-- **Stacks 0CG6, part 0CGS.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is proper if and only if its ambient deformation is. -/
@[stacks 0CG6 "0CGS: proper"]
theorem isProper_iff : IsProper T S hS D.f ↔ IsProper T S hS D.f' :=
  D.toCartesianFiniteOrderMorphismOfThickenings.isProper_iff

/-- **Stacks 0CG6, part 0CGU.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is finite if and only if its ambient deformation is. -/
@[stacks 0CG6 "0CGU: finite"]
theorem isFinite_iff : IsFinite T S hS D.f ↔ IsFinite T S hS D.f' :=
  D.toCartesianFiniteOrderMorphismOfThickenings.isFinite_iff

/-! ### Open immersions and isomorphisms -/

/-- The source `X` of the morphism of special fibres, as an algebraic space over `S`. -/
abbrev sourceSpace : AlgebraicSpaces T S hS := ⟨D.X.toFunctor, D.source_thickening.1.1⟩

/-- The target `Y` of the morphism of special fibres, as an algebraic space over `S`. -/
abbrev targetSpace : AlgebraicSpaces T S hS := ⟨D.Y.toFunctor, D.target_thickening.1.1⟩

/-- The morphism of special fibres `f : X ⟶ Y`, as a morphism of algebraic spaces. -/
abbrev smallHom : D.sourceSpace ⟶ D.targetSpace := ObjectProperty.homMk D.f

/-- The ambient deformation `f' : X' ⟶ Y'`, as a morphism of algebraic spaces. -/
abbrev ambientHom : D.X' ⟶ D.Y' := ObjectProperty.homMk D.f'

/-- The square `(f, f')` of a cartesian finite-order deformation, read in the category of
algebraic spaces over `S`: `f` is the base change of `f'` along the target thickening. -/
theorem isPullback_algebraicSpaces :
    IsPullback (ObjectProperty.homMk D.X.ι : D.sourceSpace ⟶ D.X') D.smallHom D.ambientHom
      (ObjectProperty.homMk D.Y.ι : D.targetSpace ⟶ D.Y') :=
  IsPullback.of_map_of_faithful
    (F := ObjectProperty.ι
      (fun F : (BigFppfOver T S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace T S hS F))
    D.isPullback_f.flip

/-- **Stacks 0CG6, part 0CGA.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is an open immersion if and only if its ambient deformation is. -/
@[stacks 0CG6 "0CGA: open immersion"]
theorem isOpenImmersion_iff : IsOpenImmersion T S hS D.f ↔ IsOpenImmersion T S hS D.f' := by
  refine ⟨fun hf => ?_, fun hf' => ?_⟩
  · have he : IsEtale T S hS D.f' := D.isEtale_iff.mp (isEtale_of_isOpenImmersion T S hS hf)
    have hui : UniversallyInjective T S hS D.f' :=
      D.universallyInjective_iff.mp
        (universallyInjective_of_mono T S hS D.f (mono_of_isOpenImmersion T S hS D.f hf))
    exact isOpenImmersion_of_isEtale_of_universallyInjective T S hS D.X'.property
      D.Y'.property D.f' he hui
  · exact isOpenImmersion_of_isPullback T S hS D.isPullback_algebraicSpaces hf'

/-- **Stacks 0CG6, part 0CG9.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is an isomorphism if and only if its ambient deformation is. -/
@[stacks 0CG6 "0CG9: isomorphism"]
theorem isIso_iff : IsIso D.f ↔ IsIso D.f' := by
  refine ⟨fun hf => ?_, fun hf' => ?_⟩
  · have hopen : IsOpenImmersion T S hS D.f' :=
      D.isOpenImmersion_iff.mp (isOpenImmersion_of_isIso T S hS D.f)
    have hsurj : IsSurjective T S hS D.f := fun x => by
      refine ⟨pointsMap T S hS _ (inv D.f) x, ?_⟩
      rw [← pointsMap_comp_apply, IsIso.inv_hom_id, pointsMap_id, id]
    exact isIso_of_isOpenImmersion_of_surjective_pointsMap T S hS D.f' hopen
      (D.isSurjective_iff.mp hsurj)
  · exact D.isPullback_f.isIso_fst_of_isIso

end CartesianFiniteOrderDeformation

end AlgebraicGeometry.Space

end
