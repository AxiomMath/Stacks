module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceBaseAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRestrictedData
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRingSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpCompSections

/-!
# The descended difference of two morphisms over a base kills the functions read from that base

Let `Z ⊂ X` be a first order thickening of algebraic spaces over a scheme `S`, let `W₀ ⊆ W` be a
closed subspace with inclusion `j`, let `c, c' : X ⟶ W` restrict on `Z` to one and the same
`e₀ ≫ j`, and let `qb : W ⟶ Bas` be a morphism with `c ≫ qb = c' ≫ qb`.  Their difference is
the datum `AlgebraicGeometry.Space.restrictedLiftDifferenceData`, and this file shows that the
derivation it descends to **kills every regular function read from `Bas` along `qb`**.

That is the second of the two vanishing conditions a difference has to satisfy before it is a
map out of the *relative* differentials of [Stacks Project, Tag 0619]: the first, that it kills
the sections killed by `j^♯`, is hypothesis (2) of [Stacks Project, Tag 0618] and is the field
`app_eq_of_app_eq_zero` of the datum.

## Main results

* `AlgebraicGeometry.Space.descend_restrictedLiftDifferenceData_app_inverseImage_eq_zero`: the
  descended difference of the two transported comorphisms vanishes on `j^♯(j^{-1}(qb^♯)(x))`.

## Implementation notes

This is the pair-of-morphisms counterpart of
`AlgebraicGeometry.Space.derivationFamilyOfHom_app_inverseImage_eq_zero`, which says the same of
the derivation attached to a linear map by Equation [Stacks Project, Tag 0619], and it is stated
in the same shape: on sections of `j^{-1}(qb^{-1}𝒪_{Bas})` read into `𝒪_{W₀}` through
`j^{-1}(qb^♯)` and then `j^♯`.  That is the shape the agreement of the two comorphisms is
available in, and no commutative square `j ≫ qb = b ≫ iB` is needed to state it.

The whole content is
`inverseImage_structureSharpRingInverseImage_comp_restrictedSharpThroughThickening_eq'`
at `p := qb`, fed to `Stacks.Sites.LiftDifferenceData.descend_eq_zero_of_comp_eq`.  That
agreement used to be available only for two *sections* of a morphism `W ⟶ X` back to the source
of `c` and `c'`; it is now stated at an arbitrary target, which is what makes `qb` an admissible
argument.

The hypothesis `hker` is passed through bare, exactly as
`AlgebraicGeometry.Space.restrictedLiftDifferenceData` asks for it; for an undeformed target
`AlgebraicGeometry.Space.restrictedSharpThroughThickening_app_eq_of_top` supplies it.

`AlgebraicGeometry.Space.app_structureSharpInverseImage_comp`, the composition law for the
structure map in inverse-image form read on a section, was introduced here and now lives in
`StacksFrontier/AlgebraicGeometry/Spaces/StructureSharpCompSections.lean`, imported above: it is an
identity about the structure map of a composite and has nothing to do with a thickening, and a
second consumer of it needs it without this module's large closure.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the difference of two
  lifts.
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619), the equation whose
  relative differentials this vanishing is needed for.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The descended difference of two morphisms over a base -/

variable {X W Bas : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1) (hZ : IsFirstOrderThickening B S hS X Z.1)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  (c c' : X ⟶ W)
  (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
  (h' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
  (hker : ∀ (V : (SmallEtale B S hS
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : (structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS W W₀)).obj.obj V),
    (structureSharpRingInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
      (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h).hom.app V x =
        (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h').hom.app V x)
  (qb : W ⟶ Bas) (hcc : c ≫ qb = c' ≫ qb)

include hcc in
/-- **The descended difference of two morphisms over a base kills the functions read from that
base.**  For `c, c' : X ⟶ W` agreeing on the thickening `Z ⊂ X` and over `qb : W ⟶ Bas`, the
derivation their difference descends to vanishes on every section of `𝒪_{W₀}` of the form
`j^♯(j^{-1}(qb^♯)(x))`.

The two transported comorphisms agree after `j^{-1}(qb^♯)` — that is
`inverseImage_structureSharpRingInverseImage_comp_restrictedSharpThroughThickening_eq'`
at an arbitrary target `Bas` — and a difference which vanishes after a morphism into the ambient
sheaf of rings descends to one vanishing on the sections that morphism accounts for, which is
`Stacks.Sites.LiftDifferenceData.descend_eq_zero_of_comp_eq`.

This is the pair-of-morphisms counterpart of
`AlgebraicGeometry.Space.derivationFamilyOfHom_app_inverseImage_eq_zero`. -/
theorem descend_restrictedLiftDifferenceData_app_inverseImage_eq_zero
    [HasSheafify (SmallEtale.topology B S hS
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1) AddCommGrpCat.{u}]
    (A : (SmallEtale B S hS
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : ToType (((smallEtaleInverseImageRing B S hS
      (subspaceInclusion B S hS W W₀)).obj
      (inverseImageStructureSheaf B S hS qb)).obj.obj A)) :
    (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c c' h h' hker).toQuotientDerivation.descend
        ((structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS W W₀)).hom.app A
          (((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
              (subspaceInclusion B S hS W W₀))).map
            (structureSharpRingInverseImage B S hS qb)).hom.app A x)) =
      0 :=
  (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c c' h h' hker).descend_eq_zero_of_comp_eq
    ((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
      (subspaceInclusion B S hS W W₀))).map (structureSharpRingInverseImage B S hS qb))
    _ rfl
    (inverseImage_structureSharpRingInverseImage_comp_restrictedSharpThroughThickening_eq'
      B S hS Z W₀ c c' qb e₀ h h' hcc)
    x

include hcc in
/-- **The descended difference of two morphisms over a base is a derivation over that base**, in
the shape `AlgebraicGeometry.Space.liftDifferenceDifferentialsHom` asks for it: it kills every
section of `𝒪_{W₀}` read from `Bas` along the composite `j ≫ qb`.

This is
`AlgebraicGeometry.Space.descend_restrictedLiftDifferenceData_app_inverseImage_eq_zero`, whose
sections are read through `j^{-1}(qb^♯)` and then `j^♯`, carried onto the structure map of the
composite by `AlgebraicGeometry.Space.app_structureSharpInverseImage_comp`; the two coefficient
readings of the inverse-image structure maps agree on sections by
`AlgebraicGeometry.Space.app_inverseImage_structureSharpRingInverseImage` and
`AlgebraicGeometry.Space.structureSharpRingInverseImage_eq_forget₂`.

Taking `b := j ≫ qb` for the base datum of
`AlgebraicGeometry.Space.liftDifferenceDifferentialsHom`, this is the hypothesis `hz` of that
descent — the second of the two vanishing conditions, the first being hypothesis (2) of
[Stacks Project, Tag 0618]. -/
theorem descend_restrictedLiftDifferenceData_structureSharpInverseImage_eq_zero
    [HasSheafify (SmallEtale.topology B S hS
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1) AddCommGrpCat.{u}]
    (V : (SmallEtale B S hS
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (s : ToType ((inverseImageStructureSheaf B S hS
      (subspaceInclusion B S hS W W₀ ≫ qb)).obj.obj V)) :
    (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c c' h h' hker).toQuotientDerivation.descend
        ((structureSharpInverseImage B S hS
          (subspaceInclusion B S hS W W₀ ≫ qb)).hom.app V s) =
      0 := by
  have harg : (structureSharpInverseImage B S hS
          (subspaceInclusion B S hS W W₀ ≫ qb)).hom.app V s =
      (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V
        (((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS W W₀))).map
          (structureSharpRingInverseImage B S hS qb)).hom.app V
          (((smallEtaleRingedToposHom_compInverseImageRingIso B S hS
              (subspaceInclusion B S hS W W₀) qb).inv.app
            (smallEtaleRingedTopos B S hS Bas).O).hom.app V s)) := by
    rw [app_structureSharpInverseImage_comp B S hS (subspaceInclusion B S hS W W₀) qb V s,
      app_inverseImage_structureSharpRingInverseImage B S hS
        (subspaceInclusion B S hS W W₀) qb V
        (((smallEtaleRingedToposHom_compInverseImageRingIso B S hS
            (subspaceInclusion B S hS W W₀) qb).inv.app
          (smallEtaleRingedTopos B S hS Bas).O).hom.app V s),
      structureSharpRingInverseImage_eq_forget₂ B S hS (subspaceInclusion B S hS W W₀)]
    rfl
  exact Eq.trans
    (congrArg
      (fun z : (structureRingSheaf B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS)).obj.obj V ↦
        (restrictedLiftDifferenceData B S hS Z W₀ e₀ hZ c c'
          h h' hker).toQuotientDerivation.descend z)
      harg)
    (descend_restrictedLiftDifferenceData_app_inverseImage_eq_zero
      B S hS Z W₀ hZ e₀ c c' h h' hker qb hcc V
      (((smallEtaleRingedToposHom_compInverseImageRingIso B S hS
          (subspaceInclusion B S hS W W₀) qb).inv.app
        (smallEtaleRingedTopos B S hS Bas).O).hom.app V s))

end AlgebraicGeometry.Space

end
