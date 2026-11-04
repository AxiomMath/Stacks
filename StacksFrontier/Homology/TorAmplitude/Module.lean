module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.Homology.TorAmplitude.FlatResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tor dimension of a module and finite flat resolutions

Let `R` be a commutative ring and `M` an `R`-module. A *flat resolution of length `d`* of `M` is
an exact sequence `0 → F_d → ⋯ → F_0 → M → 0` with each `F_i` flat; in the derived category this
is a complex of flat modules concentrated in cohomological degrees `[-d, 0]` representing `M[0]`.
In length `0` the condition says exactly that `M` itself is flat.

## Main results

* `StacksDraft.TorAmplitude.hasFlatRepresentative_single_zero_iff`: a module placed in degree `0`
  has a flat representative concentrated in `[0, 0]` if and only if the module is flat.

## Implementation notes

A flat resolution is recorded as `HasFlatRepresentative`, the flat-representative predicate of
Stacks 0654: the derived-category form of the augmented exact sequence of the source. The
degree-`0` case uses that a complex concentrated in degree `0` is isomorphic to a module placed
in degree `0`, and that the functor placing a module in degree `0` is fully faithful, so an
isomorphism in `D(R)` between two such complexes comes from an isomorphism of modules.

## References

* [Stacks Project, Tag 066F](https://stacks.math.columbia.edu/tag/066F)
-/

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.TorAmplitude

universe u v

attribute [local instance] HasDerivedCategory.standard

@[expose] public section

/-- Flatness transfers along an isomorphism of modules. -/
private theorem flat_of_iso {R : Type u} [CommRing R] {X Y : ModuleCat.{max u v} R}
    (hX : Module.Flat R X) (e : X ≅ Y) : Module.Flat R Y :=
  @Module.Flat.of_linearEquiv R X Y _ _ _ _ _ hX e.symm.toLinearEquiv

/-- A module placed in cohomological degree `0` has a flat representative concentrated in
`[0, 0]` exactly when the module is flat.

This is the degree-zero case of Stacks 066F: a flat resolution of length `0` of `M` is nothing
but a flat structure on `M` itself. -/
public theorem hasFlatRepresentative_single_zero_iff {R : Type u} [CommRing R]
    (M : ModuleCat.{max u v} R) :
    HasFlatRepresentative
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) 0 0 ↔
      Module.Flat R M := by
  constructor
  · rintro ⟨E, hflat, hGE, hLE, ⟨e⟩⟩
    obtain ⟨N, ⟨eE⟩⟩ := E.exists_iso_single 0
    let e' : (DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M ≅
        (DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N :=
      e ≪≫ DerivedCategory.Q.mapIso eE ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} R) 0).app N).symm
    let eMN : M ≅ N := (DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).preimageIso e'
    have hN : Module.Flat R N := flat_of_iso (hflat 0)
      ((asIso (eE.hom.f 0)) ≪≫ HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N)
    exact flat_of_iso hN eMN.symm
  · intro hM
    refine ⟨(CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj M, ?_,
      inferInstance, inferInstance,
      ⟨(DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} R) 0).app M⟩⟩
    intro n
    by_cases hn : n = 0
    · subst n
      exact flat_of_iso hM (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).symm
    · have : Subsingleton
          (((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj M).X n) :=
        ModuleCat.isZero_iff_subsingleton.mp (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
      infer_instance

/-- The general form of Stacks 066F: an `R`-module `M` has Tor dimension at most `d` if and only
if it admits a flat resolution of length `d`, that is, a complex of flat modules concentrated in
degrees `[-d, 0]` representing `M[0]`. In particular `M` has Tor dimension at most `0` if and
only if `M` is flat.

Stated over an arbitrary certified derived tensor product, so that the proof depends on no
particular construction of one. The tag sits on the specialisation to the canonical derived
tensor product,
`StacksDraft.TorAmplitude.hasTorDimensionLECanonical_iff_hasFlatRepresentative` in
`StacksFrontier.Homology.TorAmplitude.CanonicalCertificate`. -/
@[sga "4 XVII 4.1.9" "(i) ⇔ (iii) for K = M[0]", sga "6 I 5.4" "For all d, special case"]
public theorem hasTorDimensionLE_iff_hasFlatRepresentative {R : Type u} [CommRing R]
    {derivedTensor : DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R)}
    (comparison : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} R,
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
          (comparison N)
          (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (M : ModuleCat.{u} R) (d : ℕ) :
    (HasTorDimensionLE derivedTensor comparison isLeftDerived M d ↔
        HasFlatRepresentative
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) (-(d : ℤ)) 0) ∧
      (HasTorAmplitude derivedTensor comparison isLeftDerived
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) 0 0 ↔
        Module.Flat R M) := by
  refine ⟨hasTorAmplitude_iff_hasFlatRepresentative comparison isLeftDerived _ _ _, ?_⟩
  rw [hasTorAmplitude_iff_hasFlatRepresentative comparison isLeftDerived]
  exact hasFlatRepresentative_single_zero_iff M

end

end StacksDraft.TorAmplitude
