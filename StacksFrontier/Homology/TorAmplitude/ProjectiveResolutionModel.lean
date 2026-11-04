module

public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import StacksFrontier.Homology.Tor.DerivedTensorUniverse
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.Homology.TorAmplitude.FlatResolution

/-!
# The projective-resolution model of the derived tensor product

Let `R` be a commutative ring and `P` a bounded above cochain complex of flat `R`-modules. There
are two ways of computing `H^i(P ⊗ᴸ_R M)` for an `R`-module `M`: resolve `M` by projectives and
take the cohomology of `P ⊗ P_M`, which is
`StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomology`, or evaluate at `P` and `M[0]` a
derived tensor product certified as in Stacks 0652. This file identifies the two, and with them the
corresponding two Tor-amplitude predicates.

## Main definitions

* `StacksDraft.TorAmplitude.tensorSwapIso`: the isomorphism `K ⊗ L ≅ L ⊗ K` of tensor products of
  cochain complexes of `R`-modules.

## Main results

* `StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasTorAmplitude0DJF`: for a bounded above complex
  of flat modules, certified derived Tor amplitude in the sense of Stacks 0652 is the
  projective-resolution Tor amplitude of Stacks 0DJF.

## References

* [Stacks Project, Tag 0652](https://stacks.math.columbia.edu/tag/0652)
* [Stacks Project, Tag 0DJF](https://stacks.math.columbia.edu/tag/0DJF)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
  CategoryTheory.MonoidalCategory HomologicalComplex

namespace StacksDraft.TorAmplitude

universe u

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false

@[expose] public section

/-! ### Exchanging the two factors of a tensor product of cochain complexes -/


variable {R : Type u} [CommRing R]

open CochainComplex.DerivedTensor in
/-- The two factors of a tensor product of cochain complexes of `R`-modules may be exchanged:
`K ⊗ L ≅ L ⊗ K`. -/
noncomputable def tensorSwapIso (K L : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorLeft K).obj L ≅ (tensorRight K).obj L :=
  mapBifunctorIso (BraidedCategory.curriedBraidingNatIso (ModuleCat.{u} R)) K L ≪≫
    mapBifunctorFlipIso L K (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)

/-! ### The projective-resolution model at a K-flat complex -/

/-- For a K-flat complex `P`, the projective-resolution model
`StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomology P M i` of `H^i(P ⊗ᴸ_R M)` is the
degree-`i` cohomology of the termwise tensor product complex `P ⊗ M`. -/
private noncomputable def derivedTensorHomologyIsoTermwise
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) (M : ModuleCat.{u} R) (i : ℤ) :
    StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomology P M i ≅
      (StacksDraft.TorAmplitude.Termwise.tensorComplex P M).homology i := by
  have : QuasiIso ((tensorLeft P).map (ProjectiveResolution.of M).π') :=
    quasiIso_tensorLeft_map P hP _
  have : IsIso (homologyMap ((tensorLeft P).map (ProjectiveResolution.of M).π') i) :=
    (quasiIsoAt_iff_isIso_homologyMap _ i).1 inferInstance
  exact asIso (homologyMap ((tensorLeft P).map (ProjectiveResolution.of M).π') i) ≪≫
    (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapIso
      (tensorSwapIso P ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) ≪≫
        StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso M P ≪≫
        (NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight M)
          (ComplexShape.up ℤ)).app P)

/-- For a K-flat, bounded above complex `P` of flat `R`-modules, Tor amplitude of `Q P` in
`[a, b]` for an arbitrary certified derived tensor product (Stacks 0652) is the
projective-resolution Tor amplitude of `P` in `[a, b]` (Stacks 0DJF). -/
public theorem hasTorAmplitude_iff_hasTorAmplitude0DJF
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
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hKFlat : P.KFlat)
    (hbounded : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
    (hflat : ∀ i : ℤ, Module.Flat R (P.X i)) (a b : ℤ) :
    HasTorAmplitude derivedTensor comparison isLeftDerived (DerivedCategory.Q.obj P) a b ↔
      StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude P a b := by
  rw [hasTorAmplitude_iff_termwise_of_flat comparison isLeftDerived P hbounded hflat a b]
  exact ⟨fun h M i hi => (derivedTensorHomologyIsoTermwise P hKFlat M i).isZero_iff.2 (h M i hi),
    fun h M i hi => (derivedTensorHomologyIsoTermwise P hKFlat M i).isZero_iff.1 (h M i hi)⟩

end

end StacksDraft.TorAmplitude
