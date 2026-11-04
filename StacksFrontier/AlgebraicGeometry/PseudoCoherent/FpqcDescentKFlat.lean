module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentIso

/-!
# Fpqc descent of pseudo-coherence, on K-flat complexes

Stacks 09UE (`Stacks.Cohomology.PseudoCoherence.FpqcDescent.isPseudoCoherentFrom_iff_forall_fpqc`)
says that an object `E` of `D_QCoh(𝒪_X)` is `m`-pseudo-coherent exactly when its derived
pullbacks along the members of an fpqc covering are. On a K-flat complex the derived pullback is
computed degreewise, so the converse direction can be stated on complexes, with no derived
category in the statement: this is the form in which it is transported to the small étale sites
of algebraic spaces.

## Main results

* `Stacks.Cohomology.PseudoCoherence.FpqcDescent.isPseudoCoherentComplexFrom_of_fpqc_kFlat`

## References

* [Stacks Project, Tag 09UE](https://stacks.math.columbia.edu/tag/09UE)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Stacks.Cohomology.PseudoCoherence.FpqcDescent

/-- **Stacks 09UE, descent direction, on K-flat complexes.** Let `{f_i : Y_i ⟶ X}` be an fpqc
covering of schemes and let `K` be a K-flat complex of `𝒪_X`-modules with quasi-coherent
cohomology. If every degreewise pullback `f_i^*K` is `m`-pseudo-coherent, then so is `K`. -/
public theorem isPseudoCoherentComplexFrom_of_fpqc_kFlat {X : Scheme.{u}} {I : Type v}
    (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows Y f ∈ Scheme.fpqcPrecoverage X)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ)
    (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toRingedSpace K)
    (hKq : ∀ i : ℤ, (K.homology i).IsQuasicoherent) (m : ℤ)
    (h : ∀ i, RingedSpace.PseudoCoherence.IsPseudoCoherentComplexFrom (X := (Y i).toRingedSpace)
      (((RingedSpaceModuleAdjunction.modulePullback (f i).toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) m) :
    RingedSpace.PseudoCoherence.IsPseudoCoherentComplexFrom (X := X.toRingedSpace) K m := by
  let E₀ : Stacks.Duality.quasiCoherentDerivedCategory X :=
    ⟨DerivedCategory.Q.obj K, fun i => (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctorFactors _ i).app K).symm (hKq i)⟩
  exact @RingedSpace.isPseudoCoherentComplexFrom_of_iso X.toRingedSpace
    (Scheme.Modules.hasDerivedCategory X) E₀.obj m
    ((isPseudoCoherentFrom_iff_forall_fpqc Y f hf E₀ m).2 fun i =>
      ⟨_, h i, ⟨(Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat
        (f i).toLRSHom.toShHom K hK).symm⟩⟩) K (Iso.refl E₀.obj)

end Stacks.Cohomology.PseudoCoherence.FpqcDescent
