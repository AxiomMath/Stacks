module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleTorsionReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.Homology.Perfect.LargeUniverse

/-!
# Perfectness of `RΓ_c(X_k̄, F)` for a flat sheaf from its reduction modulo `p`

Let `X` be a scheme over a field `k` with a compactification `j : X ⟶ X̄`, `k̄` an extension of
`k`, and `F` a sheaf of `ℤ/pᵐℤ`-modules on `X_étale` which is flat (pow-exact). Then
`RΓ_c(X_k̄, F) = RΓ(X̄_k̄, (j_! F)|_{X̄_k̄})` is a perfect complex of `ℤ/pᵐℤ`-modules as soon as
the cohomology of the reduction modulo `p` of `(j_! F)|_{X̄_k̄}` is finite and bounded above. This
is the shape in which the finiteness and vanishing theorems for the cohomology of torsion sheaves
on curves ([Stacks, Tag 03SC], parts (1) and (5), applied to the constructible sheaf
`j_! F / p` on the proper curve `X̄_k̄`) give the perfectness asserted in [Stacks, Tag 03V3] and
used in the proof of [Stacks, Tag 03V2].

## Main results

* `Stacks.EtaleCohomology.isPerfect_compactSupportFrobeniusCohomology_single_of_reduction`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p : ℕ) [Fact p.Prime] (m : ℕ) [NeZero m]

omit [Fintype k] in
/-- **Perfectness of `RΓ_c(X_k̄, F)` for a flat sheaf `F` of `ℤ/pᵐℤ`-modules** whose extension by
zero to the compactification has, modulo `p`, finite cohomology on `X̄_k̄` vanishing above `b`. -/
theorem isPerfect_compactSupportFrobeniusCohomology_single_of_reduction
    (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X) (hF : PowExact p m F) (b : ℤ)
    (hb : ∀ i, b < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod p)) i).obj
      (derivedDirectImageSections (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
        (ZMod p) ((etaleModuleCoextendScalars (torsionCoeff p m) _).obj
          ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj F))))))
    (hf : ∀ i, Module.Finite (ZMod p)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod p)) i).obj
        (derivedDirectImageSections (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
          (ZMod p) ((etaleModuleCoextendScalars (torsionCoeff p m) _).obj
            ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
              ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj F)))))) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (p ^ m)) f j kbar
        ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩)) := by
  have hF' : PowExact p m ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj F) :=
    hF.map _ (etaleModules_pow_nsmul_id F)
  have hP := isPerfect_fieldBaseChangeCohomology_of_reduction (Over.mk j.toBase) kbar p m hF' b
    hb hf
  refine StacksDraft.Perfect.isPerfect_of_iso ?_ hP
  refine DerivedCategory.Plus.ι.mapIso ((etaleModuleDerivedGlobalSections.{u, 0} _
    (Spec (.of kbar))).mapIso ((etaleModuleDerivedDirectImage.{u, 0} _
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).mapIso
      (DerivedCategory.Plus.Q.mapIso
        ((etaleModuleInverseImage.{u, 0} _
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.mapIso ?_))))
  exact ObjectProperty.isoMk _
    ((HomologicalComplex.singleMapHomologicalComplex
      (etaleModuleExtensionByZero.{u, 0} _ j.immersion) (ComplexShape.up ℤ) 0).app F)

end Stacks.EtaleCohomology
