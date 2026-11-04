module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaOpenClosedDevissage

/-!
# The canonical Frobenius trace is invariant under quasi-isomorphism

For a scheme `Y` over a finite field `k`, the canonical Frobenius endomorphism of
`RΓ(Y_k̄, C|_{Y_k̄})` is natural in the bounded below complex `C`
(`Stacks.EtaleCohomology.frobeniusRestrictionCohomologyEndo_naturality`), and restriction to
`Y_k̄` is exact. So a quasi-isomorphism `C₁ ⟶ C₂` induces an isomorphism of the two cohomologies
intertwining the canonical endomorphisms: perfectness and the trace depend only on `C` up to
quasi-isomorphism. This extends
`Stacks.EtaleCohomology.perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_iso` from
isomorphisms of complexes to quasi-isomorphisms.

## Main results

* `isPerfect_frobeniusRestriction_iff_of_quasiIso`: perfectness of the restricted cohomology is
  invariant under quasi-isomorphism of the coefficient complex.
* `perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_quasiIso_of_isPerfect`: the trace
  of the canonical Frobenius endomorphism is invariant under quasi-isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.FilteredDerived Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

omit [Fintype k] in
/-- Restriction to `Y_k̄` carries a quasi-isomorphism to an isomorphism of `D⁺(Y_k̄)`. -/
lemma isIso_fieldBaseChangeRestrictionFunctor_map_of_quasiIso
    {N₁ N₂ : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)} (φ : N₁ ⟶ N₂)
    [QuasiIso φ.hom] : IsIso ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar).map φ) := by
  set ψ := (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map
    φ with hψ
  have : QuasiIso ψ.hom :=
    inferInstanceAs (QuasiIso (((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj Y kbar)).mapHomologicalComplex _).map φ.hom))
  have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map ψ)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ ψ.hom).2 ‹_›
  have : IsIso (DerivedCategory.Plus.Q.map ψ) := isIso_of_fully_faithful DerivedCategory.Plus.ι _
  exact this

omit [Fintype k] in
/-- The isomorphism `RΓ(Y_k̄, C₁|_{Y_k̄}) ≅ RΓ(Y_k̄, C₂|_{Y_k̄})` induced by a
quasi-isomorphism. -/
def frobeniusRestrictionCohomologyIsoOfQuasiIso
    {N₁ N₂ : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)} (φ : N₁ ⟶ N₂) [QuasiIso φ.hom] :
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar N₁)) ≅
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar N₂)) :=
  haveI := isIso_fieldBaseChangeRestrictionFunctor_map_of_quasiIso Λ Y kbar φ
  (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
    ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).mapIso
      (asIso ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar).map φ)))

omit [Fintype k] in
/-- **Perfectness of `RΓ(Y_k̄, C|_{Y_k̄})` depends only on `C` up to quasi-isomorphism.** -/
theorem isPerfect_frobeniusRestriction_iff_of_quasiIso
    {N₁ N₂ : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)} (φ : N₁ ⟶ N₂) [QuasiIso φ.hom] :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar N₁)))) ↔
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar N₂)))) :=
  let e := DerivedCategory.Plus.ι.mapIso (frobeniusRestrictionCohomologyIsoOfQuasiIso Λ Y kbar φ)
  ⟨fun h => StacksDraft.Perfect.isPerfect_of_iso e.symm h,
    fun h => StacksDraft.Perfect.isPerfect_of_iso e h⟩

/-- **The canonical Frobenius trace is invariant under quasi-isomorphism of the coefficient
complex.** -/
theorem perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_quasiIso_of_isPerfect
    {N₁ N₂ : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)} (φ : N₁ ⟶ N₂) [QuasiIso φ.hom]
    (h₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar N₁)))))
    (h₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar N₂))))) :
    perfectDerivedTrace Λ ⟨_, h₁⟩ (DerivedCategory.Plus.ι.map
        (frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard N₁)) =
      perfectDerivedTrace Λ ⟨_, h₂⟩ (DerivedCategory.Plus.ι.map
        (frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard N₂)) := by
  refine perfectDerivedTrace_congr Λ _ _
    (DerivedCategory.Plus.ι.mapIso (frobeniusRestrictionCohomologyIsoOfQuasiIso Λ Y kbar φ)) _ _ ?_
  rw [Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact (frobeniusRestrictionCohomologyEndo_naturality (Λ := Λ) Y kbar p q hcard φ).symm

end Stacks.EtaleCohomology

end
