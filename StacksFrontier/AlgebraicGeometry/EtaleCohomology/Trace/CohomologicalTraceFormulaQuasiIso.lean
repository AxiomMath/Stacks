module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CohomologicalTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DerivedStalkPerfection
public import StacksFrontier.Algebra.Homology.DerivedCategory.HomToInjectiveSingle

/-!
# The trace formula only depends on the complex up to quasi-isomorphism

Let `Y` be a scheme over a finite field `k`. A quasi-isomorphism `C ⟶ C'` of bounded below
complexes of sheaves of `Λ`-modules on `Y_étale` induces isomorphisms of `RΓ(Y_k̄, -|_{Y_k̄})`
intertwining the canonical Frobenius endomorphisms, and quasi-isomorphisms of the stalk
complexes intertwining the local Frobenius endomorphisms, the étale stalk being exact. Hence
perfectness of the stalks and the trace formula
`Stacks.EtaleCohomology.CohomologicalTraceFormula` are invariant under quasi-isomorphism, so they
only depend on the image of the complex in the derived category.

The standard model `HasDerivedCategory.standard` of the derived categories is used because the
consumed trace and Frobenius objects (`perfectDerivedTrace`, `frobeniusRestrictionCohomologyEndo`)
are defined there.

## Main results

* `Stacks.EtaleCohomology.hasPerfectStalks_iff_of_quasiIso`
* `Stacks.EtaleCohomology.cohomologicalTraceFormula_iff_of_quasiIso`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u

namespace Stacks.EtaleCohomology

section Standard

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable {Λ : Type} [Ring Λ]

/-- **The étale stalk preserves quasi-isomorphisms**: it is an exact functor. -/
theorem quasiIso_sheafFiber_map {X : Scheme.{u}} (s : GeometricPoint X)
    {K K' : CochainComplex (EtaleModules.{u, 0} Λ X) ℤ} (φ : K ⟶ K') [QuasiIso φ] :
    QuasiIso ((((Scheme.pointSmallEtale s.hom).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  have : AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    AlgebraicGeometry.aB5OfSize_moduleCat_of_univLE.{u, u + 1, 0} Λ
  have : PreservesFiniteLimits ((Scheme.pointSmallEtale s.hom).sheafFiber
    (A := ModuleCat.{u + 1} Λ)) := inferInstance
  have : ((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)).Additive :=
    Functor.additive_of_preserves_binary_products _
  infer_instance

/-- **Perfectness of the stalks is invariant under quasi-isomorphism.** -/
theorem hasPerfectStalks_iff_of_quasiIso {X : Scheme.{u}}
    {K K' : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)} (φ : K ⟶ K') [QuasiIso φ.hom] :
    HasPerfectStalks Λ K ↔ HasPerfectStalks Λ K' := by
  have hiso : ∀ s : GeometricPoint X, IsIso (DerivedCategory.Q.map
      ((((Scheme.pointSmallEtale s.hom).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).map φ.hom)) :=
    fun s => (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_sheafFiber_map s φ.hom)
  exact ⟨fun h s => StacksDraft.Perfect.isPerfect_of_iso
      (@asIso _ _ _ _ _ (hiso s)).symm (h s),
    fun h s => StacksDraft.Perfect.isPerfect_of_iso (@asIso _ _ _ _ _ (hiso s)) (h s)⟩

variable {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
  (hcard : Fintype.card k = p ^ q)

/-- **The trace formula is invariant under quasi-isomorphism.** -/
theorem cohomologicalTraceFormula_iff_of_quasiIso {Y : Over (Spec (.of k))}
    {C C' : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)} (φ : C ⟶ C') [QuasiIso φ.hom]
    (hC : HasPerfectStalks Λ C) (hC' : HasPerfectStalks Λ C') :
    CohomologicalTraceFormula Λ kbar p q hcard Y C hC ↔
      CohomologicalTraceFormula Λ kbar p q hcard Y C' hC' := by
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} Λ (fieldBaseChangeProj Y kbar)
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, 0} Λ (fieldBaseChangeProj Y kbar)
  have hq : QuasiIso (((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map φ).hom) :=
    inferInstanceAs (QuasiIso (((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj Y kbar)).mapHomologicalComplex (ComplexShape.up ℤ)).map φ.hom))
  have hR : IsIso ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar).map φ) := by
    have : IsIso (DerivedCategory.Plus.ι.map
        ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar).map φ)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
    exact isIso_of_reflects_iso _ DerivedCategory.Plus.ι
  let E := DerivedCategory.Plus.ι.mapIso
    ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).mapIso
        (@asIso _ _ _ _ _ hR)))
  have hcomm : DerivedCategory.Plus.ι.map
      (frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard C) ≫ E.hom =
        E.hom ≫ DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard C') := by
    simp only [E, Functor.mapIso_hom, asIso_hom, ← Functor.map_comp]
    exact congrArg DerivedCategory.Plus.ι.map
      (frobeniusRestrictionCohomologyEndo_naturality (Λ := Λ) Y kbar p q hcard φ).symm
  have hloc : ∀ (y : Spec (.of k) ⟶ Y.left) (h₁ h₂), perfectDerivedTrace Λ ⟨_, h₁⟩
      (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard y C)) =
        perfectDerivedTrace Λ ⟨_, h₂⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard y C')) := by
    intro y h₁ h₂
    have := quasiIso_sheafFiber_map (rationalGeometricPoint kbar y) φ.hom
    let sm : rationalPointStalkComplex.{u, 0} Λ kbar y C ⟶
        rationalPointStalkComplex.{u, 0} Λ kbar y C' :=
      ((rationalPointStalkFunctor.{u, 0} Λ kbar y).mapHomologicalComplex (ComplexShape.up ℤ)).map
        φ.hom
    have hs : IsIso (DerivedCategory.Q.map sm) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (inferInstanceAs (QuasiIso
        (((rationalPointStalkFunctor.{u, 0} Λ kbar y).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ.hom)))
    have h : rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard y C ≫ sm =
        sm ≫ rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard y C' :=
      ((NatTrans.mapHomologicalComplex
        (Stacks.Frobenius.geometricFrobeniusStalkFunctor (ModuleCat.{u + 1} Λ) kbar p q hcard y)
          (ComplexShape.up ℤ)).naturality φ.hom).symm
    refine perfectDerivedTrace_congr Λ _ _ (@asIso _ _ _ _ (DerivedCategory.Q.map sm) hs) _ _ ?_
    rw [asIso_hom, ← Functor.map_comp, ← Functor.map_comp, h]
  constructor
  · rintro ⟨hp, ht⟩
    have hp' := StacksDraft.Perfect.isPerfect_of_iso E.symm hp
    refine ⟨hp', fun {_} => ?_⟩
    refine (perfectDerivedTrace_congr Λ ⟨_, hp⟩ ⟨_, hp'⟩ E _ _ hcomm).symm.trans (ht.trans ?_)
    exact Fintype.sum_congr _ _ fun y => hloc _ _ _
  · rintro ⟨hp', ht⟩
    have hp := StacksDraft.Perfect.isPerfect_of_iso E hp'
    refine ⟨hp, fun {_} => ?_⟩
    refine (perfectDerivedTrace_congr Λ ⟨_, hp⟩ ⟨_, hp'⟩ E _ _ hcomm).trans (ht.trans ?_)
    exact Fintype.sum_congr _ _ fun y => (hloc _ _ _).symm

end Standard

end Stacks.EtaleCohomology

end
