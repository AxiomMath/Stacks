module

public import StacksFrontier.Algebra.Homology.ProjectiveHomologyBaseChange
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.Perfect.MinimalChainModel
public import StacksFrontier.RingTheory.Dualizing.DerivedLocalization

/-!
# Localized cohomology of a base change, at a prime where the cohomology is free

Let `P^•` be a bounded above complex of projective `A`-modules, `φ : A → B` a ring map, `q` a
prime of `B` and `p = φ⁻¹(q)`.  If every localized cohomology module `H^i(P^•)_p` is free over
`A_p`, then `H^n(P^• ⊗_A B)_q` is a free `B_q`-module of the same rank as `H^n(P^•)_p`.

Over `A_p` the complex `P^• ⊗_A A_p` has projective terms and projective cohomology, so its
cohomology commutes with every base change
(`HomologicalComplex.mapHomologyIsoOfProjective`), in particular with `- ⊗_{A_p} B_q`; and
localization at `p` and at `q` is exact.

## Main results

* `StacksDraft.Perfect.free_finrank_localizedModule_homology_baseChange`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace StacksDraft.Perfect

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Extension of scalars, as a left adjoint, preserves finite colimits. -/
private theorem extendScalars_preservesFiniteColimits {R S : Type u} [CommRing R] [CommRing S]
    (g : R →+* S) : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} g) :=
  have : PreservesColimitsOfSize.{0, 0} (ModuleCat.extendScalars.{u, u, u} g) :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Extension of scalars along a flat ring map preserves finite limits and finite colimits. -/
private theorem extendScalars_exact_of_flat {R S : Type u} [CommRing R] [CommRing S]
    (g : R →+* S) (hg : g.Flat) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} g) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} g) := by
  exact ⟨extendScalars_preservesFiniteLimits_of_flat' g hg, extendScalars_preservesFiniteColimits g⟩

/-- The cohomology of the localization of a complex is the localization of its cohomology. -/
private def localizedHomologyLinearEquiv {R : Type u} [CommRing R] (T : Submonoid R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (baseChangeComplex (algebraMap R (Localization T)) P).homology n ≃ₗ[Localization T]
      LocalizedModule T (P.homology n) :=
  haveI := (extendScalars_exact_of_flat (algebraMap R (Localization T))
    (RingHom.flat_algebraMap_iff.mpr inferInstance)).1
  haveI := (extendScalars_exact_of_flat (algebraMap R (Localization T))
    (RingHom.flat_algebraMap_iff.mpr inferInstance)).2
  ((StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
      (ModuleCat.extendScalars (algebraMap R (Localization T))) (ComplexShape.up ℤ) n).app P ≪≫
    (Dualizing.extendScalarsIsoLocalizedModuleFunctor.{u, u} T).app
      (P.homology n)).toLinearEquiv.trans (Shrink.linearEquiv (Localization T) _)

/-- **Localized cohomology of a base change, where the cohomology is free.**  Let `P^•` be a
bounded above complex of projective `A`-modules, `φ : A → B` a ring map, `q` a prime of `B` and
`p = φ⁻¹(q)`.  If every `H^i(P^•)_p` is free over `A_p`, then `H^n(P^• ⊗_A B)_q` is free over
`B_q`, of the rank of `H^n(P^•)_p`. -/
theorem free_finrank_localizedModule_homology_baseChange (φ : A →+* B)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (hP : ∀ i, Module.Projective A (P.X i)) (q : Ideal B) [q.IsPrime]
    (hfree : ∀ i, Module.Free (Localization.AtPrime (q.comap φ))
      (LocalizedModule (q.comap φ).primeCompl (P.homology i))) (n : ℤ) :
    Module.Free (Localization.AtPrime q)
        (LocalizedModule q.primeCompl ((baseChangeComplex φ P).homology n)) ∧
      Module.finrank (Localization.AtPrime q)
          (LocalizedModule q.primeCompl ((baseChangeComplex φ P).homology n)) =
        Module.finrank (Localization.AtPrime (q.comap φ))
          (LocalizedModule (q.comap φ).primeCompl (P.homology n)) := by
  set p := q.comap φ
  let ψ := algebraMap A (Localization.AtPrime p)
  let χ := algebraMap B (Localization.AtPrime q)
  let lam : Localization.AtPrime p →+* Localization.AtPrime q :=
    Localization.localRingHom p q φ rfl
  have hlam : lam.comp ψ = χ.comp φ :=
    RingHom.ext fun a => Localization.localRingHom_to_map p q φ rfl a
  let K := baseChangeComplex ψ P
  have : K.IsStrictlyLE b := by
    dsimp only [K, baseChangeComplex]
    infer_instance
  have hKX : ∀ i, Projective (K.X i) := fun i =>
    have := hP i
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} ψ).map_projective (P.X i) inferInstance
  have hKH : ∀ i, Projective (K.homology i) := fun i => by
    have := hfree i
    have : Module.Projective (Localization.AtPrime p)
        (LocalizedModule p.primeCompl (P.homology i)) := Module.Projective.of_free
    have : Module.Projective (Localization.AtPrime p) (K.homology i) :=
      Module.Projective.of_equiv (localizedHomologyLinearEquiv p.primeCompl P i).symm
    infer_instance
  have : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} lam) :=
    extendScalars_preservesFiniteColimits lam
  -- the localized cohomology of `P ⊗ B` at `q` is the base change of `H^n(P ⊗ A_p)` to `B_q`
  let e : LocalizedModule q.primeCompl ((baseChangeComplex φ P).homology n) ≃ₗ[
      Localization.AtPrime q]
      (ModuleCat.extendScalars lam).obj (K.homology n) :=
    (localizedHomologyLinearEquiv q.primeCompl (baseChangeComplex φ P) n).symm.trans
      (((HomologicalComplex.homologyFunctor _ _ n).mapIso
        (baseChangeComplexCompIso φ χ P ≪≫ eqToIso (by rw [← hlam]) ≪≫
          (baseChangeComplexCompIso ψ lam P).symm) ≪≫
        HomologicalComplex.mapHomologyIsoOfProjective K (ModuleCat.extendScalars lam) b hKX hKH
          n).toLinearEquiv)
  let e₀ := localizedHomologyLinearEquiv p.primeCompl P n
  have := hfree n
  have : Module.Free (Localization.AtPrime p) (K.homology n) := Module.Free.of_equiv e₀.symm
  let := lam.toAlgebra
  have hfreeT : Module.Free (Localization.AtPrime q)
      ((ModuleCat.extendScalars lam).obj (K.homology n)) :=
    inferInstanceAs (Module.Free _ (TensorProduct (Localization.AtPrime p)
      (Localization.AtPrime q) (K.homology n)))
  refine ⟨Module.Free.of_equiv e.symm, ?_⟩
  rw [e.finrank_eq, ← e₀.finrank_eq]
  exact Module.finrank_baseChange

end StacksDraft.Perfect

end
