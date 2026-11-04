module

public import StacksFrontier.Algebra.Homology.PseudoCoherentNakayamaModels
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
public import StacksFrontier.Homology.Perfect.NilpotentLifting
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived extension of scalars across models, and pseudo-coherence modulo a nilpotent ideal

Any two total derived extensions of scalars along `f : R →+* A`, built in any two pairs of models
of the derived categories, agree after the comparison equivalences of the models: both are left
derived functors of degreewise extension of scalars. As a consequence, Stacks 0H76 holds in any
models: derived extension of scalars along a surjection with nilpotent kernel preserves and
reflects pseudo-coherence.

## Main definitions

* `CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.modelIso`: two derived
  extensions of scalars agree up to the model comparison equivalences.

## Main results

* `StacksDraft.PseudoCoherence.isPseudoCoherentIn_totalDerivedExtensionScalars_iff`: along a
  surjection with nilpotent kernel, `K ⊗ᴸ_R S` is pseudo-coherent exactly when `K` is.
* `StacksDraft.PseudoCoherence.IsPseudoCoherentIn.of_totalDerivedExtensionScalars_quotient`:
  pseudo-coherence lifts along the reduction modulo a nilpotent ideal.
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.DerivedExtensionScalars StacksDraft.DerivedModel

universe u v w wR wA wR' wA'

namespace CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars

/-- **Derived extension of scalars does not depend on the models.** For derived extensions of
scalars `D` and `D'` along `f : R →+* A`, built in the models `hR, hA` and `hR', hA'` of the
derived categories, `D` followed by the comparison `hA → hA'` is the comparison `hR → hR'`
followed by `D'`, by uniqueness of left derived functors. -/
def modelIso {R : Type u} {A : Type w} [CommRing R] [CommRing A] {f : R →+* A}
    (hR : HasDerivedCategory.{wR} (ModuleCat.{max v u w} R))
    (hA : HasDerivedCategory.{wA} (ModuleCat.{max v u w} A))
    (hR' : HasDerivedCategory.{wR'} (ModuleCat.{max v u w} R))
    (hA' : HasDerivedCategory.{wA'} (ModuleCat.{max v u w} A))
    (D : @TotalDerivedExtensionScalars.{u, v, w, wR, wA} R A _ _ f hR hA)
    (D' : @TotalDerivedExtensionScalars.{u, v, w, wR', wA'} R A _ _ f hR' hA') :
    @TotalDerivedExtensionScalars.functor _ _ _ _ f hR hA D ⋙ (modelEquiv hA hA').functor ≅
      (modelEquiv hR hR').functor ⋙ @TotalDerivedExtensionScalars.functor _ _ _ _ f hR' hA' D' :=
  letI : (ModuleCat.extendScalars.{u, w, max v u w} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v u w, u, w} f).isLeftAdjoint
  leftDerivedModelIso (HomologicalComplex.quasiIso (ModuleCat.{max v u w} R) (ComplexShape.up ℤ))
    (@TotalDerivedExtensionScalars.comparison _ _ _ _ f hR hA D)
    (@TotalDerivedExtensionScalars.comparison _ _ _ _ f hR' hA' D') (modelCompQIso hR hR')
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft
      ((ModuleCat.extendScalars.{u, w, max v u w} f).mapHomologicalComplex (ComplexShape.up ℤ))
      (modelCompQIso hA hA'))

end CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars

namespace StacksDraft.PseudoCoherence

variable {R S : Type u} [CommRing R] [CommRing S]

/-- **Stacks 0H76**, in any models. Let `f : R →+* S` be surjective with nilpotent kernel and let
`D` be a derived extension of scalars along `f`. An object `K` of `D(R)` is pseudo-coherent
exactly when `K ⊗ᴸ_R S` is. -/
theorem isPseudoCoherentIn_totalDerivedExtensionScalars_iff
    [hR : HasDerivedCategory.{wR} (ModuleCat.{max v u} R)]
    [hS : HasDerivedCategory.{wA} (ModuleCat.{max v u} S)] {f : R →+* S}
    (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f))
    (D : TotalDerivedExtensionScalars.{u, v, u, wR, wA} f)
    (K : DerivedCategory (ModuleCat.{max v u} R)) :
    IsPseudoCoherentIn (D.functor.obj K) ↔ IsPseudoCoherentIn K := by
  let Dstd := @totalDerivedExtensionScalars.{u, u, v} R S _ _ f (HasDerivedCategory.standard _)
    (HasDerivedCategory.standard _)
  let e := TotalDerivedExtensionScalars.modelIso hR hS (HasDerivedCategory.standard _)
    (HasDerivedCategory.standard _) D Dstd
  rw [isPseudoCoherentIn_iff_isPseudoCoherent (h := hS) _ (HasDerivedCategory.standard _),
    isPseudoCoherentIn_iff_isPseudoCoherent (h := hR) _ (HasDerivedCategory.standard _),
    ← StacksDraft.Perfect.isPseudoCoherent_derivedExtensionScalars_iff f hf hnil]
  exact ⟨fun h => @IsPseudoCoherent.ofIso _ _ (_) _ _ h (e.app K),
    fun h => @IsPseudoCoherent.ofIso _ _ (_) _ _ h (e.app K).symm⟩

/-- **Pseudo-coherence lifts modulo a nilpotent ideal**, in any models. If `J` is a nilpotent
ideal of `R` and the derived reduction `K ⊗ᴸ_R R/J` of `K` is pseudo-coherent, then `K` is
pseudo-coherent. -/
@[sga "6 I 2.16.2" "(i), special case"]
theorem IsPseudoCoherentIn.of_totalDerivedExtensionScalars_quotient {J : Ideal R}
    [HasDerivedCategory.{wR} (ModuleCat.{max v u} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v u} (R ⧸ J))] (hJ : IsNilpotent J)
    (Dq : TotalDerivedExtensionScalars.{u, v, u, wR, wA} (Ideal.Quotient.mk J))
    {K : DerivedCategory (ModuleCat.{max v u} R)} (hK : IsPseudoCoherentIn (Dq.functor.obj K)) :
    IsPseudoCoherentIn K :=
  (isPseudoCoherentIn_totalDerivedExtensionScalars_iff Ideal.Quotient.mk_surjective
    (by rwa [Ideal.mk_ker]) Dq K).1 hK

end StacksDraft.PseudoCoherence
