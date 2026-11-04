module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FormallyEtaleAffine
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FormallyEtale.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.EtaleDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Defs
public import StacksFrontier.RingTheory.Etale.Basic

/-!
# Étale is locally of finite presentation and formally étale

A morphism of schemes is étale if and only if it is locally of finite presentation and formally
étale.

## Main results

* `AlgebraicGeometry.etale_iff_locallyOfFinitePresentation_and_formallyEtale`: a morphism of
  schemes is étale if and only if it is locally of finite presentation and formally étale.

## References

* [Stacks Project, Tag 02HM](https://stacks.math.columbia.edu/tag/02HM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes is étale exactly when it is locally of finite presentation and formally
étale. -/
@[stacks 02HM,
  stacks 025K "étale iff the unique-lifting property, for a morphism locally of finite",
  ega "IV 17.3.2" "(ii) etale",
  ega "IV 17.6.1" "a) <=> d)",
  sga "3 XI 1.6" "étale case",
  sga "4 VII 1.1" "functorial criterion",
  ega "IV 17.3.1",
  sga "3 XI 1.1",
  sga "4½ Arcata 2.1.1" "more general"]
theorem etale_iff_locallyOfFinitePresentation_and_formallyEtale
    {X S : Scheme.{u}} (f : X ⟶ S) :
    Etale f ↔ (LocallyOfFinitePresentation f ∧ FormallyEtale f) := by
  refine ⟨fun hf => ⟨inferInstance, ?_⟩, fun ⟨hlfp, hformal⟩ => ?_⟩
  · have : Unramified f := ⟨fun x => ((etaleAt_iff_smoothAt_and_unramifiedAt f x).mp
      ((etale_iff_forall_etaleAt f).mp hf x)).2⟩
    exact formallyEtale_of_unramified_flat f
  · rw [HasRingHomProperty.iff_exists_appLE (P := @Etale)
      (RingHom.Etale.stableUnderComposition.stableUnderCompositionWithLocalizationAway
        (RingHom.Etale.propertyIsLocal.HoldsForLocalizationAway
          RingHom.Etale.containsIdentities)).1]
    intro x
    have hfp := RingHom.finitePresentation_stableUnderComposition
      |>.stableUnderCompositionWithLocalizationAway
        RingHom.finitePresentation_holdsForLocalizationAway
    obtain ⟨V, U, hx, hUV, -⟩ :=
      (HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
        hfp.left).mp hlfp x
    refine ⟨V, U, hx, hUV, ?_⟩
    have hgtop : (f.resLE V.1 U.1 hUV).appTop.hom.FormallyEtale := by
      show (Scheme.Γ.map (f.resLE V.1 U.1 hUV).op).hom.FormallyEtale
      exact (formallyEtale_iff_globalSectionsMap_formallyEtale (f.resLE V.1 U.1 hUV)).mp
        (FormallyEtale.resLE f U.1 V.1 hUV hformal)
    let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    exact RingHom.etale_algebraMap.mpr
      ((Algebra.formallyEtale_iff_etale Γ(S, V) Γ(X, U)
        (RingHom.finitePresentation_algebraMap.mp
          (f.finitePresentation_appLE V.2 U.2 hUV))).mp
        ((formallyEtale_respectsIso.arrow_mk_iso_iff
          (arrowResLEAppIso f V.1 U.1 hUV)).mp hgtop))

end AlgebraicGeometry

end
