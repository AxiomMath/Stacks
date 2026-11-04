module

public import StacksFrontier.Homology.Perfect.MinimalRepresentative
public import StacksFrontier.Homology.Perfect.Saturation
public import StacksFrontier.Homology.KFlat.Flat

/-!
# Vanishing of the cohomology of a fibre spreads out

Let `R` be a ring and `N` a bounded complex of flat `R`-modules which is perfect as an object of
`D(R)`. If the cohomology of `N ⊗_R κ(p)` vanishes in all degrees `≤ n` at a prime `p`, then there
is `f ∉ p` such that the cohomology of `N ⊗_R B` vanishes in all degrees `≤ n` for every
`R`-algebra `B` in which `f` is invertible.

This is the form in which cohomology and base change is used for a proper flat family: `N` is a
Čech complex, or a cone of Čech complexes, of modules flat over the base, and `N ⊗_R B` computes
the cohomology of the base change. The proof is [Stacks, Tag 0BYP]: after inverting one element
outside `p`, `N` is represented by a complex of finite free modules concentrated in degrees
`≥ n + 1`, and both `N ⊗_R B` and that complex compute the derived extension of scalars, the first
because a bounded above complex of flat modules is K-flat ([Stacks, Tag 064K]), the second because
its terms are projective.

## Main results

* `StacksDraft.Perfect.exists_away_isZero_homology_extendScalars_of_fibre`: the spreading out.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

universe u

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-- Termwise extension of scalars of a complex of modules. -/
abbrev extendScalarsCx {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) : CochainComplex (ModuleCat.{u} B) ℤ :=
  ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj N

/-- For a bounded above complex of flat modules the total derived extension of scalars is the
termwise one, so their cohomologies agree. -/
theorem nonempty_homology_totalDerived_iso_of_flat {R B : Type u} [CommRing R] [CommRing B]
    (φ : R →+* B) (N : CochainComplex (ModuleCat.{u} R) ℤ) (d : ℤ) [N.IsStrictlyLE d]
    [∀ i, Module.Flat R (N.X i)] (i : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
        ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj (DerivedCategory.Q.obj N)) ≅
      (extendScalarsCx φ N).homology i) := by
  let D := totalDerivedExtensionScalars.{u, u, u} φ
  have : IsIso (D.comparison.app N) :=
    D.comparison_isIso_of_kFlat N (CochainComplex.KFlat.kFlat_of_flat N d)
  exact ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).mapIso
    (asIso (D.comparison.app N)) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i).app (extendScalarsCx φ N)⟩

/-- **Vanishing of the cohomology of a fibre spreads out.** Let `N` be a bounded complex of flat
`R`-modules which is perfect in `D(R)`, `p` a prime of `R`, and assume that `N ⊗_R κ(p)` has no
cohomology in degrees `≤ n`. Then there is `f ∉ p` such that for every ring map `φ : R → B`
inverting `f`, the complex `N ⊗_R B` has no cohomology in degrees `≤ n`. -/
theorem exists_away_isZero_homology_extendScalars_of_fibre {R : Type u} [CommRing R]
    (N : CochainComplex (ModuleCat.{u} R) ℤ) (c d : ℤ) [N.IsStrictlyGE c] [N.IsStrictlyLE d]
    [∀ i, Module.Flat R (N.X i)] (hN : IsPerfect (DerivedCategory.Q.obj N))
    (p : Ideal R) [p.IsPrime] (n : ℤ)
    (h : ∀ i ≤ n, IsZero ((extendScalarsCx (algebraMap R p.ResidueField) N).homology i)) :
    ∃ f : R, f ∉ p ∧ ∀ {B : Type u} [CommRing B] (φ : R →+* B), IsUnit (φ f) →
      ∀ i ≤ n, IsZero ((extendScalarsCx φ N).homology i) := by
  let K := DerivedCategory.Q.obj N
  have hK : PseudoCoherence.IsPseudoCoherent K := isPseudoCoherent_of_isPerfect.{u, u} K hN
  obtain ⟨f, hf, -, P, b, hPge, hPle, hPX, ⟨eP⟩⟩ :=
    exists_away_bounded_free_complex_representing_of_fibre_vanishing_below.{u, u} p K hK
      ⟨c, inferInstance⟩ (n + 1) (fun i hi => (h i (by omega)).of_iso
        (nonempty_homology_totalDerived_iso_of_flat (algebraMap R p.ResidueField) N d i).some)
  refine ⟨f, hf, fun {B} _ φ hφ i hi => ?_⟩
  let ψ : Localization.Away f →+* B := IsLocalization.Away.lift f hφ
  have hψ : ψ.comp (algebraMap R (Localization.Away f)) = φ :=
    IsLocalization.Away.lift_comp f hφ
  obtain ⟨e₁⟩ := totalDerived_comp_of_isPseudoCoherent_of_eq.{u, u} hψ
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R (Localization.Away f)))
    (totalDerivedExtensionScalars.{u, u, u} ψ) (totalDerivedExtensionScalars.{u, u, u} φ) hK
  obtain ⟨e₂⟩ := nonempty_homology_totalDerived_iso_of_flat φ N d i
  have hPproj : ∀ j, Projective (P.X j) := fun j =>
    Projective.of_iso (hPX j).some.symm (ModuleCat.projective_of_free
      ((Pi.basisFun (Localization.Away f) _).map ULift.moduleEquiv.symm))
  obtain ⟨e₃⟩ := nonempty_homology_totalDerived_iso_of_flat ψ P b i
  exact ((extendScalarsCx ψ P).isZero_of_isGE (n + 1) i (by omega)).of_iso
    (e₂.symm ≪≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).mapIso
    (e₁.symm ≪≫ (totalDerivedExtensionScalars.{u, u, u} ψ).functor.mapIso eP.symm) ≪≫ e₃)

end StacksDraft.Perfect

end
