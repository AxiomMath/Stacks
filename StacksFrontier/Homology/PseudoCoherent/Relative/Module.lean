module

public import StacksFrontier.Homology.PseudoCoherent.Relative.Defs
public import StacksFrontier.Homology.PseudoCoherent.Module
public import StacksFrontier.RingTheory.FinitePresentation.Relative
public import StacksFrontier.Algebra.Module.FinitePresentationRel.Basic

@[expose] public section

/-!
# Relative pseudo-coherence of a module: finiteness and resolutions

The module forms of relative pseudo-coherence in low degrees, and the characterisation by
finite free resolutions.

## Main results

* `PseudoCoherence.moduleRelativelyPseudoCoherent_iff_finiteness_and_resolutions` (Stacks 0675).

## Implementation notes

One polynomial presentation at a time, reducing to tag 064T over the polynomial algebra.
064T is cluster 10's, in `Homology/PseudoCoherent/Module.lean`.

## References

* [The Stacks Project, Lemma 15.82.7 (0675)](https://stacks.math.columbia.edu/tag/0675)
-/

open CategoryTheory CategoryTheory.Limits
open StacksDraft.PseudoCoherence

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

/-!
# Relative pseudo-coherence of modules

Let `A` be a finite-type algebra over a commutative ring `R` and let `M` be an `A`-module.
Relative pseudo-coherence in degrees `0` and `-1` is characterized by finite generation over
`A` and finite presentation relative to `R`, respectively. In arbitrary nonpositive degree it is
characterized by finite free resolutions over every polynomial presentation of `A`, and relative
pseudo-coherence is characterized by infinite finite free resolutions over every such
presentation.

## Main definitions

There are no new definitions.

## Main results

* `moduleRelativelyPseudoCoherent_iff_finiteness_and_resolutions` gives the four
  characterizations of relative pseudo-coherence for modules.

## Implementation notes

A polynomial presentation is represented by a surjective `R`-algebra homomorphism from
`MvPolynomial (Fin n) R`. The module structure used in each resolution is restriction of scalars
along this homomorphism. Finite resolutions use
`HasFiniteFreeResolutionOfLength`, while infinite resolutions use
`FiniteFreeModuleResolution`. The rings and module lie in one universe, so restriction
of scalars and the finite free resolutions use the module itself.

## References

* [Stacks Project, Tag 0675](https://stacks.math.columbia.edu/tag/0675)
-/

private theorem pseudoCoherentFrom_of_iso {S : Type u} [Ring S]
    {K K' : DerivedCategory (ModuleCat.{u} S)} {m : ℤ}
    (hK : IsPseudoCoherentFrom K m) (e : K ≅ K') :
    IsPseudoCoherentFrom K' m := by
  obtain ⟨E, hE, α, hiso, hepi⟩ := hK
  refine ⟨E, hE, α ≫ e.hom, ?_, ?_⟩
  · intro i hi
    rw [Functor.map_comp]
    have := hiso i hi
    exact IsIso.comp_isIso
  · rw [Functor.map_comp]
    have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) m).map e.hom) :=
      IsIso.epi_of_iso _
    exact epi_comp _ _

private theorem restricted_single_pseudoCoherentFrom_iff
    {S : Type u} {A : Type u} [CommRing S] [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M]
    (f : S →+* A) (m : ℤ) :
    IsPseudoCoherentFrom
        ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A M))) m ↔
      @IsModulePseudoCoherentFrom S _ _ M _ (Module.compHom M f) m := by
  let : Module S M := Module.compHom M f
  let e := ((ModuleCat.restrictScalars.{u} f).mapDerivedCategorySingleFunctor 0).app
    (ModuleCat.of A M)
  exact ⟨fun h => pseudoCoherentFrom_of_iso h e, fun h => pseudoCoherentFrom_of_iso h e.symm⟩

private theorem finite_compHom_iff_of_surjective
    {S : Type u} {A : Type u} [CommRing S] [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M]
    (f : S →+* A) (hf : Function.Surjective f) :
    @Module.Finite S M _ _ (Module.compHom M f) ↔ Module.Finite A M := by
  let : Algebra S A := f.toAlgebra
  let : Module S M := Module.compHom M f
  let : IsScalarTower S A M := ⟨fun s a m => by
    show (f s * a) • m = f s • a • m
    rw [mul_smul]⟩
  refine ⟨fun _ => Module.Finite.of_restrictScalars_finite S A M, fun _ => ?_⟩
  have : Module.Finite S A := Module.Finite.of_surjective (Algebra.linearMap S A) hf
  exact Module.Finite.trans A M

/-- Tag 064T for `M` viewed as a module over `S` along a ring map `f : S →+* A`. -/
private theorem compHom_064T {S : Type u} {A : Type u} [CommRing S] [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] (f : S →+* A) :
    letI : Module S M := Module.compHom M f
    (IsModulePseudoCoherentFrom (R := S) M 0 ↔ Module.Finite S M) ∧
    (IsModulePseudoCoherentFrom (R := S) M (-1) ↔ Module.FinitePresentation S M) ∧
    (∀ d : ℕ, IsModulePseudoCoherentFrom (R := S) M (-(d : ℤ)) ↔
      HasFiniteFreeResolutionOfLength (R := S) M d) ∧
    (IsModulePseudoCoherent (R := S) M ↔ Nonempty (FiniteFreeModuleResolution S M)) :=
  @modulePseudoCoherent_iff_finiteness_and_resolutions_of_small S _ _ _ M _ (Module.compHom M f)

/-- Relative pseudo-coherence of a module in degree `0` is finite generation. -/
private theorem moduleRelativelyPseudoCoherentFrom_zero_iff
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (M : Type u) [AddCommGroup M] [Module A M] :
    IsModuleRelativelyPseudoCoherentFrom (R := R) (A := A) M 0 ↔ Module.Finite A M := by
  simp only [IsModuleRelativelyPseudoCoherentFrom, IsRelativelyPseudoCoherentFrom]
  refine ⟨fun h => ?_, fun h n α hα => ?_⟩
  · obtain ⟨n, α, hα⟩ :=
      (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp inferInstance
    have h064T := compHom_064T M α.toRingHom
    have hh := h n α hα
    rw [restricted_single_pseudoCoherentFrom_iff M α.toRingHom 0, h064T.1] at hh
    exact (finite_compHom_iff_of_surjective M α.toRingHom hα).mp hh
  · have h064T := compHom_064T M α.toRingHom
    rw [restricted_single_pseudoCoherentFrom_iff M α.toRingHom 0, h064T.1]
    exact (finite_compHom_iff_of_surjective M α.toRingHom hα).mpr h

/-- Relative pseudo-coherence of a module in degree `-1` is relative finite presentation. -/
private theorem moduleRelativelyPseudoCoherentFrom_neg_one_iff
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (M : Type u) [AddCommGroup M] [Module A M] :
    IsModuleRelativelyPseudoCoherentFrom (R := R) (A := A) M (-1) ↔
      Module.FinitePresentationRel R A M := by
  simp only [IsModuleRelativelyPseudoCoherentFrom, IsRelativelyPseudoCoherentFrom]
  refine ⟨fun h => ?_, fun h n α hα => ?_⟩
  · refine Module.FinitePresentationRel.finitePresentationRel_of_allPresentations fun n α hα => ?_
    have h064T := compHom_064T M α.toRingHom
    rw [← h064T.2.1, ← restricted_single_pseudoCoherentFrom_iff M α.toRingHom (-1)]
    exact h n α hα
  · have h064T := compHom_064T M α.toRingHom
    rw [restricted_single_pseudoCoherentFrom_iff M α.toRingHom (-1), h064T.2.1]
    exact Module.FinitePresentationRel.allPresentations_of_allFPCovers
      (Module.FinitePresentationRel.allFPCovers_of_finitePresentationRel h) n α hα

/-- Relative pseudo-coherence of a module in degree `-d` is the existence, over every
polynomial presentation, of a finite free resolution through degree `d`. -/
private theorem moduleRelativelyPseudoCoherentFrom_neg_nat_iff
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (M : Type u) [AddCommGroup M] [Module A M] (d : ℕ) :
    IsModuleRelativelyPseudoCoherentFrom (R := R) (A := A) M (-(d : ℤ)) ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α →
        @HasFiniteFreeResolutionOfLength _ _ M _ (Module.compHom M α.toRingHom) d := by
  simp only [IsModuleRelativelyPseudoCoherentFrom, IsRelativelyPseudoCoherentFrom]
  refine forall_congr' fun n => forall_congr' fun α => forall_congr' fun _ => ?_
  have h064T := compHom_064T M α.toRingHom
  rw [restricted_single_pseudoCoherentFrom_iff M α.toRingHom (-(d : ℤ)), h064T.2.2.1 d]

/-- Relative pseudo-coherence of a module is the existence, over every polynomial
presentation, of an infinite finite free resolution. -/
private theorem moduleRelativelyPseudoCoherent_iff_resolutions
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (M : Type u) [AddCommGroup M] [Module A M] :
    IsModuleRelativelyPseudoCoherent (R := R) (A := A) M ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α →
        Nonempty (@FiniteFreeModuleResolution _ _ M _ (Module.compHom M α.toRingHom)) := by
  simp only [IsModuleRelativelyPseudoCoherent, IsRelativelyPseudoCoherent]
  refine ⟨fun h n α hα => ?_, fun h m n α hα => ?_⟩
  · have h064T := compHom_064T M α.toRingHom
    rw [← h064T.2.2.2]
    exact (pseudoCoherent_iff_all _).mpr fun m =>
      (restricted_single_pseudoCoherentFrom_iff M α.toRingHom m).mp (h m n α hα)
  · have h064T := compHom_064T M α.toRingHom
    rw [restricted_single_pseudoCoherentFrom_iff M α.toRingHom m]
    exact (pseudoCoherent_iff_all _).mp (h064T.2.2.2.mpr (h n α hα)) m

/-- **Stacks 0675.** For a module over a finite-type `R`-algebra, relative
pseudo-coherence in degrees `0`, `-1`, and `-d` is equivalent respectively to finite
generation, relative finite presentation, and the existence over every polynomial presentation
of a finite free resolution through degree `d`. Relative pseudo-coherence is equivalent to the
existence over every polynomial presentation of an infinite finite free resolution. -/
@[stacks 0675]
public theorem moduleRelativelyPseudoCoherent_iff_finiteness_and_resolutions
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (M : Type u) [AddCommGroup M] [Module A M] :
    (IsModuleRelativelyPseudoCoherentFrom (R := R) (A := A) M 0 ↔
      Module.Finite A M) ∧
    (IsModuleRelativelyPseudoCoherentFrom (R := R) (A := A) M (-1) ↔
      Module.FinitePresentationRel R A M) ∧
    (∀ d : ℕ, IsModuleRelativelyPseudoCoherentFrom (R := R) (A := A)
      M (-(d : ℤ)) ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α →
        @HasFiniteFreeResolutionOfLength _ _ M _
          (Module.compHom M α.toRingHom) d) ∧
    (IsModuleRelativelyPseudoCoherent (R := R) (A := A) M ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α →
        Nonempty (@FiniteFreeModuleResolution _ _ M _
          (Module.compHom M α.toRingHom))) :=
  ⟨moduleRelativelyPseudoCoherentFrom_zero_iff M,
    moduleRelativelyPseudoCoherentFrom_neg_one_iff M,
    moduleRelativelyPseudoCoherentFrom_neg_nat_iff M,
    moduleRelativelyPseudoCoherent_iff_resolutions M⟩

end PseudoCoherence
