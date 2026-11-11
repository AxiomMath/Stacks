module

public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctionsFrom02O8
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.FormalFunctions
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksCore.Tactic.StacksAttribute

/-!
# Full faithfulness of the completion functor, unconditionally

**Stacks 0883.** Let `A` be a Noetherian ring complete with respect to an ideal `J`, let
`f : X ⟶ Spec A` be proper and put `𝓙 = J · 𝒪_X`. Then the completion functor

  `Coh(𝒪_X) ⥤ Coh(X, 𝓙)`

of Stacks 0880 is fully faithful.

`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionFunctor/FullyFaithful.lean` proves the
source's argument from Stacks 0882, leaving the theorem on formal functions in degree zero
(Stacks 087U) as a named hypothesis, and
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/FormalFunctions.lean` reduces
Stacks 087U, in every degree, to three inputs: the finiteness of `Hᵖ(X, F)` as an `A`-module
([Stacks, Tag 02O6]) and the two uniform Artin-Rees bounds of [Stacks, Tag 02OB]. This file
discharges all three and so removes the hypothesis.

* [Stacks, Tag 02O6] is `AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`,
  which carries no hypothesis. It concludes over `Γ(Spec A, 𝒪)` rather than over `A`, and the
  two differ by the ring isomorphism `A ≅ Γ(Spec A, 𝒪)`; the transfer is
  `Stacks.Algebraization.moduleFinite_cohomologyOverBase`, and the further transfer to the
  `A`-module structure the comparison map is stated against is
  `Stacks.Cohomology.FormalFunctions.cohomologyBaseEquiv`.
* [Stacks, Tag 02OB] is
  `Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8`
  with its hypothesis `h02O8` supplied by
  `Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem`, the quantified form of the
  unconditional [Stacks, Tag 02O8].

## Main results

* `Stacks.Algebraization.isIso_cohomologyToLimit_of_isProper_of_isAdicComplete` — the theorem on
  formal functions over a complete base, [Stacks, Tag 087U], in every degree and with nothing
  assumed beyond the source's hypotheses.
* `Stacks.Algebraization.isIso_globalSectionsToLimit_of_isProper` — its degree-zero case in the
  shape Stacks 0883 and Stacks 0885 consume.
* `Stacks.Algebraization.fullyFaithful_completionFunctor_of_isProper` — **Stacks 0883**.

## Implementation notes

The completion functor is `@[no_expose]`, so the identification of its `n`-th term with
`F / 𝓙ⁿ⁺¹ F` is available only as the equation `Stacks.Algebraization.completionFunctor_obj`
and not definitionally. The two statements that cross that boundary —
`Stacks.Algebraization.rightDerived_map_completionProjection` for the projections and
`Stacks.Algebraization.completionSystem_map_eq` for the transition maps — therefore carry
`eqToHom`s, and are proved in term mode with `congrArg`: the two presentations of the category
of modules on a scheme, `X.Modules` and `SheafOfModules X.ringCatSheaf`, make the rewrite
motives ill-typed at `implicit` transparency, exactly as in `CompletionFunctor/FullyFaithful.lean`.

The transition map of the completion tower is pinned by the fact that the projection onto the
`(n+1)`-st term is an epimorphism (`Stacks.Algebraization.epi_completionProjection`), so it is
the exponent-lowering map `Stacks.Algebraization.idealPowerQuotientDrop` conjugated by those
identifications.

## References

* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 087U](https://stacks.math.columbia.edu/tag/087U)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.AffineBase Stacks.Cohomology.FormalFunctions
open scoped AlgebraicGeometry ModuleCat.Algebra

universe u

namespace Stacks.Algebraization

attribute [local instance] Stacks.Cohomology.AffineBase.baseSectionsAlgebra

/-! ### Elementary transfers -/

/-- Finiteness of a module descends along a surjective ring map. -/
private theorem moduleFinite_of_surjective_ringHom {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) (M : Type u) [AddCommGroup M]
    [Module S M] [Module R M] (hsmul : ∀ (r : R) (x : M), r • x = φ r • x)
    (hfin : Module.Finite S M) : Module.Finite R M := by
  obtain ⟨s, hs⟩ := Module.finite_def.mp hfin
  refine Module.finite_def.mpr ⟨s, le_antisymm le_top ?_⟩
  intro x hxtop
  clear hxtop
  have hx : x ∈ Submodule.span S (s : Set M) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    obtain ⟨r, rfl⟩ := hφ c
    rw [← hsmul]
    exact Submodule.smul_mem _ r ha

/-- An `eqToHom` between modules is injective, read as a vanishing criterion. -/
private theorem eqToHom_hom_eq_zero_iff {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (e : M = N)
    (y : M) : (eqToHom e).hom y = 0 ↔ y = 0 := by
  subst e
  simp

/-! ### Finiteness of the cohomology over the base ring -/

section Finite

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- The structure map `A ⟶ Γ(Spec A, 𝒪)` is surjective, being the inverse of an isomorphism. -/
private theorem surjective_ΓSpecIso_inv :
    Function.Surjective (CommRingCat.Hom.hom (Scheme.ΓSpecIso (.of A)).inv) := fun y =>
  ⟨(Scheme.ΓSpecIso (.of A)).hom y, by
    simp⟩

/-- **[Stacks, Tag 02O6] over a ring base.** For `f : X ⟶ Spec A` proper with `A` Noetherian and
`F` coherent, `Hᵖ(X, F)` is a finite `A`-module for the action through `baseRingHom`. -/
public theorem moduleFinite_cohomologyOverBase [IsNoetherianRing A] [IsProper f]
    (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] (p : ℕ) :
    Module.Finite A ↥(cohomologyOverBase A f p F) :=
  @moduleFinite_of_surjective_ringHom A ↥Γ(Spec (.of A), ⊤) _ _
    (CommRingCat.Hom.hom (Scheme.ΓSpecIso (.of A)).inv) (surjective_ΓSpecIso_inv A)
    ↥(cohomologyOverBase A f p F) _
    ((ModuleCat.restrictScalars (Scheme.Hom.appTop f).hom).obj
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj F)).isModule
    _ (fun _ _ => rfl)
    (_root_.AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology f F p)

end Finite

/-! ### The completion tower read through the ideal-power quotients -/

section Transport

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- Cohomology of the projection onto the `n`-th term of the completion, written through the
quotient projection `F ⟶ F / 𝓘ⁿ⁺¹ F`. -/
public theorem rightDerived_map_completionProjection (p n : ℕ) :
    ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
        (completionProjection X I F n) =
      ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
          (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) F.obj).ι) ≫
        eqToHom (congrArg
          ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj
          (completionFunctor_obj X I F n).symm) :=
  (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map_comp
      (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) F.obj).ι)
      (eqToHom (completionFunctor_obj X I F n).symm)).trans
    (congrArg (fun k => ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) F.obj).ι) ≫ k)
      (eqToHom_map ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p)
        (completionFunctor_obj X I F n).symm))

/-- The transition maps of the completion tower are the exponent-lowering maps between the
ideal-power quotients, up to the identification of the terms. -/
public theorem completionSystem_map_eq {n m : ℕ} (h : n ≤ m) :
    ((completionFunctor X I).obj F).obj.map (homOfLE h).op =
      eqToHom (completionFunctor_obj X I F m) ≫
        idealPowerQuotientDrop I (Nat.add_le_add_right h 1) F.obj ≫
          eqToHom (completionFunctor_obj X I F n).symm :=
  have := epi_completionProjection X I F m
  (cancel_epi (C := X.Modules) (completionProjection X I F m)).1
    ((completionProjection_naturality_le X I F h).trans
      ((comp_eqToHom_symm_comp_eqToHom
            (cokernel.π (C := X.Modules) (idealPowerMultiple I (m + 1) F.obj).ι)
            (completionFunctor_obj X I F m)
            (idealPowerQuotientDrop I (Nat.add_le_add_right h 1) F.obj ≫
              eqToHom (completionFunctor_obj X I F n).symm)).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun k => k ≫ eqToHom (completionFunctor_obj X I F n).symm)
              (idealPowerQuotientDrop_π I (Nat.add_le_add_right h 1) F.obj)))).symm)

end Transport

/-! ### The theorem on formal functions over a complete base -/

section FormalFunctions

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (J : Ideal A) [IsAdicComplete J A]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]

/-- **The theorem on formal functions over a complete base, [Stacks, Tag 087U].** For `A`
Noetherian and complete with respect to `J`, `f : X ⟶ Spec A` proper and `F` coherent, the
comparison `Hᵖ(X, F) ⟶ limₙ Hᵖ(X, F / 𝓙ⁿ F)` is an isomorphism in every degree `p`.

This is `Stacks.Algebraization.isIso_cohomologyToLimit` with its three hypotheses discharged:
the finiteness of the cohomology by [Stacks, Tag 02O6], and the two uniform Artin-Rees bounds
by [Stacks, Tag 02OB] over the unconditional [Stacks, Tag 02O8].

This is the declaration [Stacks, Tag 087U] is registered on; the conditional statements of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/FormalFunctions.lean`, where the
comparison map and the reduction are built, are untagged. -/
@[stacks 087U "for all p ≥ 0: A Noetherian and J-adically complete, f : X ⟶ Spec A proper, \
F coherent; 02O6 and 02OB are proved theorems used in the proof",
  sga "2 IX 1.3" "The edge φ'_i"]
public theorem isIso_cohomologyToLimit_of_isProper_of_isAdicComplete
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (p : ℕ) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    IsIso (cohomologyToLimit (baseIdealSheaf A J f) F p) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let := baseAlgebra A f
  obtain ⟨c, hker, -, hrange⟩ :=
    exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8 A f ‹IsProper f› J F.obj
      (AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent F.property) p
      Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem
  refine isIso_cohomologyToLimit A J f F p ?_ ?_ ?_
  · have := moduleFinite_cohomologyOverBase A f F.obj p
    exact Module.Finite.equiv (cohomologyBaseEquiv A f F.obj p).symm
  · refine ⟨c, fun n x hx => ?_⟩
    rw [rightDerived_map_completionProjection (baseIdealSheaf A J f) F p (n + c)] at hx
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx
    have h1 : (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
        (cokernel.π (C := X.Modules)
          (idealPowerMultiple (baseIdealSheaf A J f) (n + c + 1) F.obj).ι)).hom x = 0 :=
      (eqToHom_hom_eq_zero_iff _ _).1 hx
    have h2 : x ∈ J ^ (n + c + 1 - c) •
        (⊤ : Submodule A ↥(cohomologyOverBase A f p F.obj)) :=
      hker (n + c + 1) (by omega) (LinearMap.mem_ker.2 h1)
    rw [show n + c + 1 - c = n + 1 from by omega] at h2
    have hle : J ^ (n + 1) • (⊤ : Submodule A ↥(cohomologyOverBase A f p F.obj)) ≤
        J ^ n • (⊤ : Submodule A ↥(cohomologyOverBase A f p F.obj)) :=
      Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) le_rfl
    have h3 : x ∈ J ^ n • (⊤ : Submodule A ↥(cohomologyOverBase A f p F.obj)) := hle h2
    exact Stacks.FormalFunctions.map_mem_pow_smul_top
      (cohomologyBaseEquiv A f F.obj p).symm.toLinearMap J n h3
  · refine ⟨c, fun n y => ?_⟩
    have hmap : (completionCohomologySystem (baseIdealSheaf A J f) F p).map
          (homOfLE (Nat.le_add_right n c)).op =
        eqToHom (congrArg
            ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj
            (completionFunctor_obj X (baseIdealSheaf A J f) F (n + c))) ≫
          ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
              (idealPowerQuotientDrop (baseIdealSheaf A J f)
                (Nat.add_le_add_right (Nat.le_add_right n c) 1) F.obj) ≫
            eqToHom (congrArg
              ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj
              (completionFunctor_obj X (baseIdealSheaf A J f) F n).symm) :=
      (congrArg ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
          (completionSystem_map_eq (baseIdealSheaf A J f) F (Nat.le_add_right n c))).trans
        (by simp only [Functor.map_comp, eqToHom_map])
    have h5 := hrange (n + 1) (n + c + 1) (by omega)
    have hmem : (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
          (idealPowerQuotientDrop (baseIdealSheaf A J f)
            (Nat.add_le_add_right (Nat.le_add_right n c) 1) F.obj)).hom
            ((eqToHom (congrArg
              ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj
              (completionFunctor_obj X (baseIdealSheaf A J f) F (n + c)))).hom y) ∈
        LinearMap.range (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
          (cokernel.π (C := X.Modules)
            (idealPowerMultiple (baseIdealSheaf A J f) (n + 1) F.obj).ι)).hom := by
      rw [← h5]
      exact ⟨_, rfl⟩
    obtain ⟨x, hx⟩ := hmem
    refine ⟨x, ?_⟩
    rw [rightDerived_map_completionProjection (baseIdealSheaf A J f) F p n, hmap]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [hx]

/-- **[Stacks, Tag 087U] in degree zero**, in the shape Stacks 0883 consumes: for `f` proper
over a Noetherian `J`-adically complete base, the comparison
`H⁰(X, F) ⟶ limₙ H⁰(X, F / 𝓙ⁿ F)` is an isomorphism for every coherent `F`. -/
public theorem isIso_globalSectionsToLimit_of_isProper
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    IsIso (globalSectionsToLimit (baseIdealSheaf A J f) F) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact isIso_globalSectionsToLimit_of_isIso_cohomologyToLimit _ F
    (isIso_cohomologyToLimit_of_isProper_of_isAdicComplete A J f F 0)

/-- **Stacks 0883.** Let `A` be a Noetherian ring complete with respect to an ideal `J`, let
`f : X ⟶ Spec A` be proper and let `𝓙 = J · 𝒪_X`. Then the completion functor
`Coh(𝒪_X) ⥤ Coh(X, 𝓙)` of Stacks 0880 is fully faithful. -/
@[stacks 0883]
public theorem fullyFaithful_completionFunctor_of_isProper :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    Nonempty (completionFunctor X (baseIdealSheaf A J f)).FullyFaithful := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact fullyFaithful_completionFunctor A J f
    fun H => isIso_globalSectionsToLimit_of_isProper A J f H

end FormalFunctions

end Stacks.Algebraization

end
