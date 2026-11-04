module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesFiniteConsequence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FullyFaithfulComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.FormalFunctions
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.RingBase

/-!
# The theorem on formal functions over a complete base, with nothing assumed

**Stacks 087U.** Let `A` be a Noetherian ring complete with respect to an ideal `J`, let
`f : X ⟶ Spec A` be proper and let `F` be a coherent sheaf on `X`. Then

  `Hᵖ(X, F) = limₙ Hᵖ(X, F / Jⁿ F)`

for every `p ≥ 0`.

`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/FormalFunctions.lean` proves this
from three inputs, carried there as the hypotheses `hfin`, `hker` and `hstab`. All three are now
theorems of this library:

* `hfin` is [Stacks, Tag 02O6], `AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`;
* `hker` and `hstab` are the two uniform Artin-Rees bounds of [Stacks, Tag 02OB],
  `Stacks.Cohomology.FormalFunctions`
  `.exists_uniform_bound_cohomology_idealPowerQuotient_unconditional`.

This file discharges all three and states the tag with no hypothesis beyond the source's.

## Main results

* `Stacks.Algebraization.moduleFinite_cohomology_of_isProper` — [Stacks, Tag 02O6] in the
  `A`-module structure that `Stacks.Algebraization.baseAlgebra` puts on the cohomology.
* `Stacks.Algebraization.exists_kernelBound_rightDerived_completionProjection` and
  `Stacks.Algebraization.exists_stableImage_rightDerived_completionProjection` — the two uniform
  bounds of [Stacks, Tag 02OB], in the shape
  `Stacks.Algebraization.isIso_cohomologyToLimit` consumes them.
* `Stacks.Algebraization.isIso_cohomologyToLimit_unconditional` — **Stacks 087U** for every
  `p ≥ 0`, with no hypothesis.

## Implementation notes

[Stacks, Tag 02OB] and [Stacks, Tag 087U] speak about the same maps in two spellings, and the
whole work of this file is the identification.

*The maps.* The `n`-th term of the completion functor is `F / 𝓘ⁿ⁺¹ F`, but only up to the
propositional equality `Stacks.Algebraization.completionFunctor_obj`: `completionFunctor` is
`no_expose`, so the term `((completionFunctor X I).obj F).obj.obj (op n)` cannot be unfolded, and
`Stacks.Algebraization.completionProjection` is by definition the quotient projection followed by
the `eqToHom` of that equality. `completionTermInv` names that `eqToHom`;
`completionTermInv_comp_map` says that it carries the transition map of the completion system to
the exponent-lowering map `idealPowerQuotientDrop` of [Stacks, Tag 02OB], which is what makes the
two spellings of the tower agree. Both are proved by cancelling the quotient projection, which is
an epimorphism, and appealing to
`Stacks.Algebraization.completionProjection_naturality_le`.

*The scalars.* The two `A`-module structures on `Hᵖ(X, F)` — restriction of scalars along
`baseRingHom`, which [Stacks, Tag 02OB] uses, and the `baseSectionsAlgebra` structure, which
[Stacks, Tag 087U] uses — are not definitionally equal; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/FormalFunctions/FormalFunctionsFrom02O8.lean`. They are identified
by `Stacks.Cohomology.FormalFunctions.cohomologyBaseEquiv`, and the submodule `Jⁿ · Hᵖ(X, F)` is
transported across it by `mem_pow_smul_top_cohomology`, the converse of
`Stacks.Cohomology.FormalFunctions.mem_pow_smul_top_cohomologyOverBase`.

*The index shift.* The completion system is zero-indexed with `n`-th term `F / 𝓘ⁿ⁺¹ F`, while
[Stacks, Tag 02OB] is indexed by the exponent. Clause (1) of [Stacks, Tag 02OB] is therefore
applied at the exponent `n + c + 1`, where its bound reads `Jⁿ⁺¹`, and the kernel bound asked for
by [Stacks, Tag 087U] follows because `Jⁿ⁺¹ ⊆ Jⁿ`; clause (3) is applied at the exponents `n + 1`
and `n + c + 1`.

## References

* [Stacks Project, Tag 087U](https://stacks.math.columbia.edu/tag/087U)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry hiding moduleGlobalSections
open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry ModuleCat.Algebra
open Stacks.AlgebraicGeometry.IdealPower

universe u

namespace Stacks.Algebraization

open Stacks.Cohomology.AffineBase Stacks.Cohomology.FormalFunctions
open Stacks.AlgebraicGeometry.ProperCohomologyFinite

/-! ### The terms of the completion as ideal-power quotients -/

section Terms

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- The identification of `F / 𝓘ⁿ⁺¹ F` with the `n`-th term of the completion of `F`.

This is the `eqToHom` factor of `Stacks.Algebraization.completionProjection`. It cannot be
avoided: `Stacks.Algebraization.completionFunctor` is `no_expose`, so the `n`-th term of the
completion is not an ideal-power quotient by unfolding, only by
`Stacks.Algebraization.completionFunctor_obj`. -/
public abbrev completionTermInv (n : ℕ) :
    idealPowerQuotient I (n + 1) F.obj ⟶ ((completionFunctor X I).obj F).obj.obj (op n) :=
  eqToHom (completionFunctor_obj X I F n).symm

/-- The inverse identification, from the `n`-th term of the completion to `F / 𝓘ⁿ⁺¹ F`. -/
public abbrev completionTermHom (n : ℕ) :
    ((completionFunctor X I).obj F).obj.obj (op n) ⟶ idealPowerQuotient I (n + 1) F.obj :=
  eqToHom (completionFunctor_obj X I F n)

/-- The two identifications of the `n`-th term of the completion are inverse to each other. -/
public theorem completionTermHom_comp_inv (n : ℕ) :
    completionTermHom I F n ≫ completionTermInv I F n = 𝟙 _ := by
  simp

/-- The two identifications of the `n`-th term of the completion are inverse to each other, in
the other order. -/
public theorem completionTermInv_comp_hom (n : ℕ) :
    completionTermInv I F n ≫ completionTermHom I F n = 𝟙 _ := by
  simp

/-- **The projection onto the `n`-th term of the completion is the quotient projection**, read
through the identification of that term with `F / 𝓘ⁿ⁺¹ F`. This is the definition of
`Stacks.Algebraization.completionProjection`. -/
public theorem completionProjection_eq_completionTermInv (n : ℕ) :
    completionProjection X I F n =
      cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) F.obj).ι ≫
        completionTermInv I F n :=
  rfl

/-- **The transition maps of the completion system are the exponent-lowering maps of
[Stacks, Tag 02OB]**, under the identification of the terms with the ideal-power quotients.

Both composites are determined by their restriction along the quotient projection, which is an
epimorphism, and there both are the projection onto `F / 𝓘ⁿ⁺¹ F`. -/
public theorem completionTermInv_comp_map {m n : ℕ} (h : n ≤ m) :
    completionTermInv I F m ≫ ((completionFunctor X I).obj F).obj.map (homOfLE h).op =
      idealPowerQuotientDrop I (Nat.add_le_add_right h 1) F.obj ≫ completionTermInv I F n := by
  have hepi : Epi (cokernel.π (C := X.Modules) (idealPowerMultiple I (m + 1) F.obj).ι) :=
    coequalizer.π_epi
  refine (@cancel_epi _ _ _ _ _ _ hepi _ _).1 ?_
  exact (Category.assoc _ _ _).symm.trans
    ((completionProjection_naturality_le X I F h).trans
      ((congrArg (fun k => k ≫ completionTermInv I F n)
          (idealPowerQuotientDrop_π I (Nat.add_le_add_right h 1) F.obj)).symm.trans
        (Category.assoc _ _ _)))

/-! ### The same identifications after applying cohomology -/

variable (p : ℕ)

/-- `Hᵖ` of the projection onto the `n`-th term of the completion, factored through the
ideal-power quotient. -/
public theorem rightDerived_completionProjection (n : ℕ) :
    ((moduleGlobalSections X).rightDerived p).map (completionProjection X I F n) =
      ((moduleGlobalSections X).rightDerived p).map
          (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) F.obj).ι) ≫
        ((moduleGlobalSections X).rightDerived p).map (completionTermInv I F n) :=
  ((moduleGlobalSections X).rightDerived p).map_comp _ _

/-- `Hᵖ` of the quotient projection, recovered from `Hᵖ` of the projection onto the `n`-th term
of the completion. -/
public theorem rightDerived_cokernelπ (n : ℕ) :
    ((moduleGlobalSections X).rightDerived p).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) F.obj).ι) =
      ((moduleGlobalSections X).rightDerived p).map (completionProjection X I F n) ≫
        ((moduleGlobalSections X).rightDerived p).map (completionTermHom I F n) :=
  ((((moduleGlobalSections X).rightDerived p).map_comp
        (completionProjection X I F n) (completionTermHom I F n)).symm.trans
    (congrArg ((moduleGlobalSections X).rightDerived p).map
      (((Category.assoc _ _ _).trans
          (congrArg (fun k => cokernel.π (C := X.Modules)
              (idealPowerMultiple I (n + 1) F.obj).ι ≫ k)
            (completionTermInv_comp_hom I F n))).trans (Category.comp_id _)))).symm

/-- **A class dies in the `n`-th term of the completion exactly when it dies in
`F / 𝓘ⁿ⁺¹ F`.** The two differ by an isomorphism. -/
public theorem rightDerived_completionProjection_apply_eq_zero_iff (n : ℕ)
    (x : ↥(((moduleGlobalSections X).rightDerived p).obj F.obj)) :
    (((moduleGlobalSections X).rightDerived p).map (completionProjection X I F n)).hom x = 0 ↔
      (((moduleGlobalSections X).rightDerived p).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) F.obj).ι)).hom x = 0 := by
  constructor <;> intro hx
  · rw [ConcreteCategory.congr_hom (rightDerived_cokernelπ I F p n) x]
    simp [hx]
  · rw [ConcreteCategory.congr_hom (rightDerived_completionProjection I F p n) x]
    simp [hx]

/-- **The transition maps of the system of cohomology modules of the completion are the
exponent-lowering maps of [Stacks, Tag 02OB]**, conjugated by the identifications of the terms
with the ideal-power quotients. -/
public theorem rightDerived_completionSystem_map {m n : ℕ} (h : n ≤ m) :
    (completionCohomologySystem I F p).map (homOfLE h).op =
      ((moduleGlobalSections X).rightDerived p).map (completionTermHom I F m) ≫
        ((moduleGlobalSections X).rightDerived p).map
            (idealPowerQuotientDrop I (Nat.add_le_add_right h 1) F.obj) ≫
          ((moduleGlobalSections X).rightDerived p).map (completionTermInv I F n) := by
  have hmor : completionTermHom I F m ≫
      idealPowerQuotientDrop I (Nat.add_le_add_right h 1) F.obj ≫ completionTermInv I F n =
      ((completionFunctor X I).obj F).obj.map (homOfLE h).op :=
    ((congrArg (fun k => completionTermHom I F m ≫ k)
          (completionTermInv_comp_map I F h).symm).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ ((completionFunctor X I).obj F).obj.map (homOfLE h).op)
            (completionTermHom_comp_inv I F m)))).trans (Category.id_comp _)
  exact (congrArg ((moduleGlobalSections X).rightDerived p).map hmor).symm.trans
    ((((moduleGlobalSections X).rightDerived p).map_comp _ _).trans
      (congrArg (fun k => ((moduleGlobalSections X).rightDerived p).map
          (completionTermHom I F m) ≫ k)
        (((moduleGlobalSections X).rightDerived p).map_comp _ _)))

/-- **The stable-image bound, transported to the completion system.** If the image of the
exponent-lowering map `Hᵖ(X, F / 𝓘ᵐ⁺¹ F) ⟶ Hᵖ(X, F / 𝓘ⁿ⁺¹ F)` is contained in the image of
`Hᵖ(X, F)`, then every class in the `m`-th term of the system of cohomology modules of the
completion has its image in the `n`-th term coming from `Hᵖ(X, F)`. -/
public theorem exists_rightDerived_completionProjection_eq_of_range {m n : ℕ} (h : n ≤ m)
    (hr : LinearMap.range (((moduleGlobalSections X).rightDerived p).map
        (idealPowerQuotientDrop I (Nat.add_le_add_right h 1) F.obj)).hom ≤
      LinearMap.range (((moduleGlobalSections X).rightDerived p).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) F.obj).ι)).hom)
    (y : ↥((completionCohomologySystem I F p).obj (op m))) :
    ∃ x : ↥(((moduleGlobalSections X).rightDerived p).obj F.obj),
      (((moduleGlobalSections X).rightDerived p).map (completionProjection X I F n)).hom x =
        ((completionCohomologySystem I F p).map (homOfLE h).op).hom y := by
  obtain ⟨x, hx⟩ := hr ⟨(((moduleGlobalSections X).rightDerived p).map
    (completionTermHom I F m)).hom y, rfl⟩
  refine ⟨x, ?_⟩
  calc (((moduleGlobalSections X).rightDerived p).map (completionProjection X I F n)).hom x
      = (((moduleGlobalSections X).rightDerived p).map (completionTermInv I F n)).hom
          ((((moduleGlobalSections X).rightDerived p).map
            (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) F.obj).ι)).hom x) :=
        ConcreteCategory.congr_hom (rightDerived_completionProjection I F p n) x
    _ = (((moduleGlobalSections X).rightDerived p).map (completionTermInv I F n)).hom
          ((((moduleGlobalSections X).rightDerived p).map
            (idealPowerQuotientDrop I (Nat.add_le_add_right h 1) F.obj)).hom
              ((((moduleGlobalSections X).rightDerived p).map
                (completionTermHom I F m)).hom y)) := by rw [hx]
    _ = ((completionCohomologySystem I F p).map (homOfLE h).op).hom y :=
        (ConcreteCategory.congr_hom (rightDerived_completionSystem_map I F p h) y).symm

end Terms

/-! ### The two `A`-module structures on the cohomology -/

attribute [local instance] baseSectionsAlgebra

section Scalars

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (J : Ideal A)
  (F : X.Modules) (p : ℕ)

/-- **`Jᵐ · Hᵖ(X, F)` for the `cohomologyOverBase` structure lands in `Jᵐ · Hᵖ(X, F)` for the
`baseSectionsAlgebra` structure.**

This is the converse of
`Stacks.Cohomology.FormalFunctions.mem_pow_smul_top_cohomologyOverBase`, with the same proof: the
generators `a • x` agree by `Stacks.Cohomology.FormalFunctions.cohomologyBaseEquiv`, so the
induction on membership in a product of an ideal and a submodule goes through. -/
public lemma mem_pow_smul_top_cohomology (m : ℕ) (y : cohomologyOverBase A f p F)
    (hy : y ∈ J ^ m • (⊤ : Submodule A (cohomologyOverBase A f p F))) :
    (cohomologyBaseEquiv A f F p).symm y ∈
      J ^ m • (⊤ : Submodule A (cohomology (Over.mk f) F p)) := by
  refine Submodule.smul_induction_on hy (fun a ha z _ => ?_) fun z w hz hw => ?_
  · rw [map_smul]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [map_add]
    exact add_mem hz hw

end Scalars

/-! ### The three inputs of Stacks 087U -/

section Inputs

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (J : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) [IsProper f]
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (p : ℕ)

/-- **[Stacks, Tag 02O6], with no hypothesis, in the `A`-module structure that
`Stacks.Algebraization.baseAlgebra` puts on the cohomology.** For `A` Noetherian,
`f : X ⟶ Spec A` proper and `F` coherent, `Hᵖ(X, F)` is a finite `A`-module.

`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology` states the finiteness over
`Γ(Spec A, ⊤)`; it is moved to `A` across the surjective ring map `Scheme.ΓSpecIso`, exactly as
in `…ProperCohomologyFinite.moduleFinite_cohomology_ringBase_of_isCoherent`,
and then to the `baseSectionsAlgebra` structure along
`Stacks.Cohomology.FormalFunctions.cohomologyBaseEquiv`. -/
public theorem moduleFinite_cohomology_of_isProper :
    Module.Finite A (cohomology (Over.mk f) F.obj p) := by
  have hco : F.obj.IsCoherent := F.property
  have hΓ := AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology f F.obj p
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
  have hA : Module.Finite A (cohomologyOverBase A f p F.obj) :=
    moduleFinite_compHom_of_surjective (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom hsurj
      ((ModuleCat.restrictScalars f.appTop.hom).obj
        (((moduleGlobalSections X).rightDerived p).obj F.obj))
  exact Module.Finite.equiv (cohomologyBaseEquiv A f F.obj p).symm

/-- **The uniform kernel bound of [Stacks, Tag 02OB], with no hypothesis, in the shape
`Stacks.Algebraization.isIso_cohomologyToLimit` consumes it.** There is one `c` such that a class
in `Hᵖ(X, F)` dying in the `(n + c)`-th term of the completion lies in `Jⁿ · Hᵖ(X, F)`.

Clause (1) of
`Stacks.Cohomology.FormalFunctions`
`.exists_uniform_bound_cohomology_idealPowerQuotient_unconditional` at the
exponent `n + c + 1` bounds the kernel by `Jⁿ⁺¹ · Hᵖ(X, F)`, which is contained in
`Jⁿ · Hᵖ(X, F)`. -/
public theorem exists_kernelBound_rightDerived_completionProjection [IsLocallyNoetherian X] :
    ∃ c : ℕ, ∀ (n : ℕ) (x : cohomology (Over.mk f) F.obj p),
      (((moduleGlobalSections X).rightDerived p).map
          (completionProjection X (baseIdealSheaf A J f) F (n + c))).hom x = 0 →
        x ∈ J ^ n • (⊤ : Submodule A (cohomology (Over.mk f) F.obj p)) := by
  obtain ⟨c, hker, -, -⟩ :=
    exists_uniform_bound_cohomology_idealPowerQuotient_unconditional A f inferInstance J F.obj
      ⟨F.property.1, F.property.2⟩ p
  refine ⟨c, fun n x hx => ?_⟩
  have hx1 : (((moduleGlobalSections X).rightDerived p).map
      (cokernel.π (C := X.Modules)
        (idealPowerMultiple (baseIdealSheaf A J f) (n + c + 1) F.obj).ι)).hom x = 0 :=
    (rightDerived_completionProjection_apply_eq_zero_iff (baseIdealSheaf A J f) F p (n + c) x).1 hx
  have h2 := hker (n + c + 1) (by omega) (LinearMap.mem_ker.2 hx1)
  rw [show n + c + 1 - c = n + 1 by omega] at h2
  exact mem_pow_smul_top_cohomology A f J F.obj p n x
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)) h2)

/-- **The uniform stable-image bound of [Stacks, Tag 02OB], with no hypothesis, in the shape
`Stacks.Algebraization.isIso_cohomologyToLimit` consumes it.** There is one `c` such that the
image of the transition map from the `(n + c)`-th to the `n`-th term of the system of cohomology
modules of the completion is contained in the image of `Hᵖ(X, F)`.

Clause (3) of
`Stacks.Cohomology.FormalFunctions`
`.exists_uniform_bound_cohomology_idealPowerQuotient_unconditional` at the
exponents `n + 1` and `n + c + 1` says exactly that, for the exponent-lowering maps; the two
spellings are identified by
`Stacks.Algebraization.exists_rightDerived_completionProjection_eq_of_range`. -/
public theorem exists_stableImage_rightDerived_completionProjection [IsLocallyNoetherian X] :
    ∃ c : ℕ, ∀ (n : ℕ)
      (y : ↥((completionCohomologySystem (baseIdealSheaf A J f) F p).obj (op (n + c)))),
      ∃ x : ↥(((moduleGlobalSections X).rightDerived p).obj F.obj),
        (((moduleGlobalSections X).rightDerived p).map
            (completionProjection X (baseIdealSheaf A J f) F n)).hom x =
          ((completionCohomologySystem (baseIdealSheaf A J f) F p).map
            (homOfLE (Nat.le_add_right n c)).op).hom y := by
  obtain ⟨c, -, -, hrange⟩ :=
    exists_uniform_bound_cohomology_idealPowerQuotient_unconditional A f inferInstance J F.obj
      ⟨F.property.1, F.property.2⟩ p
  refine ⟨c, fun n y => exists_rightDerived_completionProjection_eq_of_range
    (baseIdealSheaf A J f) F p (Nat.le_add_right n c) ?_ y⟩
  exact (hrange (n + 1) (n + c + 1) (by omega)).le

end Inputs

/-! ### Stacks 087U with no hypothesis -/

section Main

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (J : Ideal A) [IsAdicComplete J A]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (p : ℕ)

/-- **The theorem on formal functions over a complete base, with no hypothesis**, stated with
local Noetherianity of `X` as an instance.

`AlgebraicGeometry.IsLocallyNoetherian` is a `Prop`, so this and
`Stacks.Algebraization.isIso_cohomologyToLimit_unconditional` — which derives the instance from
properness — are interchangeable. -/
public theorem isIso_cohomologyToLimit_of_isLocallyNoetherian [IsLocallyNoetherian X] :
    IsIso (cohomologyToLimit (baseIdealSheaf A J f) F p) :=
  isIso_cohomologyToLimit A J f F p (moduleFinite_cohomology_of_isProper A f F p)
    (exists_kernelBound_rightDerived_completionProjection A J f F p)
    (exists_stableImage_rightDerived_completionProjection A J f F p)

/-- **Stacks 087U, with no hypothesis.** Let `A` be a Noetherian ring complete with respect to an
ideal `J`, let `f : X ⟶ Spec A` be proper and let `F` be a coherent sheaf on `X`. Then for every
`p ≥ 0` the canonical map

  `Hᵖ(X, F) ⟶ limₙ Hᵖ(X, F / Jⁿ F)`

is an isomorphism.

This is `Stacks.Algebraization.isIso_cohomologyToLimit_of_isProper` with all three of its
hypotheses discharged: `hfin` by [Stacks, Tag 02O6]
(`Stacks.Algebraization.moduleFinite_cohomology_of_isProper`) and `hker`, `hstab` by the two
uniform Artin-Rees bounds of [Stacks, Tag 02OB]
(`Stacks.Algebraization.exists_kernelBound_rightDerived_completionProjection` and
`Stacks.Algebraization.exists_stableImage_rightDerived_completionProjection`). Nothing is
assumed beyond the source's hypotheses.

An alias of `Stacks.Algebraization.isIso_cohomologyToLimit_of_isProper_of_isAdicComplete`. -/
public alias isIso_cohomologyToLimit_unconditional :=
  Stacks.Algebraization.isIso_cohomologyToLimit_of_isProper_of_isAdicComplete

end Main

end Stacks.Algebraization

end
