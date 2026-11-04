module

public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessTwists.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive

/-!
# The twist-power bridge over a ring, and [Stacks, Tag 02O6] from a family of twists

`StacksFrontier/AlgebraicGeometry/CohomologyFinitenessTwists/Basic.lean` reduces
[Stacks, Tag 02O6] **over a field** to a family of twists, and it is field-only for exactly one
reason: the identification `Hⁿ(X, 𝒢^{⊞ r}) ≅ (Hⁿ(X, 𝒢))^r` was available only as the `k`-linear
`AlgebraicGeometry.nonempty_cohomologyOverField_biprodPow_linearEquiv`. Its absence over a ring
is why `AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_exists_epi` of
`StacksFrontier/AlgebraicGeometry/CohomologyFinitenessNoetherian/Basic.lean` takes the supply of
resolving modules abstractly rather than as a family of twists. This file supplies the `A`-linear
identification and carries the ring level up to the same statements the field level has.

**The construction is shorter than the field one, and the reason is an instance in the library.** The
field development builds the splitting `Hⁿ(𝒜 ⊞ ℬ) ≅ Hⁿ(𝒜) × Hⁿ(ℬ)` out of the long exact
sequence of a split short exact sequence, on the ground that a right derived functor is not known
to be additive. That is true of Mathlib and **false of this repository**:
`CategoryTheory.Functor.additive_rightDerived` of
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/DerivedFunctorAdditive.lean` is a public
instance, so `CategoryTheory.Functor.mapBiprod` applies to
`(moduleGlobalSections X).rightDerived n` directly once
`CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts` turns additivity into
preservation of binary biproducts — that step is a lemma and not an instance, which is the only
thing standing in the way of `inferInstance`. No short exact sequence, no connecting map and no
splitting argument is needed, and the result holds with no hypothesis on `f` and **no Noetherian
hypothesis**.

**Two indexings, and the crossing is performed here.** The statements below are stated in the
`CategoryTheory.Functor.rightDerived` (`ℕ`-indexed) spelling that [Stacks, Tag 02O6] and the
ring-base development use, and each of the three conclusions is also given in the
`CategoryTheory.Functor.rightDerivedPlus` (`ℤ`-indexed) spelling the tagged statements and the
dévissage use. The crossing is `Stacks.DerivedIndexing.rightDerivedIso`, and
`moduleFinitePlus_cohomology_ringBase_iff` below states it for the ring-base cohomology with no
hypothesis at all — the existing
`ProperCohomologyFinite.moduleFinitePlus_cohomology_ringBase_of_isCoherent` performs the same
crossing but carries coherence of `Rⁿ f_* F` and quasi-coherence of `F`, which the crossing itself
does not need.

## Main results

* `AlgebraicGeometry.nonempty_cohomology_ringBase_biprod_linearEquiv`:
  `Hⁿ(X, 𝒜 ⊞ ℬ) ≃ₗ[A] Hⁿ(X, 𝒜) × Hⁿ(X, ℬ)`, for any morphism to `Spec A` and any modules.
* `AlgebraicGeometry.nonempty_cohomology_ringBase_biprodPow_linearEquiv`:
  **`Hⁿ(X, 𝒢^{⊞ r}) ≃ₗ[A] (Fin r → Hⁿ(X, 𝒢))`** — the `A`-linear analogue of
  `AlgebraicGeometry.nonempty_cohomologyOverField_biprodPow_linearEquiv`, and the lemma whose
  absence made the twist machinery field-only.
* `AlgebraicGeometry.moduleFinite_cohomology_ringBase_biprodPow`: finiteness of `Hⁿ(X, 𝒢)` as an
  `A`-module passes to every power of `𝒢`.
* `AlgebraicGeometry.moduleFinitePlus_cohomology_ringBase_iff`: the two indexings of the ring-base
  cohomology have the same finiteness, unconditionally.
* `AlgebraicGeometry.exists_isCoherent_and_forall_moduleFinite_and_epi_of_epi_biprodPow`: a
  surjection from a power of a member of the family is a resolving module in the sense
  `AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_exists_epi` takes.
* `AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_epi_biprodPow` and
  `…_of_epi_biprodPow_of_le`: **[Stacks, Tag 02O6] over a Noetherian ring from a family of
  twists**, with and without the vanishing degree as a hypothesis.
* `AlgebraicGeometry.forall_moduleFinitePlus_cohomology_ringBase_of_epi_biprodPow` and
  `AlgebraicGeometry.forall_moduleFinitePlus_cohomology_ringBase_of_exists_epi`: the same in the
  `ℤ`-indexed spelling, the second being the crossing of
  `AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_exists_epi` itself.
* `AlgebraicGeometry.forall_isCoherent_rightDerived_of_epi_biprodPow` and
  `AlgebraicGeometry.forall_isCoherent_rightDerivedPlus_of_epi_biprodPow`: [Stacks, Tag 02O5] over
  an affine Noetherian base from the family of twists, in both indexings.

## Implementation notes

**No tag attribute is attached to anything here, and this file proves no tag.** Every statement
that reaches the conclusion of [Stacks, Tag 02O6] or of [Stacks, Tag 02O5] carries the finiteness
of the cohomology of the twists and the existence of the surjection as explicit hypotheses; the
first is [Stacks, Tag 01XT] and the second is a clause of [Stacks, Tag 01YS], and neither is in
the library. By the covering-set rule the attribute belongs on none of these declarations. The
attribute tokens are deliberately not spelled out in this comment: a comment-blind attribute grep
reads a spelled token as coverage.

**The field case is recovered at `A = k`, but not by elaboration.**
`AlgebraicGeometry.cohomologyOverField` restricts scalars along `f.appLE ⊤ ⊤ _`, which unfolds to
`f.app ⊤ ≫ X.presheaf.map (homOfLE _).op` and is *not* `rfl`-equal to the `f.appTop` the ring-base
spelling uses; the two meet through
`Stacks.AlgebraicGeometry.ProperCohomologyFinite.cohomologyOverField_eq_restrictScalars_appTop`
and through nothing else. Specialising `nonempty_cohomology_ringBase_biprodPow_linearEquiv` to a
field and rewriting with that bridge gives
`AlgebraicGeometry.nonempty_cohomologyOverField_biprodPow_linearEquiv` back, so the statement here
is not a weakening of the field one; it is the same statement at a ring.

**The family is a hypothesis and carries no geometry.** As in the field file, `𝒯` is an arbitrary
`ℕ`-indexed family of modules on `X`: nothing below knows that its members are twists, that `X` is
projective space, or which model of projective space is meant.

**Which coherence predicate.** `SheafOfModules.IsCoherent` here is the root-level class declared in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentFinitePresentation.lean`. The enclosing
namespace is `AlgebraicGeometry` and not one beginning with `Stacks`, so the relative name resolves
to it and not to the distinct `Stacks.SheafOfModules.IsCoherent`, which has the same two fields.
Verified with `pp.fullNames` on both these statements and on the two consumers they are fed to, so
the compositions below need no bridge.

## References

* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.ProperCohomologyFinite

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (T : ℕ → X.Modules)

/-! ### The `A`-linear splitting of the cohomology of a biproduct -/

/-- **The cohomology of a biproduct is the product of the cohomologies**, as `A`-modules, with no
hypothesis on `f` and none on the modules.

Both functors involved are additive — `(moduleGlobalSections X).rightDerived n` by
`CategoryTheory.Functor.additive_rightDerived` and `ModuleCat.restrictScalars` by instance search
— so each preserves binary biproducts, and `ModuleCat.biprodIsoProd` identifies the biproduct of
`A`-modules with the product type. This is the ring-base analogue of
`AlgebraicGeometry.nonempty_cohomologyOverField_biprod_linearEquiv`, which goes through the long
exact sequence of a split short exact sequence instead; the derived functor's additivity makes
that detour unnecessary. -/
theorem nonempty_cohomology_ringBase_biprod_linearEquiv (G H : X.Modules) (n : ℕ) :
    Nonempty
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
          (((moduleGlobalSections X).rightDerived n).obj (G ⊞ H)) ≃ₗ[A]
        (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
            (((moduleGlobalSections X).rightDerived n).obj G) ×
          (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
            (((moduleGlobalSections X).rightDerived n).obj H)) :=
  have : PreservesBinaryBiproducts ((moduleGlobalSections X).rightDerived n) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have : PreservesBinaryBiproducts
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  ⟨(((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).mapIso
        (((moduleGlobalSections X).rightDerived n).mapBiprod G H)) ≪≫
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).mapBiprod
        (((moduleGlobalSections X).rightDerived n).obj G)
        (((moduleGlobalSections X).rightDerived n).obj H) ≪≫
      ModuleCat.biprodIsoProd _ _).toLinearEquiv⟩

/-- **The cohomology of a power is the power of the cohomology**, as `A`-modules, with no
hypothesis on `f` and none on the module. This is the `A`-linear analogue of
`AlgebraicGeometry.nonempty_cohomologyOverField_biprodPow_linearEquiv`, and the single lemma whose
absence confined the twist machinery of
`StacksFrontier/AlgebraicGeometry/CohomologyFinitenessTwists/Basic.lean` to a field.

At `r = 0` the power is a zero object, so its cohomology is a zero object — an additive functor
preserves zero objects — and both sides are subsingletons. -/
theorem nonempty_cohomology_ringBase_biprodPow_linearEquiv (G : X.Modules) (n : ℕ) :
    ∀ r : ℕ, Nonempty
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
          (((moduleGlobalSections X).rightDerived n).obj (G.biprodPow r)) ≃ₗ[A]
        (Fin r → (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
          (((moduleGlobalSections X).rightDerived n).obj G)))
  | 0 => by
    have hz : IsZero
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
          (((moduleGlobalSections X).rightDerived n).obj (G.biprodPow 0))) :=
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).map_isZero
        (((moduleGlobalSections X).rightDerived n).map_isZero
          (show IsZero (G.biprodPow 0) from isZero_zero X.Modules))
    have : Subsingleton
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
          (((moduleGlobalSections X).rightDerived n).obj (G.biprodPow 0))) :=
      ModuleCat.subsingleton_of_isZero hz
    have : Subsingleton
        (Fin 0 → (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
          (((moduleGlobalSections X).rightDerived n).obj G)) :=
      ⟨fun a b => funext fun i => i.elim0⟩
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  | (r + 1) => by
    obtain ⟨e⟩ := nonempty_cohomology_ringBase_biprod_linearEquiv A f G (G.biprodPow r) n
    obtain ⟨e'⟩ := nonempty_cohomology_ringBase_biprodPow_linearEquiv G n r
    exact ⟨e.trans (((LinearEquiv.refl A _).prodCongr e').trans
      (Fin.consLinearEquiv A (fun _ : Fin (r + 1) =>
        (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
          (((moduleGlobalSections X).rightDerived n).obj G))))⟩

/-- **Finiteness of the cohomology passes to a power**, with no hypothesis on `f`, none on the
module and **no Noetherian hypothesis on `A`**: a finite power of a finite module is finite. This
is the ring-level twist bridge, the statement that
`StacksFrontier/AlgebraicGeometry/CohomologyFinitenessNoetherian/Basic.lean` records as absent. -/
theorem moduleFinite_cohomology_ringBase_biprodPow (G : X.Modules) (n : ℕ)
    (h : Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj G))) (r : ℕ) :
    Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (G.biprodPow r))) := by
  obtain ⟨e⟩ := nonempty_cohomology_ringBase_biprodPow_linearEquiv A f G n r
  have := h
  exact Module.Finite.equiv e.symm

/-! ### The crossing between the two indexings -/

/-- **The two indexings of the ring-base cohomology have the same finiteness**, with no
hypothesis on `f`, on `A` or on the module: `Stacks.DerivedIndexing.rightDerivedIso` is a natural
isomorphism of functors and restriction of scalars carries it to an `A`-linear equivalence.

`ProperCohomologyFinite.moduleFinitePlus_cohomology_ringBase_of_isCoherent` performs the same
crossing in one direction, but carries quasi-coherence of `F` and coherence of `Rⁿ f_* F`, neither
of which the crossing uses. -/
theorem moduleFinitePlus_cohomology_ringBase_iff (G : X.Modules) (n : ℕ) :
    Module.Finite A
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
          (((moduleGlobalSections X).rightDerivedPlus (n : ℤ)).obj G)) ↔
      Module.Finite A
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
          (((moduleGlobalSections X).rightDerived n).obj G)) :=
  have e := ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).mapIso
    ((Stacks.DerivedIndexing.rightDerivedIso (moduleGlobalSections X) n).app G)).toLinearEquiv
  ⟨fun h => have := h; Module.Finite.equiv e.symm, fun h => have := h; Module.Finite.equiv e⟩

/-- **The abstract-hypothesis form of [Stacks, Tag 02O6] over a Noetherian ring, in the
`ℤ`-indexed spelling.** `AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_exists_epi`
is stated in the `ℕ`-indexed `CategoryTheory.Functor.rightDerived`; this is the same theorem with
both occurrences in the `CategoryTheory.Functor.rightDerivedPlus` indexing that the tagged
statements and the dévissage development use. -/
theorem forall_moduleFinitePlus_cohomology_ringBase_of_exists_epi [IsNoetherianRing A]
    [IsProper f]
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ E : X.Modules, SheafOfModules.IsCoherent E ∧
        (∀ n : ℕ, Module.Finite A
          ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
            (((moduleGlobalSections X).rightDerivedPlus (n : ℤ)).obj E))) ∧ ∃ φ : E ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G → ∀ n : ℕ, Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerivedPlus (n : ℤ)).obj G)) := by
  intro G hG n
  refine (moduleFinitePlus_cohomology_ringBase_iff A f G n).2 ?_
  refine forall_moduleFinite_cohomology_ringBase_of_exists_epi A f (fun E hE => ?_) G hG n
  obtain ⟨E', hE', hfin, φ, hφ⟩ := hgen E hE
  exact ⟨E', hE', fun m => (moduleFinitePlus_cohomology_ringBase_iff A f E' m).1 (hfin m), φ, hφ⟩

/-! ### A power of a twist is a resolving module -/

/-- **A surjection from a power of a member of the family is a resolving module.** If every member
of `𝒯` is coherent with `A`-finite cohomology in every degree, a surjection `(𝒯 d)^{⊞ r} ⟶ 𝒢`
exhibits `𝒢` as a quotient of a coherent module whose cohomology is `A`-finite in every degree,
which is the hypothesis `AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_exists_epi`
takes. There is no hypothesis on `f` and no Noetherian hypothesis.

This is the ring-base analogue of
`AlgebraicGeometry.exists_isCoherent_and_forall_finiteDimensional_and_epi_of_epi_biprodPow`;
coherence of the power is `AlgebraicGeometry.SheafOfModules.isCoherent_biprodPow` as there, and
finiteness of its cohomology is `moduleFinite_cohomology_ringBase_biprodPow` above in place of
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_biprodPow`. -/
theorem exists_isCoherent_and_forall_moduleFinite_and_epi_of_epi_biprodPow
    (hTcoh : ∀ d : ℕ, SheafOfModules.IsCoherent (T d))
    (hTfin : ∀ d n : ℕ, Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (T d))))
    (G : X.Modules) (hG : ∃ d r : ℕ, ∃ φ : (T d).biprodPow r ⟶ G, Epi φ) :
    ∃ E : X.Modules, SheafOfModules.IsCoherent E ∧
      (∀ n : ℕ, Module.Finite A
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
          (((moduleGlobalSections X).rightDerived n).obj E))) ∧ ∃ φ : E ⟶ G, Epi φ := by
  obtain ⟨d, r, φ, hφ⟩ := hG
  exact ⟨(T d).biprodPow r, SheafOfModules.isCoherent_biprodPow (T d) (hTcoh d) r,
    fun n => moduleFinite_cohomology_ringBase_biprodPow A f (T d) n (hTfin d n) r, φ, hφ⟩

/-! ### [Stacks, Tag 02O6] over a Noetherian ring from a family of twists -/

/-- **The descending induction of [Stacks, Tag 02O6] over a Noetherian ring, run on a family of
twists**, with the vanishing degree as a hypothesis and no condition on `f`. The ring-base
analogue of
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_biprodPow_of_le`. -/
theorem forall_moduleFinite_cohomology_ringBase_of_epi_biprodPow_of_le [IsNoetherianRing A]
    (N : ℕ)
    (hN : ∀ G : X.Modules, SheafOfModules.IsCoherent G → ∀ n : ℕ, N ≤ n → Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj G)))
    (hTcoh : ∀ d : ℕ, SheafOfModules.IsCoherent (T d))
    (hTfin : ∀ d n : ℕ, Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (T d))))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ d r : ℕ, ∃ φ : (T d).biprodPow r ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G → ∀ n : ℕ, Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj G)) :=
  forall_moduleFinite_cohomology_ringBase_of_exists_epi_of_le A f N hN
    fun G hG => exists_isCoherent_and_forall_moduleFinite_and_epi_of_epi_biprodPow
      A f T hTcoh hTfin G (hgen G hG)

/-- **[Stacks, Tag 02O6] over a Noetherian ring from a family of twists.** For `X` proper over
`Spec A` with `A` Noetherian, if there is a family `𝒯` of coherent modules whose cohomology is a
finite `A`-module in every degree and such that every coherent module on `X` is a quotient of a
power of a member of `𝒯`, then `Hⁿ(X, ℱ)` is a finite `A`-module for every coherent `ℱ` and every
`n`.

This is the ring level of
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_biprodPow`, and it is what
the ring-level twist bridge above unlocks: the hypotheses are the Čech computation of
[Stacks, Tag 01XT] and the "quotient of twists" clause of [Stacks, Tag 01YS], at a Noetherian ring
base rather than only over a field. -/
theorem forall_moduleFinite_cohomology_ringBase_of_epi_biprodPow [IsNoetherianRing A]
    [IsProper f]
    (hTcoh : ∀ d : ℕ, SheafOfModules.IsCoherent (T d))
    (hTfin : ∀ d n : ℕ, Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (T d))))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ d r : ℕ, ∃ φ : (T d).biprodPow r ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G → ∀ n : ℕ, Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj G)) :=
  forall_moduleFinite_cohomology_ringBase_of_exists_epi A f
    fun G hG => exists_isCoherent_and_forall_moduleFinite_and_epi_of_epi_biprodPow
      A f T hTcoh hTfin G (hgen G hG)

/-- **[Stacks, Tag 02O6] over a Noetherian ring from a family of twists, in the `ℤ`-indexed
spelling.** The same theorem as `forall_moduleFinite_cohomology_ringBase_of_epi_biprodPow` with
both occurrences of the cohomology in the `CategoryTheory.Functor.rightDerivedPlus` indexing. -/
theorem forall_moduleFinitePlus_cohomology_ringBase_of_epi_biprodPow [IsNoetherianRing A]
    [IsProper f]
    (hTcoh : ∀ d : ℕ, SheafOfModules.IsCoherent (T d))
    (hTfin : ∀ d n : ℕ, Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerivedPlus (n : ℤ)).obj (T d))))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ d r : ℕ, ∃ φ : (T d).biprodPow r ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G → ∀ n : ℕ, Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerivedPlus (n : ℤ)).obj G)) := by
  intro G hG n
  refine (moduleFinitePlus_cohomology_ringBase_iff A f G n).2 ?_
  exact forall_moduleFinite_cohomology_ringBase_of_epi_biprodPow A f T hTcoh
    (fun d m => (moduleFinitePlus_cohomology_ringBase_iff A f (T d) m).1 (hTfin d m)) hgen G hG n

/-! ### [Stacks, Tag 02O5] over an affine Noetherian base from the same family -/

/-- **[Stacks, Tag 02O5] over an affine Noetherian base from a family of twists.** Coherence of
`Rⁿ f_* ℱ` for every coherent `ℱ`, because over a Noetherian ring finiteness of `Hⁿ(X, ℱ)` as an
`A`-module *is* coherence of `Rⁿ f_* ℱ`
(`ProperCohomologyFinite.moduleFinite_cohomology_ringBase_iff_isCoherent`), so the two tags are
one obligation over an affine base and the family of twists discharges it. -/
theorem forall_isCoherent_rightDerived_of_epi_biprodPow [IsNoetherianRing A] [IsProper f]
    (hTcoh : ∀ d : ℕ, SheafOfModules.IsCoherent (T d))
    (hTfin : ∀ d n : ℕ, Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (T d))))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ d r : ℕ, ∃ φ : (T d).biprodPow r ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, (((Scheme.Modules.pushforward f).rightDerived n).obj G).IsCoherent :=
  forall_isCoherent_rightDerived_of_exists_epi A f
    fun G hG => exists_isCoherent_and_forall_moduleFinite_and_epi_of_epi_biprodPow
      A f T hTcoh hTfin G (hgen G hG)

/-- **[Stacks, Tag 02O5] over an affine Noetherian base from a family of twists, in the
`ℤ`-indexed spelling.** The previous theorem transported along
`Stacks.DerivedIndexing.rightDerivedIso` for the pushforward functor, which is the crossing that
`…ProperCohomologyFinite.forall_isCoherent_rightDerivedPlus_iff_forall_moduleFinite_cohomology`
uses for the same pair of spellings, the elided prefix being
`Stacks.AlgebraicGeometry`. -/
theorem forall_isCoherent_rightDerivedPlus_of_epi_biprodPow [IsNoetherianRing A] [IsProper f]
    (hTcoh : ∀ d : ℕ, SheafOfModules.IsCoherent (T d))
    (hTfin : ∀ d n : ℕ, Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (T d))))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ d r : ℕ, ∃ φ : (T d).biprodPow r ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj G).IsCoherent := by
  intro G hG n
  have := forall_isCoherent_rightDerived_of_epi_biprodPow A f T hTcoh hTfin hgen G hG n
  exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) n).app G).symm

end AlgebraicGeometry

end
