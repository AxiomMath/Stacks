module

public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessCoproduct.Basic
public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessTwists.RingBase
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.RingBaseCriterion

/-!
# [Stacks, Tag 02O6] over a Noetherian ring from the "quotient of twists" clause as stated

`StacksFrontier/AlgebraicGeometry/CohomologyFinitenessCoproduct/Basic.lean` reduces
[Stacks, Tag 02O6] **over a field** to clause (1) of [Stacks, Tag 01YS] at the shape the source
states it: a surjection `∐ⱼ 𝒯(dⱼ) ⟶ 𝒢` from a finite coproduct of members of a family, the indices
`dⱼ` being **unequal in general**.
`StacksFrontier/AlgebraicGeometry/CohomologyFinitenessTwists/RingBase.lean` carries the same
reduction to a **Noetherian ring base**, but only at the *power* shape `(𝒯 d)^{⊞ r} ⟶ 𝒢` with a
single `d`, which is the separate [Stacks, Tag 01QB] and a strengthening of what clause (1) gives.

So the two axes were developed separately and never crossed: the heterogeneous shape existed only
over a field and the ring base existed only at the power shape. This file is that crossing. Its
conclusions are the ring-base statements, from the heterogeneous hypothesis, and the last of them
reads the finite-type clause of [Stacks, Tag 0EX4] off from a family of twists, which is what the
ring base is wanted for.

**The splitting is four lines and needs no short exact sequence.** Over a field the analogous
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_biproduct` inducts on the number of
summands, splitting one off through the kernel sequence of its projection. That detour exists
because Mathlib has no instance making a right derived functor additive — true of Mathlib and
**false of this repository**, where `CategoryTheory.Functor.additive_rightDerived` of
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/DerivedFunctorAdditive.lean` is a public
instance. An additive functor preserves finite biproducts
(`CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive`), so
`CategoryTheory.Functor.mapBiproduct` applies to `(moduleGlobalSections X).rightDerived n` and
again to `ModuleCat.restrictScalars`, and `ModuleCat.biproductIsoPi` identifies the resulting
biproduct of `A`-modules with the dependent function type. Nothing here is an induction.

**Why the whole family is handled at once rather than by iterating the binary case.**
`AlgebraicGeometry.nonempty_cohomology_ringBase_biprod_linearEquiv` already gives the binary
splitting, and iterating it is how the power case is proved. It cannot reach the heterogeneous
case directly, because a coproduct over `Fin r` of a family that is not constant has no
`biprodPow` presentation; `CategoryTheory.Limits.PreservesBiproduct` at the shape `Fin r` is the
statement that does, and it costs no more than the binary one.

## Main results

* `AlgebraicGeometry.nonempty_cohomology_ringBase_biproduct_linearEquiv`:
  `Hⁿ(X, ⨁ⱼ ℰⱼ) ≃ₗ[A] ∀ j, Hⁿ(X, ℰⱼ)` for a finite family, with no hypothesis on `f`, none on the
  modules and no Noetherian hypothesis. This is the heterogeneous analogue of
  `AlgebraicGeometry.nonempty_cohomology_ringBase_biprodPow_linearEquiv`.
* `AlgebraicGeometry.moduleFinite_cohomology_ringBase_biproduct` and
  `AlgebraicGeometry.moduleFinite_cohomology_ringBase_coproduct`: `A`-finiteness of the cohomology
  passes to a finite biproduct and hence to a finite coproduct.
* `AlgebraicGeometry.exists_isCoherent_and_forall_moduleFinite_and_epi_of_epi_coproduct`: a
  surjection from a finite coproduct of members of the family is a resolving module in the sense
  `AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_exists_epi` takes.
* `AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_epi_coproduct_of_le` and
  `AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_epi_coproduct`:
  **[Stacks, Tag 02O6] over a Noetherian ring from clause (1) of [Stacks, Tag 01YS]**, with and
  without the vanishing degree as a hypothesis.
* `AlgebraicGeometry.forall_moduleFinitePlus_cohomology_ringBase_of_epi_coproduct`: the same in
  the `CategoryTheory.Functor.rightDerivedPlus` indexing.
* `AlgebraicGeometry.forall_isCoherent_rightDerived_of_epi_coproduct` and
  `AlgebraicGeometry.forall_isCoherent_rightDerivedPlus_of_epi_coproduct`: [Stacks, Tag 02O5] over
  an affine Noetherian base from the same family, in both indexings.
* `AlgebraicGeometry.exists_coproduct_family_of_forall_moduleFinite`: the three hypotheses are
  **jointly satisfiable** on every `X` whose coherent cohomology is already known to be `A`-finite
  — witnessed by the family of all coherent modules, with one summand.
* `AlgebraicGeometry.isFiniteType_rightDerived_of_forall_epi_coproduct_ringBase`: **the
  finite-type clause of [Stacks, Tag 0EX4] over a locally Noetherian base, from a family of
  twists at every Noetherian ring base.** This is the end of the chain the heterogeneous shape was
  missing: clause (1) of [Stacks, Tag 01YS] plus [Stacks, Tag 01XT] at a ring base now reach the
  tag.

## Implementation notes

**No tag attribute is attached to anything here, and this file proves no tag.** Every statement
that reaches the conclusion of [Stacks, Tag 02O6], of [Stacks, Tag 02O5] or of the finite-type
clause of [Stacks, Tag 0EX4] carries the `A`-finiteness of the cohomology of the family and the
existence of the surjection as explicit hypotheses; the first is [Stacks, Tag 01XT] and the second
is clause (1) of [Stacks, Tag 01YS], and neither is in the library. By the covering-set rule the
attribute belongs on none of these declarations. The attribute tokens are deliberately not spelled
out in this comment: a comment-blind attribute grep reads a spelled token as coverage.

**The heterogeneous hypothesis is weaker than the power one, and nothing aimed at the power slot
is lost.** `AlgebraicGeometry.exists_epi_coproduct_of_epi_biprodPow` proves the power form implies
the coproduct form, and it does not mention the base: its field-base section variables are unused
and so absent from its signature. Feeding it the `hgen` of
`AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_epi_biprodPow` therefore produces the
`hgen` of the theorem below, with no bridging lemma.

**The index type is a variable.** Clause (1) indexes the twists by `ℤ`; the power-form ring-base
file indexes its family by `ℕ`. A variable index type covers both and keeps one statement where
there would otherwise be two.

**The field case is recovered at `A = k`, but not by elaboration.**
`AlgebraicGeometry.cohomologyOverField` restricts scalars along `f.appLE ⊤ ⊤ _`, which unfolds to
`f.app ⊤ ≫ X.presheaf.map (homOfLE _).op` and is *not* `rfl`-equal to the `f.appTop` the ring-base
spelling uses; the two meet through
`Stacks.AlgebraicGeometry.ProperCohomologyFinite.cohomologyOverField_eq_restrictScalars_appTop`
and through nothing else. Across that bridge
`forall_moduleFinite_cohomology_ringBase_of_epi_coproduct` at a field and
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_coproduct` imply each other,
so neither is a weakening of the other.

**Which coherence predicate.** `SheafOfModules.IsCoherent` here is the root-level class declared
in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentFinitePresentation.lean`. The enclosing
namespace is `AlgebraicGeometry` and not one beginning with `Stacks`, so the relative name resolves
to it and not to the distinct `Stacks.SheafOfModules.IsCoherent`, which has the same two fields. It
is the predicate `AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_exists_epi`,
`AlgebraicGeometry.SheafOfModules.isCoherent_biproduct` and
`…TopDegreeFiniteType.isFiniteType_rightDerived_of_forall_exists_epi_ringBase` all take, the elided
prefix being `Stacks.AlgebraicGeometry`, so the compositions below need no bridge.

**`HasBiproduct` is a binder, not an instance.**
`AlgebraicGeometry.Scheme.Modules.hasFiniteBiproducts` is used as a local instance, exactly as in
`StacksFrontier/AlgebraicGeometry/CohomologyFinitenessCoproduct/Basic.lean`, which records the
reason: without it the declarations forming a biproduct fail to synthesize `HasBiproduct`,
while a consumer that only *states* the hypothesis needs no such instance, because `∐` asks for
`CategoryTheory.Limits.HasCoproduct`, which instance search supplies on an abelian category.

The `[HasBiproduct E]` binders of the two biproduct lemmas are therefore load-bearing for
*consumability* and not for the proof, in both directions: with that local instance in scope, deleting the binder still compiles, while with the
binder deleted *and* the local instance absent the application fails to synthesize
`HasBiproduct E`. The binder exists so that a file which does not activate the local instance can
still supply it.

## References

* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01QB](https://stacks.math.columbia.edu/tag/01QB)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
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

universe v u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasFiniteBiproducts_modules

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  {ι : Type v} (T : ι → X.Modules)

/-! ### The `A`-linear splitting of the cohomology of a finite biproduct -/

/-- **The cohomology of a finite biproduct is the product of the cohomologies**, as `A`-modules,
with no hypothesis on `f`, none on the modules and no Noetherian hypothesis. The summands are not
required to be equal, which is what distinguishes this from
`AlgebraicGeometry.nonempty_cohomology_ringBase_biprodPow_linearEquiv`.

Both functors involved are additive — `(moduleGlobalSections X).rightDerived n` by
`CategoryTheory.Functor.additive_rightDerived` and `ModuleCat.restrictScalars` by instance search
— so each preserves biproducts indexed by a finite type, and `ModuleCat.biproductIsoPi` identifies
the biproduct of `A`-modules with the dependent function type. -/
theorem nonempty_cohomology_ringBase_biproduct_linearEquiv {J : Type} [Finite J]
    (E : J → X.Modules) [HasBiproduct E] (n : ℕ) :
    Nonempty
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
          (((moduleGlobalSections X).rightDerived n).obj (⨁ E)) ≃ₗ[A]
        (∀ j, (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
          (((moduleGlobalSections X).rightDerived n).obj (E j)))) :=
  ⟨((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).mapIso
      (((moduleGlobalSections X).rightDerived n).mapBiproduct E) ≪≫
    (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).mapBiproduct
      (((moduleGlobalSections X).rightDerived n).obj ∘ E) ≪≫
    ModuleCat.biproductIsoPi _).toLinearEquiv⟩

/-- **Finiteness of the cohomology passes to a finite biproduct**, with no hypothesis on `f`, none
on the modules and **no Noetherian hypothesis on `A`**: a finite product of finite modules is
finite, by `Module.Finite.pi`. -/
theorem moduleFinite_cohomology_ringBase_biproduct {J : Type} [Finite J] (E : J → X.Modules)
    [HasBiproduct E] (n : ℕ)
    (h : ∀ j, Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (E j)))) :
    Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (⨁ E))) := by
  obtain ⟨e⟩ := nonempty_cohomology_ringBase_biproduct_linearEquiv A f E n
  have := h
  exact Module.Finite.equiv e.symm

/-- **Finiteness of the cohomology passes to a finite coproduct**, which in an additive category
is the biproduct. This is the shape in which clause (1) of [Stacks, Tag 01YS] produces the
resolving module: a finite coproduct `∐ⱼ 𝒪(dⱼ)` of twists of varying degree. -/
theorem moduleFinite_cohomology_ringBase_coproduct {J : Type} [Finite J] (E : J → X.Modules)
    [HasBiproduct E] (n : ℕ)
    (h : ∀ j, Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (E j)))) :
    Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (∐ E))) :=
  have := moduleFinite_cohomology_ringBase_biproduct A f E n h
  Module.Finite.equiv
    ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).mapIso
      (((moduleGlobalSections X).rightDerived n).mapIso (biproduct.isoCoproduct E))).toLinearEquiv

/-! ### A finite coproduct of members of the family is a resolving module -/

/-- **A surjection from a finite coproduct of members of `𝒯` is a resolving module.** If every
member of `𝒯` is coherent with `A`-finite cohomology in every degree, a surjection
`∐ⱼ 𝒯(dⱼ) ⟶ 𝒢` exhibits `𝒢` as a quotient of a coherent module whose cohomology is `A`-finite in
every degree, which is the hypothesis
`AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_exists_epi` takes. The indices `dⱼ`
need not be equal, which is what clause (1) of [Stacks, Tag 01YS] provides. There is no hypothesis
on `f` and no Noetherian hypothesis.

Coherence of the coproduct is `AlgebraicGeometry.SheafOfModules.isCoherent_biproduct` transported
along `CategoryTheory.Limits.biproduct.isoCoproduct`, coherent modules being closed under
isomorphism as a weak Serre class ([Stacks, Tag 01BY] (5)); `A`-finiteness of its cohomology is
`moduleFinite_cohomology_ringBase_coproduct` above, in place of the field-base
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_coproduct`. -/
theorem exists_isCoherent_and_forall_moduleFinite_and_epi_of_epi_coproduct
    (hTcoh : ∀ a : ι, SheafOfModules.IsCoherent (T a))
    (hTfin : ∀ (a : ι) (n : ℕ), Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (T a))))
    (G : X.Modules)
    (hG : ∃ (r : ℕ) (d : Fin r → ι), ∃ φ : (∐ fun j => T (d j)) ⟶ G, Epi φ) :
    ∃ E : X.Modules, SheafOfModules.IsCoherent E ∧
      (∀ n : ℕ, Module.Finite A
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
          (((moduleGlobalSections X).rightDerived n).obj E))) ∧ ∃ φ : E ⟶ G, Epi φ := by
  obtain ⟨r, d, φ, hφ⟩ := hG
  refine ⟨∐ fun j => T (d j), ?_, ?_, φ, hφ⟩
  · have hb := SheafOfModules.isCoherent_biproduct (fun j => T (d j)) fun j => hTcoh (d j)
    let P : ObjectProperty X.Modules := fun M => SheafOfModules.IsCoherent M
    let _ : P.IsWeakSerreClass := _root_.SheafOfModules.coherentModules_isWeakSerreClass
    exact P.prop_of_iso (biproduct.isoCoproduct (fun j => T (d j))) hb
  · exact fun n => moduleFinite_cohomology_ringBase_coproduct A f (fun j => T (d j)) n
      fun j => hTfin (d j) n

/-- The resolving-module hypothesis, for every coherent `𝒢`, from a generating family of
coproducts. -/
private theorem forall_exists_isCoherent_and_forall_moduleFinite_and_epi_of_epi_coproduct
    (hTcoh : ∀ a : ι, SheafOfModules.IsCoherent (T a))
    (hTfin : ∀ (a : ι) (n : ℕ), Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (T a))))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ (r : ℕ) (d : Fin r → ι), ∃ φ : (∐ fun j => T (d j)) ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ E : X.Modules, SheafOfModules.IsCoherent E ∧
        (∀ n : ℕ, Module.Finite A
          ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
            (((moduleGlobalSections X).rightDerived n).obj E))) ∧ ∃ φ : E ⟶ G, Epi φ :=
  fun G hG => exists_isCoherent_and_forall_moduleFinite_and_epi_of_epi_coproduct
    A f T hTcoh hTfin G (hgen G hG)

/-! ### [Stacks, Tag 02O6] over a Noetherian ring from a family of twists of varying degree -/

/-- **The descending induction of [Stacks, Tag 02O6] over a Noetherian ring, run on clause (1) of
[Stacks, Tag 01YS]**, with the vanishing degree as a hypothesis and no condition on `f`. The
ring-base analogue of
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_coproduct_of_le`. -/
theorem forall_moduleFinite_cohomology_ringBase_of_epi_coproduct_of_le [IsNoetherianRing A]
    (N : ℕ)
    (hN : ∀ G : X.Modules, SheafOfModules.IsCoherent G → ∀ n : ℕ, N ≤ n → Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj G)))
    (hTcoh : ∀ a : ι, SheafOfModules.IsCoherent (T a))
    (hTfin : ∀ (a : ι) (n : ℕ), Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (T a))))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ (r : ℕ) (d : Fin r → ι), ∃ φ : (∐ fun j => T (d j)) ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G → ∀ n : ℕ, Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj G)) :=
  forall_moduleFinite_cohomology_ringBase_of_exists_epi_of_le A f N hN
    (forall_exists_isCoherent_and_forall_moduleFinite_and_epi_of_epi_coproduct
      A f T hTcoh hTfin hgen)

/-- **[Stacks, Tag 02O6] over a Noetherian ring from clause (1) of [Stacks, Tag 01YS] at the shape
the source states it.** For `X` proper over `Spec A` with `A` Noetherian, if there is a family `𝒯`
of coherent modules whose cohomology is a finite `A`-module in every degree and such that every
coherent module on `X` is a quotient of a finite **coproduct** of members of `𝒯`, then `Hⁿ(X, ℱ)`
is a finite `A`-module for every coherent `ℱ` and every `n`.

This is the statement the ring base was missing. Its field-base counterpart is
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_epi_coproduct`, and the
power-form ring-base counterpart is
`AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_epi_biprodPow`, whose hypothesis is
the stronger [Stacks, Tag 01QB]. On `ℙⁿ` the family is the twists and the two hypotheses are the
Čech computation of [Stacks, Tag 01XT] and clause (1) of [Stacks, Tag 01YS].

The vanishing degree is supplied by
`AlgebraicGeometry.exists_forall_moduleFinite_cohomology_ringBase_of_le_of_isProper`, which needs
only properness, and a coherent module is quasi-coherent by [Stacks, Tag 01BW]. -/
theorem forall_moduleFinite_cohomology_ringBase_of_epi_coproduct [IsNoetherianRing A]
    [IsProper f]
    (hTcoh : ∀ a : ι, SheafOfModules.IsCoherent (T a))
    (hTfin : ∀ (a : ι) (n : ℕ), Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (T a))))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ (r : ℕ) (d : Fin r → ι), ∃ φ : (∐ fun j => T (d j)) ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G → ∀ n : ℕ, Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj G)) :=
  forall_moduleFinite_cohomology_ringBase_of_exists_epi A f
    (forall_exists_isCoherent_and_forall_moduleFinite_and_epi_of_epi_coproduct
      A f T hTcoh hTfin hgen)

/-- **[Stacks, Tag 02O6] over a Noetherian ring from clause (1) of [Stacks, Tag 01YS], in the
`ℤ`-indexed spelling.** The same theorem as
`forall_moduleFinite_cohomology_ringBase_of_epi_coproduct`
with both occurrences of the cohomology in the `CategoryTheory.Functor.rightDerivedPlus` indexing
that the tagged statements and the dévissage development use; the crossing is
`AlgebraicGeometry.moduleFinitePlus_cohomology_ringBase_iff`. -/
theorem forall_moduleFinitePlus_cohomology_ringBase_of_epi_coproduct [IsNoetherianRing A]
    [IsProper f]
    (hTcoh : ∀ a : ι, SheafOfModules.IsCoherent (T a))
    (hTfin : ∀ (a : ι) (n : ℕ), Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerivedPlus (n : ℤ)).obj (T a))))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ (r : ℕ) (d : Fin r → ι), ∃ φ : (∐ fun j => T (d j)) ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G → ∀ n : ℕ, Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerivedPlus (n : ℤ)).obj G)) := by
  intro G hG n
  refine (moduleFinitePlus_cohomology_ringBase_iff A f G n).2 ?_
  exact forall_moduleFinite_cohomology_ringBase_of_epi_coproduct A f T hTcoh
    (fun a m => (moduleFinitePlus_cohomology_ringBase_iff A f (T a) m).1 (hTfin a m)) hgen G hG n

/-! ### [Stacks, Tag 02O5] over an affine Noetherian base from the same family -/

/-- **[Stacks, Tag 02O5] over an affine Noetherian base from clause (1) of [Stacks, Tag 01YS].**
Coherence of `Rⁿ f_* ℱ` for every coherent `ℱ`, because over a Noetherian ring finiteness of
`Hⁿ(X, ℱ)` as an `A`-module *is* coherence of `Rⁿ f_* ℱ`
(`Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_cohomology_ringBase_iff_isCoherent`)
so the two tags are one obligation over an affine base and the family of twists discharges it. -/
theorem forall_isCoherent_rightDerived_of_epi_coproduct [IsNoetherianRing A] [IsProper f]
    (hTcoh : ∀ a : ι, SheafOfModules.IsCoherent (T a))
    (hTfin : ∀ (a : ι) (n : ℕ), Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (T a))))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ (r : ℕ) (d : Fin r → ι), ∃ φ : (∐ fun j => T (d j)) ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, (((Scheme.Modules.pushforward f).rightDerived n).obj G).IsCoherent :=
  forall_isCoherent_rightDerived_of_exists_epi A f
    (forall_exists_isCoherent_and_forall_moduleFinite_and_epi_of_epi_coproduct
      A f T hTcoh hTfin hgen)

/-- **[Stacks, Tag 02O5] over an affine Noetherian base from clause (1) of [Stacks, Tag 01YS], in
the `ℤ`-indexed spelling.** The previous theorem transported along
`Stacks.DerivedIndexing.rightDerivedIso` for the pushforward functor. -/
theorem forall_isCoherent_rightDerivedPlus_of_epi_coproduct [IsNoetherianRing A] [IsProper f]
    (hTcoh : ∀ a : ι, SheafOfModules.IsCoherent (T a))
    (hTfin : ∀ (a : ι) (n : ℕ), Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (T a))))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ (r : ℕ) (d : Fin r → ι), ∃ φ : (∐ fun j => T (d j)) ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj G).IsCoherent := by
  intro G hG n
  have := forall_isCoherent_rightDerived_of_epi_coproduct A f T hTcoh hTfin hgen G hG n
  exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) n).app G).symm

/-! ### The hypotheses are jointly satisfiable -/

/-- **The three hypotheses of `forall_moduleFinite_cohomology_ringBase_of_epi_coproduct` are
jointly satisfiable**, on every `X` whose coherent cohomology is `A`-finite in every degree. The
witnessing family is the family of *all* coherent modules, and the surjection onto `𝒢` is the
single-summand coproduct `∐_{j : Fin 1} 𝒢 ⟶ 𝒢`, which is a split epimorphism.

This rules out vacuity, which no check of the axioms used detects: a hypothesis set can be
fully proved, free of extra axioms, and satisfied by nothing at all. It takes the conclusion as its hypothesis, so it does **not**
discharge the hypotheses on projective space — there the family is the twists and the finiteness
of their cohomology is [Stacks, Tag 01XT], which is absent. What it establishes is that the set is
consistent, and that it holds wherever the conclusion does. The ring-base analogue of
`AlgebraicGeometry.exists_coproduct_family_of_forall_finiteDimensional`. -/
theorem exists_coproduct_family_of_forall_moduleFinite
    (h : ∀ G : X.Modules, SheafOfModules.IsCoherent G → ∀ n : ℕ, Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj G))) :
    ∃ (J : Type (u + 1)) (S : J → X.Modules),
      (∀ a : J, SheafOfModules.IsCoherent (S a)) ∧
      (∀ (a : J) (n : ℕ), Module.Finite A
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
          (((moduleGlobalSections X).rightDerived n).obj (S a)))) ∧
      ∀ G : X.Modules, SheafOfModules.IsCoherent G →
        ∃ (r : ℕ) (d : Fin r → J), ∃ φ : (∐ fun j => S (d j)) ⟶ G, Epi φ := by
  refine ⟨{G : X.Modules // SheafOfModules.IsCoherent G}, Subtype.val, fun a => a.2,
    fun a n => h a.1 a.2 n, fun G hG => ⟨1, fun _ => ⟨G, hG⟩,
      Sigma.desc fun _ => 𝟙 G, ?_⟩⟩
  have : IsSplitEpi (Sigma.desc fun _ : Fin 1 => 𝟙 G) :=
    IsSplitEpi.mk' ⟨Sigma.ι (fun _ : Fin 1 => G) 0, by simp⟩
  infer_instance

/-! ### The finite-type clause of Tag 0EX4 from a family of twists -/

open Stacks.AlgebraicGeometry.TopDegreeFiniteType in
/-- **The finite-type clause of [Stacks, Tag 0EX4] over a locally Noetherian base, from a family
of twists of varying degree at every Noetherian ring base.** For `g : Y ⟶ Z` proper with `Z`
locally Noetherian and `F` quasi-coherent of finite type, `R ᵉ g_* F` is of finite type in every
degree `e`, given that every proper scheme over every Noetherian affine ring base carries a family
in the sense of `forall_moduleFinite_cohomology_ringBase_of_epi_coproduct`.

This is the end of the chain that the heterogeneous shape was missing. The hypothesis is clause
(1) of [Stacks, Tag 01YS] together with [Stacks, Tag 01XT], stated at the ring base and at the
shape the source states clause (1) — not at the stronger single-degree [Stacks, Tag 01QB] — and
the conclusion is the tag's finite-type clause. The two steps are
`exists_isCoherent_and_forall_moduleFinite_and_epi_of_epi_coproduct`, which turns the family into
the resolving-module hypothesis, and
`…TopDegreeFiniteType.isFiniteType_rightDerived_of_forall_exists_epi_ringBase`, which takes that
hypothesis to the tag, the elided prefix being `Stacks.AlgebraicGeometry`. No bridging lemma
intervenes.

There is no hypothesis on the fibres of `g`: over a locally Noetherian base the tag's
fibre-dimension bound is provably inert, which is recorded at the same namespace's
`isFiniteType_rightDerived_of_forall_topologicalKrullDim_fiber_le_of_ringBase`. -/
theorem isFiniteType_rightDerived_of_forall_epi_coproduct_ringBase {Y Z : Scheme.{u}}
    (g : Y ⟶ Z) [IsProper g] [IsLocallyNoetherian Z] (F : Y.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (e : ℕ)
    (hfam : ∀ (B : Type u) [CommRing B], IsNoetherianRing B → ∀ (X₀ : Scheme.{u})
      (g₀ : X₀ ⟶ Spec (.of B)), IsProper g₀ →
      ∃ (κ : Type u) (S : κ → X₀.Modules),
        (∀ a : κ, SheafOfModules.IsCoherent (S a)) ∧
        (∀ (a : κ) (n : ℕ), Module.Finite B
          ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of B)).inv ≫ g₀.appTop).hom).obj
            (((moduleGlobalSections X₀).rightDerived n).obj (S a)))) ∧
        ∀ G : X₀.Modules, SheafOfModules.IsCoherent G →
          ∃ (r : ℕ) (c : Fin r → κ), ∃ φ : (∐ fun j => S (c j)) ⟶ G, Epi φ) :
    (((Scheme.Modules.pushforward g).rightDerived e).obj F).IsFiniteType :=
  isFiniteType_rightDerived_of_forall_exists_epi_ringBase g F e (by
    intro B inst hN X₀ g₀ hg₀
    have := hN
    have := hg₀
    obtain ⟨κ, S, hScoh, hSfin, hSgen⟩ := hfam B hN X₀ g₀ hg₀
    exact forall_exists_isCoherent_and_forall_moduleFinite_and_epi_of_epi_coproduct
      B g₀ S hScoh hSfin hSgen)

end AlgebraicGeometry

end
