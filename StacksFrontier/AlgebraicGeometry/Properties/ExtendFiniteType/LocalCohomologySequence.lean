module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRelations
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.FiniteModule
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SectionsWithSupport

/-!
# The cohomology sequence of a vanishing locus in an affine spectrum

Let `A` be a ring, let `I ⊆ A` be an ideal, let `Z = V(I)` be its vanishing locus in
`X = Spec A` and let `U = X ∖ Z`.  For a sheaf of modules on `X` there is a long exact sequence
relating the cohomology of `X` with support in `Z`, the cohomology of `X` and the cohomology of
`U`.  When the sheaf is the sheaf `M̃` attached to an `A`-module `M`, the cohomology of `X`
vanishes in positive degrees, and the long exact sequence collapses to

`0 ⟶ H⁰_Z(X, M̃) ⟶ Γ(X, M̃) ⟶ Γ(U, M̃) ⟶ H¹_Z(X, M̃) ⟶ 0`

together with isomorphisms `H^p(U, M̃) ≅ H^{p+1}_Z(X, M̃)` for `p ≥ 1`.

## Main results

* `Stacks.LocalCohomologySequence.isZero_ambientCohomology_tilde`: the positive-degree
  cohomology of `M̃` on `Spec A`, as a module over the global functions, vanishes.
* `Stacks.LocalCohomologySequence.exact_cohomologyWithSupport_sequence`: the four-term exact
  sequence and the isomorphisms in degrees `≥ 1`.
* `Stacks.LocalCohomologySequence.finite_complementCohomology_iff`: in degrees `≥ 1` the
  cohomology of `U` is a finite module over the global functions exactly when the cohomology
  with support in one degree higher is.
* `Stacks.LocalCohomologySequence.ambientCohomologyZeroIso`: the degree-zero middle term of the
  sequence is the global sections functor.

## Implementation notes

The terms of the sequence are the right derived functors of sections with support, of global
sections and of sections over the complement, all three as functors to modules over the ring of
global functions; they are the functors of Tag 0G71 and the sequence is that tag's long exact
sequence.  The middle term `H^n(Spec A, M̃)` vanishes for `n > 0` by Serre vanishing, Tag 01XB,
which is stated for the abelian-group-valued cohomology functor of Tag 01E3; the comparison
`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso` of Tag 01F1 identifies the
forgetful image of the module-valued functor with it, and forgetting the module structure is a
faithful additive functor, so it reflects zero objects
(`Stacks.LocalCohomologySequence.isZero_of_faithful`).

Exactness of a four-term sequence with zero ends is recorded as `Mono` of the first map,
`CategoryTheory.ComposableArrows.Exact` of the three-arrow chain, and `Epi` of the last map.
The three-arrow chain is extracted from the six-term window of Tag 0G71 by rebuilding the
`Exact` structure: the two chains have the same `map'` at every index that occurs, so each
field of the structure transfers once the index is a numeral.

The isomorphisms in degrees `≥ 1` are not part of the data of the long exact sequence; the
connecting map is a monomorphism because the term before it vanishes and an epimorphism because
the term after it vanishes, and modules over a ring form a balanced category.

The terms are modules over `Γ(Spec A, 𝒪)` rather than over `A`.  That ring is the `RingCat`
coercion of the sections of the structure sheaf, whereas `A` enters through the `CommRingCat`
coercion, so the two are not interchangeable in instance search; the canonical isomorphism
`M ≅ Γ(Spec A, M̃)` of `A`-modules is `AlgebraicGeometry.tilde.isIso_toOpen_top`.

## References

* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0G71](https://stacks.math.columbia.edu/tag/0G71)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.SectionsWithSupport
open RingedSpaceModuleAdjunction

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.LocalCohomologySequence

variable {A : CommRingCat.{u}}

/-- A faithful functor which preserves zero morphisms reflects zero objects. -/
theorem isZero_of_faithful {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C]
    [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.Faithful] {X : C}
    (h : IsZero (F.obj X)) : IsZero X :=
  (IsZero.iff_id_eq_zero _).mpr <| F.map_injective <| by
    rw [F.map_id, F.map_zero]
    exact h.eq_of_src _ _

/-- The vanishing locus `V(I)`, as a subset of the space underlying `Spec A`. -/
def zeroLocusSubset (I : Ideal A) : Set (Spec A).toRingedSpace :=
  PrimeSpectrum.zeroLocus (I : Set A)

/-- The vanishing locus of an ideal is closed. -/
theorem isClosed_zeroLocusSubset (I : Ideal A) : IsClosed (zeroLocusSubset I) :=
  PrimeSpectrum.isClosed_zeroLocus _

/-- The open complement of the vanishing locus is the open `Spec A ∖ V(I)`. -/
theorem openComplement_zeroLocusSubset (I : Ideal A) :
    openComplement (zeroLocusSubset I) (isClosed_zeroLocusSubset I) = zeroLocusCompl I :=
  rfl

/-- The sheaf `M̃` attached to an `A`-module, as a module over the structure sheaf of the
ringed space underlying `Spec A`. -/
abbrev tildeSheaf (M : ModuleCat.{u} A) : ModuleSheaves (Spec A).toRingedSpace :=
  tilde M

/-- `H^n_{V(I)}(Spec A, -)`, the `n`-th right derived functor of the sections with support in
the vanishing locus of `I`, valued in modules over the global functions. -/
abbrev cohomologyWithSupport (I : Ideal A) (n : ℕ) :
    ModuleSheaves (Spec A).toRingedSpace ⥤ GlobalModules (Spec A).toRingedSpace :=
  (sectionsWithSupport (Spec A).toRingedSpace (zeroLocusSubset I)
    (isClosed_zeroLocusSubset I)).rightDerived n

/-- `H^n(Spec A, -)`, valued in modules over the global functions. -/
abbrev ambientCohomology (A : CommRingCat.{u}) (n : ℕ) :
    ModuleSheaves (Spec A).toRingedSpace ⥤ GlobalModules (Spec A).toRingedSpace :=
  (SheafOfModules.evaluation (structureSheafRing (Spec A).toRingedSpace)
    (op ⊤)).rightDerived n

/-- `H^n(Spec A ∖ V(I), -)`, valued in modules over the global functions. -/
abbrev complementCohomology (I : Ideal A) (n : ℕ) :
    ModuleSheaves (Spec A).toRingedSpace ⥤ GlobalModules (Spec A).toRingedSpace :=
  (sectionsOnComplement (Spec A).toRingedSpace (zeroLocusSubset I)
    (isClosed_zeroLocusSubset I)).rightDerived n

/-- The map `H^n_{V(I)}(Spec A, -) ⟶ H^n(Spec A, -)` forgetting the support condition. -/
abbrev supportInclusion (I : Ideal A) (n : ℕ) :
    cohomologyWithSupport I n ⟶ ambientCohomology A n :=
  NatTrans.rightDerived
    (show sectionsWithSupport (Spec A).toRingedSpace (zeroLocusSubset I)
        (isClosed_zeroLocusSubset I) ⟶ _ from
      kernel.ι (restrictionToComplement (Spec A).toRingedSpace (zeroLocusSubset I)
        (isClosed_zeroLocusSubset I))) n

/-- The map `H^n(Spec A, -) ⟶ H^n(Spec A ∖ V(I), -)` restricting to the complement. -/
abbrev complementRestriction (I : Ideal A) (n : ℕ) :
    ambientCohomology A n ⟶ complementCohomology I n :=
  NatTrans.rightDerived (restrictionToComplement (Spec A).toRingedSpace (zeroLocusSubset I)
    (isClosed_zeroLocusSubset I)) n

/-- **Serre vanishing in module-valued form.** The cohomology of `M̃` on `Spec A` vanishes in
positive degrees, as a module over the global functions. -/
theorem isZero_ambientCohomology_tilde (M : ModuleCat.{u} A) (n : ℕ) (hn : 0 < n) :
    IsZero ((ambientCohomology A n).obj (tildeSheaf M)) := by
  refine isZero_of_faithful (forget₂
    (ModuleCat.{u} ((Spec A).ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u}) ?_
  refine IsZero.of_iso ?_
    ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
      (Spec A).ringCatSheaf ⊤ n).app (tildeSheaf M))
  exact Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen (Spec A)
    (tilde M : (Spec A).Modules) ⊤ (isAffineOpen_top _) n hn

/-- **Stacks Project, Tag 0BK0 (2)**, with cohomology with support in place of local cohomology.
For an ideal `I` of a ring `A` and an `A`-module `M`, write `X = Spec A`, `Z = V(I)` and
`U = X ∖ Z`.  There is a connecting map `H^n(U, M̃) ⟶ H^{n+1}_Z(X, M̃)` for which the sequence

`0 ⟶ H⁰_Z(X, M̃) ⟶ Γ(X, M̃) ⟶ Γ(U, M̃) ⟶ H¹_Z(X, M̃) ⟶ 0`

is exact and `H^p(U, M̃) ⟶ H^{p+1}_Z(X, M̃)` is an isomorphism for every `p ≥ 1`. -/
@[stacks 0BK0 "(2), with cohomology with support in place of local cohomology",
  sga "2 II Corollary4" "(4.2), (4.3)"]
theorem exact_cohomologyWithSupport_sequence (I : Ideal A) (M : ModuleCat.{u} A) :
    ∃ delta : ∀ n : ℕ, complementCohomology I n ⟶ cohomologyWithSupport I (n + 1),
      Mono ((supportInclusion I 0).app (tildeSheaf M)) ∧
      (ComposableArrows.mk₃ ((supportInclusion I 0).app (tildeSheaf M))
        ((complementRestriction I 0).app (tildeSheaf M))
        ((delta 0).app (tildeSheaf M))).Exact ∧
      Epi ((delta 0).app (tildeSheaf M)) ∧
      ∀ p : ℕ, 0 < p → IsIso ((delta p).app (tildeSheaf M)) := by
  obtain ⟨delta, hmono, hexact⟩ := longExact_rightDerived_sectionsWithSupport
    (Spec A).toRingedSpace (zeroLocusSubset I) (isClosed_zeroLocusSubset I)
  have hepi : ∀ p : ℕ, Epi ((delta p).app (tildeSheaf M)) := fun p =>
    ((hexact p (tildeSheaf M)).exact' 2 3 4).epi_f
      ((isZero_ambientCohomology_tilde M (p + 1) p.succ_pos).eq_zero_of_tgt _)
  refine ⟨delta, hmono _, ?_, hepi 0, fun p hp => ?_⟩
  · refine ComposableArrows.Exact.mk
      (ComposableArrows.IsComplex.mk fun i hi => ?_) fun i hi => ?_
    · match i, hi with
      | 0, _ => exact (hexact 0 (tildeSheaf M)).toIsComplex.zero 0
      | 1, _ => exact (hexact 0 (tildeSheaf M)).toIsComplex.zero 1
    · match i, hi with
      | 0, _ => exact (hexact 0 (tildeSheaf M)).exact 0
      | 1, _ => exact (hexact 0 (tildeSheaf M)).exact 1
  · have : Mono ((delta p).app (tildeSheaf M)) :=
      ((hexact p (tildeSheaf M)).exact' 1 2 3).mono_g
        ((isZero_ambientCohomology_tilde M p hp).eq_zero_of_src _)
    have := hepi p
    exact isIso_of_mono_of_epi _

/-- In degrees `≥ 1` the cohomology of the complement is isomorphic to the cohomology with
support in one degree higher. -/
theorem nonempty_iso_complementCohomology (I : Ideal A) (M : ModuleCat.{u} A) (p : ℕ)
    (hp : 0 < p) :
    Nonempty ((complementCohomology I p).obj (tildeSheaf M) ≅
      (cohomologyWithSupport I (p + 1)).obj (tildeSheaf M)) := by
  obtain ⟨delta, -, -, -, hiso⟩ := exact_cohomologyWithSupport_sequence I M
  have := hiso p hp
  exact ⟨asIso ((delta p).app (tildeSheaf M))⟩

/-- For `p ≥ 1` the cohomology `H^p(U, M̃)` is a finite module over the global functions exactly
when `H^{p+1}_Z(X, M̃)` is. -/
theorem finite_complementCohomology_iff (I : Ideal A) (M : ModuleCat.{u} A) (p : ℕ)
    (hp : 0 < p) :
    Module.Finite ((structureSheafRing (Spec A).toRingedSpace).obj.obj (op ⊤))
        ((complementCohomology I p).obj (tildeSheaf M)) ↔
      Module.Finite
        ((structureSheafRing (Spec A).toRingedSpace).obj.obj (op ⊤))
        ((cohomologyWithSupport I (p + 1)).obj (tildeSheaf M)) := by
  obtain ⟨e⟩ := nonempty_iso_complementCohomology I M p hp
  exact ⟨fun _ => Module.Finite.equiv e.toLinearEquiv,
    fun _ => Module.Finite.equiv e.symm.toLinearEquiv⟩

/-- The degree-zero term `H⁰(Spec A, -)` of the sequence is the global sections functor. -/
def ambientCohomologyZeroIso :
    ambientCohomology A 0 ≅
      SheafOfModules.evaluation
        (structureSheafRing (Spec A).toRingedSpace) (op ⊤) :=
  Functor.rightDerivedZeroIsoSelf _

end Stacks.LocalCohomologySequence

end
