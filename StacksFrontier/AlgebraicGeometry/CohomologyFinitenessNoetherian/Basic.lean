module

public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.RingBase
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.EulerCharVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SituationProjective

/-!
# [Stacks, Tag 02O6] over a Noetherian ring from a supply of resolving modules

[Stacks, Tag 02O6] says that for `A` Noetherian, `f : X ⟶ Spec A` proper and `ℱ` coherent, each
`Hⁿ(X, ℱ)` is a finite `A`-module. The reduction of that statement to a single hypothesis — every
coherent module is a quotient of a coherent module whose cohomology is already finite — exists in
this repository only **over a field**, in
`StacksFrontier/AlgebraicGeometry/CohomologyFinitenessResolution/Basic.lean`, where the
cohomology is a `k`-vector space and finiteness is `FiniteDimensional`. That is not the tag's
statement, and it is not what the Noetherian-stage consumers need. This file makes the same
reduction at an arbitrary commutative ring base, in the `A`-module spelling
`StacksFrontier/AlgebraicGeometry/ProperCohomologyFinite/RingBase.lean` lands the tag's
conclusion in.

**The two inputs that are unconditional.** Above a single degree there is nothing to assume: a
proper `X` is quasi-compact, hence has a finite affine cover, and separated, hence has affine
diagonal, so [Stacks, Tag 01XI] kills the cohomology of every quasi-coherent module beyond the
size of that cover, and a vanishing module is finite. And the property propagates across a short
exact sequence in the one position the induction needs: `Hⁿ(X, ℱ₃)` sits in the long exact
sequence of the higher direct images between `Hⁿ(X, ℱ₂)` and `Hⁿ⁺¹(X, ℱ₁)`, and over a Noetherian
ring a module between two finite modules in an exact sequence is finite.

**Why Noetherianness is needed here and not over a field, and where exactly.** Over a field,
finiteness of the middle term of a three term exact sequence is `Module.finiteDimensional_of_exact`
and holds unconditionally, because a subspace of a finite-dimensional space is finite-dimensional.
Over a general ring that fails, and the replacement is
`Module.finite_of_exact_of_isNoetherianRing` below: the kernel of the second map is contained in
the range of the first, which is Noetherian because `A` is and the source is finite, so the kernel
is finite, and the quotient by it embeds in the third module. That is the *only* place
Noetherianness enters this file; the vanishing input and the descending induction are
Noetherian-free.

**What is not here.** The hypothesis is suppliable on projective space by the Čech computation of
[Stacks, Tag 01XT] together with the "quotient of twists" clause of [Stacks, Tag 01YS], neither of
which is in the library. The twist-power bridge of
`StacksFrontier/AlgebraicGeometry/CohomologyFinitenessTwists/Basic.lean` is stated over a field
only, because the `k`-linear identification of the cohomology of a power is; the corresponding
`A`-linear identification is not made *here*, but it is available —
`AlgebraicGeometry.nonempty_cohomology_ringBase_biprodPow_linearEquiv` of
`StacksFrontier/AlgebraicGeometry/CohomologyFinitenessTwists/RingBase.lean` supplies it with no
hypothesis on `f`, none on the module and no Noetherian hypothesis, and
`AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_epi_biprodPow` there feeds it
straight into the `hgen` slot of
`forall_moduleFinite_cohomology_ringBase_of_exists_epi` below, so the abstract supply of
resolving modules is now also available as a family of twists at a Noetherian ring base.

## Main results

* `Module.finite_of_exact_of_isNoetherianRing`: over a Noetherian ring, the middle module of a
  three term exact sequence of finite modules is finite.
* `Module.finite_of_isZero`: a module with one element is finite.
* `AlgebraicGeometry.moduleFinite_cohomology_ringBase_three_of_shortExact`: `Hⁿ(X, ℱ₃)` is a
  finite `A`-module as soon as `Hⁿ(X, ℱ₂)` and `Hⁿ⁺¹(X, ℱ₁)` are. **No hypothesis on `f` or on
  the modules.**
* `AlgebraicGeometry.exists_isZero_rightDerived_moduleGlobalSections_of_isProper`: **
  unconditional.** For `X` proper over `Spec A` there is a degree beyond which the cohomology of
  every quasi-coherent module vanishes.
* `AlgebraicGeometry.exists_forall_moduleFinite_cohomology_ringBase_of_le_of_isProper`: the same,
  read as finiteness; **unconditional, and with no Noetherian hypothesis.**
* `AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_exists_epi_of_le`: the descending
  induction, with the vanishing degree as a hypothesis and no condition on `f`.
* `AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_exists_epi`: **[Stacks, Tag 02O6]
  over a Noetherian ring from the single hypothesis that every coherent module is a quotient of a
  coherent module with finite cohomology.**
* `AlgebraicGeometry.forall_isCoherent_rightDerived_of_exists_epi`: the same hypothesis gives
  [Stacks, Tag 02O5] over an affine Noetherian base, by the equivalence of
  `StacksFrontier/AlgebraicGeometry/ProperCohomologyFinite/RingBase.lean`.

## Implementation notes

**No tag attribute is attached to anything here, and this file proves no tag.** The two theorems
that reach the conclusion of [Stacks, Tag 02O6] carry the supply of resolving modules as an
explicit hypothesis, which is the content of [Stacks, Tag 01XT] and of a clause of
[Stacks, Tag 01YS]; by the covering-set rule the attribute belongs on neither. The attribute
tokens are deliberately not spelled out in this comment: a comment-blind attribute grep reads a
spelled token as coverage.

**The `δ`-functor is built here rather than reused.** `EulerCharAdditivity/Basic.lean` builds the
long exact sequence of global-sections cohomology, but both the functor it derives and the
`δ`-functor are `private` there and are stated over a field after restriction of scalars. The
generic constructor `Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives` is public
and needs nothing beyond additivity of the functor and enough injectives, so it is instantiated
here at the public `Stacks.Cohomology.AffineBase.moduleGlobalSections`, whose target is
`ModuleCat Γ(X, ⊤)` and mentions no base. Only one of its exactness fields is used — exactness at
`Eⁿ(ℱ₃)`, between the map out of `Eⁿ(ℱ₂)` and the connecting map into `Eⁿ⁺¹(ℱ₁)` — so the
connecting morphisms appear in no statement.

**Restriction of scalars is free on exactness.** `Module.restrictScalars` changes neither the
carrier nor the underlying map, so `Function.Exact` transports along it by `fun x => h x`. That is
why the `A`-module statements can be read off a long exact sequence of `Γ(X, ⊤)`-modules with no
further work, and it is the same observation the field development makes with its private
`function_exact_restrictToBase`.

**`Module.finite_of_exact_of_isNoetherianRing` duplicates a private lemma.**
`StacksFrontier/Algebra/Homology/InjectiveDimension/Noetherian.lean` carries the same fact as a
`private lemma module_finite_of_exact`, reachable from nowhere else. It is restated here in the
`Function.Exact` idiom rather than de-privatised, since that file's only consumer is its own next
declaration; the two could be merged.

In detail, since "the same fact" understates the difference: the private lemma's hypothesis is
`∀ x, φ₂ x = 0 → ∃ y, φ₁ y = x`, which is only `ker φ₂ ≤ range φ₁`, so it is **strictly more
general** than the `Function.Exact` form here; its finiteness hypotheses are instance binders
rather than explicit arguments; and it proves the fact through `isNoetherian_of_le`,
`LinearMap.quotKerEquivRange` and `Module.Finite.of_submodule_quotient` where this one is a
one-line adapter for Mathlib's `isNoetherian_of_range_eq_ker`. So the two are not duplicates by
the hypothesis test, and routing either to the other is a *move* of the fact to a file both trees
can import — `StacksFrontier/Algebra/Homology/InjectiveDimension/Noetherian.lean` is not in this
file's import closure and `StacksDraft.InjectiveDimension` is not
a home for a `Module`-namespace algebra fact. Mathlib's own `Module.Finite.of_exact` does not
cover either, since it requires `Function.Surjective` of the second map.

**At a field this is the existing field statement, but not by elaboration.** In both
directions: the conclusion below with `A := k` and the conclusion of
`forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_isProper` imply each other by
`id` *after* one rewrite with
`Stacks.AlgebraicGeometry.ProperCohomologyFinite.cohomologyOverField_eq_restrictScalars_appTop`,
and **not** without it: `AlgebraicGeometry.cohomologyOverField` restricts scalars along
`f.appLE ⊤ ⊤ _`, which is `f.app ⊤ ≫ X.presheaf.map (homOfLE _).op` and is therefore *not*
`rfl`-equal to the `f.appTop` the ring-base spelling uses. So the two developments meet through
that bridge and through nothing else; a consumer that tries `exact` across the seam gets a
type mismatch naming two terms that print almost identically.

**Which coherence predicate.** `SheafOfModules.IsCoherent` here is the root-level class declared in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentFinitePresentation.lean`. The enclosing
namespace is `AlgebraicGeometry` and not one beginning with `Stacks`, so the relative name resolves
to it and not to the distinct `Stacks.SheafOfModules.IsCoherent`, which has the same two fields; the
statements of `StacksFrontier/AlgebraicGeometry/ProperCohomologyFinite/RingBase.lean` use the same
one, so the two compose with no bridge.

## References

* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.ProperCohomologyFinite

universe u

namespace Module

/-- **Over a Noetherian ring the middle module of a three term exact sequence of finite modules
is finite.** This is the replacement for `Module.finiteDimensional_of_exact`, which is
unconditional over a field because a subspace of a finite-dimensional space is
finite-dimensional.

The kernel of `b` is contained in the range of `a`, which is Noetherian because `A` is and `M` is
finite; so `ker b` is Noetherian, and `N` is Noetherian by `isNoetherian_of_range_eq_ker`. -/
theorem finite_of_exact_of_isNoetherianRing {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M N P : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] (hM : Module.Finite A M) (hP : Module.Finite A P)
    (a : M →ₗ[A] N) (b : N →ₗ[A] P) (h : Function.Exact a b) : Module.Finite A N :=
  have := hM
  have := hP
  have : IsNoetherian A M := isNoetherian_of_isNoetherianRing_of_finite A M
  have : IsNoetherian A P := isNoetherian_of_isNoetherianRing_of_finite A P
  have : IsNoetherian A N := isNoetherian_of_range_eq_ker a b (LinearMap.exact_iff.mp h).symm
  inferInstance

/-- A module with one element is finite over any ring. The ring-base analogue of
`AlgebraicGeometry.finiteDimensional_of_isZero`, which is what makes the vanishing degrees free.

Stated for an object of `ModuleCat A` and with the vanishing an explicit argument, so that the
object is fixed by unification against the expected type: an instance *binder* would not be found
at a goal phrased with `ModuleCat.restrictScalars`, whose object carries the same carrier behind a
semireducible definition. -/
theorem finite_of_isZero {A : Type u} [CommRing A] {M : ModuleCat.{u} A}
    (h : CategoryTheory.Limits.IsZero M) : Module.Finite A M :=
  have : Subsingleton M := ModuleCat.subsingleton_of_isZero h
  have : Finite M := Finite.of_subsingleton
  inferInstance

end Module

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- The long exact sequence of global-sections cohomology, valued in `Γ(X, ⊤)`-modules, as the
cohomological `δ`-functor of [Stacks, Tag 010Q]. There is no base and no hypothesis on `X`: the
generic constructor needs only additivity of the functor and enough injectives on `X.Modules`.
Only exactness at `Eⁿ(ℱ₃)` is used below, so the connecting morphisms appear in no statement. -/
private def moduleGlobalSectionsDeltaFunctor (X : Scheme.{u}) :
    CategoryTheory.DeltaFunctor X.Modules (ModuleCat.{u} Γ(X, ⊤)) :=
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (moduleGlobalSections X)

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-! ### Propagation across a short exact sequence -/

/-- **Finiteness of the right-hand cohomology of a short exact sequence, over a Noetherian ring.**
`Hⁿ(X, ℱ₃)` is a finite `A`-module as soon as `Hⁿ(X, ℱ₂)` and `Hⁿ⁺¹(X, ℱ₁)` are: the long exact
sequence of global-sections cohomology is exact at `Hⁿ(X, ℱ₃)` between the map out of
`Hⁿ(X, ℱ₂)` and the connecting map into `Hⁿ⁺¹(X, ℱ₁)`, and restriction of scalars to `A` leaves
both the carriers and the maps alone, so the exactness is the same statement about `A`-modules.

There is no hypothesis on `f`, on the modules, or on coherence. This is the ring-base analogue of
`finiteDimensional_cohomologyOverField_three_of_shortExact`, which needs no Noetherian
hypothesis. -/
theorem moduleFinite_cohomology_ringBase_three_of_shortExact [IsNoetherianRing A]
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (n : ℕ)
    (h₂ : Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj S.X₂)))
    (h₁ : Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived (n + 1)).obj S.X₁))) :
    Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj S.X₃)) :=
  have hex : Function.Exact
      (((moduleGlobalSectionsDeltaFunctor X).functor n).map S.g)
      ((moduleGlobalSectionsDeltaFunctor X).δ hS n) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((moduleGlobalSectionsDeltaFunctor X).exact_δ₁ hS n)
  Module.finite_of_exact_of_isNoetherianRing h₂ h₁
    ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).map
      (((moduleGlobalSectionsDeltaFunctor X).functor n).map S.g)).hom
    ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).map
      ((moduleGlobalSectionsDeltaFunctor X).δ hS n)).hom
    (fun x => hex x)

/-! ### Above the vanishing bound there is nothing to assume -/

/-- **Vanishing of the cohomology in high degrees, unconditionally.** For `X` proper over
`Spec A` there is a single degree `N` beyond which `Hⁿ(X, ℱ)` vanishes for *every* quasi-coherent
`ℱ`, in the `Γ(X, ⊤)`-module spelling of [Stacks, Tag 01XK].

The bound is the size of a finite affine open cover of `X`, which exists because a proper
morphism is quasi-compact; `X` is separated because `f` is and `Spec A` is, so the absolute
diagonal is affine, and [Stacks, Tag 01XI] applies. This is the ring-base analogue of
`exists_isZero_cohomologyOverField_of_isProper`, and nothing in it mentions `A` except through
`f`. -/
theorem exists_isZero_rightDerived_moduleGlobalSections_of_isProper [IsProper f] :
    ∃ N : ℕ, ∀ F : X.Modules, F.IsQuasicoherent →
      ∀ n : ℕ, N ≤ n → IsZero (((moduleGlobalSections X).rightDerived n).obj F) := by
  have : CompactSpace X := (AlgebraicGeometry.quasiCompact_iff_compactSpace f).mp inferInstance
  have hsep : IsSeparated (terminal.from X) := by
    have : IsSeparated (f ≫ terminal.from (Spec (.of A))) := inferInstance
    simpa using this
  have : IsAffineHom (pullback.diagonal (terminal.from X)) := inferInstance
  obtain ⟨t, U, hU, hcover⟩ :=
    Stacks.Cohomology.FiniteCover.exists_fin_affine_cover_of_isCompact X ⊤ (by
      change IsCompact (Set.univ : Set X); exact isCompact_univ)
  refine ⟨t, fun F hF n hn => ?_⟩
  have := hF
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff (moduleGlobalSections X) n F).2
    ((isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup X F n).2
      (Stacks.Cohomology.FiniteCover.isZero_Hgroup_of_finite_affine_cover X F U hU ⊤ hcover n hn))

/-- **Finiteness of the cohomology in high degrees, unconditionally and with no Noetherian
hypothesis.** For `X` proper over `Spec A` there is a single degree `N` beyond which `Hⁿ(X, ℱ)` is
a finite `A`-module for every quasi-coherent `ℱ`, because beyond that degree it vanishes. -/
theorem exists_forall_moduleFinite_cohomology_ringBase_of_le_of_isProper [IsProper f] :
    ∃ N : ℕ, ∀ F : X.Modules, F.IsQuasicoherent → ∀ n : ℕ, N ≤ n → Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj F)) := by
  obtain ⟨N, hN⟩ := exists_isZero_rightDerived_moduleGlobalSections_of_isProper A f
  exact ⟨N, fun F hF n hn => Module.finite_of_isZero
    (((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom)).map_isZero
      (hN F hF n hn))⟩

/-! ### The descending induction -/

/-- **[Stacks, Tag 02O6] over a Noetherian ring by descending induction on the degree.** Suppose
`Hⁿ(X, ℱ)` is a finite `A`-module for every coherent `ℱ` and every `n ≥ N`, and that every
coherent module is the target of an epimorphism from a coherent module whose cohomology is finite
in *every* degree. Then `Hⁿ(X, ℱ)` is a finite `A`-module for every coherent `ℱ` and every `n`.

There is no hypothesis on `f`: properness enters only through `N`, which is discharged in
`forall_moduleFinite_cohomology_ringBase_of_exists_epi`. The step takes the kernel of the
epimorphism, coherent by [Stacks, Tag 01BY] (3), and applies
`moduleFinite_cohomology_ringBase_three_of_shortExact` to its kernel sequence. -/
theorem forall_moduleFinite_cohomology_ringBase_of_exists_epi_of_le [IsNoetherianRing A] (N : ℕ)
    (hN : ∀ G : X.Modules, SheafOfModules.IsCoherent G → ∀ n : ℕ, N ≤ n → Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj G)))
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ E : X.Modules, SheafOfModules.IsCoherent E ∧
        (∀ n : ℕ, Module.Finite A
          ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
            (((moduleGlobalSections X).rightDerived n).obj E))) ∧ ∃ φ : E ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G → ∀ n : ℕ, Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj G)) := by
  have key : ∀ d : ℕ, ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, N ≤ n + d → Module.Finite A
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
          (((moduleGlobalSections X).rightDerived n).obj G)) := by
    intro d
    induction d with
    | zero => exact fun G hG n hn => hN G hG n (by omega)
    | succ d ih =>
      intro G hG n hn
      by_cases hnd : N ≤ n + d
      · exact ih G hG n hnd
      obtain ⟨E, hE, hEfin, φ, hφ⟩ := hgen G hG
      have := hE
      have := hG
      have hker : SheafOfModules.IsCoherent (kernel φ) := SheafOfModules.kernel_isCoherent φ
      have hSE : (ShortComplex.kernelSequence φ).ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact φ) inferInstance hφ
      exact moduleFinite_cohomology_ringBase_three_of_shortExact A f hSE n (hEfin n)
        (ih (kernel φ) hker (n + 1) (by omega))
  exact fun G hG n => key N G hG n (by omega)

/-- **[Stacks, Tag 02O6] over a Noetherian ring from a supply of resolving modules.** For `X`
proper over `Spec A` with `A` Noetherian, if every coherent module on `X` is a quotient of a
coherent module whose cohomology is a finite `A`-module in every degree, then `Hⁿ(X, ℱ)` is a
finite `A`-module for every coherent `ℱ` and every `n`.

The vanishing degree is supplied by
`exists_forall_moduleFinite_cohomology_ringBase_of_le_of_isProper`, and a coherent module is
quasi-coherent by [Stacks, Tag 01BW]. This is the statement the Noetherian-stage consumers of
this tree need, and the field-only
`forall_finiteDimensional_cohomologyOverField_of_exists_epi_of_isProper` is not an instance of it
nor it of that. -/
theorem forall_moduleFinite_cohomology_ringBase_of_exists_epi [IsNoetherianRing A] [IsProper f]
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ E : X.Modules, SheafOfModules.IsCoherent E ∧
        (∀ n : ℕ, Module.Finite A
          ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
            (((moduleGlobalSections X).rightDerived n).obj E))) ∧ ∃ φ : E ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G → ∀ n : ℕ, Module.Finite A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj G)) := by
  obtain ⟨N, hN⟩ := exists_forall_moduleFinite_cohomology_ringBase_of_le_of_isProper A f
  refine forall_moduleFinite_cohomology_ringBase_of_exists_epi_of_le A f N
    (fun G hG n hn => hN G ?_ n hn) hgen
  have := hG
  exact isQuasicoherent_of_isCoherent G

/-- **[Stacks, Tag 02O5] over an affine Noetherian base from the same hypothesis.** Coherence of
`Rⁿ f_* ℱ` for every coherent `ℱ` follows from the supply of resolving modules, because over a
Noetherian ring finiteness of `Hⁿ(X, ℱ)` as an `A`-module *is* coherence of `Rⁿ f_* ℱ`, by
`isCoherent_rightDerived_of_moduleFinite_cohomology_ringBase` of
`Stacks.AlgebraicGeometry.ProperCohomologyFinite`.

So the two tags are one obligation over an affine base, and the hypothesis below is the single
thing that remains to be computed on projective space. -/
theorem forall_isCoherent_rightDerived_of_exists_epi [IsNoetherianRing A] [IsProper f]
    (hgen : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∃ E : X.Modules, SheafOfModules.IsCoherent E ∧
        (∀ n : ℕ, Module.Finite A
          ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
            (((moduleGlobalSections X).rightDerived n).obj E))) ∧ ∃ φ : E ⟶ G, Epi φ) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, (((Scheme.Modules.pushforward f).rightDerived n).obj G).IsCoherent := by
  intro G hG n
  have := hG
  have : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  exact isCoherent_rightDerived_of_moduleFinite_cohomology_ringBase A f G n
    (forall_moduleFinite_cohomology_ringBase_of_exists_epi A f hgen G hG n)

end AlgebraicGeometry

end
