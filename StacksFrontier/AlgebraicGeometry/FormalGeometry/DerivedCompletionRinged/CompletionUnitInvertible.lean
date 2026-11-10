module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Completion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CompletionUnitIso
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.GeneratedIdealSheaf
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.SliceRestrictionDescent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingCriterionCoextension

/-!
# The completion map is invertible on a derived-complete complex

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪` and write
`K^∧ = R𝑆heafHom_𝒪(Č(f), K)` for the candidate completion functor of [Stacks, Tag 099B] built
in `Completion.lean`. The dévissage of `CompletionUnitIso.lean`,
`AlgebraicGeometry.RingedSite.isIso_completionUnit_app_of_forall_memVanishingIdeal`, makes
`K ⟶ K^∧` invertible once `R𝑆heafHom_𝒪(𝒪_{f_S}, K) = 0` for every non-empty subset `S` of the
index set. This file lowers that hypothesis first to the generators — it is enough that
`R𝑆heafHom_𝒪(𝒪_{f_i}, K) = 0` for each `i` — and then all the way to **derived completeness of
`K` itself**, which is the `hη` hypothesis of
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_of_completion`.

## Main results

* `AlgebraicGeometry.RingedSite.memVanishingIdeal_prodGlobalSection_of_mem`: the vanishing locus
  of `K` contains the subproduct `f_S` as soon as it contains one `f_i` with `i ∈ S`.
* `AlgebraicGeometry.RingedSite.isIso_completionUnit_app_of_memVanishingIdeal_generators`:
  `K ⟶ K^∧` is invertible once `R𝑆heafHom_𝒪(𝒪_{f_i}, K) = 0` for each generator.
* `AlgebraicGeometry.RingedSite.memVanishingIdeal_of_isDerivedComplete`: a generator that is a
  section of `I` over every object lies in the vanishing locus of every `K` derived complete
  along `I`.
* **`hη` at an arbitrary sheaf of ideals `I`** — `K ⟶ K^∧` is invertible on every `K` derived
  complete along `I`, provided each `f_i` is a section of `I` — is
  `AlgebraicGeometry.RingedSite.isIso_completionUnit_app_of_isDerivedComplete` of
  `CompletionUnitIso.lean`, and is not repeated here; at `ℐ` below the generator form above and
  the descent `memVanishingIdeal_of_isDerivedComplete` give it directly.
* `AlgebraicGeometry.RingedSite.isIso_completionUnit_app_of_isDerivedComplete_generatedIdealSheaf`:
  **`hη` at the ideal sheaf `ℐ = (f_1, …, f_r)`, with nothing carried.** This is the `hη`
  argument of `isRightAdjoint_ι_isDerivedComplete_of_completion_generatedIdealSheaf`.
* `isRightAdjoint_ι_isDerivedComplete_generatedIdealSheaf_of_isDerivedComplete_completion`:
  the [Stacks, Tag 099F] reduction at `ℐ` with `hη` discharged, so that only `hΦ` and `hcomm`
  remain.

## Implementation notes

The multiplicativity is the composition of two known results and contains no new mathematics.
The implication (1) ⇒ (2) of [Stacks, Tag 0997],
`AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_awayRestrictScalars_of_isZero` of
`VanishingCriterionCoextension.lean`, turns the vanishing of `R𝑆heafHom_𝒪(𝒪_{f_i}, K)` into right
orthogonality of `K` to `D(𝒪_{f_i})` — and `AlgebraicGeometry.RingedSite.MemVanishingIdeal` and
`AlgebraicGeometry.RingedSite.IsRightOrthogonalAway` of `VanishingIdeal.lean` are by definition
that implication's hypothesis and conclusion, so no bridge is needed. Right orthogonality then
propagates from the singleton `{i}` to any larger `S` by
`AlgebraicGeometry.RingedSite.memVanishingIdeal_prodGlobalSection_of_subset`, because `f_i`
divides `f_S`.

Why this is not in `Completion.lean`: importing `VanishingCriterionCoextension.lean` there
changes the instances in scope enough that the `omit` clause of
`AlgebraicGeometry.RingedSite.completionFunctor_obj_eq_derivedSheafHom_flip` in
`KoszulLimitFormula.lean` — a downstream consumer of `Completion.lean` — stops being
discharged, Lean reporting `cannot omit referenced section variable` for
`X.J.WEqualsLocallyBijective AddCommGrpCat`. Keeping these declarations here leaves the import
surface of `Completion.lean` alone, and nothing else is lost: they are all statements about the
completion map and are reached from the library's root import all the same.

*From the slices to the site.* `hη` asks for the invertibility of `K ⟶ K^∧` for a `K` that is
derived complete along the ideal sheaf, which is
`AlgebraicGeometry.RingedSite.IsDerivedComplete` — a condition over every object `U` of the site
about the restriction `K|_U` to the slice. It therefore yields `T(K|_U, g) = 0` for every local
section `g` of the ideal over `U`, and not `T(K, f_i) = 0` on the site itself, which is what
(1) ⇔ (3) of [Stacks, Tag 0997] converts into the vanishing. Descending the latter from the
former is `AlgebraicGeometry.RingedSite.memVanishingIdeal_of_forall_isDerivedCompleteAt_over` of
`SliceRestrictionDescent.lean`.

Taking `g` to be the *value of `f_i` over `U`* is the only thing the predicate has to be fed, and
it is the only place the membership hypothesis is used: the descent carries no information about
the ideal sheaf, by design, so at a free `I` the membership of the generators in `I` must be
supplied. At `I = generatedIdealSheaf f` it is a theorem of `GeneratedIdealSheaf.lean` and
nothing is carried.

The spelling of the slice scalar is what makes that projection a projection and not a transport.
`((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U` and
`(Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)` are different spellings of one sheaf of
rings and instance search does not pass between them, so a statement mixing a scalar in one
spelling with a category in the other has no `Linear` instance at all. Both
`AlgebraicGeometry.RingedSite.IsDerivedComplete` and the descent keep to
`Stacks.SheafOfModules.terminalSectionToEnd` at the scalar
`((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U`, so the existential the predicate produces
is the descent's hypothesis on the nose.

*Sheafification of abelian groups* is needed by the descent and is not carried: it holds on every
`RingedSite.{u, u, u}` by `AlgebraicGeometry.RingedSite.hasSheafifyAddCommGroup`, and the proofs
below supply it, so the statements have the same instance surface as the reduction they feed.

### What this does not close

Of the three hypotheses of
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_of_completion`, this file closes
`hη` only. `hΦ` — every `K^∧` is derived complete along `ℐ` — is closed in
`GeneratedIdealComplete.lean`, by
`AlgebraicGeometry.RingedSite.isDerivedComplete_generatedIdealSheaf_completionFunctor_obj`, using
the additivity of the vanishing locus of [Stacks, Tag 0998]. `hcomm` is not a consequence of the
other two — the two-object counterexample
`Stacks.Algebraization.CompletionUnitSharpness.exists_completionFunctor_and_not_isRightAdjoint_ι`
of `StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletion.lean` satisfies `hΦ` and `hη`
and its inclusion has no left adjoint. So [Stacks, Tag 099F] does **not** close here; the
assembly waiting for `hcomm` alone is
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_generatedIdealSheaf_of_comm`
of `GeneratedIdealComplete.lean`.

Nothing carries a `stacks` attribute. The multiplicativity is a step inside the proof of
[Stacks, Tag 0998] — recorded there under the right-orthogonality condition as
`AlgebraicGeometry.RingedSite.isRightOrthogonalAway_mulGlobalSection` — and the invertibility
statements are steps inside the proof of [Stacks, Tag 099B], whose conclusion they do not reach:
`hη` is a *hypothesis* of that tag's reduction, not a clause of the tag.

## References

* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 0997](https://stacks.math.columbia.edu/tag/0997)
* [Stacks Project, Tag 0998](https://stacks.math.columbia.edu/tag/0998)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The vanishing locus of `K` contains every subproduct `f_S` of a global section it
contains.** If `R𝑆heafHom_𝒪(𝒪_{f_i}, K) = 0` and `i ∈ S`, then `R𝑆heafHom_𝒪(𝒪_{f_S}, K) = 0`.

This is the multiplicativity that the source of [Stacks, Tag 099B] uses to pass from the
generators `f_i` to the subproducts `f_S`: the implication (1) ⇒ (2) of [Stacks, Tag 0997] turns
the vanishing at `f_i` into right orthogonality to `D(𝒪_{f_i})`, which propagates to `f_S`
because `f_i` divides it. Nothing is assumed of `K` or of the sections. -/
theorem memVanishingIdeal_prodGlobalSection_of_mem
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {S : Finset (Fin r)} {i : Fin r}
    (hi : i ∈ S) (H : MemVanishingIdeal X K (f i)) :
    MemVanishingIdeal X K (prodGlobalSection f S) := by
  refine memVanishingIdeal_prodGlobalSection_of_subset X K f
    (Finset.singleton_subset_iff.mpr hi) ?_
  rw [prodGlobalSection_singleton]
  exact isZero_derivedSheafHom_awayRestrictScalars_of_isZero X (f i) K H

/-- **The completion map `K ⟶ K^∧` is invertible as soon as the derived internal Hom into `K`
kills each generator `𝒪_{f_i}`.** The multiplicativity above raises the hypothesis from the
generators to the subproducts `f_S`, and
`AlgebraicGeometry.RingedSite.isIso_completionUnit_app_of_forall_memVanishingIdeal` then runs the
dévissage of the stupid filtration of `Č(f)`.

Nothing is assumed of `K` or of the sections. This is `hη` on the near side of the slice-site
descent: derived completeness along an ideal sheaf is a condition on the restrictions `K|_U`,
whereas the vanishing here is the condition on the site; the descent between them is
`memVanishingIdeal_of_isDerivedComplete` below. -/
theorem isIso_completionUnit_app_of_memVanishingIdeal_generators
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : ∀ i : Fin r, MemVanishingIdeal X K (f i)) :
    IsIso ((completionUnit X f).app K) :=
  isIso_completionUnit_app_of_forall_memVanishingIdeal X f K fun _ hS ↦ by
    obtain ⟨i, hi⟩ := hS
    exact memVanishingIdeal_prodGlobalSection_of_mem X f K hi (hK i)

end Derived

section Descent

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isMulCommutative_ringSheaf_over linearCatCenterOver

/-- **A generator belonging to the ideal sheaf lies in the vanishing locus of every complex
derived complete along that ideal sheaf**: if `K` is derived complete along `I` in the sense of
[Stacks, Tag 0999] and the value of `f_i` over every object of the site is a section of `I`
there, then `R𝑆heafHom_𝒪(𝒪_{f_i}, K) = 0`.

Derived completeness along `I` is a condition on the *restrictions* `K|_V`: it gives
`T(K|_V, g|_V) = 0` for every object `V` and every section `g` of `I` over `V`. Taking `g` to be
the value of `f_i` over `V` — which is where the membership hypothesis is used, and the only
place it is used — this supplies the whole family of slice conditions that
`AlgebraicGeometry.RingedSite.memVanishingIdeal_of_forall_isDerivedCompleteAt_over` descends to
the site, after which (1) ⇔ (3) of [Stacks, Tag 0997] is the vanishing.

Nothing is assumed of the site beyond [Stacks, Tag 0999]'s own setting: the sheafification of
abelian groups that the descent uses is available on every ringed site of these universes, by
`AlgebraicGeometry.RingedSite.hasSheafifyAddCommGroup`, and is supplied in the proof rather than
carried. -/
theorem memVanishingIdeal_of_isDerivedComplete
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : IsDerivedComplete.{u, u, u, u} X I K) (i : Fin r)
    (hmem : ∀ U : X.C, globalSectionVal (f i) (op U) ∈ I.toSubmodule.obj (op U)) :
    MemVanishingIdeal X K (f i) :=
  have : HasSheafify X.J AddCommGrpCat.{u} := hasSheafifyAddCommGroup X.J
  memVanishingIdeal_of_forall_isDerivedCompleteAt_over X (f i) K fun V ↦
    (hK V (globalSectionVal (f i) (op V)) (hmem V)).2.2.2.2

/-- **`hη` for [Stacks, Tag 099B] at its own ideal sheaf, with nothing carried.** If `K` is
derived complete along the ideal sheaf `ℐ = (f_1, …, f_r)` generated by the sections the Čech
complex is built from, then `K ⟶ K^∧` is invertible.

The membership hypothesis of `isIso_completionUnit_app_of_isDerivedComplete` of
`CompletionUnitIso.lean` is discharged outright at `ℐ` by
`AlgebraicGeometry.RingedSite.forall_globalSectionVal_mem_toSubmodule_generatedIdealSheaf`, so
this statement has no hypotheses beyond derived completeness of `K` itself. It is the `hη`
argument of
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_of_completion_generatedIdealSheaf`
verbatim. -/
theorem isIso_completionUnit_app_of_isDerivedComplete_generatedIdealSheaf
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : IsDerivedComplete.{u, u, u, u} X (generatedIdealSheaf f) K) :
    IsIso ((completionUnit X f).app K) :=
  isIso_completionUnit_app_of_memVanishingIdeal_generators X f K fun i ↦
    memVanishingIdeal_of_isDerivedComplete X f (generatedIdealSheaf f) K hK i
      (forall_globalSectionVal_mem_toSubmodule_generatedIdealSheaf f i)

/-- **[Stacks, Tag 099F] for the ideal sheaf generated by `f_1, …, f_r`, with `hη` discharged.**
This is
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_of_completion_generatedIdealSheaf`
with its second hypothesis proved rather than assumed: only `hΦ` — every completion `K^∧` is
derived complete along `ℐ` — and `hcomm` — the completion functor carries `K ⟶ K^∧` to
`K^∧ ⟶ (K^∧)^∧` — remain.

`hcomm` is not a consequence of the other two: the two-object counterexample
`Stacks.Algebraization.CompletionUnitSharpness.exists_completionFunctor_and_not_isRightAdjoint_ι`
satisfies `hΦ` and `hη` and its inclusion has no left adjoint. -/
theorem isRightAdjoint_ι_isDerivedComplete_generatedIdealSheaf_of_isDerivedComplete_completion
    (hΦ : ∀ K, IsDerivedComplete.{u, u, u, u} X (generatedIdealSheaf f)
      ((completionFunctor X f).obj K))
    (hcomm : ∀ K, (completionFunctor X f).map ((completionUnit X f).app K) =
      (completionUnit X f).app ((completionFunctor X f).obj K)) :
    (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X (generatedIdealSheaf f))).IsRightAdjoint :=
  isRightAdjoint_ι_isDerivedComplete_of_completion_generatedIdealSheaf X f hΦ
    (isIso_completionUnit_app_of_isDerivedComplete_generatedIdealSheaf X f) hcomm

end Descent

end AlgebraicGeometry.RingedSite

end
