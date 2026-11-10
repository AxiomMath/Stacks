module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CompleteGlobalSection
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.IdealOfGlobalSections

/-!
# Derived completeness along a globally generated ideal sheaf, tested at the generators

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪`, let `ℐ` be the sheaf
of ideals they generate and let `K ∈ D(𝒪)`. The predicate of [Stacks, Tag 0999] which this
library writes `AlgebraicGeometry.RingedSite.IsDerivedComplete` is a condition *per slice* and
*per local section of `ℐ`*: it asks `T(K|_V, g) = 0` for every object `V` of `𝒞` and every
section `g` of `ℐ` over `V`. This file collapses that double quantification to a condition on
the `r` generators read over `𝒞` itself, and then, through the equivalence of conditions (1) and
(3) of [Stacks, Tag 0997], to the vanishing of the `r` derived internal Homs
`R𝑆heafHom_𝒪(𝒪_{f_i}, K)` — and to the vanishing at every non-empty subproduct `f_S`.

## Main results

All names are in the namespace `AlgebraicGeometry.RingedSite`.

* `isDerivedComplete_idealOfGlobalSections_of_forall_isDerivedCompleteAt`: **from the
  generators to the ideal sheaf.** If `K` is derived complete at multiplication by each `f_i`, a
  condition over `𝒞`, then `K` is derived complete along `(f_1, …, f_r)` in the sense of
  [Stacks, Tag 0999].
* `isDerivedCompleteAt_of_isDerivedComplete_idealOfGlobalSections`:
  the converse at a single generator.
* `isDerivedComplete_idealOfGlobalSections_iff`: the two together, as an equivalence.
* `isDerivedComplete_idealOfGlobalSections_iff_forall_memVanishingIdeal`:
  the same equivalence with the condition at each generator read, through [Stacks, Tag 0997], as
  the vanishing of `R𝑆heafHom_𝒪(𝒪_{f_i}, K)`.
* `isDerivedComplete_idealOfGlobalSections_iff_forall_memVanishingIdeal_prodGlobalSection`:
  the same equivalence with the vanishing asked at every non-empty subproduct `f_S` rather than
  at the generators alone.

## Implementation notes

The generating family is universally quantified and the index set `S` of a subproduct is
quantified inside each statement; nothing here chooses a generating family for an ideal sheaf,
which is a choice that provably cannot be made functorially — see
`StacksFrontier/RingTheory/Cech/FunctorialCechFamilyObstruction.lean`.

Two passages compose to the first result:

* **descent to the slices.** Derived restriction to the slice site over `V` is additive,
  preserves the countable products of the derived categories and carries multiplication by a
  global section to multiplication by its value on the slice, so it transports the invertibility
  of the Milnor difference `1 - f_i·shift`. That is
  `AlgebraicGeometry.RingedSite.isDerivedCompleteAtSection_of_isDerivedCompleteAt` of
  `CompleteGlobalSection.lean`. It is the direction that needs no locality; the ascent, which
  does, is `isDerivedCompleteAt_of_forall_isDerivedCompleteAtSection` there, and it is what the
  converse below runs through.
* **passage from the generators to the remaining local sections of `ℐ`.** The sections at which
  the Milnor condition holds form a sheaf of ideals, [Stacks, Tag 0998], so a sheaf of ideals
  containing the generators is contained in it; that is
  `AlgebraicGeometry.RingedSite.isDerivedComplete_idealOfGlobalSections` of
  `IdealOfGlobalSections.lean`.

No multiplicativity of a sheaf of ideals is used for the subproducts, and neither
[Stacks, Tag 0998] in its assembled form nor the implication (1) ⇒ (2) of [Stacks, Tag 0997]
enters. Each `𝒪_{f_S}` with `S` non-empty is the localization at the single *global* section
`AlgebraicGeometry.RingedSite.prodGlobalSection f S`, so the equivalence of conditions (1) and
(3) reaches it directly, and the condition at `f_S` is got from the condition at any one
`f_i` with `i ∈ S` by closure of derived completeness under multiplication by a central
endomorphism — `AlgebraicGeometry.RingedSite.isDerivedCompleteAt_prodGlobalSection_of_mem`.

### What this gives for Tag 099F

The reduction of [Stacks, Tag 099B] to three properties of the Čech candidate is
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_of_completion` of
`Completion.lean`, and all three of its hypotheses are discharged at the ideal sheaf generated
by `f_1, …, f_r`: the second of them, invertibility of `K ⟶ K^∧` on a derived-complete `K`, is
`AlgebraicGeometry.RingedSite.isIso_completionUnit_app_of_isDerivedComplete` of
`CompletionUnitIso.lean`, and the first and third are in `CompletionIdempotent.lean`. The
conclusion of [Stacks, Tag 099F] for a globally generated sheaf of ideals therefore already
holds, as `AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_idealOfGlobalSections`
and, at the tag's own shape, as
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_of_eq_idealOfGlobalSections` of
`FiniteTypeGlobalSections.lean`.

So nothing on the critical path of Tag 099F is blocked on the implication (3) ⇒ (1) of
[Stacks, Tag 0997] or on the passage between the global and the per-slice shape of the Milnor
condition; both were in place before this file, which only packages their composite. What is
still open for Tag 099F is its general case, a sheaf of ideals of finite type that is only
*locally* generated by finitely many sections: the consumers that carry the tag's conclusion as
an instance hypothesis
`[(ObjectProperty.ι (AlgebraicGeometry.RingedSite.IsDerivedComplete X ℐ)).IsRightAdjoint]` do so
for an arbitrary `ℐ`, which the globally generated case cannot supply. The obstruction is
recorded in the section "What remains for Tag 099F" of `FiniteTypeGlobalSections.lean`: the
local reflectors exist, but objects of a derived category do not glue along a cover from
isomorphisms on the pieces, so the globalization has to be performed on complexes, which is
[Stacks, Tags 099D and 099E]. One route to Tag 099D is moreover *refuted*, by
`Stacks.FunctorialCechFamily.isEmpty_functorialGenerators` of
`StacksFrontier/RingTheory/Cech/FunctorialCechFamilyObstruction.lean`; this file stays clear of it
by quantifying the generating family universally in every statement.

No `@[stacks]` attribute is attached. [Stacks, Tag 0997] is a three-way equivalence whose
proved part, the equivalence of (1) and (3), is registered on
`AlgebraicGeometry.RingedSite.memVanishingIdeal_iff_isDerivedCompleteAt` of
`VanishingFromComplete.lean`; the statements below are composites of it with the two passages
above and state no tag in full. [Stacks, Tag 0999] is carried by the predicate itself.

## References

* [Stacks Project, Tag 0997](https://stacks.math.columbia.edu/tag/0997)
* [Stacks Project, Tag 0998](https://stacks.math.columbia.edu/tag/0998)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] linearCatCenterRingSheaf
  isMulCommutative_over overCatCenterLinear
  overFunctor_preservesFiniteLimits overFunctor_preservesFiniteColimits
  hasProductsOfShape_nat_derivedCategory_over

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  {r : ℕ} (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

attribute [local instance] hasProductsOfShape_nat_derivedCategory

/-- **Derived completeness at every generator gives derived completeness along the ideal sheaf
they generate.** If `K` is derived complete at multiplication by each of the global sections
`f_1, …, f_r` — the Milnor condition read over `𝒞` itself — then `K` is derived complete along
the sheaf of ideals `(f_1, …, f_r)` in the sense of [Stacks, Tag 0999], whose condition is asked
over every object of `𝒞` and at every local section of that sheaf of ideals. -/
theorem isDerivedComplete_idealOfGlobalSections_of_forall_isDerivedCompleteAt
    (hf : ∀ i : Fin r, IsDerivedCompleteAt K
      (Stacks.SheafOfModules.globalSectionToEnd
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (awayFamily X (f i)) :
        CatCenter (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    IsDerivedComplete.{u, u, u, u} X (idealOfGlobalSections X f) K :=
  isDerivedComplete_idealOfGlobalSections X f K fun i V =>
    isDerivedCompleteAtSection_of_isDerivedCompleteAt X K (f i) (hf i) V.unop

/-- **Derived completeness along the ideal sheaf generated by `f_1, …, f_r` gives it at each
generator**, as a condition over `𝒞`. This is the converse of
`isDerivedComplete_idealOfGlobalSections_of_forall_isDerivedCompleteAt`. -/
theorem isDerivedCompleteAt_of_isDerivedComplete_idealOfGlobalSections
    (hK : IsDerivedComplete.{u, u, u, u} X (idealOfGlobalSections X f) K) (i : Fin r) :
    IsDerivedCompleteAt K
      (Stacks.SheafOfModules.globalSectionToEnd
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (awayFamily X (f i)) :
        CatCenter (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  isDerivedCompleteAt_awayFamily_of_isDerivedComplete X K (f i) (idealOfGlobalSections X f)
    (fun U => globalSectionVal_mem_idealOfGlobalSections X f i (op U)) hK

/-- **Derived completeness along a globally generated sheaf of ideals is exactly derived
completeness at each generator.** The double quantification of [Stacks, Tag 0999] — over the
objects of `𝒞` and over the local sections of `(f_1, …, f_r)` — collapses to the `r` conditions
on `𝒞`. -/
theorem isDerivedComplete_idealOfGlobalSections_iff :
    IsDerivedComplete.{u, u, u, u} X (idealOfGlobalSections X f) K ↔
      ∀ i : Fin r, IsDerivedCompleteAt K
        (Stacks.SheafOfModules.globalSectionToEnd
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (awayFamily X (f i)) :
          CatCenter (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  ⟨isDerivedCompleteAt_of_isDerivedComplete_idealOfGlobalSections X K f,
    isDerivedComplete_idealOfGlobalSections_of_forall_isDerivedCompleteAt X K f⟩

/-- **Derived completeness along `(f_1, …, f_r)` is the vanishing of the `r` derived internal
Homs `R𝑆heafHom_𝒪(𝒪_{f_i}, K)`.** This is
`isDerivedComplete_idealOfGlobalSections_iff` read through the equivalence of conditions (1) and
(3) of [Stacks, Tag 0997] at each generator, `memVanishingIdeal_iff_isDerivedCompleteAt`. -/
theorem isDerivedComplete_idealOfGlobalSections_iff_forall_memVanishingIdeal :
    IsDerivedComplete.{u, u, u, u} X (idealOfGlobalSections X f) K ↔
      ∀ i : Fin r, MemVanishingIdeal X K (f i) :=
  (isDerivedComplete_idealOfGlobalSections_iff X K f).trans
    (forall_congr' fun i => (memVanishingIdeal_iff_isDerivedCompleteAt X (f i) K).symm)

/-- **Derived completeness along `(f_1, …, f_r)` is the vanishing of `R𝑆heafHom_𝒪(𝒪_{f_S}, K)`
for every non-empty `S ⊆ {1, …, r}`.** The condition at the subproducts is formally stronger than
the condition at the generators and is in fact equivalent to it: the generators are the
singletons, and conversely `f_S` is reached from any one `f_i` with `i ∈ S` because derived
completeness at a central endomorphism is closed under multiplication by an arbitrary one
(`isDerivedCompleteAt_prodGlobalSection_of_mem`), `f_S` being itself a *global* section.

Emptiness of `S` must be excluded: `f_∅ = 1` is a unit, so `𝒪_{f_∅} = 𝒪` and the vanishing
there fails for every non-zero `K`. -/
theorem isDerivedComplete_idealOfGlobalSections_iff_forall_memVanishingIdeal_prodGlobalSection :
    IsDerivedComplete.{u, u, u, u} X (idealOfGlobalSections X f) K ↔
      ∀ S : Finset (Fin r), S.Nonempty → MemVanishingIdeal X K (prodGlobalSection f S) := by
  refine ⟨fun hK S hS =>
    memVanishingIdeal_prodGlobalSection_of_isDerivedComplete X K f (idealOfGlobalSections X f)
      (fun i U => globalSectionVal_mem_idealOfGlobalSections X f i (op U)) hK hS,
    fun h => (isDerivedComplete_idealOfGlobalSections_iff_forall_memVanishingIdeal X K f).2
      fun i => ?_⟩
  simpa only [prodGlobalSection_singleton] using h {i} (Finset.singleton_nonempty i)

end AlgebraicGeometry.RingedSite

end
