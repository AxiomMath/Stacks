module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleCohomologyColimit
public import StacksFrontier.RingTheory.SpreadingOut.ColimitSystem
public import StacksFrontier.RingTheory.SpreadingOut.ColimitSystemUnivLE

/-!
# The colimit statement of Stacks 09YQ as an honest colimit cocone of abelian groups

[Stacks, Tag 09YQ] concludes an **equality of groups**: for a directed index `I`, an inverse
system `D : Iᵒᵖ ⥤ Scheme` of quasi-compact and quasi-separated schemes with affine transition
morphisms, a limit cone `c` with vertex `X = lim X_i`, a system `F` of abelian sheaves on the
small étale sites of the levels in the sense of [Stacks, Tag 0EZL], and a sheaf `𝒢` on the small
étale site of `X` presenting `colim f_i^{-1}F_i`,

`colim_i H^p(X_i, F_i) = H^p(X, 𝒢)` for every `p ≥ 0`.

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleCohomologyColimit.lean` states
that conclusion **elementwise**, as
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsCohomologyColimit`: the cocone legs
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem.leg` are jointly surjective,
and a class at a level killed by its leg is killed by some transition. This file proves that
those two clauses are **exactly** the assertion that the cohomology cocone is a colimit cocone in
`AddCommGrpCat`, which is what the docstring of `IsCohomologyColimit` asserts and what a faithful
registration of the tag's own equality of groups needs.

## Main definitions

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.cohomologyIdem` — the transition of a
  presented system along an *identity* index, which is an idempotent endomorphism of
  `H^p(X_i, F_i)` and in general not the identity (see the implementation notes).
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.stableCohomologySubgroup` — its image, the
  **stable part** of `H^p(X_i, F_i)`.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.stableCohomologyDiagram` and
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.stableCohomologyCocone` — the functor
  `I ⥤ AddCommGrpCat` of the stable parts with the transitions of the system as its arrows, and
  the cocone on it with legs the maps to `H^p(X, 𝒢)`. These exist for **every** presented
  system.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.HasCohomologyIdentityLaw` — the hypothesis
  that the transition along an identity index acts as the identity on cohomology.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.levelCohomologyDiagram` and
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.levelCohomologyCocone` — under that
  hypothesis, the diagram whose object at `i` is `H^p(X_i, F_i)` itself and whose arrows are
  `Stacks.EtaleCohomology.etaleCohomologyTransition`, with the same cocone. This is the tag's
  own diagram, spelled with no subgroup in it.

## Main results

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_iff_nonempty_isColimit`
  — **the bridge, hypothesis-free**: for a directed index,
  `IsCohomologyColimit E p` holds if and only if `stableCohomologyCocone E p` is a colimit
  cocone in `AddCommGrpCat.{u + 1}`. Both directions are proved; the one a registration of
  Tag 09YQ needs is `isColimit_stableCohomologyCocone`.
* `isCohomologyColimit_iff_nonempty_isColimit_level` — **the bridge in the tag's own spelling**:
  with the identity law in hand, `IsCohomologyColimit E p` holds if and only if
  `levelCohomologyCocone E p hid` is a colimit cocone, i.e. if and only if `H^p(X, 𝒢)` *is*
  `colim_i H^p(X_i, F_i)`.
* `hasCohomologyIdentityLaw_iff_forall_stableCohomologySubgroup_eq_top` — **exactly when the stable
  part is the whole group**: the stable subgroup is all of `H^p(X_i, F_i)` at every level if and
  only if the identity law holds. This is what decides which of the two bridges states the tag; see
  the discussion below.

## Why there are two diagrams, and why neither is a weakening

A `CategoryTheory.Limits.IsColimit` needs a **functor**, and the assignment
`i ↦ H^p(X_i, F_i)` with the maps `Stacks.EtaleCohomology.etaleCohomologyTransition` is not one:
[Stacks, Tag 0EZL] — `Stacks.EtaleCohomology.EtaleSheafSystem` — follows the source in imposing
only the cocycle condition and no identity law, so the transition along an identity index is
merely an idempotent. The gap is not bookkeeping. It is proved in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleSystemIdentityLaw.lean`: the
system with all transitions zero (`zeroTransitionSystem`) is a legitimate system with a colimit
presentation, and `id_eq_zero_of_isIso_systemTransitionMap_zeroTransitionSystem` shows its
identity transition is invertible only on a zero sheaf. So no plain functor on `I` can have the
`H^p(X_i, F_i)` as its objects and the transitions as its arrows, and the elementwise
`IsCohomologyColimit` is not equivalent to any statement that pretends otherwise.

The repair is the one this development already uses on the sheaves, in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleKaroubiColimit.lean`: split the
idempotent. `AddCommGrpCat` is abelian, so the splitting is concrete — the image subgroup — and
`stableCohomologyDiagram` is the resulting honest functor, with no hypothesis added and the
colimit taken in `AddCommGrpCat` rather than in a Karoubi envelope. Nothing is lost on the way to
the limit: a class and its image under the idempotent have the same leg
(`leg_cohomologyIdem`), and a class killed by its leg has the same fate as its stable part
(`etaleCohomologyTransition_cohomologyIdem`), which is why the equivalence with the elementwise
statement is an honest `Iff`.

`HasCohomologyIdentityLaw` is then not an extra mathematical hypothesis but the exact condition
under which the tag's literal diagram exists; it holds in the source, where the transition along
an identity is the identity, and under it the two diagrams have the same objects. Both bridges
are proved, so a consumer with the identity law in hand gets the tag's own spelling, and a
consumer without it still gets a colimit of abelian groups.

## Does passing to the stable part change the group?

This is the question a registration of Tag 09YQ has to answer, because the tag's left-hand side
is a colimit of the **full** groups `H^p(X_i, F_i)`, and `stableCohomologyDiagram` has the stable
subgroups as its objects. The answer is settled here rather than argued, by
`hasCohomologyIdentityLaw_iff_forall_stableCohomologySubgroup_eq_top`:

**the stable subgroup is the full group at every level if and only if the identity law holds.**

Three consequences, which is everything a consumer needs.

*The colimit vertex is never a subgroup.* Both cocones have vertex
`AddCommGrpCat.of (Sheaf.H E.sheaf p)` — the full `H^p(X, 𝒢)`, which is the tag's right-hand
side — and both have the honest legs `PresentedSystem.leg`. Only the *diagram* differs.

*Under the identity law the two statements are the same statement.* The stable subgroups are then
all `⊤` (`stableCohomologySubgroup_eq_top_of_hasCohomologyIdentityLaw`), and
`levelCohomologyDiagram` — objects literally `Sheaf.H (E.sys.obj (Opposite.op i)) p`, arrows
literally `Stacks.EtaleCohomology.etaleCohomologyTransition` — is available with its own bridge.
**A registration of Tag 09YQ should be made against `isColimit_levelCohomologyCocone`**, not
against the stable form: it is the tag's own diagram, with the identity law as its only extra
input, and the identity law is exactly the source's `φ_{ii} = id`.

*Without the identity law there is no second group to disagree with.* The identity transition is
then only an idempotent, so `i ↦ H^p(X_i, F_i)` with these arrows is not a functor and
`colim_i H^p(X_i, F_i)` has no referent at all; the stable form is not a different colimit of the
tag's diagram but the only colimit the datum supports — it is the Karoubi colimit of
`SmallEtaleKaroubiColimit.lean`, carried out in `AddCommGrpCat`. What the elementwise `Iff` does
buy in that case is real and should not be overstated into more: `IsCohomologyColimit` quantifies
over the full groups at every level and over all of `H^p(X, 𝒢)`, and
`isCohomologyColimit_iff_nonempty_isColimit` is an equivalence with it in both directions, so the
stable cocone being a colimit is *equivalent to* a condition on the full groups. It does not make
the stable subgroups equal to them.

Nothing in this tree discharges `HasCohomologyIdentityLaw` for a general system, and that is a
statement about the tree, not a gap in this file: `EtaleSheafSystem`
(`Colimits/SheafSystems.lean`, `@[stacks 0EZL]`) has fields `obj`, `map` and `map_comp` and no
`map_id`, and the sheaf-level identity law that would imply this one is *refuted* for a legitimate
system by `id_eq_zero_of_isIso_systemTransitionMap_zeroTransitionSystem`. The one system of the
development for which the sheaf-level law is proved is the direct-image system
(`Stacks.EtaleCohomology.directImageSystem_map_id`), and that proof has not been transported to
`Sheaf.H`.

## Implementation notes

**The variance.** For `a : i ⟶ j` in `Iᵒᵖ` the transition `etaleCohomologyTransition` goes
`H^p(X_j, F_j) → H^p(X_i, F_i)` (`PresentedSystem.transition_comp`), so both diagrams here are
functors on `I` and not on `Iᵒᵖ`; the object at `i : I` is the one at `Opposite.op i`.
`Opposite.op (Opposite.unop i) = i` holds by definitional unfolding, which is what lets a family
indexed by `Iᵒᵖ` be read as a cocone indexed by `I`, exactly as in `SmallEtaleKaroubiColimit.lean`.

**The criterion used.** The concrete description of a filtered colimit of abelian groups —
jointly surjective legs, and an element of a stage that dies in the vertex dying at a later
stage — is `Stacks.SpreadingOut.LocalModuleSystem.isColimitAddCommGrpCatOf`, which this file
imports rather than restates; the two converse halves are Mathlib's
`CategoryTheory.Limits.Concrete.isColimit_exists_rep` and
`CategoryTheory.Limits.Concrete.isColimit_exists_of_rep_eq`. The import of
`StacksFrontier.RingTheory.SpreadingOut.ColimitSystem` into an étale-cohomology module is only for
that criterion, which is general and lives there.

**Universes.** The coefficients are at `AddCommGrpCat.{u + 1}` and the index `I` is at its own
level `v`, so `UnivLE.{v, u + 1}` is needed: it is what makes a colimit of shape `I` exist in
`AddCommGrpCat.{u + 1}` and makes the forgetful functor preserve it. It is a universe side
condition, not a restriction on the mathematics, and it is already a hypothesis of the other
consumers in this development — see
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.nonempty_devissage`. `Nonempty I` and
`IsDirected I (· ≤ ·)` are what make `I` filtered; `IsDirected` is a hypothesis of Tag 09YQ
itself.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  [∀ i : Iᵒᵖ, HasExt.{u + 1} (Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1})]
  {c : Cone D} [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})]
  {P : (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) →
      (𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) →
      (∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢) → Prop}

/-! ### The idempotent of an identity transition, and the stable part of the cohomology -/

/-- **The transition of a presented system along an identity index, on cohomology.** The cocycle
condition of [Stacks, Tag 0EZL] makes this an idempotent endomorphism of `H^p(X_i, F_i)`
(`cohomologyIdem_cohomologyIdem`); the identity law, which the source does not impose on a
system, would make it the identity. -/
def cohomologyIdem (E : PresentedSystem P) (p : ℕ) (i : Iᵒᵖ) :
    Sheaf.H.{u + 1, u + 1} (E.sys.obj i) p →+ Sheaf.H.{u + 1, u + 1} (E.sys.obj i) p :=
  etaleCohomologyTransition E.sys (𝟙 i) p

/-- **A transition absorbs the identity idempotent of its source level**: passing to the stable
part before transitioning changes nothing. -/
theorem etaleCohomologyTransition_cohomologyIdem (E : PresentedSystem P) (p : ℕ) {i j : Iᵒᵖ}
    (a : i ⟶ j) (x : Sheaf.H.{u + 1, u + 1} (E.sys.obj j) p) :
    etaleCohomologyTransition E.sys a p (cohomologyIdem E p j x) =
      etaleCohomologyTransition E.sys a p x := by
  rw [cohomologyIdem, E.transition_comp a (𝟙 j) p x, Category.comp_id]

/-- **A transition lands in the stable part of its target level.** -/
theorem cohomologyIdem_etaleCohomologyTransition (E : PresentedSystem P) (p : ℕ) {i j : Iᵒᵖ}
    (a : i ⟶ j) (x : Sheaf.H.{u + 1, u + 1} (E.sys.obj j) p) :
    cohomologyIdem E p i (etaleCohomologyTransition E.sys a p x) =
      etaleCohomologyTransition E.sys a p x := by
  rw [cohomologyIdem, E.transition_comp (𝟙 i) a p x, Category.id_comp]

/-- **The identity transition on cohomology is idempotent.** -/
theorem cohomologyIdem_cohomologyIdem (E : PresentedSystem P) (p : ℕ) (i : Iᵒᵖ)
    (x : Sheaf.H.{u + 1, u + 1} (E.sys.obj i) p) :
    cohomologyIdem E p i (cohomologyIdem E p i x) = cohomologyIdem E p i x :=
  cohomologyIdem_etaleCohomologyTransition E p (𝟙 i) x

/-- **A class and its stable part have the same image on the limit.** -/
theorem leg_cohomologyIdem (E : PresentedSystem P) (p : ℕ) (i : Iᵒᵖ)
    (x : Sheaf.H.{u + 1, u + 1} (E.sys.obj i) p) :
    E.leg i p (cohomologyIdem E p i x) = E.leg i p x :=
  E.leg_comp_transition (𝟙 i) p x

/-- **The stable part of the cohomology at a level**: the image of the idempotent
`cohomologyIdem`, which is the splitting of that idempotent in the abelian category
`AddCommGrpCat`. Under the identity law it is all of `H^p(X_i, F_i)`. -/
def stableCohomologySubgroup (E : PresentedSystem P) (p : ℕ) (i : Iᵒᵖ) :
    AddSubgroup (Sheaf.H.{u + 1, u + 1} (E.sys.obj i) p) :=
  (cohomologyIdem E p i).range

/-- A class is stable exactly when the identity transition fixes it. -/
theorem mem_stableCohomologySubgroup_iff (E : PresentedSystem P) (p : ℕ) (i : Iᵒᵖ)
    {x : Sheaf.H.{u + 1, u + 1} (E.sys.obj i) p} :
    x ∈ stableCohomologySubgroup E p i ↔ cohomologyIdem E p i x = x := by
  rw [stableCohomologySubgroup, AddMonoidHom.mem_range]
  refine ⟨?_, fun h => ⟨x, h⟩⟩
  rintro ⟨y, rfl⟩
  exact cohomologyIdem_cohomologyIdem E p i y

/-! ### The cohomology diagram and cocone of a presented system -/

/-- **The cohomology diagram of a presented system.** The object at `i : I` is the stable part of
`H^p(X_i, F_i)` and the arrow of `α : i ⟶ j` is the transition of the system along `α.op`,
restricted to the stable parts. This is a functor for every presented system: the identity law
that `H^p(X_i, F_i)` itself lacks holds on the stable part by
`mem_stableCohomologySubgroup_iff`. -/
def stableCohomologyDiagram (E : PresentedSystem P) (p : ℕ) : I ⥤ AddCommGrpCat.{u + 1} where
  obj i := AddCommGrpCat.of (stableCohomologySubgroup E p (Opposite.op i))
  map {i j} α := AddCommGrpCat.ofHom
    (AddMonoidHom.mk'
      (fun x : stableCohomologySubgroup E p (Opposite.op i) =>
        (⟨etaleCohomologyTransition E.sys α.op p x.1,
          (mem_stableCohomologySubgroup_iff E p (Opposite.op j)).2
            (cohomologyIdem_etaleCohomologyTransition E p α.op x.1)⟩ :
            stableCohomologySubgroup E p (Opposite.op j)))
      (fun x y => Subtype.ext (map_add (etaleCohomologyTransition E.sys α.op p) x.1 y.1)))
  map_id i := by
    ext x
    exact (mem_stableCohomologySubgroup_iff E p (Opposite.op i)).1 x.2
  map_comp {i j k} α β := by
    ext x
    exact (E.transition_comp β.op α.op p x.1).symm

/-- The arrows of `stableCohomologyDiagram` are the transitions of the system. -/
theorem stableCohomologyDiagram_map_val (E : PresentedSystem P) (p : ℕ) {i j : I} (α : i ⟶ j)
    (x : stableCohomologySubgroup E p (Opposite.op i)) :
    ((stableCohomologyDiagram E p).map α x).1 = etaleCohomologyTransition E.sys α.op p x.1 :=
  rfl

/-- **The cohomology cocone of a presented system**: the cocone on `stableCohomologyDiagram`
with vertex `H^p(X, 𝒢)` whose legs are the maps
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem.leg`. The cocone law is
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem.leg_comp_transition`. -/
def stableCohomologyCocone (E : PresentedSystem P) (p : ℕ) :
    Cocone (stableCohomologyDiagram E p) where
  pt := AddCommGrpCat.of (Sheaf.H.{u + 1, u + 1} E.sheaf p)
  ι :=
    { app := fun i => AddCommGrpCat.ofHom
        ((E.leg (Opposite.op i) p).comp (stableCohomologySubgroup E p (Opposite.op i)).subtype)
      naturality := fun i j α => by
        ext x
        exact E.leg_comp_transition α.op p x.1 }

/-- The legs of `stableCohomologyCocone` are the legs of the presented system. -/
theorem stableCohomologyCocone_ι_app_apply (E : PresentedSystem P) (p : ℕ) (i : I)
    (x : stableCohomologySubgroup E p (Opposite.op i)) :
    (stableCohomologyCocone E p).ι.app i x = E.leg (Opposite.op i) p x.1 :=
  rfl

/-! ### The bridge -/

/-- **The elementwise statement of Tag 09YQ makes the cohomology cocone a colimit cocone.**

This is the direction a registration of [Stacks, Tag 09YQ] needs: it turns
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsCohomologyColimit` into the tag's own
equality of groups, `H^p(X, 𝒢) = colim_i H^p(X_i, F_i)` in `AddCommGrpCat.{u + 1}`.

Joint surjectivity is the first clause of `IsCohomologyColimit` composed with
`leg_cohomologyIdem`, which moves the chosen class into the stable part without changing its
leg; the eventual vanishing is the second clause verbatim. -/
def isColimit_stableCohomologyCocone [IsDirected I (· ≤ ·)] [Nonempty I] [UnivLE.{v, u + 1}]
    (E : PresentedSystem P) (p : ℕ) (h : IsCohomologyColimit E p) :
    IsColimit (stableCohomologyCocone E p) := by
  refine Stacks.SpreadingOut.LocalModuleSystem.isColimitAddCommGrpCatOfUnivLE.{v, u + 1} _ _
    (fun y => ?_) (fun j y hy => ?_)
  · obtain ⟨i, x, hx⟩ := h.exists_leg_eq y
    exact ⟨i.unop, ⟨cohomologyIdem E p i x, ⟨x, rfl⟩⟩, (leg_cohomologyIdem E p i x).trans hx⟩
  · obtain ⟨k, a, hk⟩ := h.exists_transition_eq_zero (Opposite.op j) y.1 hy
    exact ⟨k.unop, a.unop, Subtype.ext hk⟩

/-- A colimit cocone over a directed index in `AddCommGrpCat` has jointly surjective legs, and an
element killed by its leg is killed by some transition. -/
private theorem exists_rep_and_exists_map_eq_zero_of_isColimit [IsDirected I (· ≤ ·)]
    [Nonempty I] [UnivLE.{v, u + 1}] {F : I ⥤ AddCommGrpCat.{u + 1}} {t : Cocone F}
    (hc : IsColimit t) :
    (∀ y : t.pt, ∃ j z, t.ι.app j z = y) ∧
      ∀ j z, t.ι.app j z = 0 → ∃ k, ∃ f : j ⟶ k, F.map f z = 0 := by
  let : PreservesFilteredColimitsOfSize.{v, v} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE _
  refine ⟨Concrete.isColimit_exists_rep _ hc, fun j z hz => ?_⟩
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq _ hc z 0
    (hz.trans (map_zero _).symm)
  exact ⟨k, f, by rwa [map_zero] at hfg⟩

/-- **Conversely, a colimit cocone gives the elementwise statement.** A filtered colimit of
abelian groups is computed on elements, so joint surjectivity of the legs and the eventual
vanishing of a class killed by its leg are consequences of the universal property; the passage
between a class and its stable part is `leg_cohomologyIdem` and
`etaleCohomologyTransition_cohomologyIdem`. -/
theorem isCohomologyColimit_of_isColimit [IsDirected I (· ≤ ·)] [Nonempty I]
    [UnivLE.{v, u + 1}] (E : PresentedSystem P) (p : ℕ)
    (hc : IsColimit (stableCohomologyCocone E p)) : IsCohomologyColimit E p := by
  obtain ⟨h₁, h₂⟩ := exists_rep_and_exists_map_eq_zero_of_isColimit hc
  refine ⟨fun y => ?_, fun i x hx => ?_⟩
  · obtain ⟨j, z, hz⟩ := h₁ y
    exact ⟨Opposite.op j, z.1, hz⟩
  · obtain ⟨k, f, hf⟩ := h₂ i.unop ⟨cohomologyIdem E p i x, ⟨x, rfl⟩⟩
      ((leg_cohomologyIdem E p i x).trans hx)
    exact ⟨Opposite.op k, f.op,
      (etaleCohomologyTransition_cohomologyIdem E p f.op x).symm.trans (Subtype.ext_iff.mp hf)⟩

/-- **The elementwise statement of Tag 09YQ is exactly the colimit statement.** For a directed
index, `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsCohomologyColimit` holds if and only
if the cohomology cocone of the presented system is a colimit cocone in `AddCommGrpCat.{u + 1}`.
This is the assertion the docstring of `IsCohomologyColimit` makes, and it holds for every
presented system with no further hypothesis. -/
theorem isCohomologyColimit_iff_nonempty_isColimit [IsDirected I (· ≤ ·)] [Nonempty I]
    [UnivLE.{v, u + 1}] (E : PresentedSystem P) (p : ℕ) :
    IsCohomologyColimit E p ↔ Nonempty (IsColimit (stableCohomologyCocone E p)) :=
  ⟨fun h => ⟨isColimit_stableCohomologyCocone E p h⟩,
    fun h => isCohomologyColimit_of_isColimit E p h.some⟩

/-! ### The tag's own diagram, under the identity law -/

/-- **The identity law on cohomology**: the transition along an identity index acts as the
identity on `H^p(X_i, F_i)`. [Stacks, Tag 0EZL] does not impose it — see the discussion in the
module docstring and the counterexample in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleSystemIdentityLaw.lean` — and
it is exactly what is needed for the cohomology groups of the levels themselves to form a
diagram. -/
def HasCohomologyIdentityLaw (E : PresentedSystem P) (p : ℕ) : Prop :=
  ∀ (i : Iᵒᵖ) (x : Sheaf.H.{u + 1, u + 1} (E.sys.obj i) p),
    etaleCohomologyTransition E.sys (𝟙 i) p x = x

/-- **Under the identity law the stable part is the whole cohomology group.** So the diagram of
`stableCohomologyDiagram` then has the groups `H^p(X_i, F_i)` of [Stacks, Tag 09YQ] themselves as
its objects, and `isColimit_stableCohomologyCocone` and `isColimit_levelCohomologyCocone` are the
same statement. -/
theorem stableCohomologySubgroup_eq_top_of_hasCohomologyIdentityLaw (E : PresentedSystem P)
    (p : ℕ) (hid : HasCohomologyIdentityLaw E p) (i : Iᵒᵖ) :
    stableCohomologySubgroup E p i = ⊤ :=
  (AddSubgroup.eq_top_iff' _).2 fun x => (mem_stableCohomologySubgroup_iff E p i).2 (hid i x)

/-- **Exactly when passing to the stable part loses nothing.** The stable part is all of
`H^p(X_i, F_i)` at every level if and only if the system satisfies the identity law on cohomology.

This is what decides which of this file's two bridges states [Stacks, Tag 09YQ]: with the identity
law the stable diagram *is* the tag's diagram of the full groups, and without it the tag's diagram
does not exist, the identity transition being only an idempotent. Either way the colimit vertex is
the full `H^p(X, 𝒢)`; only the diagram is at issue. -/
theorem hasCohomologyIdentityLaw_iff_forall_stableCohomologySubgroup_eq_top
    (E : PresentedSystem P) (p : ℕ) :
    HasCohomologyIdentityLaw E p ↔ ∀ i : Iᵒᵖ, stableCohomologySubgroup E p i = ⊤ :=
  ⟨stableCohomologySubgroup_eq_top_of_hasCohomologyIdentityLaw E p,
    fun h i x => (mem_stableCohomologySubgroup_iff E p i).1 (by simp [h i])⟩

/-- **The diagram of the cohomology of the levels**, for a system satisfying the identity law:
the object at `i : I` is `H^p(X_i, F_i)` itself and the arrow of `α : i ⟶ j` is
`Stacks.EtaleCohomology.etaleCohomologyTransition` along `α.op`. This is the diagram
[Stacks, Tag 09YQ] takes the colimit of. -/
def levelCohomologyDiagram (E : PresentedSystem P) (p : ℕ) (hid : HasCohomologyIdentityLaw E p) :
    I ⥤ AddCommGrpCat.{u + 1} where
  obj i := AddCommGrpCat.of (Sheaf.H.{u + 1, u + 1} (E.sys.obj (Opposite.op i)) p)
  map {i j} α := AddCommGrpCat.ofHom (etaleCohomologyTransition E.sys α.op p)
  map_id i := by
    ext x
    exact hid (Opposite.op i) x
  map_comp {i j k} α β := by
    ext x
    exact (E.transition_comp β.op α.op p x).symm

/-- **The cocone of [Stacks, Tag 09YQ]**: the cocone on `levelCohomologyDiagram` with vertex
`H^p(X, 𝒢)` and legs `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem.leg`. -/
def levelCohomologyCocone (E : PresentedSystem P) (p : ℕ) (hid : HasCohomologyIdentityLaw E p) :
    Cocone (levelCohomologyDiagram E p hid) where
  pt := AddCommGrpCat.of (Sheaf.H.{u + 1, u + 1} E.sheaf p)
  ι :=
    { app := fun i => AddCommGrpCat.ofHom (E.leg (Opposite.op i) p)
      naturality := fun i j α => by
        ext x
        exact E.leg_comp_transition α.op p x }

/-- **[Stacks, Tag 09YQ] as an equality of groups.** For a system satisfying the identity law on
cohomology, the elementwise statement makes `H^p(X, 𝒢)` the colimit of the diagram of the
`H^p(X_i, F_i)` along the transition maps, in `AddCommGrpCat.{u + 1}`. -/
def isColimit_levelCohomologyCocone [IsDirected I (· ≤ ·)] [Nonempty I] [UnivLE.{v, u + 1}]
    (E : PresentedSystem P) (p : ℕ) (hid : HasCohomologyIdentityLaw E p)
    (h : IsCohomologyColimit E p) : IsColimit (levelCohomologyCocone E p hid) := by
  refine Stacks.SpreadingOut.LocalModuleSystem.isColimitAddCommGrpCatOfUnivLE.{v, u + 1} _ _
    (fun y => ?_) (fun j y hy => ?_)
  · obtain ⟨i, x, hx⟩ := h.exists_leg_eq y
    exact ⟨i.unop, x, hx⟩
  · obtain ⟨k, a, hk⟩ := h.exists_transition_eq_zero (Opposite.op j) y hy
    exact ⟨k.unop, a.unop, hk⟩

/-- **Conversely**, the colimit statement for the diagram of the levels gives the elementwise
statement. -/
theorem isCohomologyColimit_of_isColimit_level [IsDirected I (· ≤ ·)] [Nonempty I]
    [UnivLE.{v, u + 1}] (E : PresentedSystem P) (p : ℕ) (hid : HasCohomologyIdentityLaw E p)
    (hc : IsColimit (levelCohomologyCocone E p hid)) : IsCohomologyColimit E p := by
  obtain ⟨h₁, h₂⟩ := exists_rep_and_exists_map_eq_zero_of_isColimit hc
  refine ⟨fun y => ?_, fun i x hx => ?_⟩
  · obtain ⟨j, z, hz⟩ := h₁ y
    exact ⟨Opposite.op j, z, hz⟩
  · obtain ⟨k, f, hf⟩ := h₂ i.unop x hx
    exact ⟨Opposite.op k, f.op, hf⟩

/-- **The bridge in the tag's own spelling.** For a directed index and a system satisfying the
identity law on cohomology, the elementwise statement of [Stacks, Tag 09YQ] holds if and only if
`H^p(X, 𝒢)` is the colimit of the `H^p(X_i, F_i)` along the transitions of the system. -/
theorem isCohomologyColimit_iff_nonempty_isColimit_level [IsDirected I (· ≤ ·)] [Nonempty I]
    [UnivLE.{v, u + 1}] (E : PresentedSystem P) (p : ℕ) (hid : HasCohomologyIdentityLaw E p) :
    IsCohomologyColimit E p ↔ Nonempty (IsColimit (levelCohomologyCocone E p hid)) :=
  ⟨fun h => ⟨isColimit_levelCohomologyCocone E p hid h⟩,
    fun h => isCohomologyColimit_of_isColimit_level E p hid h.some⟩

end Stacks.EtaleCohomology.SmallEtaleLimitCohomology
