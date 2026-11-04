module

public import StacksFrontier.AlgebraicGeometry.LiftInvertible.NilpotentUnits
public import StacksFrontier.AlgebraicGeometry.PicSurjectiveFinite.Basic

/-!
# Lifting an invertible module along a closed immersion from a star-shaped cover

Let `i : Z ⟶ X` be a **surjective** closed immersion and let `L` be an invertible `𝒪_Z`-module.
[Stacks, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY) asserts that `L` is the pullback
of an invertible `𝒪_X`-module whenever `X` is Noetherian of dimension at most one. This file
proves that conclusion from a *combinatorial hypothesis on the trivializing cover*: that the
cover is **star-shaped** around one of its members.

Concretely: a cover of `X` by charts over whose inverse images `L` is trivial, one distinguished
chart `V` (the centre), with the property that **two distinct charts meet only inside `V`**, and
with each overlap of a chart with the centre affine — or already carrying the central generator,
which is the case for the centre's own overlap with itself. Then `L` is the pullback of an
invertible `𝒪_X`-module.

## Why that hypothesis is the whole of the difficulty

Over an affine open the sections of `𝒪_X` surject onto those of `𝒪_Z`, and when `i` is onto the
kernel consists of nilpotents, so that surjection surjects on units
(`Stacks.LiftInvertible.exists_unitsMap_app_eq_of_surjective`). So the transition unit of two
chart trivializations of `L` lifts to a unit on `X` — but **one overlap at a time, and not
canonically**, so a family of chosen lifts satisfies neither the restriction law nor the cocycle
law. That is the real content of Tag 09NY, and the reason the tag is not a consequence of a
lifting lemma: the degree-two Čech obstruction has to vanish.

A star-shaped cover makes it vanish *identically*. Only the overlaps of a chart with the centre
carry a chosen lift; every other transition is **defined** as the ratio of two of those lifts,
which is legitimate because an overlap of two distinct charts lies inside the centre, where both
lifts are defined. The restriction law then holds by functoriality of restriction and the
cocycle law by unit arithmetic — the three laws below mention neither `L` nor the lifting of
units nor any hypothesis on the ideal sheaf.

This is the shape of the two-layer cover of a Noetherian space of dimension at most one produced
by `Stacks.Topology.Dimension.exists_isolating_cover_of_topologicalKrullDim_le_one`, for an
**irreducible** `X`: the centre is the dense open subordinate to the trivializing cover, the
remaining charts are the isolating neighbourhoods of the finitely many points of its complement,
and that the latter meet pairwise inside the former is one of that theorem's conclusions. What
is **not** proved here is the production of such a cover from the dimension bound; see the
implementation notes.

## Main definitions

* `Stacks.LiftInvertible.appUnits`: the map on units induced by `i` on sections, in the spelling
  in which the transition units of local generators live.
* `Stacks.LiftInvertible.StarLiftData`: chart data with a distinguished central chart, a
  generator of `L` over the inverse image of the centre, and a chosen unit on each overlap with
  the centre expressing that chart's generator through the central one.
* `Stacks.LiftInvertible.StarLiftData.transition`: the transition units on `X` — the ratio of
  two chosen lifts over an open inside the centre, and one elsewhere.
* `Stacks.LiftInvertible.StarLiftData.toLiftedChartData`: the star data read as the input of the
  comparison of `Stacks.PicFinite.LiftedChartData`.

## Main results

* `Stacks.LiftInvertible.exists_appUnits_eq`: a unit of `Γ(Z, i⁻¹U)` is the image of a unit of
  `Γ(X, U)`, for `U` affine and `i.ker ≤ X.nilradical`, i.e. for `i` onto.
* `Stacks.LiftInvertible.StarLiftData.transition_restrict`,
  `Stacks.LiftInvertible.StarLiftData.transition_symm` and
  `Stacks.LiftInvertible.StarLiftData.transition_cocycle`: the three laws of a unit cocycle, for
  the transitions built from the chosen lifts. **This is where the star shape is used**, and the
  only place.
* `Stacks.LiftInvertible.StarLiftData.map_transition`: the transition unit pulls back to the
  ratio of the two chart generators.
* `nonempty_starLiftData_of_ker_le_nilradical_of_generator_eq_or_isAffineOpen`, in
  `Stacks.LiftInvertible`:
  **the chosen lifts exist** when `i` is onto and each overlap with the centre is affine or
  already carries the central generator. The second alternative is what keeps the hypothesis
  satisfiable: the centre is the chart of every point it contains, and in the one-dimensional
  application it is a dense open with finite complement, not an affine.
* `Stacks.LiftInvertible.nonempty_starLiftData_of_isNilpotent_ker_of_generator_eq_or_isAffineOpen`
  and `Stacks.LiftInvertible.nonempty_starLiftData_of_isNilpotent_ker`: its nilpotent special
  case, and the all-affine form of that, which asks in particular that the centre be affine.
* `Stacks.LiftInvertible.exists_modulePullback_iso_of_starLiftData`: **the conclusion of Tag
  09NY** from star data, in Tag 09NY's own spelling.
* `Stacks.LiftInvertible.exists_modulePullback_iso_of_starChartData_of_ker_le_nilradical`: the
  same with the chosen lifts replaced by `i.ker ≤ X.nilradical` and the condition on the
  overlaps. **This is Tag 09NY for a surjective closed immersion admitting a star-shaped
  trivializing cover with affine central overlaps.**
  `Stacks.LiftInvertible.exists_modulePullback_iso_of_starChartData_of_isNilpotent_ker` is its
  nilpotent special case.

## Implementation notes

No `@[stacks 09NY]` attribute is attached to anything in this file. Tag 09NY asserts the
conclusion for every closed immersion into a Noetherian scheme of dimension at most one, with no
hypothesis on the ideal sheaf and none on the cover, and both of this file's hypotheses are
genuine restrictions:

* **Surjectivity of `i` is not removable; nilpotency of `i.ker` was never needed.** What the
  chosen lifts require is that the kernel over each affine open consist of nilpotents, which is
  `i.ker ≤ X.nilradical` and, for a closed immersion, is exactly surjectivity of the underlying
  map. Only one kernel element is ever inverted, so no uniform nilpotency exponent enters;
  nilpotency of `i.ker` implies the bound. Surjectivity itself cannot
  be dropped: for `Spec k[t]/(t(t-1)) ⟶ Spec k[t]` the map on units is `kˣ → kˣ × kˣ`, the units
  of `k[t]` being the constants, so in characteristic `≠ 2` the unit `(1, -1)` has no lift and
  the chosen lifts of this file do not exist — and that `i` is precisely not onto, its image
  being two points of the affine line. A proof of Tag 09NY for a closed immersion that is not
  onto must modify the trivializations themselves. The surjective case is the one that matters
  downstream and needs no hypothesis on `X` at all: `Z = X_red` has the same underlying space as
  `X` by construction, and that is the instance of Tag 09NY which
  [Stacks, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ) consumes.
* **The star cover is not produced from the dimension bound here.** Three steps separate the two,
  all in the topology of a one-dimensional Noetherian scheme rather than in sheaf theory, and the
  first of them is proved.
  (a) The dimension bound and Noetherianness have to be transported from `X` to an affine
  chart's spectrum, which is where the punctured-basic-open lemma
  `exists_basicOpen_sdiff_singleton_eq_basicOpen_of_topologicalKrullDim_le_one` of
  `StacksFrontier/AlgebraicGeometry/LiftInvertible/PuncturedBasicOpen.lean` states its
  hypotheses. **Proved**, as
  `Stacks.LiftInvertible.topologicalKrullDim_primeSpectrum_le_of_isAffineOpen` and
  `Stacks.LiftInvertible.noetherianSpace_primeSpectrum_of_isAffineOpen`.
  (b) An isolating neighbourhood then has to be shrunk inside a chart so that its punctured part
  is again *basic*, hence affine, and so that it meets the complement of the centre in its own
  point alone — which asks for a function in the maximal ideal of that point avoiding every
  minimal prime, i.e. prime avoidance, and for the punctured-basic-open lemma with one extra
  finite set of primes to avoid.
  (c) A reducible `X` needs the per-component pieces of a punctured neighbourhood — which
  `Stacks.Topology.Dimension.exists_isolating_cover_of_topologicalKrullDim_le_one` does supply,
  as a *disjoint* decomposition — glued into one unit, which calls for a chosen lift per
  irreducible component rather than per point. For irreducible `X`, (c) is vacuous.

The chart index is the carrier of `X`, as in `Stacks.PicFinite.ChartData`, which `StarLiftData`
extends: the centre is then the chart of every point it contains, and "two distinct charts meet
only inside the centre" is `Stacks.PicFinite.ChartData.inf_chart_le` with `V` the centre. That
is why no separate index type for the outer charts appears.

**Three spellings of the section ring are in play** and instance search distinguishes all of
them: `Γ(Z, i⁻¹W)`, the `RingCat` carrier
`(_root_.structureSheaf Z.toRingedSpace.sheaf).obj.obj (op (i⁻¹W))` in which
`Stacks.SheafOfModules.generatorRatioUnit` lives, and
`structureSheafRing` in which Tag 09NY states its modules. The first two are
equal by `rfl`, but `Units.map` of a ring map into the first does **not** elaborate against a
`Units` of the second, because the `Monoid` instance is found before the carriers are unified.
`Stacks.LiftInvertible.appUnits` fixes the codomain once, at the generator API's spelling, and
every statement below uses it; the crossing to Tag 09NY's spelling happens once, in the final
theorem, where it is an `Eq` and `isDefEq` settles it.

**Which `IsInvertible`.** The construction runs in `Stacks.SheafOfModules.IsInvertible`, the
class the gluing of a unit cocycle concludes; Tag 09NY asks for the definitionally identical
`AlgebraicGeometry.SheafOfModules.IsInvertible`, and the two are crossed once, by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`.

**Which pullback.** Tag 09NY is stated with
`RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom`, the construction produces
`AlgebraicGeometry.Scheme.Modules.pullback i`, and the two functors are equal by `rfl`, so no
comparison isomorphism appears.

## References

* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
* [Stacks Project, Tag 0C0T](https://stacks.math.columbia.edu/tag/0C0T)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0055](https://stacks.math.columbia.edu/tag/0055)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules

universe u

namespace Stacks.LiftInvertible

variable {X Z : Scheme.{u}}

/-- **The map on units induced by `i` on sections of the structure sheaf**, with the codomain
written in the `RingCat` spelling in which the transition units of local generators live. This
is `Stacks.PicFinite.pull` on units; declaring the codomain is what makes it elaborate, because
`Units.map` resolves the `Monoid` instance of its target before the two spellings of the section
ring are unified. -/
noncomputable def appUnits (i : Z ⟶ X) (W : X.Opens) :
    (Γ(X, W))ˣ →*
      ((_root_.structureSheaf Z.toRingedSpace.sheaf).obj.obj (op (i ⁻¹ᵁ W)))ˣ :=
  Units.map (Stacks.PicFinite.pull i W).toMonoidHom

/-- The underlying section of `appUnits i W u` is the image of `u` under
`Stacks.PicFinite.pull i W`. -/
theorem appUnits_val (i : Z ⟶ X) (W : X.Opens) (u : (Γ(X, W))ˣ) :
    (appUnits i W u).val = Stacks.PicFinite.pull i W u.val :=
  rfl

/-- **A unit on the inverse image of an affine open lifts, when the ideal sheaf lies in the
nilradical.** This is `Stacks.LiftInvertible.exists_units_app_eq` in the spelling `appUnits`
fixes. The hypothesis `i.ker ≤ X.nilradical` is weaker than nilpotency of `i.ker` and, for a
closed immersion, says exactly that the underlying map of `i` is surjective. -/
theorem exists_appUnits_eq (i : Z ⟶ X) [IsClosedImmersion i] (hker : i.ker ≤ X.nilradical)
    {U : X.Opens} (hU : IsAffineOpen U)
    (v : ((_root_.structureSheaf Z.toRingedSpace.sheaf).obj.obj (op (i ⁻¹ᵁ U)))ˣ) :
    ∃ w : (Γ(X, U))ˣ, appUnits i U w = v := by
  obtain ⟨w, hw⟩ := exists_units_app_eq i hU (ker_app_le_nilradical i hker ⟨U, hU⟩) v
  exact ⟨w, Units.ext hw⟩

/-- **Chart data star-shaped around a central chart, with chosen lifts of the transition units
against the centre.** Extends `Stacks.PicFinite.ChartData i V L` — a cover of `X` by charts of
which two distinct ones meet only inside `V`, with a generator of `L` over the inverse image of
each chart — by a generator over the inverse image of `V` itself and, for every chart, a unit on
its overlap with `V` through which that chart's generator is expressed in the central one.

Only the overlaps with the centre carry chosen data; every other transition unit is built from
these by `Stacks.LiftInvertible.StarLiftData.transition`. -/
structure StarLiftData (i : Z ⟶ X) (V : X.Opens) (L : Z.Modules) extends
    Stacks.PicFinite.ChartData i V L where
  /-- A generator of `L` over the inverse image of the central chart. -/
  centerGen : GeneratorSections Z.toRingedSpace L (i ⁻¹ᵁ V)
  /-- The chosen unit on the overlap of a chart with the centre. -/
  unit : ∀ p : X, (Γ(X, V ⊓ chart p))ˣ
  /-- The chosen unit carries the central generator to the chart's generator. -/
  smul_unit : ∀ p : X,
    (generatorRestrict (X := Z.toRingedSpace) L
        ((Opens.map i.base).map (homOfLE (inf_le_right : V ⊓ chart p ≤ chart p))).le
        (generator p)).val =
      (appUnits i (V ⊓ chart p) (unit p)).val •
        (generatorRestrict (X := Z.toRingedSpace) L
          ((Opens.map i.base).map (homOfLE (inf_le_left : V ⊓ chart p ≤ V))).le centerGen).val

namespace StarLiftData

variable {i : Z ⟶ X} {V : X.Opens} {L : Z.Modules} (D : StarLiftData i V L)

/-- The chosen unit of the chart of `p`, restricted to an open inside both the centre and that
chart. -/
noncomputable def liftUnit (p : X) {W : X.Opens} (hV : W ≤ V) (hp : W ≤ D.chart p) :
    (Γ(X, W))ˣ :=
  Units.map (X.presheaf.map (homOfLE (le_inf hV hp)).op).hom (D.unit p)

/-- Restricting `liftUnit` from `W` to a smaller open `W'` gives `liftUnit` on `W'`. -/
theorem liftUnit_restrict (p : X) {W W' : X.Opens} (hV : W ≤ V) (hp : W ≤ D.chart p)
    (h : W' ≤ W) :
    Units.map (X.presheaf.map (homOfLE h).op).hom (D.liftUnit p hV hp) =
      D.liftUnit p (h.trans hV) (h.trans hp) := by
  refine Units.ext ?_
  have hcomp : X.presheaf.map (homOfLE (le_inf hV hp)).op ≫ X.presheaf.map (homOfLE h).op =
      X.presheaf.map (homOfLE (le_inf (h.trans hV) (h.trans hp))).op := by
    rw [← X.presheaf.map_comp]
    congr 1
  exact congrArg (fun q => (CommRingCat.Hom.hom q) (D.unit p).val) hcomp

/-- The restricted chosen unit carries the central generator to the chart's generator, over any
open inside both the centre and the chart. -/
theorem smul_liftUnit (p : X) {W : X.Opens} (hV : W ≤ V) (hp : W ≤ D.chart p) :
    (generatorRestrict (X := Z.toRingedSpace) L
        ((Opens.map i.base).map (homOfLE hp)).le (D.generator p)).val =
      (appUnits i W (D.liftUnit p hV hp)).val •
        (generatorRestrict (X := Z.toRingedSpace) L
          ((Opens.map i.base).map (homOfLE hV)).le D.centerGen).val := by
  have hk : W ≤ V ⊓ D.chart p := le_inf hV hp
  have key := congrArg (L.val.map ((Opens.map i.base).map (homOfLE hk)).op) (D.smul_unit p)
  rw [PresheafOfModules.map_smul L.val ((Opens.map i.base).map (homOfLE hk)).op] at key
  have htrans : ∀ {U : X.Opens} (hU : V ⊓ D.chart p ≤ U)
      (s : GeneratorSections Z.toRingedSpace L (i ⁻¹ᵁ U)),
      L.val.map ((Opens.map i.base).map (homOfLE hk)).op
          (generatorRestrict (X := Z.toRingedSpace) L
            ((Opens.map i.base).map (homOfLE hU)).le s).val =
        (generatorRestrict (X := Z.toRingedSpace) L
          ((Opens.map i.base).map (homOfLE (hk.trans hU))).le s).val :=
    fun hU s => congrArg Subtype.val (generatorRestrict_trans (X := Z.toRingedSpace) L _ _ s)
  rw [← htrans inf_le_right, key, htrans inf_le_left]
  exact congrArg (fun c => c • (generatorRestrict (X := Z.toRingedSpace) L
    ((Opens.map i.base).map (homOfLE hV)).le D.centerGen).val)
    (Stacks.PicFinite.pull_restrict i hk (D.unit p).val)

/-- The restricted chosen unit is the transition unit from the central generator to the chart's
generator. -/
theorem map_liftUnit (p : X) {W : X.Opens} (hV : W ≤ V) (hp : W ≤ D.chart p) :
    appUnits i W (D.liftUnit p hV hp) =
      generatorRatioUnit (X := Z.toRingedSpace) L (i ⁻¹ᵁ W)
        (generatorRestrict (X := Z.toRingedSpace) L
          ((Opens.map i.base).map (homOfLE hV)).le D.centerGen)
        (generatorRestrict (X := Z.toRingedSpace) L
          ((Opens.map i.base).map (homOfLE hp)).le (D.generator p)) :=
  (generatorRatioUnit_eq (X := Z.toRingedSpace) L (i ⁻¹ᵁ W) _ _ _
    (D.smul_liftUnit p hV hp)).symm

open Classical in
/-- **The transition units of the star data.** Over an open inside the centre, the ratio of the
two charts' chosen units; elsewhere one, which is correct because an open not inside the centre
meets only one chart. -/
noncomputable def transition (p q : X) (W : X.Opens) (hp : W ≤ D.chart p)
    (hq : W ≤ D.chart q) : (Γ(X, W))ˣ :=
  if h : W ≤ V then D.liftUnit p h hp / D.liftUnit q h hq else 1

open Classical in
/-- Over an open inside the centre, the transition unit is the ratio of the two chosen units. -/
theorem transition_of_le (p q : X) (W : X.Opens) (hp : W ≤ D.chart p) (hq : W ≤ D.chart q)
    (h : W ≤ V) :
    D.transition p q W hp hq = D.liftUnit p h hp / D.liftUnit q h hq :=
  dite_eq_left h

open Classical in
/-- Over an open not inside the centre, the transition unit is one. -/
theorem transition_of_not_le (p q : X) (W : X.Opens) (hp : W ≤ D.chart p) (hq : W ≤ D.chart q)
    (h : ¬ W ≤ V) : D.transition p q W hp hq = 1 :=
  dite_eq_right h

/-- The transition unit from a chart to itself is one. -/
theorem transition_self (p : X) (W : X.Opens) (hp hq : W ≤ D.chart p) :
    D.transition p p W hp hq = 1 := by
  by_cases h : W ≤ V
  · rw [D.transition_of_le p p W hp hq h, div_self']
  · exact D.transition_of_not_le p p W hp hq h

/-- Swapping the two charts inverts the transition unit. -/
theorem transition_symm (p q : X) (W : X.Opens) (hp : W ≤ D.chart p) (hq : W ≤ D.chart q) :
    D.transition q p W hq hp = (D.transition p q W hp hq)⁻¹ := by
  by_cases h : W ≤ V
  · rw [D.transition_of_le q p W hq hp h, D.transition_of_le p q W hp hq h, inv_div]
  · rw [D.transition_of_not_le q p W hq hp h, D.transition_of_not_le p q W hp hq h, inv_one]

/-- **The cocycle law.** The transition units from `p` to `q` and from `q` to `r` compose to the
transition unit from `p` to `r`. -/
theorem transition_cocycle (p q r : X) (W : X.Opens) (hp : W ≤ D.chart p) (hq : W ≤ D.chart q)
    (hr : W ≤ D.chart r) :
    D.transition q r W hq hr * D.transition p q W hp hq = D.transition p r W hp hr := by
  by_cases h : W ≤ V
  · rw [D.transition_of_le q r W hq hr h, D.transition_of_le p q W hp hq h,
      D.transition_of_le p r W hp hr h]
    exact div_mul_div_cancel' _ _ _
  · rw [D.transition_of_not_le q r W hq hr h, D.transition_of_not_le p q W hp hq h,
      D.transition_of_not_le p r W hp hr h, one_mul]

/-- **The restriction law.** This is where the star shape is used: an open on which the law is
not a restriction of the chosen units lies in only one chart, by
`Stacks.PicFinite.ChartData.eq_of_not_le`. -/
theorem transition_restrict (p q : X) {W W' : X.Opens} (hp : W ≤ D.chart p)
    (hq : W ≤ D.chart q) (h : W' ≤ W) :
    Units.map (X.presheaf.map (homOfLE h).op).hom (D.transition p q W hp hq) =
      D.transition p q W' (h.trans hp) (h.trans hq) := by
  by_cases hW : W ≤ V
  · rw [D.transition_of_le p q W hp hq hW,
      D.transition_of_le p q W' (h.trans hp) (h.trans hq) (h.trans hW), map_div,
      D.liftUnit_restrict p hW hp h, D.liftUnit_restrict q hW hq h]
  · obtain rfl := D.toChartData.eq_of_not_le hp hq hW
    rw [D.transition_self p W hp hq, map_one,
      D.transition_self p W' (h.trans hp) (h.trans hq)]

/-- **The transition unit pulls back to the ratio of the two chart generators.** Over an open
inside the centre both charts' generators are expressed through the central one and the ratio of
those expressions is the transition unit; elsewhere the two charts coincide. -/
theorem map_transition (p q : X) (W : X.Opens) (hp : W ≤ D.chart p) (hq : W ≤ D.chart q) :
    appUnits i W (D.transition p q W hp hq) =
      generatorRatioUnit (X := Z.toRingedSpace) L (i ⁻¹ᵁ W)
        (generatorRestrict (X := Z.toRingedSpace) L
          ((Opens.map i.base).map (homOfLE hq)).le (D.generator q))
        (generatorRestrict (X := Z.toRingedSpace) L
          ((Opens.map i.base).map (homOfLE hp)).le (D.generator p)) := by
  by_cases hW : W ≤ V
  · rw [D.transition_of_le p q W hp hq hW, map_div, D.map_liftUnit p hW hp,
      D.map_liftUnit q hW hq, div_eq_mul_inv,
      ← generatorRatioUnit_symm (X := Z.toRingedSpace) L (i ⁻¹ᵁ W)]
    exact generatorRatioUnit_comp (X := Z.toRingedSpace) L (i ⁻¹ᵁ W) _ _ _
  · obtain rfl := D.toChartData.eq_of_not_le hp hq hW
    rw [D.transition_self p W hp hq, map_one]
    exact (generatorRatioUnit_self (X := Z.toRingedSpace) L (i ⁻¹ᵁ W) _).symm

/-- The transition units of the star data, as gluing data on `X`. -/
noncomputable def transitionCocycle : UnitTransitionCocycle X.toRingedSpace D.chart where
  transition p q W hp hq := D.transition p q W hp hq
  restrict hp hq h := D.transition_restrict _ _ hp hq h
  symm p q W hp hq := D.transition_symm p q W hp hq
  cocycle p q r W hp hq hr := D.transition_cocycle p q r W hp hq hr

/-- The star data, read as the input of the comparison of
`Stacks.PicFinite.LiftedChartData`. -/
noncomputable def toLiftedChartData : Stacks.PicFinite.LiftedChartData i L where
  chart := D.chart
  mem_chart := D.mem_chart
  generator := D.generator
  cocycle := D.transitionCocycle
  pull_transition p q W hp hq :=
    (congrArg Units.val (D.map_transition p q W hp hq)).trans
      (generatorRatioUnit_val (X := Z.toRingedSpace) L (i ⁻¹ᵁ W) _ _)

end StarLiftData

/-- **The chosen lifts exist when the ideal sheaf lies in the nilradical and, on each overlap
with the centre, either that overlap is affine or the two generators already agree.** Over an
affine open the sections of `𝒪_X` surject onto those of `𝒪_Z`, and a surjection of commutative
rings whose kernel consists of nilpotents surjects on units, so the transition unit of the two
generators over the inverse image of `V ⊓ chart p` is the image of a unit on `V ⊓ chart p`;
where the two generators already agree the chosen unit is `1` and nothing is lifted.

The hypothesis `i.ker ≤ X.nilradical` is weaker than nilpotency of `i.ker` and, for a closed
immersion, says exactly that the underlying map of `i` is **surjective**.

**The second alternative is what makes the hypothesis satisfiable**, because the centre is the
chart of every point it contains: there `V ⊓ chart p` is `V` itself, which in the
one-dimensional application is a dense open with finite complement and is *not* affine. Nothing
has to be lifted there, the chart's generator being the central one. -/
theorem nonempty_starLiftData_of_ker_le_nilradical_of_generator_eq_or_isAffineOpen (i : Z ⟶ X)
    [IsClosedImmersion i] (hker : i.ker ≤ X.nilradical) {V : X.Opens} {L : Z.Modules}
    (C : Stacks.PicFinite.ChartData i V L)
    (centerGen : GeneratorSections Z.toRingedSpace L (i ⁻¹ᵁ V))
    (h : ∀ p : X,
      (generatorRestrict (X := Z.toRingedSpace) L
            ((Opens.map i.base).map (homOfLE (inf_le_right : V ⊓ C.chart p ≤ C.chart p))).le
            (C.generator p)).val =
          (generatorRestrict (X := Z.toRingedSpace) L
            ((Opens.map i.base).map (homOfLE (inf_le_left : V ⊓ C.chart p ≤ V))).le
            centerGen).val ∨
        IsAffineOpen (V ⊓ C.chart p)) :
    Nonempty (StarLiftData i V L) := by
  have hex : ∀ p : X, ∃ w : (Γ(X, V ⊓ C.chart p))ˣ,
      (generatorRestrict (X := Z.toRingedSpace) L
          ((Opens.map i.base).map (homOfLE (inf_le_right : V ⊓ C.chart p ≤ C.chart p))).le
          (C.generator p)).val =
        (appUnits i (V ⊓ C.chart p) w).val •
          (generatorRestrict (X := Z.toRingedSpace) L
            ((Opens.map i.base).map (homOfLE (inf_le_left : V ⊓ C.chart p ≤ V))).le
            centerGen).val := by
    intro p
    rcases h p with heq | haff
    · exact ⟨1, by rw [heq, map_one, Units.val_one, one_smul]⟩
    obtain ⟨w, hw⟩ := exists_appUnits_eq i hker haff
      (generatorRatioUnit (X := Z.toRingedSpace) L (i ⁻¹ᵁ (V ⊓ C.chart p))
        (generatorRestrict (X := Z.toRingedSpace) L
          ((Opens.map i.base).map (homOfLE (inf_le_left : V ⊓ C.chart p ≤ V))).le centerGen)
        (generatorRestrict (X := Z.toRingedSpace) L
          ((Opens.map i.base).map (homOfLE (inf_le_right : V ⊓ C.chart p ≤ C.chart p))).le
          (C.generator p)))
    refine ⟨w, ?_⟩
    have h1 : (appUnits i (V ⊓ C.chart p) w).val =
        generatorRatio (X := Z.toRingedSpace) L (i ⁻¹ᵁ (V ⊓ C.chart p))
          (generatorRestrict (X := Z.toRingedSpace) L
            ((Opens.map i.base).map (homOfLE (inf_le_left : V ⊓ C.chart p ≤ V))).le centerGen)
          (generatorRestrict (X := Z.toRingedSpace) L
            ((Opens.map i.base).map (homOfLE (inf_le_right : V ⊓ C.chart p ≤ C.chart p))).le
            (C.generator p)) :=
      (congrArg Units.val hw).trans
        (generatorRatioUnit_val (X := Z.toRingedSpace) L (i ⁻¹ᵁ (V ⊓ C.chart p)) _ _)
    rw [h1]
    exact generatorRatio_spec (X := Z.toRingedSpace) L (i ⁻¹ᵁ (V ⊓ C.chart p)) _ _
  choose u hu using hex
  exact ⟨{ toChartData := C, centerGen := centerGen, unit := u, smul_unit := hu }⟩

/-- **The chosen lifts exist when the ideal sheaf is nilpotent and, on each overlap with the
centre, either that overlap is affine or the two generators already agree.** The special case of
`Stacks.LiftInvertible.nonempty_starLiftData_of_ker_le_nilradical_of_generator_eq_or_isAffineOpen`
in which the ideal sheaf has a uniform nilpotency exponent. -/
theorem nonempty_starLiftData_of_isNilpotent_ker_of_generator_eq_or_isAffineOpen (i : Z ⟶ X)
    [IsClosedImmersion i] (hnil : IsNilpotent i.ker) {V : X.Opens} {L : Z.Modules}
    (C : Stacks.PicFinite.ChartData i V L)
    (centerGen : GeneratorSections Z.toRingedSpace L (i ⁻¹ᵁ V))
    (h : ∀ p : X,
      (generatorRestrict (X := Z.toRingedSpace) L
            ((Opens.map i.base).map (homOfLE (inf_le_right : V ⊓ C.chart p ≤ C.chart p))).le
            (C.generator p)).val =
          (generatorRestrict (X := Z.toRingedSpace) L
            ((Opens.map i.base).map (homOfLE (inf_le_left : V ⊓ C.chart p ≤ V))).le
            centerGen).val ∨
        IsAffineOpen (V ⊓ C.chart p)) :
    Nonempty (StarLiftData i V L) :=
  nonempty_starLiftData_of_ker_le_nilradical_of_generator_eq_or_isAffineOpen i
    (ker_le_nilradical_of_isNilpotent i hnil) C centerGen h

/-- **The chosen lifts exist when the ideal sheaf is nilpotent and every overlap with the centre
is affine.** The all-affine case of
`Stacks.LiftInvertible.nonempty_starLiftData_of_isNilpotent_ker_of_generator_eq_or_isAffineOpen`;
it asks in particular that the centre itself be affine. -/
theorem nonempty_starLiftData_of_isNilpotent_ker (i : Z ⟶ X) [IsClosedImmersion i]
    (hnil : IsNilpotent i.ker) {V : X.Opens} {L : Z.Modules}
    (C : Stacks.PicFinite.ChartData i V L)
    (centerGen : GeneratorSections Z.toRingedSpace L (i ⁻¹ᵁ V))
    (haff : ∀ p : X, IsAffineOpen (V ⊓ C.chart p)) :
    Nonempty (StarLiftData i V L) :=
  nonempty_starLiftData_of_isNilpotent_ker_of_generator_eq_or_isAffineOpen i hnil C centerGen
    fun p => Or.inr (haff p)

/-- **The conclusion of Tag 09NY from star data.** An invertible module on a closed subscheme
trivialized by a star-shaped cover whose transition units against the centre have been lifted is
the pullback of an invertible module on the ambient scheme.

Stated in the spelling of [Stacks, Tag 0C0T];
`Stacks.LiftInvertible.exists_modulePullback_iso_of_starLiftData` is the same statement in the
spelling of Tag 09NY. The tag is withheld: Tag 09NY has no hypothesis on the cover. -/
theorem exists_isInvertible_pullback_iso_of_starLiftData (i : Z ⟶ X) {V : X.Opens}
    (L : Z.Modules) (D : StarLiftData i V L) :
    ∃ M : X.Modules,
      AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
          ((Presheaf.isSheaf_iff_isSheaf_comp _ X.presheaf
            (forget₂ CommRingCat RingCat)).mp X.IsSheaf) M ∧
        Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback i).obj M ≅ L) :=
  ⟨D.toLiftedChartData.descend,
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry X.presheaf _ _).mp
      D.toLiftedChartData.isInvertible_descend,
    ⟨D.toLiftedChartData.pullbackIso⟩⟩

/-- **The conclusion of Tag 09NY from star data, in Tag 09NY's own spelling.** The two pullback
functors `AlgebraicGeometry.Scheme.Modules.pullback i` and
`RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom` are equal by `rfl`, so no
comparison isomorphism is needed. The tag is withheld: Tag 09NY has no hypothesis on the
cover. -/
theorem exists_modulePullback_iso_of_starLiftData (i : Z ⟶ X) {V : X.Opens}
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) (D : StarLiftData i V L) :
    ∃ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) M),
      Nonempty ((modulePullback i.toLRSHom.toShHom).obj M ≅ L) := by
  obtain ⟨M, hM, hiso⟩ := exists_isInvertible_pullback_iso_of_starLiftData i L D
  exact ⟨M, hM, hiso⟩

/-- **Tag 09NY for a surjective closed immersion admitting a star-shaped trivializing cover with
affine central overlaps.** The hypotheses are a cover of `X` by charts over whose inverse images
`L` is trivial, one of them distinguished as the centre `V`, two distinct charts meeting only
inside `V`, each overlap with `V` affine, and `i.ker ≤ X.nilradical` — which for a closed
immersion says exactly that the underlying map of `i` is surjective, and which nilpotency of
`i.ker` implies.

The tag is withheld: Tag 09NY has no hypothesis on the cover and none on the ideal sheaf, and
without surjectivity the units do not lift — see the module docstring for the counterexample. -/
theorem exists_modulePullback_iso_of_starChartData_of_ker_le_nilradical (i : Z ⟶ X)
    [IsClosedImmersion i] (hker : i.ker ≤ X.nilradical) {V : X.Opens}
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    (C : Stacks.PicFinite.ChartData i V L)
    (centerGen : GeneratorSections Z.toRingedSpace L (i ⁻¹ᵁ V))
    (h : ∀ p : X,
      (generatorRestrict (X := Z.toRingedSpace) L
            ((Opens.map i.base).map (homOfLE (inf_le_right : V ⊓ C.chart p ≤ C.chart p))).le
            (C.generator p)).val =
          (generatorRestrict (X := Z.toRingedSpace) L
            ((Opens.map i.base).map (homOfLE (inf_le_left : V ⊓ C.chart p ≤ V))).le
            centerGen).val ∨
        IsAffineOpen (V ⊓ C.chart p)) :
    ∃ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) M),
      Nonempty ((modulePullback i.toLRSHom.toShHom).obj M ≅ L) := by
  obtain ⟨D⟩ :=
    nonempty_starLiftData_of_ker_le_nilradical_of_generator_eq_or_isAffineOpen i hker C centerGen h
  exact exists_modulePullback_iso_of_starLiftData i L D

/-- **Tag 09NY for a closed immersion with nilpotent ideal sheaf admitting a star-shaped
trivializing cover with affine central overlaps.** The special case of
`Stacks.LiftInvertible.exists_modulePullback_iso_of_starChartData_of_ker_le_nilradical` in which
the ideal sheaf has a uniform nilpotency exponent. The tag is withheld: Tag 09NY has no
hypothesis on the cover and none on the ideal sheaf. -/
theorem exists_modulePullback_iso_of_starChartData_of_isNilpotent_ker (i : Z ⟶ X)
    [IsClosedImmersion i] (hnil : IsNilpotent i.ker) {V : X.Opens}
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    (C : Stacks.PicFinite.ChartData i V L)
    (centerGen : GeneratorSections Z.toRingedSpace L (i ⁻¹ᵁ V))
    (h : ∀ p : X,
      (generatorRestrict (X := Z.toRingedSpace) L
            ((Opens.map i.base).map (homOfLE (inf_le_right : V ⊓ C.chart p ≤ C.chart p))).le
            (C.generator p)).val =
          (generatorRestrict (X := Z.toRingedSpace) L
            ((Opens.map i.base).map (homOfLE (inf_le_left : V ⊓ C.chart p ≤ V))).le
            centerGen).val ∨
        IsAffineOpen (V ⊓ C.chart p)) :
    ∃ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) M),
      Nonempty ((modulePullback i.toLRSHom.toShHom).obj M ≅ L) :=
  exists_modulePullback_iso_of_starChartData_of_ker_le_nilradical i
    (ker_le_nilradical_of_isNilpotent i hnil) L C centerGen h

end Stacks.LiftInvertible

end
