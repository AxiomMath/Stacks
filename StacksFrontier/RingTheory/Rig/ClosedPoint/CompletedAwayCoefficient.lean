module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.RestrictedPowerSeries.CoefficientIdeal
public import StacksFrontier.RingTheory.Rig.ClosedPoint.CompletedAwayFlatDescent
public import StacksFrontier.RingTheory.Rig.FlatEtaleLocalization

/-!
# The two routes from a completed principal localization into restricted power series

Let `I` be a finitely generated ideal of a commutative ring `A`, let `f : A`, and write `A{σ}`
for the restricted power series ring and `A_{\{f\}}` for the completed principal localization of
`A` at `f`.  There are two ring homomorphisms `A_{\{f\}} → A_{\{f\}}{σ}` in sight:

* the coefficient inclusion of the ring `A_{\{f\}}`, and
* the completed principal localization of the coefficient inclusion `A → A{σ}`, read through the
  identification `A{σ}_{\{f\}} = A_{\{f\}}{σ}` of Stacks 0GGG.

The fourth paragraph of the proof of Stacks 0GGR needs them to be the same map: the prime it
works with on `A_{\{f\}}` is produced by Stacks 0GGG as the contraction along the second route,
while the paragraph it reduces to asks for the contraction along the first.  The source says
only "details omitted"; this module supplies the identity and the resulting equality of
contractions.

The two maps agree on the image of `A` — on a constant both give the constant series of its
image in `A_{\{f\}}` — and `A` has dense image in `A_{\{f\}}`, so `Rig.completedHom_ext`
concludes.  Continuity of either map is read off the same computation: the ideal of definition
of `A_{\{f\}}` is extended from `A`, so its image under a map is determined by the map's
restriction to `A`.

## Main results

* `Rig.restrictedPowerSeriesCompletedAwayEquiv_comp_completedAwayMap`: the identification turns
  the completed principal localization of the coefficient inclusion into the coefficient
  inclusion of the completed principal localization.
* `Rig.comap_coefficientRingHom_completedAway`: consequently the two contractions of a prime of
  `A_{\{f\}}{σ}` to `A_{\{f\}}` agree.

## Implementation notes

The identification of `A{σ}_{\{f\}}` with `A_{\{f\}}{σ}` is not a bundled isomorphism in this
development: it is the ring homomorphism
`TopologicalRing.restrictedPowerSeriesMap ∘ TopologicalRing.completedAwayRestrictedPowerSeriesMap`,
whose bijectivity is
`TopologicalRing.bijective_restrictedPowerSeriesMap_comp_completedAway`.  That composite is
abbreviated here as `Rig.restrictedPowerSeriesCompletedAwayEquiv`, and only its defining
property on the image of `A{σ}` is used.

The coefficient ideal of `A_{\{f\}}{σ}` is the one extended from `A` through
`Localization.Away f`, which is the presentation the identification delivers; the fourth
paragraph of Stacks 0GGR also needs it extended from `A_{\{f\}}` in one step, and
`RestrictedPowerSeries.congrEquiv` moves between the two.

## References

* [Stacks Project, Tag 0GGG](https://stacks.math.columbia.edu/tag/0GGG)
* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
-/

@[expose] public section

namespace Rig

section

universe u v

variable {A : Type u} [CommRing A]

open TopologicalRing RestrictedPowerSeries

/-- The coefficient ideal of `A_{\{f\}}{σ}`, extended from `A` through `Localization.Away f`:
the presentation in which Stacks 0GGG's identification `A{σ}_{\{f\}} = A_{\{f\}}{σ}` delivers
it. -/
public noncomputable abbrev completedAwayCoefficientIdeal (I : Ideal A) (f : A) :
    Ideal (CompletedAway I f) :=
  (I.map (algebraMap A (Localization.Away f))).map
    (algebraMap (Localization.Away f) (CompletedAway I f))

/-- The ideal of definition of `A_{\{f\}}` is extended from `A` in one step as well. -/
public theorem completedAwayCoefficientIdeal_eq (I : Ideal A) (f : A) :
    completedAwayCoefficientIdeal I f = I.map (algebraMap A (CompletedAway I f)) := by
  rw [completedAwayCoefficientIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq A (Localization.Away f) (CompletedAway I f)]

/-- The image of the ideal of definition of `A_{\{f\}}` under a map is extended from `A`. -/
private theorem map_completedAwayCoefficientIdeal_eq_map_comp {R : Type*} [CommRing R]
    (I : Ideal A) (f : A) (g : CompletedAway I f →+* R) :
    (completedAwayCoefficientIdeal I f).map g = I.map (g.comp (algebraMap A (CompletedAway I f))) :=
  by rw [completedAwayCoefficientIdeal_eq, Ideal.map_map]

/-- **The induced map of completed principal localizations carries the ideal of definition onto
the ideal of definition.**  For `φ : A → B`, the map `A_{\{f\}} → B_{\{φ f\}}` extends the ideal
of definition of `A_{\{f\}}` exactly onto that of `B_{\{φ f\}}`.

This is the bridge between the two spellings of the coefficient ideal of `B_{\{φ f\}}{σ}` that
the fourth paragraph of the proof of Stacks 0GGR has to reconcile: the identification of Stacks
0GGG delivers that ring for the ideal extended from `B`, whereas the restricted power series
ring over `A_{\{f\}}` maps to it for the ideal extended from `A_{\{f\}}` along `A_{\{f\}} →
B_{\{φ f\}}`.  Those are the two sides here, so `RestrictedPowerSeries.congrEquiv` applied to
this equality identifies the two rings. -/
public theorem map_completedAwayCoefficientIdeal_completedAwayMap {B : Type u} [CommRing B]
    (φ : A →+* B) (I : Ideal A) (f : A) :
    (completedAwayCoefficientIdeal I f).map (RingHom.completedAwayMap φ I f) =
      completedAwayCoefficientIdeal (I.map φ) (φ f) := by
  rw [map_completedAwayCoefficientIdeal_eq_map_comp, completedAwayCoefficientIdeal_eq (I.map φ),
    RingHom.completedAwayMap_comp_base, ← Ideal.map_map]

/-- **Stacks 0GGG as a map.**  The identification of the completed principal localization of
`A{σ}` at `f` with the restricted power series ring over `A_{\{f\}}`: the canonical map out of
the completion followed by the coefficientwise map.  It is bijective by
`TopologicalRing.bijective_restrictedPowerSeriesMap_comp_completedAway`. -/
public noncomputable abbrev restrictedPowerSeriesCompletedAwayEquiv (I : Ideal A) (hI : I.FG)
    (σ : Type v) (f : A) :
    CompletedAway (coefficientIdeal I σ) (coefficientRingHom I σ f) →+*
      RestrictedPowerSeries (completedAwayCoefficientIdeal I f) σ :=
  (restrictedPowerSeriesMap (B := CompletedAway I f)
      (I.map (algebraMap A (Localization.Away f))) σ).comp
    (completedAwayRestrictedPowerSeriesMap I hI σ f)

/-- The identification of Stacks 0GGG is bijective. -/
public theorem bijective_restrictedPowerSeriesCompletedAwayEquiv (I : Ideal A) (hI : I.FG)
    (σ : Type v) (f : A) :
    Function.Bijective (restrictedPowerSeriesCompletedAwayEquiv I hI σ f) :=
  bijective_restrictedPowerSeriesMap_comp_completedAway I hI σ f

/-- Both routes send a constant to the constant series of its image in `A_{\{f\}}`. -/
private theorem comp_algebraMap_eq (I : Ideal A) (hI : I.FG) (σ : Type v) (f : A) :
    ((restrictedPowerSeriesCompletedAwayEquiv I hI σ f).comp
          (RingHom.completedAwayMap (coefficientRingHom I σ) I f)).comp
        (algebraMap A (CompletedAway I f)) =
      (coefficientRingHom (completedAwayCoefficientIdeal I f) σ).comp
        (algebraMap A (CompletedAway I f)) := by
  refine RingHom.ext fun a => ?_
  have h1 := DFunLike.congr_fun
    (RingHom.completedAwayMap_comp_base (coefficientRingHom I σ) I f) a
  have h2 := DFunLike.congr_fun
    (restrictedPowerSeriesMap_comp_completedAway_comp_algebraMap I hI σ f)
    (coefficientRingHom I σ a)
  have hstep1 : restrictedPowerSeriesMap (B := Localization.Away f) I σ
        (coefficientRingHom I σ a) =
      coefficientRingHom (I.map (algebraMap A (Localization.Away f))) σ
        (algebraMap A (Localization.Away f) a) :=
    restrictedPowerSeriesMap_coefficientRingHom I σ a
  have hstep2 : restrictedPowerSeriesMap (B := CompletedAway I f)
        (I.map (algebraMap A (Localization.Away f))) σ
        (coefficientRingHom (I.map (algebraMap A (Localization.Away f))) σ
          (algebraMap A (Localization.Away f) a)) =
      coefficientRingHom (completedAwayCoefficientIdeal I f) σ
        (algebraMap (Localization.Away f) (CompletedAway I f)
          (algebraMap A (Localization.Away f) a)) :=
    restrictedPowerSeriesMap_coefficientRingHom _ σ _
  exact (congrArg (restrictedPowerSeriesCompletedAwayEquiv I hI σ f) h1).trans
    (h2.trans ((congrArg (restrictedPowerSeriesMap (B := CompletedAway I f)
        (I.map (algebraMap A (Localization.Away f))) σ) hstep1).trans
      (hstep2.trans (congrArg (coefficientRingHom (completedAwayCoefficientIdeal I f) σ)
        (IsScalarTower.algebraMap_apply A (Localization.Away f) (CompletedAway I f) a).symm))))

/-- The image of the ideal of definition under either route is the coefficient ideal, which is
what makes both routes continuous. -/
private theorem map_completedAwayCoefficientIdeal (I : Ideal A) (f : A) (σ : Type v)
    (g : CompletedAway I f →+* RestrictedPowerSeries (completedAwayCoefficientIdeal I f) σ)
    (hg : g.comp (algebraMap A (CompletedAway I f)) =
      (coefficientRingHom (completedAwayCoefficientIdeal I f) σ).comp
        (algebraMap A (CompletedAway I f))) :
    (completedAwayCoefficientIdeal I f).map g =
      coefficientIdeal (completedAwayCoefficientIdeal I f) σ := by
  rw [map_completedAwayCoefficientIdeal_eq_map_comp, hg, ← Ideal.map_map,
    ← completedAwayCoefficientIdeal_eq]

/-- **Stacks 0GGG's identification carries the completed localization of the coefficient
inclusion to the coefficient inclusion of the completed localization.**  Composing
`A_{\{f\}} → A{σ}_{\{f\}}`, the completed principal localization of `A → A{σ}`, with the
identification `A{σ}_{\{f\}} = A_{\{f\}}{σ}` gives the coefficient inclusion
`A_{\{f\}} → A_{\{f\}}{σ}`.

This is the compatibility the fourth paragraph of the proof of Stacks 0GGR leaves as "details
omitted": it is what makes the two routes from `A_{\{f\}}` into the restricted power series
ring over it one and the same map. -/
public theorem restrictedPowerSeriesCompletedAwayEquiv_comp_completedAwayMap (I : Ideal A)
    (hI : I.FG) (σ : Type v) (f : A) :
    (restrictedPowerSeriesCompletedAwayEquiv I hI σ f).comp
        (RingHom.completedAwayMap (coefficientRingHom I σ) I f) =
      coefficientRingHom (completedAwayCoefficientIdeal I f) σ := by
  set K : Ideal (CompletedAway I f) := completedAwayCoefficientIdeal I f with hK
  set T := RestrictedPowerSeries K σ
  let first := (restrictedPowerSeriesCompletedAwayEquiv I hI σ f).comp
    (RingHom.completedAwayMap (coefficientRingHom I σ) I f)
  let second := coefficientRingHom K σ
  let : TopologicalSpace (CompletedAway I f) := K.adicTopology
  have : T2Space T := t2Space_restrictedPowerSeries K σ
  have hKfg : K.FG := by
    rw [hK, completedAwayCoefficientIdeal_eq]
    exact hI.map _
  have hbase : first.comp (algebraMap A (CompletedAway I f)) =
      second.comp (algebraMap A (CompletedAway I f)) := comp_algebraMap_eq I hI σ f
  have hcont : ∀ g : CompletedAway I f →+* T,
      g.comp (algebraMap A (CompletedAway I f)) =
        second.comp (algebraMap A (CompletedAway I f)) → Continuous g := by
    intro g hg
    rw [isAdic_coefficientIdeal K hKfg σ]
    exact continuous_adic_of_map_le K (coefficientIdeal K σ) g
      (map_completedAwayCoefficientIdeal I f σ g hg).le
  exact completedHom_ext f
    (denseRange_algebraMap_adicCompletion (I.map (algebraMap A (Localization.Away f))) (hI.map _))
    first second (hcont first hbase) (hcont second rfl) hbase

/-- **The two contractions to `A_{\{f\}}` agree.**  For a prime `Q` of `A_{\{f\}}{σ}`, the
contraction of `Q` along the coefficient inclusion of `A_{\{f\}}` is the contraction along the
completed principal localization of `A → A{σ}` of the prime that `Q` corresponds to on
`A{σ}_{\{f\}}`.

This is the form the fourth paragraph of the proof of Stacks 0GGR uses it in: Stacks 0GGG hands
out a rig-closed prime of `A_{\{f\}}` as a contraction along the second route, and the paragraph
it reduces to asks for a contraction along the first. -/
public theorem comap_coefficientRingHom_completedAway (I : Ideal A) (hI : I.FG)
    (σ : Type v) (f : A)
    (Q : Ideal (RestrictedPowerSeries (completedAwayCoefficientIdeal I f) σ)) :
    Q.comap (coefficientRingHom (completedAwayCoefficientIdeal I f) σ) =
      (Q.comap (restrictedPowerSeriesCompletedAwayEquiv I hI σ f)).comap
        (RingHom.completedAwayMap (coefficientRingHom I σ) I f) := by
  rw [Ideal.comap_comap,
    ← restrictedPowerSeriesCompletedAwayEquiv_comp_completedAwayMap I hI σ f]

end

end Rig

end
