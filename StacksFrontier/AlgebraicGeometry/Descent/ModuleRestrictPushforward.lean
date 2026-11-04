module

public import StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueRestrictIso

/-!
# The chart comparison for an arbitrary open immersion

`AlgebraicGeometry.RestrictIsoGlueData` asks, for each pair of charts `a : A ⟶ S` and
`b : B ⟶ S` and each open `V` of `S` inside both ranges, for an isomorphism
`a_* M |_V ≅ b_* N |_V` of sheaves of modules on `V`.  This file reduces that to an isomorphism
of the inverse images of `M` and `N` on `V` itself, which is the form in which comparisons of
modules on charts are actually available.

The reduction has two steps.  An open `V` inside the range of an open immersion `a` admits a
*unique* morphism `V ⟶ A` over `S` — `AlgebraicGeometry.openLift`, unique because an open
immersion is a monomorphism — and for any factorisation `b ≫ a = c` of a morphism through an
open immersion the inverse image along `c` of a direct image along `a` is the inverse image along
`b`, by the counit of the restriction–direct image adjunction.  Together they give
`AlgebraicGeometry.restrictPushforwardOpenLiftIso`:

`a_* M |_V ≅ (openLift a hV)^* M`.

Uniqueness of `openLift` is what makes this usable on overlaps: if `V` lies in the range of a
third chart `c = p ≫ a`, then `openLift a hV` is *equal* to `openLift c hV' ≫ p`, so the
comparison over `V` is the inverse image along `openLift c hV'` of a comparison on the third
chart.  That is the mechanism by which a comparison living on the intersection chart produces
the data `RestrictIsoGlueData` wants, with no section-level computation.

## Main definitions

* `AlgebraicGeometry.openLift`: the factorisation `V ⟶ A` of the inclusion of an open contained
  in the range of an open immersion `a : A ⟶ S`.
* `AlgebraicGeometry.pullbackPushforwardCounitIso`: the counit `a^*(a_* M) ≅ M` of an open
  immersion.
* `AlgebraicGeometry.pullbackPushforwardIso`: `c^*(a_* M) ≅ b^* M` for `b ≫ a = c`.
* `AlgebraicGeometry.restrictPushforwardOpenLiftIso`: **the chart comparison**
  `a_* M |_V ≅ (openLift a hV)^* M`.
* `AlgebraicGeometry.restrictPushforwardIsoOfPullbackIso`: the comparison of two charts over a
  common open, from a comparison of the inverse images.

## Main results

* `AlgebraicGeometry.openLift_comp`: the factorisation factorises.
* `AlgebraicGeometry.eq_openLift`: **it is the only one that does.**
* `AlgebraicGeometry.openLift_comp_eq`: the factorisation through a chart that itself factorises
  through another is the composite of the two, which is the statement used on overlaps.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### The factorisation of an open inside the range of an open immersion -/

section OpenLift

variable {S A : Scheme.{u}} (a : A ⟶ S) [IsOpenImmersion a]

/-- **The factorisation of the inclusion of an open contained in the range of an open
immersion.**  An open immersion is a monomorphism, so this is the only morphism `V ⟶ A` whose
composite with `a` is the inclusion of `V`. -/
def openLift {V : S.Opens} (hV : V ≤ a.opensRange) : V.toScheme ⟶ A :=
  IsOpenImmersion.lift a V.ι (by
    rw [Scheme.Opens.range_ι]
    exact fun x hx ↦ hV hx)

/-- The factorisation `openLift a hV` followed by `a` is the inclusion of `V` into `S`. -/
@[simp] theorem openLift_comp {V : S.Opens} (hV : V ≤ a.opensRange) :
    openLift a hV ≫ a = V.ι :=
  IsOpenImmersion.lift_fac _ _ _

/-- **The factorisation is unique**, an open immersion being a monomorphism. -/
theorem eq_openLift {V : S.Opens} (hV : V ≤ a.opensRange) (b : V.toScheme ⟶ A)
    (hb : b ≫ a = V.ι) : b = openLift a hV :=
  (cancel_mono a).mp (hb.trans (openLift_comp a hV).symm)

/-- The range of a morphism factoring through `a` is contained in the range of `a`. -/
theorem opensRange_le_of_comp {C : Scheme.{u}} {p : C ⟶ A} {c : C ⟶ S} (hc : p ≫ a = c)
    [IsOpenImmersion c] : c.opensRange ≤ a.opensRange := by
  intro x hx
  obtain ⟨z, hz⟩ := hx
  refine ⟨p.base z, ?_⟩
  have h2 : (p ≫ a).base z = x := by
    rw [hc]
    exact hz
  simpa using h2

/-- **The factorisation through a chart that factorises through another is the composite.**  If
`p ≫ a = c` with `c` an open immersion and `V` lies in the range of `c`, then the factorisation
of `V` through `a` is the factorisation through `c` followed by `p`. -/
theorem openLift_comp_eq {C : Scheme.{u}} {p : C ⟶ A} {c : C ⟶ S} (hc : p ≫ a = c)
    [IsOpenImmersion c] {V : S.Opens} (hV : V ≤ c.opensRange) :
    openLift c hV ≫ p = openLift a (hV.trans (opensRange_le_of_comp a hc)) :=
  eq_openLift a _ _ (by rw [Category.assoc, hc, openLift_comp])

end OpenLift

/-! ### The chart comparison -/

section ChartComparison

variable {S A : Scheme.{u}} (a : A ⟶ S) [IsOpenImmersion a] (M : A.Modules)

/-- **The counit `a^*(a_* M) ≅ M` of an open immersion.**  The inverse image along an open
immersion is the restriction (`Scheme.Modules.restrictFunctorIsoPullback`), and the restriction of
a direct image along an open immersion is the module itself
(`Scheme.Modules.restrictFunctorAdjCounitIso`). -/
def pullbackPushforwardCounitIso :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pushforward a).obj M) ≅ M :=
  ((Scheme.Modules.restrictFunctorIsoPullback a).app
      ((Scheme.Modules.pushforward a).obj M)).symm ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso a).app M

/-- **The inverse image of a direct image along an open immersion, through a factorisation.**  For
`b ≫ a = c` with `a` an open immersion, `c^*(a_* M) ≅ b^* M`. -/
def pullbackPushforwardIso {Z : Scheme.{u}} {b : Z ⟶ A} {c : Z ⟶ S} (h : b ≫ a = c) :
    (Scheme.Modules.pullback c).obj ((Scheme.Modules.pushforward a).obj M) ≅
      (Scheme.Modules.pullback b).obj M :=
  ((Scheme.Modules.pullbackCongr h).app ((Scheme.Modules.pushforward a).obj M)).symm ≪≫
    ((Scheme.Modules.pullbackComp b a).app ((Scheme.Modules.pushforward a).obj M)).symm ≪≫
    (Scheme.Modules.pullback b).mapIso (pullbackPushforwardCounitIso a M)

/-- **The chart comparison at an open inside the range of an open immersion.**  Over an open `V`
of `S` contained in the range of `a`, the restriction of the direct image `a_* M` is the inverse
image of `M` along the factorisation `AlgebraicGeometry.openLift` of `V`. -/
def restrictPushforwardOpenLiftIso {V : S.Opens} (hV : V ≤ a.opensRange) :
    Scheme.Modules.restrict ((Scheme.Modules.pushforward a).obj M) V.ι ≅
      (Scheme.Modules.pullback (openLift a hV)).obj M :=
  (Scheme.Modules.restrictFunctorIsoPullback V.ι).app _ ≪≫
    pullbackPushforwardIso a M (openLift_comp a hV)

end ChartComparison

/-- **The comparison of two charts over a common open, from a comparison of the inverse
images.**  For open immersions `a` and `b` and an open `V` of `S` in both ranges, an isomorphism
of the inverse images of `M` and `N` along the factorisations of `V` gives
`a_* M |_V ≅ b_* N |_V`. -/
def restrictPushforwardIsoOfPullbackIso {S A B : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S)
    [IsOpenImmersion a] [IsOpenImmersion b] (M : A.Modules) (N : B.Modules) {V : S.Opens}
    (ha : V ≤ a.opensRange) (hb : V ≤ b.opensRange)
    (e : (Scheme.Modules.pullback (openLift a ha)).obj M ≅
      (Scheme.Modules.pullback (openLift b hb)).obj N) :
    (Scheme.Modules.restrict ((Scheme.Modules.pushforward a).obj M) V.ι ≅
      Scheme.Modules.restrict ((Scheme.Modules.pushforward b).obj N) V.ι) :=
  restrictPushforwardOpenLiftIso a M ha ≪≫ e ≪≫ (restrictPushforwardOpenLiftIso b N hb).symm

end AlgebraicGeometry

end
