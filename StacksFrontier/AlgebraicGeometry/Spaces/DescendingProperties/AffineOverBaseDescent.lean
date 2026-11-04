module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Affineness over a base at a late stage of a limit of algebraic spaces

Let `Y` be a quasi-compact and quasi-separated algebraic space over `S` and let `X = lim X_i`
be a directed limit, over `Y` and with affine transition morphisms, of quasi-compact and
quasi-separated algebraic spaces, the standing situation of Stacks 084R. If `X ⟶ Y` is affine
then `X_i ⟶ Y` is affine for all `i` large enough. This is Stacks 0A0R.

The whole of that argument except one step is carried out here. That step is Stacks 07SQ, that a
directed limit with affine transition morphisms which is an *affine* algebraic space has an
affine stage; the one statement below that consumes it carries it as the named hypothesis
`h07SQ` rather than assuming it in a form that would let the conclusion be claimed for free.
Stacks 07SQ is now proved, as
`AlgebraicGeometry.Space.DescentSituation.exists_isAffineSpace_system_obj` in
`StacksFrontier/AlgebraicGeometry/Spaces/DescendingProperties/AffineStage.lean`, and that file —
which imports this one, so the dependency runs only in that direction — discharges the
hypothesis, giving `AlgebraicGeometry.Space.DescentSituation.exists_isAffineHom_system_app`.
No declaration in this file or in that one carries the tag 0A0R.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_of_isAffineSpace_source`: a morphism of presheaves from
  an affine algebraic space to an affine object of the site is affine.
* `AlgebraicGeometry.Space.isAffineHom_of_isAffineSpace_pullback_of_etaleChart`: the descent
  step, unconditionally — if `Y` has a surjective étale chart `h_W ⟶ Y` with `W` affine and
  `X ×_Y W` is an affine algebraic space, then `X ⟶ Y` is affine. This is the implication
  (4) ⇒ (2) of Stacks 03WG, fed by the observation that a morphism out of an affine space to
  an affine object is affine.
* `AlgebraicGeometry.Space.DescentSituation.isAffineSpace_baseChangeOver_limitCone_pt`:
  unconditionally, the base change of the limit along an affine point of `Y` is an affine
  algebraic space as soon as `X ⟶ Y` is affine.
* `AlgebraicGeometry.Space.DescentSituation.isAffineHom_app_of_le`: unconditionally,
  affineness of `X_i ⟶ Y` propagates to every later stage.
* `AlgebraicGeometry.Space.DescentSituation.exists_isAffineHom_system_app_of_affineStage`:
  **Stacks 0A0R, conditional on Stacks 07SQ**, which enters as the hypothesis `h07SQ`. The
  hypothesis is discharged, and the tag registered, in
  `AlgebraicGeometry.Space.DescentSituation.exists_isAffineHom_system_app`.

## Implementation notes

*The shape of the statement.* Situation 084R is
`AlgebraicGeometry.Space.DescentSituation`, and the system being one of algebraic spaces *over*
`Y` is a natural transformation `t` to the constant system at `Y`, exactly as in Stacks 086X,
`AlgebraicGeometry.Space.DescentSituation.exists_isSeparated_system_app`, which is the
separatedness twin of this tag and whose proof this one follows step for step. The structure
morphism of the limit is carried as a morphism `f` together with the compatibility `hf`,
rather than read off at the distinguished stage, which is the same data and is what the
base-change construction consumes. The conclusion is the source's "for `i` large enough",
namely an index beyond which *every* stage is affine over `Y`, not merely one stage.

*Where the hypotheses are used.* Quasi-compactness of `Y` is what produces the affine chart
`W ⟶ Y` the source chooses, by Stacks 03H6; quasi-separatedness of `Y` is what keeps the
stages of the base-changed situation quasi-compact, and it is consumed inside
`AlgebraicGeometry.Space.DescentSituation.baseChangeOver`. The source's hypothesis that the
stages are quasi-compact and quasi-separated is part of Situation 084R and so is carried by
the `DescentSituation` argument.

*Why the chart is a chart of `Y` and not of a stage.* Stacks 086X base changes along an affine
chart of the distinguished *stage*, pushed into `Y`, because a chart of `Y` is not what the
descent of separatedness there needs. Affineness descends along a surjective étale chart of
the *target* — that is the implication (4) ⇒ (2) of Stacks 03WG — so here the chart must be
one of `Y` itself, which is exactly why this tag assumes `Y` quasi-compact where 086X does
not.

*The index universe.* `AlgebraicGeometry.Space.DescentSituation` leaves the index universe
free, but the base-change construction and the cardinality hypothesis `#I < B.cutoff.ord.cof`
of Stacks 07SF both live at the site universe, so the index type is taken in `Type u` here, as
it is throughout the rest of the section.

## References

* [Stacks Project, Tag 0A0R](https://stacks.math.columbia.edu/tag/0A0R)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 086X](https://stacks.math.columbia.edu/tag/086X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Affine morphisms out of an affine algebraic space -/

/-- **A morphism from an affine algebraic space to an affine object of the site is affine.**
The source is isomorphic to a representable presheaf on an affine object, Yoneda is full, so
the morphism is a represented one up to that isomorphism, and a morphism of affine schemes is
affine. -/
theorem isAffineHom_of_isAffineSpace_source {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAffineSpace B S hS F) {W : BigFppfOver B S hS}
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) (h : F ⟶ yoneda.obj W) :
    IsAffineHom B S hS h := by
  obtain ⟨V, hV, ⟨e⟩⟩ := hF
  have hmap : yoneda.map (yoneda.preimage (e.inv ≫ h)) = e.inv ≫ h := yoneda.map_preimage _
  have h₁ : IsAffineHom B S hS (e.inv ≫ h) := by
    rw [← hmap]
    have _ := hV
    have _ := hW
    exact isAffineHom_of_presheaf
      ((presheaf_yoneda_map_iff B S hS
          (P := @_root_.AlgebraicGeometry.IsAffineHom.{u}) inferInstance _).mpr
        (_root_.AlgebraicGeometry.isAffineHom_of_isAffine _))
  simpa using isAffineHom_iso_comp (F' := F) e.hom h₁

/-! ### The descent step of Stacks 03WG -/

/-- **Affineness over a base with an affine surjective étale chart.** Let `p : X ⟶ Y` be a
morphism of algebraic spaces over `S` and let `a : h_W ⟶ Y` be a surjective étale morphism
with `W` an affine object of the site. If the base change `X ×_Y W` is an affine algebraic
space then `p` is affine.

This is the reduction "`X ×_Y W` is affine and it suffices to check that `X_i ×_Y W` is affine
for some `i`" of the proof of Stacks 0A0R: the base change `X ×_Y W ⟶ h_W` is a morphism from
an affine algebraic space to an affine object of the site, hence affine, and the implication
(4) ⇒ (2) of Stacks 03WG descends that to `p`. -/
theorem isAffineHom_of_isAffineSpace_pullback_of_etaleChart
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (p : X ⟶ Y) {W : BigFppfOver B S hS}
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) (a : yoneda.obj W ⟶ Y)
    (hsurj : IsSurjective B S hS a) (hetale : IsEtale B S hS a)
    (hpb : IsAffineSpace B S hS (pullback p a)) :
    IsAffineHom B S hS p := by
  refine ((isAffineHom_tfae_of_isAlgebraicSpace B S hS p hX hY).out 4 2).1 ?_
  exact ⟨W, a, hsurj, hetale,
    isAffineHom_of_isAffineSpace_source B S hS hpb hW (pullback.snd p a)⟩

/-! ### Stacks 0A0R -/

section OverBase

variable (hZ : B.Contains (⊤_ Scheme.{u})) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

/-- **The base change of an affine limit along an affine point of the base is affine.** If the
structure morphism `f : X ⟶ Y` of the limit of a descent situation over `Y` is affine and
`u : h_U ⟶ Y` is a point of `Y` with `U` an affine object of the site, then the limit of the
base-changed descent situation, which is `X ×_Y U`, is an affine algebraic space.

Its projection to `h_U` is a base change of `f`, hence affine by Stacks 03WI, and the source of
an affine morphism with affine target is affine. -/
theorem DescentSituation.isAffineSpace_baseChangeOver_limitCone_pt
    (D : DescentSituation B S hS hZ I) (hY : IsAlgebraicSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (t : D.system ⟶ (Functor.const Iᵒᵖ).obj Y) (f : D.limitCone.pt ⟶ Y)
    (hf : ∀ j, D.limitCone.π.app j ≫ t.app j = f) (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) (u : yoneda.obj U ⟶ Y)
    (haff : IsAffineHom B S hS f) :
    IsAffineSpace B S hS
      (D.baseChangeOver B S hS hZ hY hYqs t f hf U hU u).limitCone.pt :=
  (IsAffineHom.of_isPullback (IsPullback.of_hasPullback f u) haff).isAffineSpace_source
    (isAffineSpace_yoneda B S hS U hU)

/-- **Affineness over the base propagates to every later stage.** The transition morphism from a
later stage is affine and composes with the structure morphism of the earlier stage to that of
the later one, so Stacks 03WH applies. -/
theorem DescentSituation.isAffineHom_app_of_le (D : DescentSituation B S hS hZ I)
    (t : D.system ⟶ (Functor.const Iᵒᵖ).obj Y) {i : I}
    (hi : IsAffineHom B S hS (t.app (op i))) {k : I} (hik : i ≤ k) :
    IsAffineHom B S hS (t.app (op k)) := by
  have hk : D.system.map (homOfLE hik).op ≫ t.app (op i) = t.app (op k) := by simp
  rw [← hk]
  exact isAffineHom_comp B S hS _ _ (D.transition_affine _) hi

/-- **Stacks 0A0R, conditional on Stacks 07SQ.** Let `Y` be a quasi-compact and quasi-separated
algebraic space over `S` and let `X = lim X_i` be a directed limit, over `Y` and with affine
transition morphisms, of quasi-compact and quasi-separated algebraic spaces over `S`, as in the
standing situation of Stacks 084R. If `X ⟶ Y` is affine then `X_i ⟶ Y` is affine for all `i`
large enough.

Choose an affine object `W` of the site with `h_W ⟶ Y` surjective and étale, which exists
because `Y` is quasi-compact, by Stacks 03H6. Base changing the whole situation along it is
again a situation of Stacks 084R — the stages stay quasi-compact because `W` is quasi-compact
and `Y` is quasi-separated — whose limit is `X ×_Y W`, an affine algebraic space because
`X ⟶ Y` is affine and `W` is affine. So some stage `X_i ×_Y W` is affine, which is what the
hypothesis `h07SQ` supplies, and affineness of `X_i ⟶ Y` then descends from that by the
implication (4) ⇒ (2) of Stacks 03WG along the chart `h_W ⟶ Y`. Finally the transition
morphisms are affine, so `X_k ⟶ Y` is affine for every `k ≥ i`.

The hypothesis `h07SQ` is **Stacks 07SQ**: in the situation of Stacks 084R, an affine limit has
an affine stage. Everything else the source's proof uses is discharged here. Stacks 07SQ is
proved downstream, in
`StacksFrontier/AlgebraicGeometry/Spaces/DescendingProperties/AffineStage.lean`, which imports this
file; `AlgebraicGeometry.Space.DescentSituation.exists_isAffineHom_system_app` there feeds it to
this statement and is the unconditional Stacks 0A0R, which is where the tag sits. This statement
stays conditional and untagged, since a tag on a hypothetical would claim the result and prove
nothing. -/
theorem DescentSituation.exists_isAffineHom_system_app_of_affineStage
    (D : DescentSituation B S hS hZ I) (hI : #I < B.cutoff.ord.cof)
    (hY : IsAlgebraicSpace B S hS Y) (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (t : D.system ⟶ (Functor.const Iᵒᵖ).obj Y) (f : D.limitCone.pt ⟶ Y)
    (hf : ∀ j, D.limitCone.π.app j ≫ t.app j = f) (haff : IsAffineHom B S hS f)
    (h07SQ : ∀ (E : DescentSituation B S hS hZ I), #I < B.cutoff.ord.cof →
      IsAffineSpace B S hS E.limitCone.pt →
      ∃ i : I, E.base ≤ i ∧ IsAffineSpace B S hS (E.system.obj (op i))) :
    ∃ i, D.base ≤ i ∧ ∀ k, i ≤ k → IsAffineHom B S hS (t.app (op k)) := by
  -- an affine surjective étale chart of `Y`, which exists because `Y` is quasi-compact
  obtain ⟨W, a, hW, haS, haE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y hY).mp hYqc
  -- the base changed descent situation, and affineness of its limit `X ×_Y W`
  have hlim : IsAffineSpace B S hS
      (D.baseChangeOver B S hS hZ hY hYqs t f hf W hW a).limitCone.pt :=
    D.isAffineSpace_baseChangeOver_limitCone_pt B S hS hZ hY hYqs t f hf W hW a haff
  obtain ⟨i, hbi₀, hi⟩ :=
    h07SQ (D.baseChangeOver B S hS hZ hY hYqs t f hf W hW a) hI hlim
  have hbi : D.base ≤ i := hbi₀
  -- the base change of the stage along the chart of `Y` is affine, so the stage is affine
  -- over `Y` by the implication (4) ⇒ (2) of Stacks 03WG
  have hstage : IsAffineHom B S hS (t.app (op i)) :=
    isAffineHom_of_isAffineSpace_pullback_of_etaleChart B S hS (D.algebraicSpace i) hY
      (t.app (op i)) hW a (isSurjective_of_presheafSurjective B S hS a haS) haE hi
  -- and propagate it to all later stages along the affine transition morphisms
  exact ⟨i, hbi, fun _ hik => D.isAffineHom_app_of_le B S hS hZ t hstage hik⟩

end OverBase

end AlgebraicGeometry.Space

end
