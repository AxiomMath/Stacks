module

public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.ImpurityAffineLimitDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityAffineLocalBase

/-!
# The ascent of purity to `Spec 𝒪_{V, v}`

In the standing situation of Stacks 0CV6 — a finite type decent morphism `f : X ⟶ Y` of
algebraic spaces over `S`, a finite type quasi-coherent `𝒪_X`-module `ℱ` and a point `y` of
`Y` — the proof of Stacks 0CW4 begins "consider the morphism `Spec(𝒪_{Y, ȳ}) ⟶ Y`" and then
works over that base, keeping the hypothesis that `ℱ` is pure above the chosen point. The step
it leaves silent is the *ascent*: purity above `y` has to become purity of the base change
above the closed point of the local base. This file proves that ascent in the form the
consumers of Stacks 0CW3, clause (2), need it, from purity above `y` and one geometric input.

## What purity above the local base amounts to

Purity above `y` is the failure of condition (4) of Stacks 0CVB: no impurity whose structure
morphism `T ⟶ Y` is quasi-finite at `t`. The base change `Spec 𝒪_{V, v} ⟶ V ⟶ Y` is *not*
quasi-finite — it is not even locally of finite type — so Stacks 0CVF,
`AlgebraicGeometry.Space.isPureAbove_baseChange_of_isQuasiFiniteAt`, does not apply, and an
impurity of the base change above the closed point reads, under
`AlgebraicGeometry.Space.PointedOver.isImpurity_alongBaseChange_iff`, as an impurity of `ℱ`
above `y` whose structure morphism is neither quasi-finite nor flat at `t`.

Stacks 0CVB closes that gap by its implication (1) ⟹ (4): an impurity whose structure
morphism is the local base itself gives one over an affine étale neighbourhood, *because the
local base is a cofiltered limit of such neighbourhoods*, and the limit descent of impurities
is Stacks 0CV9. Both halves of that argument are available here:
`AlgebraicGeometry.Space.AffineLimitPresentation.exists_isImpurity_stageDiagram` is Stacks 0CV9
with nothing granted, and
`AlgebraicGeometry.Space.exists_isImpurity_isQuasiFiniteAt_of_exists_isImpurity_isEtale` is
Stacks 0CVB, (3) ⟹ (4). What is missing is only the limit presentation itself — the sentence
"`𝒪 = colim 𝒪(V)` over affine étale neighbourhoods, hence `Y^{sh} = lim V`" of the source's
proof of Stacks 0CVB — and that is the single hypothesis carried below,
`AlgebraicGeometry.Space.SpecStalkAffineLimitPresentation`.

## Main definitions

* `AlgebraicGeometry.Space.PrePureSituation.specStalkDiagram`: the impurity diagram of `ℱ`
  above `y` whose test scheme is `Spec 𝒪_{V, v}` and whose structure morphism is the one of
  `AlgebraicGeometry.Space.PrePureSituation.specStalkPointedOver`. These are exactly the
  diagrams that condition (1) of Stacks 0CVB speaks about, and the only ones the specialization
  step of Stacks 0CW3, clause (2), uses over the local base.
* `AlgebraicGeometry.Space.SpecStalkAffineLimitPresentation`: the carried input, that every
  such diagram admits a presentation of its test scheme as a cofiltered limit of affine schemes
  over `Y` whose structure morphisms are quasi-finite at the point below the closed point.

## Main results

* `AlgebraicGeometry.Space.not_isImpurity_of_affineLimitPresentation`: **Stacks 0CVB, the
  implication (1) ⟹ (4) in contrapositive**, with nothing granted: purity above `y` excludes
  every impurity whose test scheme is presented as a cofiltered limit of affine test schemes
  quasi-finite over `Y` at the points below `t`.
* `AlgebraicGeometry.Space.exists_specializes_fibre_of_isPureAbove`: **the ascent.** Purity of
  `ℱ` above `y`, with the limit presentation granted, makes every point of
  `Ass_{X_𝒪/Spec 𝒪_{V, v}}(ℱ_𝒪)` specialize to a point of the fibre over the closed point.
  This is condition (2) of Stacks 0CVB for the base change, and it is what the specialization
  step of Stacks 0CW3, clause (2), supplies over an affine local base from purity.
* `EtaleOverSource.relativeWeaklyAssociatedPoints_subset_range_of_exists_specializes`: Stacks
  0CW3, clause (2), from that specialization alone — the generalization of
  `EtaleOverSource.relativeWeaklyAssociatedPoints_subset_range_of_isAffineLocalAt` which drops
  the affine local base and purity in favour of the one consequence of them that the proof uses.
* `AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints_subset_range_specStalkBaseChange`:
  the two composed, which is the form the dévissage of Stacks 083F consumes.

## Why the hypothesis is not the conclusion

The carried hypothesis quantifies over *every* diagram with test scheme `Spec 𝒪_{V, v}`,
whether or not it is an impurity, and asks for a limit presentation of that test scheme over
`Y`. It mentions neither purity nor the relative assassin. In particular:

* it is not implied by the conclusion: the conclusion is a statement about specializations of
  relatively associated points and says nothing about limit presentations of the base;
* it does not imply the conclusion on its own: `hpure` is load-bearing, since the presentations
  it provides exist for an impure module just as much as for a pure one — the limit descent
  then produces an impurity over an affine étale neighbourhood, which is a contradiction only
  because `ℱ` was assumed pure above `y`;
* it is not vacuous: such diagrams exist as soon as a point of `X_𝒪` is given, and the
  presentation asked for is the source's own `Y^{sh} = lim V`.

`AlgebraicGeometry.Space.isPureAbove_baseChange_iff_forall_exists_isImpurity_isQuasiFiniteAt`
records, for contrast, what goes wrong with the obvious alternative: a hypothesis carrying the
*transfer* of impurities from the base change back to `Y` is, granted purity above `y`,
**equivalent** to the purity of the base change it is supposed to prove, exactly as the
composition of Stacks 0CVV with Morphisms 05LW is equivalent to its own conclusion
(`AlgebraicGeometry.mem_nhds_iff_specializes_subset_of_isLocallyConstructible`). Such a
hypothesis cannot be carried: it is the conclusion.

The other route — deducing the ascent from universal purity by Stacks 0CVE, and universal
purity from Stacks 0CW5 — is circular in the same way, and visibly so: `IsPureAbove
c.baseChange` is a conjunct of `AlgebraicGeometry.Space.PurityStrictlyHenselianReduction`
itself, the hypothesis Stacks 0CW5 carries here. Nothing below uses Stacks 0CW4, Stacks 0CW5
or universal purity.

## What discharges the carried input, and what does not

The mathematics of the source's sentence is proved, in
`StacksFrontier/AlgebraicGeometry/Spaces/Flat/SpecStalkAffineNhdsSystem.lean`. Take `V` *étale*
over `Y` — an atlas chart, as
`AlgebraicGeometry.Space.PrePureSituation.exists_pointedOver_isAffineLocalAt` does — and let
the stages be the affine open neighbourhoods `U` of `v` in `V`. Then
`𝒪_{V, v} = colim_U 𝒪(U)`, and `Spec` carries that filtered colimit of rings to the limit of
the spectra because it is right adjoint to global sections, so
`Spec 𝒪_{V, v} = lim_U Spec 𝒪(U) = lim_U U`; each `U ⟶ V ⟶ Y` is étale, being an open
immersion followed by an étale morphism, hence quasi-finite at every point. All of that is
`AlgebraicGeometry.Space.isLimitAffineNhdsSiteCone`, which is the same limit *inside the site*,
and `AlgebraicGeometry.Space.exists_unique_presheafHom_specStalk`, which is it in the
presheaf-level form the `isLimit` field of
`AlgebraicGeometry.Space.AffineLimitPresentation` asks for.

What was left over was **not** mathematics but the cardinality clause of that structure, and it
has since been corrected. The clause used to be `#J < B.cutoff.ord.cof`, and under that clause
the carried input was *false* for an interesting chart: the basic opens `D(f)`, `f ∉ 𝔭`, number
`#A`, which is bounded by `B.cutoff` — `Scheme.size` of a site object is — but by nothing
smaller, and on the cutoff `AlgebraicGeometry.exists_size_cutoff` produces the cofinality is
`ℵ₁`, so that clause asked for a *countable* system of neighbourhoods. Worse, no other system
would do either: `Spec 𝒪_{V, v}` is the spectrum of a local ring, so its only open neighbourhood
of the closed point is itself, hence every projection `Spec 𝒪_{V, v} ⟶ Tᵢ` of a presentation
factors through an affine open of `Tᵢ` on which `Tᵢ ⟶ Y` is of finite type, and the resulting
`#J`-many finite-type subalgebras of `𝒪_{V, v}` exhaust it only if the `#J` opens they come from
refine every neighbourhood of `v`. For `V` the affine plane over an uncountable field and `v` its
generic point there is no countable such family.

That cofinality bound was a requirement of the limit-descent *route*, through
`AlgebraicGeometry.Space.isAlgebraicSpace_limit`, and not of Stacks 0CV9, and the clause is now
`AlgebraicGeometry.Space.SiteLimitBound`: the *disjunction* of that bookkeeping with a
cofinality-free package — fewer objects than the cutoff itself, one cardinal bounding all the
Hom-sets, and monomorphic transition morphisms. The structure is thereby strictly easier to
inhabit and Stacks 0CV9 strictly stronger; the whole limit chain it rests on has the second
package beside the first, from Stacks 07SF down through Stacks 086V, Stacks 0CUJ, Stacks 0CUI,
Stacks 0CUK and Stacks 086W, with every `@[stacks]` registration left on the form carrying the
source's own hypothesis. The same artifact is recorded for the index sets of Stacks 07SF in the
notes of
`StacksFrontier/AlgebraicGeometry/Spaces/NoetherianApproximationFromPresentation.lean`. A third
package, with the monomorphy replaced by one cardinal bounding the sizes of all the stages, is
what the affine étale neighbourhoods of a geometric point satisfy, and it is the one through which
the strict henselization itself is presented in
`StacksFrontier/AlgebraicGeometry/Spaces/Flat/StrictHenselizationImpurity.lean`.

Consequently the carried input is now **proved**, not carried, for the charts the consumers
supply: `AlgebraicGeometry.Space.specStalkAffineLimitPresentation_of_isEtale` discharges it from
the single hypothesis that `a` is étale, over the system of *all* affine open neighbourhoods of
`v`, which satisfies the cofinality-free package because those neighbourhoods inject into the
affine opens of `V`, because the system is a partial order, and because its transition morphisms
are open immersions. `AlgebraicGeometry.Space.specStalkAffineLimitPresentation` is kept beside
it, discharging the input from `a` étale together with
`AlgebraicGeometry.Space.HasSmallAffineNhdsBasis` — a basis of affine open neighbourhoods of `v`
small for the site — for a caller who has that from elsewhere. Neither hypothesis names `ℱ` or
purity or the relative assassin, so neither is an instance of the family
`AlgebraicGeometry.Space.isPureAbove_baseChange_iff_forall_exists_isImpurity_isQuasiFiniteAt`
excludes.

For a morphism `a : V ⟶ Y` which is *not* quasi-finite at `v` the input is false as stated, and
deliberately so: the stage structure morphisms could not then be quasi-finite. A caller must
supply an étale — or at least quasi-finite — chart, which is what an atlas gives. That is the one
hypothesis the discharge above still needs.

## Implementation notes

The ascent is proved in the form of condition (2) of Stacks 0CVB rather than as `IsPureAbove`
of the base change, and that is not a weakening of what the consumers need: the specialization
step of Stacks 0CW3, clause (2) — `AlgebraicGeometry.Space.purityFibreSpecialization` — uses
purity over an affine local base only through the diagram whose test scheme *is* the base, and
those are precisely the diagrams of condition (1). The full `IsPureAbove` of the base change
would in addition ask for the diagrams whose test scheme is merely quasi-finite over
`Spec 𝒪_{V, v}`; presenting those as limits over `Y` needs the descent of a finite type scheme
along `Spec 𝒪_{V, v} = lim U` as well, which is a strictly larger input and which none of the
consumers in this development require.

## References

* [Stacks Project, Tag 0CVB](https://stacks.math.columbia.edu/tag/0CVB)
* [Stacks Project, Tag 0CV9](https://stacks.math.columbia.edu/tag/0CV9)
* [Stacks Project, Tag 0CVD](https://stacks.math.columbia.edu/tag/0CVD)
* [Stacks Project, Tag 0CVE](https://stacks.math.columbia.edu/tag/0CVE)
* [Stacks Project, Tag 0CVF](https://stacks.math.columbia.edu/tag/0CVF)
* [Stacks Project, Tag 0CW3](https://stacks.math.columbia.edu/tag/0CW3)
* [Stacks Project, Tag 0CW4](https://stacks.math.columbia.edu/tag/0CW4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site needs more heartbeats
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out). -/
local instance (priority := high) hasPullbacks_presheaf_PurityAscentSpecStalk :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site over `S`, supplied directly: instance search
for them now times out. -/
local instance (priority := high) hasLimit_cospan_presheaf_PurityAscentSpecStalk
    {Z₁ Z₂ Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z₁ ⟶ Z) (f : Z₂ ⟶ Z) :
    HasLimit (cospan g f) :=
  HasLimitsOfShape.has_limit _

/-! ### Stacks 0CVB, the implication (1) implies (4) -/

/-- **Purity above `y` excludes every impurity whose test scheme is a cofiltered limit of
affine test schemes quasi-finite over `Y`.** If the test scheme `T` of an impurity diagram is
presented as `T = lim Tᵢ` with each `Tᵢ` affine over `Y` and each `Tᵢ ⟶ Y` quasi-finite at the
point below `t`, then the diagram is not an impurity.

This is the implication (1) ⟹ (4) of Stacks 0CVB in contrapositive, with nothing granted: by
Stacks 0CV9 the impurity descends to a stage, and the stage diagram is one of those that purity
above `y` excludes. The source applies it to `T = Y^{sh} = lim V` over the affine étale
neighbourhoods of a geometric point above `y`. -/
theorem not_isImpurity_of_affineLimitPresentation {P : PrePureSituation.{u, u} B S hS}
    (hpure : IsPureAbove P) {D : ImpurityDiagram P} (A : AffineLimitPresentation D)
    (hqf : ∀ i, IsQuasiFiniteAt B S hS (A.base i) (A.stagePoint i)) :
    ¬ D.IsImpurity := fun hD =>
  (A.exists_isImpurity_stageDiagram hD).elim fun i hi => hpure (A.stageDiagram i) (hqf i) hi

/-- **Purity above `y` excludes every impurity whose test scheme is a cofiltered limit of
affine test schemes étale over `Y`.** This is
`AlgebraicGeometry.Space.not_isImpurity_of_affineLimitPresentation` for étale stages, which is
the shape of the source's limit `Y^{sh} = lim V` over affine étale neighbourhoods: an étale
morphism of algebraic spaces is locally quasi-finite by Stacks 03XU, hence quasi-finite at every
point. -/
theorem not_isImpurity_of_affineLimitPresentation_of_isEtale
    {P : PrePureSituation.{u, u} B S hS} (hpure : IsPureAbove P) {D : ImpurityDiagram P}
    (A : AffineLimitPresentation D) (hetale : ∀ i, IsEtale B S hS (A.base i)) :
    ¬ D.IsImpurity :=
  not_isImpurity_of_affineLimitPresentation hpure A fun i =>
    isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS
      (isAlgebraicSpace_yoneda B S hS (A.stage.obj i))
      (isLocallyQuasiFinite_of_isEtale B S hS P.hY (hetale i)) _

/-! ### The impurity diagrams over `Spec 𝒪_{V, v}` -/

/-- **The impurity diagrams of condition (1) of Stacks 0CVB, at `Spec 𝒪_{V, v}`.** For a scheme
`V` of the site with a morphism `a : V ⟶ Y` and a point `v` above the chosen point `y`, this is
the impurity diagram of `ℱ` above `y` whose test scheme is `Spec 𝒪_{V, v}`, whose structure
morphism is the one of
`AlgebraicGeometry.Space.PrePureSituation.specStalkPointedOver`, whose `t` is the closed point
and whose distinguished point is a given point `ξ` of `X_𝒪 = Spec 𝒪_{V, v} ×_Y X` above a given
point `t'`.

The specialization `t' ⤳ 𝔪` it needs is free: every point of the spectrum of a local ring
specializes to the closed point. -/
noncomputable def PrePureSituation.specStalkDiagram (P : PrePureSituation.{u, u} B S hS)
    (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ P.Y) (v : points B S hS (yoneda.obj V))
    (hv : pointsMap B S hS (yoneda.obj V) a v = P.y)
    (t' : points B S hS
      (yoneda.obj (BigFppfOver.specStalk B S hS V (pointsToScheme B S hS V v))))
    (xi : points B S hS (pullback (P.specStalkPointedOver V a v hv).g P.f))
    (hxi : pointsMap B S hS (pullback (P.specStalkPointedOver V a v hv).g P.f)
      (pullback.fst (P.specStalkPointedOver V a v hv).g P.f) xi = t') :
    ImpurityDiagram P where
  T := BigFppfOver.specStalk B S hS V (pointsToScheme B S hS V v)
  g := (P.specStalkPointedOver V a v hv).g
  t' := t'
  t := BigFppfOver.specStalkClosedPoint B S hS V (pointsToScheme B S hS V v)
  specializes := by
    rw [BigFppfOver.pointsToScheme_specStalkClosedPoint]
    exact IsLocalRing.specializes_closedPoint _
  mapsToChosenPoint := (P.specStalkPointedOver V a v hv).mapsPoint
  xi := xi
  xi_liesOver := hxi

/-- **The carried input: `Spec 𝒪_{V, v}` is a cofiltered limit of affine schemes quasi-finite
over `Y`.** Every impurity diagram of `ℱ` above `y` with test scheme `Spec 𝒪_{V, v}` and the
canonical structure morphism admits a presentation of that test scheme as a cofiltered limit
`Spec 𝒪_{V, v} = lim Tᵢ` of affine schemes over `Y`, with each `Tᵢ ⟶ Y` quasi-finite at the
point below the closed point.

This is the source's "`𝒪 = colim 𝒪(V)` over the affine étale neighbourhoods, hence
`Y^{sh} = lim V`" in the form Stacks 0CV9 consumes it, and it is the only thing granted by
`AlgebraicGeometry.Space.exists_specializes_fibre_of_isPureAbove`. It says nothing about
purity, about impurities or about the relative assassin: the quantifier runs over all diagrams
with that test scheme, impure or not, so no hypothesis about the module can make it vacuous. -/
def SpecStalkAffineLimitPresentation (P : PrePureSituation.{u, u} B S hS)
    (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ P.Y) (v : points B S hS (yoneda.obj V))
    (hv : pointsMap B S hS (yoneda.obj V) a v = P.y) : Prop :=
  ∀ (t' : points B S hS
      (yoneda.obj (BigFppfOver.specStalk B S hS V (pointsToScheme B S hS V v))))
    (xi : points B S hS (pullback (P.specStalkPointedOver V a v hv).g P.f))
    (hxi : pointsMap B S hS (pullback (P.specStalkPointedOver V a v hv).g P.f)
      (pullback.fst (P.specStalkPointedOver V a v hv).g P.f) xi = t'),
    ∃ A : AffineLimitPresentation (P.specStalkDiagram V a v hv t' xi hxi),
      ∀ i, IsQuasiFiniteAt B S hS (A.base i) (A.stagePoint i)

/-! ### The ascent -/

/-- **The ascent of purity along `Spec 𝒪_{V, v} ⟶ V ⟶ Y`.** Let `ℱ` be pure above `y`, let `V`
be a scheme of the site over `Y` and `v` a point of it above `y`. Granted the limit
presentation of `Spec 𝒪_{V, v}`, every point of the relative assassin
`Ass_{X_𝒪/Spec 𝒪_{V, v}}(ℱ_𝒪)` of the base change specializes to a point of the fibre of
`X_𝒪 ⟶ Spec 𝒪_{V, v}` over the closed point.

This is condition (2) of Stacks 0CVB for the base change — the negation of condition (1) — and
it is exactly what the specialization step of Stacks 0CW3, clause (2), gets out of purity over
an affine local base. A point of the assassin with no specialization into the closed fibre is
the distinguished point of one of the diagrams of
`AlgebraicGeometry.Space.PrePureSituation.specStalkDiagram`, and those are excluded by
`AlgebraicGeometry.Space.not_isImpurity_of_affineLimitPresentation`. -/
theorem exists_specializes_fibre_of_isPureAbove (P : PrePureSituation.{u, u} B S hS)
    (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ P.Y) (v : points B S hS (yoneda.obj V))
    (hv : pointsMap B S hS (yoneda.obj V) a v = P.y) (hpure : IsPureAbove P)
    (hlim : SpecStalkAffineLimitPresentation P V a v hv) :
    ∀ x ∈ relativeWeaklyAssociatedPoints B S hS
        (P.specStalkPointedOver V a v hv).baseChange.structureSpaceMorphism
        (P.specStalkPointedOver V a v hv).baseChange.F,
      ∃ θ : points B S hS (P.specStalkPointedOver V a v hv).baseChange.X,
        x ⤳ θ ∧ pointsMap B S hS (P.specStalkPointedOver V a v hv).baseChange.X
            (P.specStalkPointedOver V a v hv).baseChange.f θ =
          (P.specStalkPointedOver V a v hv).baseChange.y := by
  intro x hx
  obtain ⟨A, hA⟩ := hlim (pointsMap B S hS
    (pullback (P.specStalkPointedOver V a v hv).g P.f)
    (pullback.fst (P.specStalkPointedOver V a v hv).g P.f) x) x rfl
  have hnot := not_isImpurity_of_affineLimitPresentation hpure A hA
  have hass : (P.specStalkDiagram V a v hv _ x rfl).IsRelativeWeakAssassinPoint
      (P.specStalkDiagram V a v hv _ x rfl).xi := hx
  have hmem : (P.specStalkDiagram V a v hv _ x rfl).t ∈
      pointsMap B S hS (P.specStalkDiagram V a v hv _ x rfl).baseChange
        (P.specStalkDiagram V a v hv _ x rfl).toT ''
          closure {(P.specStalkDiagram V a v hv _ x rfl).xi} := by
    by_contra h
    exact hnot ⟨hass, h⟩
  obtain ⟨θ, hθ, hmap⟩ := (P.specStalkDiagram V a v hv _ x rfl).mem_image_closure_xi_iff.1 hmem
  exact ⟨θ, hθ, hmap⟩

/-! ### Stacks 0CW3, clause (2), from the specialization alone -/

/-- **Stacks 0CW3, clause (2), from the specialization step alone.** Let `g : X' ⟶ X` be étale
over `Y` with `X' ⟶ Y` decent and of finite type. If every point of the relative assassin
`Ass_{X/Y}(ℱ)` specializes to a point of the fibre `F = f^{-1}(\{y\})` and the image of
`|X'| → |X|` contains that fibre, then it contains the whole relative assassin.

This is `EtaleOverSource.relativeWeaklyAssociatedPoints_subset_range_of_isAffineLocalAt` with
its two hypotheses — the affine local base and purity above `y` — replaced by the single
consequence of them that the proof uses, namely the specialization that
`AlgebraicGeometry.Space.purityFibreSpecialization` extracts from them. -/
theorem EtaleOverSource.relativeWeaklyAssociatedPoints_subset_range_of_exists_specializes
    {P : PrePureSituation.{u, u} B S hS} (c : EtaleOverSource P)
    (hinto : ∀ x ∈ relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F,
      ∃ θ : points B S hS P.X, x ⤳ θ ∧ pointsMap B S hS P.X P.f θ = P.y)
    (hfibre : pointsMap B S hS P.X P.f ⁻¹' {P.y} ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom)) :
    relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom) := by
  intro x hx
  obtain ⟨θ, hspec, hθ⟩ := hinto x hx
  exact hspec.mem_open
    (isOpen_range_pointsMap_of_isEtale B S hS c.g.hom c.X'.2 P.hX c.isEtale) (hfibre hθ)

/-- **The assassin containment over `Spec 𝒪_{V, v}`.** For an étale morphism `g : X'' ⟶ X_𝒪`
over `Spec 𝒪_{V, v}` whose image on points contains the fibre over the closed point, purity of
`ℱ` above `y` — with the limit presentation of `Spec 𝒪_{V, v}` granted — forces the whole
relative assassin `Ass_{X_𝒪/Spec 𝒪_{V, v}}(ℱ_𝒪)` into that image.

This composes `AlgebraicGeometry.Space.exists_specializes_fibre_of_isPureAbove` with
`EtaleOverSource.relativeWeaklyAssociatedPoints_subset_range_of_exists_specializes`, and it is
the conclusion the dévissage of Stacks 083F takes from Stacks 0CW3, clause (2), over the local
base. Note that no purity of the base change is used, hence neither Stacks 0CW4 nor
Stacks 0CW5 nor `AlgebraicGeometry.Space.PurityStrictlyHenselianReduction`. -/
theorem relativeWeaklyAssociatedPoints_subset_range_specStalkBaseChange
    (P : PrePureSituation.{u, u} B S hS) (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ P.Y)
    (v : points B S hS (yoneda.obj V)) (hv : pointsMap B S hS (yoneda.obj V) a v = P.y)
    (c : EtaleOverSource (P.specStalkPointedOver V a v hv).baseChange)
    (hpure : IsPureAbove P) (hlim : SpecStalkAffineLimitPresentation P V a v hv)
    (hfibre : pointsMap B S hS (P.specStalkPointedOver V a v hv).baseChange.X
          (P.specStalkPointedOver V a v hv).baseChange.f ⁻¹'
        {(P.specStalkPointedOver V a v hv).baseChange.y} ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom)) :
    relativeWeaklyAssociatedPoints B S hS
        (P.specStalkPointedOver V a v hv).baseChange.structureSpaceMorphism
        (P.specStalkPointedOver V a v hv).baseChange.F ⊆
      Set.range (pointsMap B S hS c.X'.1 c.g.hom) :=
  c.relativeWeaklyAssociatedPoints_subset_range_of_exists_specializes
    (exists_specializes_fibre_of_isPureAbove P V a v hv hpure hlim) hfibre

/-! ### The transfer of impurities is not a hypothesis one may carry -/

/-- **A hypothesis transferring impurities from a base change back to the base is the purity of
that base change.** Granted purity of `ℱ` above `y`, the statement "every impurity of the base
change above `y'` whose structure morphism is quasi-finite at `t` yields an impurity of `ℱ`
above `y` whose structure morphism is quasi-finite at `t`" is **equivalent** to purity of the
base change above `y'`.

So that statement cannot be carried as a hypothesis towards the ascent: it is the conclusion.
The forward implication is the reason — purity of the base change makes the transfer vacuous,
because there is nothing to transfer — and it is the same defect as in the composition of
Stacks 0CVV with Morphisms 05LW, whose generalization hypothesis is equivalent to its own
conclusion by `AlgebraicGeometry.mem_nhds_iff_specializes_subset_of_isLocallyConstructible`.
The hypothesis carried by `AlgebraicGeometry.Space.exists_specializes_fibre_of_isPureAbove` is
of a different shape: it quantifies over diagrams without asking them to be impurities, and
asserts a limit presentation of the test scheme rather than the existence of an impurity. -/
theorem isPureAbove_baseChange_iff_forall_exists_isImpurity_isQuasiFiniteAt
    {P : PrePureSituation.{u, u} B S hS} (c : PointedOver P) (hpure : IsPureAbove P) :
    IsPureAbove c.baseChange ↔
      ∀ E : ImpurityDiagram c.baseChange, IsQuasiFiniteAt B S hS E.g E.t → E.IsImpurity →
        ∃ D : ImpurityDiagram P, IsQuasiFiniteAt B S hS D.g D.t ∧ D.IsImpurity := by
  refine ⟨fun h E hqf hE => absurd hE (h E hqf), fun h E hqf hE => ?_⟩
  obtain ⟨D, hqfD, hD⟩ := h E hqf hE
  exact hpure D hqfD hD

end AlgebraicGeometry.Space

end
