module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.PushforwardFinite
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.RelativeWeakAssassin
public import StacksFrontier.AlgebraicGeometry.Divisors.RelativeWeakAssassin.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.BaseChange

/-!
# Purity along a fibre under a closed immersion

Let `i : Z ⟶ X` be a closed immersion, let `f : X ⟶ S` be of finite type and let `ℱ` be a
finite type quasi-coherent module on `Z`. Purity of `ℱ` along the fibre of `i ≫ f` over a point
of `S` is the same as purity of its direct image `i_*ℱ` along the fibre of `f` over that point,
and likewise for universal purity.

The mechanism is that base change carries the closed immersion `i` to a closed immersion between
the two base-changed total spaces, that the relative assassin of a finite direct image is the
image of the relative assassin upstairs, and that a closed embedding over the base neither
creates nor destroys the meeting of the closure of a point with a fibre.

## Main definitions

* `AlgebraicGeometry.prePureSituationComp` and
  `AlgebraicGeometry.prePureSituationPushforward` are the two pre-pure situations being compared.

## Main results

* `AlgebraicGeometry.relativeAssassin_pushforward_eq_image`: the relative assassin of a finite
  direct image is the image of the relative assassin of the module itself.
* `AlgebraicGeometry.disjoint_closure_range_fiberι_comp_iff`: a closed embedding over the base
  does not change whether the closure of a point meets a fibre.
* `AlgebraicGeometry.isPureAlong_iff_pushforward` and
  `AlgebraicGeometry.isUniversallyPureAlong_iff_pushforward` are the two halves of the source.

## Implementation notes

The relative assassin of a finite direct image is obtained from the corresponding statement for
the relative weak assassin, which the two are equal to for a morphism locally of finite type.

The two equivalences are proved from a single pair of transport lemmas, one in each direction,
which produce an impurity diagram over the *same* base datum `(T, g, t', t)` as the given one.
Keeping that datum fixed is what lets both the plain and the universal statement reuse them: the
étale neighbourhood tested by `AlgebraicGeometry.IsPureAlong` is built from exactly those
fields, so it is literally unchanged by the transport. The transported diagram is therefore
returned as an explicit structure literal rather than as an abstract diagram together with
equalities of its fields.

## References

* [Stacks Project, Tag 05K1](https://stacks.math.columbia.edu/tag/05K1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

/-- The relative assassin of a finite direct image is the image of the relative assassin of the
module itself. This is the relative-assassin form of [Stacks, Tag 0CUD]. -/
theorem relativeAssassin_pushforward_eq_image {Z X T : Scheme.{u}} (q : Z ⟶ X) (h : X ⟶ T)
    [IsFinite q] [LocallyOfFiniteType h] [LocallyOfFiniteType (q ≫ h)] (G : Z.Modules)
    [G.IsQuasicoherent] :
    Stacks.Divisors.relativeAssassin h ((Scheme.Modules.pushforward q).obj G) =
      q '' Stacks.Divisors.relativeAssassin (q ≫ h) G := by
  rw [← relativeWeaklyAssociatedPoints_eq_relativeAssassin h,
    relativeWeaklyAssociatedPoints_pushforward_eq_image,
    relativeWeaklyAssociatedPoints_eq_relativeAssassin]

/-- A closed embedding over a base neither creates nor destroys the meeting of the closure of a
point with a fibre: for `q : Z ⟶ X` which is a closed embedding on spaces and `k = q ≫ h`, the
closure of `q y` misses the fibre of `h` over `t` exactly when the closure of `y` misses the
fibre of `k` over `t`. -/
theorem disjoint_closure_range_fiberι_comp_iff {Z X T : Scheme.{u}} (q : Z ⟶ X) (h : X ⟶ T)
    (k : Z ⟶ T) (hq : IsClosedEmbedding q.base) (hcomm : q ≫ h = k) (y : Z) (t : T) :
    Disjoint (closure {q.base y}) (Set.range (h.fiberι t)) ↔
      Disjoint (closure {y}) (Set.range (k.fiberι t)) := by
  have hclosure : closure ({q.base y} : Set X) = q.base '' closure ({y} : Set Z) := by
    rw [← Set.image_singleton]
    exact hq.closure_image_eq {y}
  have hfib : ∀ z : Z, q.base z ∈ Set.range (h.fiberι t) ↔ z ∈ Set.range (k.fiberι t) := fun z ↦ by
    simp only [h.range_fiberι, k.range_fiberι, ← hcomm, Set.mem_preimage, Scheme.Hom.comp_apply]
  rw [Set.disjoint_left, Set.disjoint_left, hclosure]
  constructor
  · exact fun hdis z hz hzf ↦ hdis ⟨z, hz, rfl⟩ ((hfib z).2 hzf)
  · rintro hdis _ ⟨z, hz, rfl⟩ hxf
    exact hdis hz ((hfib z).1 hxf)

section ClosedImmersion

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ S)
  [LocallyOfFiniteType f] [QuasiCompact f] (F : Z.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
  (s : S)

/-- The pre-pure situation of a finite type quasi-coherent module on the source of a closed
immersion, taken over the composite structure morphism. -/
abbrev prePureSituationComp : PrePureSituation.{u} where
  S := S
  X := Z
  f := i ≫ f
  F := F
  s := s

/-- The pre-pure situation of the direct image of a finite type quasi-coherent module along a
closed immersion. -/
abbrev prePureSituationPushforward : PrePureSituation.{u} where
  S := S
  X := X
  f := f
  F := (Scheme.Modules.pushforward i).obj F
  isFiniteType := (isFiniteType_iff_pushforward_isFiniteType i F).mp inferInstance
  s := s

/-- An impurity of the direct image gives an impurity of the module itself, over the same base
datum: pull the closed immersion back along the test family and take a point of the relative
assassin upstairs lying above the chosen one. -/
private theorem exists_isImpurity_prePureSituationComp
    (D : ImpurityDiagram (prePureSituationPushforward i f F s))
    (hD : IsImpurity _ D) :
    ∃ (X_T : Scheme.{u}) (toX : X_T ⟶ Z) (toT : X_T ⟶ D.T)
      (hpb : IsPullback toX toT (i ≫ f) D.g) (xi : X_T) (hxi : toT.base xi = D.t'),
      IsImpurity (prePureSituationComp i f F s)
        { T := D.T, g := D.g, t' := D.t', t := D.t, specializes := D.specializes
          mapsToChosenPoint := D.mapsToChosenPoint
          X_T := X_T, toX := toX, toT := toT, isPullback := hpb
          xi := xi, xi_liesOver := hxi } := by
  have : LocallyOfFiniteType D.toT := MorphismProperty.of_isPullback D.isPullback inferInstance
  let q : pullback i D.toX ⟶ D.X_T := pullback.snd i D.toX
  let z : pullback i D.toX ⟶ Z := pullback.fst i D.toX
  have hsmall : IsPullback z q i D.toX := IsPullback.of_hasPullback i D.toX
  have : IsClosedImmersion q := MorphismProperty.of_isPullback hsmall ‹IsClosedImmersion i›
  let d : BaseChangeDiagram :=
    { X' := pullback i D.toX, X := Z, S' := D.X_T, S := X
      g' := z, f' := q, f := i, g := D.toX, isPullback := hsmall, F := F }
  have : d.F.IsQuasicoherent := d.isQuasicoherent
  have hAss : D.xi ∈ Stacks.Divisors.relativeAssassin D.toT
      ((Scheme.Modules.pushforward q).obj d.pulledBack) := by
    rw [← relativeAssassin_eq_of_moduleIso D.toT (pullbackPushforwardFiberIso d)]
    exact hD.1
  rw [relativeAssassin_pushforward_eq_image q D.toT d.pulledBack] at hAss
  obtain ⟨y, hyAss, hxy⟩ := hAss
  have hxi : (q ≫ D.toT).base y = D.t' := by
    simpa only [Scheme.Hom.comp_apply, hxy] using D.xi_liesOver
  refine ⟨pullback i D.toX, z, q ≫ D.toT, hsmall.paste_vert D.isPullback, y, hxi, hyAss, ?_⟩
  refine Set.disjoint_iff_inter_eq_empty.mp
    ((disjoint_closure_range_fiberι_comp_iff q D.toT (q ≫ D.toT) q.isClosedEmbedding rfl y
      D.t).mp ?_)
  simpa only [hxy] using Set.disjoint_iff_inter_eq_empty.mpr hD.2

/-- An impurity of a finite type quasi-coherent module on the source of a closed immersion gives
an impurity of its direct image, over the same base datum: push the chosen point forward along
the base change of the closed immersion. -/
private theorem exists_isImpurity_prePureSituationPushforward
    (D : ImpurityDiagram (prePureSituationComp i f F s)) (hD : IsImpurity _ D) :
    ∃ (X_T : Scheme.{u}) (toX : X_T ⟶ X) (toT : X_T ⟶ D.T)
      (hpb : IsPullback toX toT f D.g) (xi : X_T) (hxi : toT.base xi = D.t'),
      IsImpurity (prePureSituationPushforward i f F s)
        { T := D.T, g := D.g, t' := D.t', t := D.t, specializes := D.specializes
          mapsToChosenPoint := D.mapsToChosenPoint
          X_T := X_T, toX := toX, toT := toT, isPullback := hpb
          xi := xi, xi_liesOver := hxi } := by
  have : LocallyOfFiniteType D.toT := MorphismProperty.of_isPullback D.isPullback inferInstance
  let p : pullback f D.g ⟶ X := pullback.fst f D.g
  let r : pullback f D.g ⟶ D.T := pullback.snd f D.g
  have hcompat : (D.toX ≫ i) ≫ f = D.toT ≫ D.g := by
    simpa only [Category.assoc] using D.isPullback.w
  let q : D.X_T ⟶ pullback f D.g := pullback.lift (D.toX ≫ i) D.toT hcompat
  have hqsnd : q ≫ r = D.toT := pullback.lift_snd (D.toX ≫ i) D.toT hcompat
  have houter : IsPullback D.toX (q ≫ r) (i ≫ f) D.g := hqsnd ▸ D.isPullback
  have hsmall : IsPullback D.toX q i p :=
    (IsPullback.paste_vert_iff (IsPullback.of_hasPullback f D.g)
      (pullback.lift_fst (D.toX ≫ i) D.toT hcompat).symm).mp houter
  have : IsClosedImmersion q := MorphismProperty.of_isPullback hsmall ‹IsClosedImmersion i›
  let d : BaseChangeDiagram :=
    { X' := D.X_T, X := Z, S' := pullback f D.g, S := X
      g' := D.toX, f' := q, f := i, g := p, isPullback := hsmall, F := F }
  have : d.F.IsQuasicoherent := d.isQuasicoherent
  have hxi : r.base (q.base D.xi) = D.t' := by
    refine Eq.trans ?_ D.xi_liesOver
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun m : D.X_T ⟶ D.T ↦ m.base D.xi) hqsnd
  have hAssAmbient : q.base D.xi ∈ Stacks.Divisors.relativeAssassin r
      ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pushforward i).obj F)) := by
    rw [relativeAssassin_eq_of_moduleIso r (pullbackPushforwardFiberIso d),
      relativeAssassin_pushforward_eq_image q r d.pulledBack]
    exact ⟨D.xi, hqsnd ▸ hD.1, rfl⟩
  refine ⟨pullback f D.g, p, r, IsPullback.of_hasPullback f D.g, q.base D.xi, hxi,
    hAssAmbient, ?_⟩
  exact Set.disjoint_iff_inter_eq_empty.mp
    ((disjoint_closure_range_fiberι_comp_iff q r D.toT q.isClosedEmbedding hqsnd D.xi D.t).mpr
      (Set.disjoint_iff_inter_eq_empty.mpr hD.2))

/-- **Stacks Project, Tag 05K1.** Purity along a fibre is unchanged by pushing a finite type
quasi-coherent module forward along a closed immersion. -/
@[stacks 05K1 "purity along the fibre"]
theorem isPureAlong_iff_pushforward :
    IsPureAlong (prePureSituationComp i f F s) ↔
      IsPureAlong (prePureSituationPushforward i f F s) := by
  constructor
  · intro hP D hEt hElem hImp
    obtain ⟨X_T, toX, toT, hpb, xi, hxi, hE⟩ :=
      exists_isImpurity_prePureSituationComp i f F s D hImp
    exact hP
      { T := D.T, g := D.g, t' := D.t', t := D.t,
        specializes := D.specializes, mapsToChosenPoint := D.mapsToChosenPoint,
        X_T := X_T, toX := toX, toT := toT, isPullback := hpb,
        xi := xi, xi_liesOver := hxi } hEt hElem hE
  · intro hQ D hEt hElem hImp
    obtain ⟨X_T, toX, toT, hpb, xi, hxi, hE⟩ :=
      exists_isImpurity_prePureSituationPushforward i f F s D hImp
    exact hQ
      { T := D.T, g := D.g, t' := D.t', t := D.t,
        specializes := D.specializes, mapsToChosenPoint := D.mapsToChosenPoint,
        X_T := X_T, toX := toX, toT := toT, isPullback := hpb,
        xi := xi, xi_liesOver := hxi } hEt hElem hE

/-- **Stacks Project, Tag 05K1.** Universal purity along a fibre is unchanged by pushing a finite
type quasi-coherent module forward along a closed immersion. -/
@[stacks 05K1 "universal purity along the fibre"]
theorem isUniversallyPureAlong_iff_pushforward :
    IsUniversallyPureAlong (prePureSituationComp i f F s) ↔
      IsUniversallyPureAlong (prePureSituationPushforward i f F s) := by
  refine ⟨fun hP D hImp ↦ ?_, fun hQ D hImp ↦ ?_⟩
  · obtain ⟨_, _, _, _, _, _, hE⟩ := exists_isImpurity_prePureSituationComp i f F s D hImp
    exact hP _ hE
  · obtain ⟨_, _, _, _, _, _, hE⟩ := exists_isImpurity_prePureSituationPushforward i f F s D hImp
    exact hQ _ hE

end ClosedImmersion

end AlgebraicGeometry

end
