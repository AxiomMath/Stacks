module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreFiniteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal

/-!
# Generic finiteness for a quasi-separated target

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is quasi-separated
and locally of finite type, let `Y` be a quasi-separated algebraic space and let `y` be a point
of `|Y|` of codimension zero, that is, one whose local ring has dimension zero. Writing
`Spec(k) ⟶ Y` for a field-valued representative of `y` and `X_k = X ×_Y Spec(k)` for the
corresponding field fibre, **Stacks 0AD0** asserts the equivalence of

1. the set-theoretic fibre `f^{-1}({y}) ⊂ |X|` is finite,
2. the point set `|X_k|` is finite,
3. there are open subspaces `X' ⊂ X` and `Y' ⊂ Y` with `f(X') ⊂ Y'`, `y ∈ |Y'|` and
   `f^{-1}({y}) ⊂ |X'|` such that `f|_{X'} : X' ⟶ Y'` is finite.

For the equivalence of (1) and (2), a quasi-separated algebraic space is decent and a
quasi-separated morphism is a decent morphism, so the source is decent as well, and the
equivalence is then the comparison of conditions (1) and (4) of Stacks 0ACK for decent source
and target. For the implications out of (3), a finite morphism of algebraic spaces has finite
fibres by Stacks 0A4X, and an open subspace injects on points, so a fibre contained in the open
subspace is identified with a fibre of the restriction. For the converse, the fibre is covered
by a quasi-compact open subspace of `X`, over which condition (3) of Stacks 0ACZ applies.

## Main results

* `AlgebraicGeometry.Space.finite_setFibre_iff_finite_fieldFibre_of_isAbsolutelyQuasiSeparated`:
  **Stacks 0AD0**, the equivalence of conditions (1) and (2).
* `AlgebraicGeometry.Space.finite_setFibre_of_isFinite_openRestriction`: **Stacks 0AD0**,
  condition (3) implies condition (1). This needs no hypothesis on `f`, on `Y` or on `y`.
* `AlgebraicGeometry.Space.finite_fieldFibre_of_isFinite_openRestriction`: **Stacks 0AD0**,
  condition (3) implies condition (2). The source omits the proof of this implication.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isFinite_openRestriction_of_finite_setFibre`:
  **Stacks 0AD0**, conditions (1) and (2) imply condition (3).

## Implementation notes

The implication from (1) and (2) to (3) rests on condition (3) of Stacks 0ACZ,
`AlgebraicGeometry.Space.exists_isOpenSubspace_isFinite_pullback_snd_of_finite_fieldFiber`.

The codimension-zero hypothesis on `y` is not used for the equivalence of conditions (1) and
(2): that is Stacks 0ACK, whose statement places no condition on the point of the target. Only
the implication to condition (3) needs it.

The hypotheses are exactly the printed ones, and in particular `f` is only assumed *locally* of
finite type, not of finite type. The comparison of conditions (1) and (4) of Stacks 0ACK,
`AlgebraicGeometry.Space.finite_univ_points_fieldFibre_of_finite_setFibre_of_isDecent`, asks
only for local finite type, so no quasi-compactness of `f` enters. This is why the equivalence
of (1) and (2) is not an instance of
`AlgebraicGeometry.Space.finite_fieldFiber_iff_finite_setFiber_of_decent`, which is Stacks 0ACZ
and assumes `f` of finite type.

Decency of the target is read off quasi-separatedness by
`AlgebraicGeometry.Space.isDecentSpace_of_isAbsolutelyQuasiSeparated`, which is the chain
`(η) ⇒ (ζ) ⇒ (ε) ⇒ (δ) ⇒ (γ)` of Stacks 03JX. Decency of the source is not a hypothesis of the
tag and is obtained from quasi-separatedness of `f` through Stacks 03M5 and Stacks 0ABY, which
is how the source obtains it too.

Condition (3) is rendered as the data of a subfunctor `U` of `X` and a subfunctor `V` of `Y`,
both open subspaces, together with a morphism `g : U ⟶ V` whose square with the two inclusions
and `f` commutes — which says at once that `f` carries `U` into `V` and that `g` is the
restriction of `f` — plus the two conditions on points and finiteness of `g`. The implications
out of (3) take these as explicit data; the converse concludes their existence.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03M5](https://stacks.math.columbia.edu/tag/03M5)
* [Stacks Project, Tag 0ABY](https://stacks.math.columbia.edu/tag/0ABY)
* [Stacks Project, Tag 0ACK](https://stacks.math.columbia.edu/tag/0ACK)
* [Stacks Project, Tag 0ACZ](https://stacks.math.columbia.edu/tag/0ACZ)
* [Stacks Project, Tag 0AD0](https://stacks.math.columbia.edu/tag/0AD0)
* [Stacks Project, Tag 0A4X](https://stacks.math.columbia.edu/tag/0A4X)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_GenericallyFiniteQuasiSeparated :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site over `S`, at a single cospan. -/
local instance (priority := high) hasPullback_presheaf_GenericallyFiniteQuasiSeparated
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- A quasi-separated morphism of algebraic spaces over `S` out of an algebraic space whose
target is a decent algebraic space has a decent source.

This is the composite of the implications "quasi-separated implies very reasonable implies
reasonable implies decent" of Stacks 03M5 with "a decent morphism with decent target has decent
source", Stacks 0ABY. -/
theorem isDecentSpace_source_of_isQuasiSeparated (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hqs : IsQuasiSeparated B S hS f)
    (hYdec : IsDecentSpace B S hS Y) :
    IsDecentSpace B S hS X :=
  isDecentSpace_of_isDecent B S hS hX hY f hYdec
    (isDecent_of_isReasonable B S hS hX hY f
      (isReasonable_of_isVeryReasonable B S hS hX hY
        (isVeryReasonable_of_isQuasiSeparated B S hS hX hY hqs)))

/-- **Stacks 0AD0, the equivalence of conditions (1) and (2).** Let `f : X ⟶ Y` be a
quasi-separated morphism of algebraic spaces over `S` which is locally of finite type, let `Y`
be a quasi-separated algebraic space, let `y` be a point of `|Y|` of codimension zero and let
`p` be a field-valued representative of `y`, with field of definition `k`. Then the
set-theoretic fibre `f^{-1}({y}) ⊂ |X|` is finite exactly when the point set of the field
fibre `X_k = X ×_Y Spec(k)` is finite.

Quasi-separatedness of `Y` makes `Y` decent (Stacks 03JX) and quasi-separatedness of `f` then
makes `X` decent (Stacks 03M5 and Stacks 0ABY), so both implications are instances of the
comparison of conditions (1) and (4) of Stacks 0ACK for decent source and target: condition (4)
implies condition (1) because the comparison map `|X_k| → |X|` has image the set-theoretic
fibre, and the converse is
`AlgebraicGeometry.Space.finite_univ_points_fieldFibre_of_finite_setFibre_of_isDecent` once the
fibre is nonempty, an empty fibre leaving `|X_k|` without points by the same surjectivity.

The codimension-zero hypothesis on `y` is the source's; this implication does not use it. -/
@[stacks 0AD0 "the equivalence of conditions (1) and (2)"]
theorem finite_setFibre_iff_finite_fieldFibre_of_isAbsolutelyQuasiSeparated
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hqs : IsQuasiSeparated B S hS f) (hft : IsLocallyOfFiniteType B S hS f)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (y : points B S hS Y) (_hy : localRingDimension B S hS y = 0)
    (p : FieldValuedPoint B S hS Y) (hp : p.class B S hS Y = y) :
    {x : points B S hS X | pointsMap B S hS X f x = y}.Finite ↔
      (Set.univ : Set (points B S hS (fieldFibre B S hS f p))).Finite := by
  subst hp
  have hYdec : IsDecentSpace B S hS Y :=
    isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS Y hY hYqs
  have hXdec : IsDecentSpace B S hS X :=
    isDecentSpace_source_of_isQuasiSeparated B S hS hX hY f hqs hYdec
  exact ⟨fun hset => finite_univ_points_fieldFibre_of_finite_setFibre_of_isDecent B S hS hX hY f
    p hft hXdec hYdec hset, finite_setFibre_of_finite_fieldFibre B S hS hX hY f p⟩

/-- **Stacks 0AD0, condition (3) implies condition (1).** Let `f : X ⟶ Y` be a morphism of
presheaves on the big fppf site of `S`, let `y` be a point of `|Y|`, let `U ⊂ X` and `V ⊂ Y`
be open subspaces and let `g : U ⟶ V` be a morphism whose square with the two inclusions and
`f` commutes, so that `f` carries `U` into `V` and `g` restricts `f`. If `y` lies in `|V|`, if
the set-theoretic fibre `f^{-1}({y}) ⊂ |X|` is contained in `|U|` and if `g` is finite, then
`f^{-1}({y})` is finite.

A finite morphism of algebraic spaces is universally closed with discrete fibres (Stacks 0A4X),
so each of its set-theoretic fibres is finite. The inclusion `|V| → |Y|` is injective because
the inclusion of an open subspace is a monomorphism, so the point `v` of `|V|` above `y` is the
only one, and a point of `|U|` lands on `y` under `f` exactly when it lands on `v` under `g`.
The fibre `f^{-1}({y})` is therefore the image under `|U| → |X|` of a fibre of `g`.

No hypothesis on `f`, on `Y` or on `y` is needed: the quasi-separatedness, finite type and
codimension-zero hypotheses of the tag are used only for the other implications. -/
@[stacks 0AD0 "condition (3) implies condition (1)"]
theorem finite_setFibre_of_isFinite_openRestriction (f : X ⟶ Y) (y : points B S hS Y)
    (U : Subfunctor X) (V : Subfunctor Y) (g : U.toFunctor ⟶ V.toFunctor)
    (hU : IsOpenSubspace B S hS U) (hV : IsOpenSubspace B S hS V)
    (hcomm : g ≫ V.ι = U.ι ≫ f)
    (hy : y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι))
    (hfib : {x : points B S hS X | pointsMap B S hS X f x = y} ⊆
      Set.range (pointsMap B S hS U.toFunctor U.ι))
    (hg : IsFinite B S hS g) :
    {x : points B S hS X | pointsMap B S hS X f x = y}.Finite := by
  obtain ⟨v, hv⟩ := hy
  obtain ⟨huc, -, -, hdisc⟩ :=
    universallyClosed_isSeparated_isLocallyOfFiniteType_and_discreteFibres_of_isFinite
      B S hS hU.1 hV.1 g hg
  obtain ⟨p, hp⟩ := Quot.exists_rep v
  have hpc : p.class B S hS V.toFunctor = v := hp
  have hgfibre : (setFibre B S hS g p).Finite :=
    finite_setFibre_of_universallyClosed_of_discrete_fibre B S hS hU.1 hV.1 g huc p (hdisc p)
  refine Set.Finite.subset (hgfibre.image (pointsMap B S hS U.toFunctor U.ι)) ?_
  intro x hx
  obtain ⟨u, hu⟩ := hfib hx
  refine ⟨u, ?_, hu⟩
  have hstep : pointsMap B S hS V.toFunctor V.ι (pointsMap B S hS U.toFunctor g u) = y := by
    rw [← pointsMap_comp_apply B S hS g V.ι u, hcomm, pointsMap_comp_apply B S hS U.ι f u, hu]
    exact hx
  have hmem : pointsMap B S hS U.toFunctor g u = p.class B S hS V.toFunctor := by
    rw [hpc]
    exact pointsMap_injective_of_mono B S hS V.ι (hstep.trans hv.symm)
  exact hmem

/-- **Stacks 0AD0, condition (3) implies condition (2).** In the situation of condition (3) of
the tag, with `f` in addition quasi-separated and locally of finite type and `Y` a
quasi-separated algebraic space, the point set of the field fibre `X_k` over a field-valued
representative `p` of `y` is finite.

The source omits the proof of this implication. It is obtained here by composing
`AlgebraicGeometry.Space.finite_setFibre_of_isFinite_openRestriction` with the equivalence of
conditions (1) and (2). -/
@[stacks 0AD0 "condition (3) implies condition (2)"]
theorem finite_fieldFibre_of_isFinite_openRestriction (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hqs : IsQuasiSeparated B S hS f) (hft : IsLocallyOfFiniteType B S hS f)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (y : points B S hS Y) (hy0 : localRingDimension B S hS y = 0)
    (p : FieldValuedPoint B S hS Y) (hp : p.class B S hS Y = y)
    (U : Subfunctor X) (V : Subfunctor Y) (g : U.toFunctor ⟶ V.toFunctor)
    (hU : IsOpenSubspace B S hS U) (hV : IsOpenSubspace B S hS V)
    (hcomm : g ≫ V.ι = U.ι ≫ f)
    (hy : y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι))
    (hfib : {x : points B S hS X | pointsMap B S hS X f x = y} ⊆
      Set.range (pointsMap B S hS U.toFunctor U.ι))
    (hg : IsFinite B S hS g) :
    (Set.univ : Set (points B S hS (fieldFibre B S hS f p))).Finite :=
  (finite_setFibre_iff_finite_fieldFibre_of_isAbsolutelyQuasiSeparated B S hS hX hY f hqs hft
      hYqs y hy0 p hp).mp
    (finite_setFibre_of_isFinite_openRestriction B S hS f y U V g hU hV hcomm hy hfib hg)


/-! ### Existence of the finite restriction: Stacks 0AD0, conditions (1) and (2) imply (3) -/

section FiniteRestriction

attribute [local instance] CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange

private theorem pointsMap_yoneda_eq_class
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : FieldValuedPoint B S hS Y)
    (q : FieldValuedPoint B S hS
      (yoneda.obj (p.siteObject B S hS Y))) :
    pointsMap B S hS (yoneda.obj (p.siteObject B S hS Y))
      (yonedaEquiv.symm p.value) q.class = p.class := by
  let α := yonedaEquiv.symm p.value
  let r := FieldValuedPoint.map B S hS _ α q
  have hpval : α.app (Opposite.op (p.siteObject B S hS Y))
      (𝟙 (p.siteObject B S hS Y)) = p.value :=
    yonedaEquiv.apply_symm_apply p.value
  have hdom : FieldValuedPoint.Dominates B S hS Y r p := by
    refine ⟨q.value, ?_⟩
    show Y.map q.value.op p.value =
      (FieldValuedPoint.map B S hS _ α q).value
    rw [← hpval]
    show Y.map q.value.op
        (α.app (Opposite.op (p.siteObject B S hS Y)) (𝟙 (p.siteObject B S hS Y))) =
      α.app (Opposite.op
        (q.siteObject B S hS (yoneda.obj (p.siteObject B S hS Y))))
        ((yoneda.obj (p.siteObject B S hS Y)).map q.value.op
          (𝟙 (p.siteObject B S hS Y)))
    exact (congrArg (fun k => k (𝟙 (p.siteObject B S hS Y))) (α.naturality q.value.op)).symm
  have hc : FieldValuedPoint.HasCommonExtension B S hS Y r p :=
    ⟨r, FieldValuedPoint.dominates_refl B S hS Y r, hdom⟩
  simpa [r, α, FieldValuedPoint.siteObject] using
    FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS Y hc


private theorem fieldFiber_nonempty_implies_setFiber_nonempty
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) :
    (Set.univ : Set (points B S hS
      (pullback f (yonedaEquiv.symm p.value)))).Nonempty →
    (setFibre B S hS f p).Nonempty := by
  intro h
  obtain ⟨w⟩ := h
  obtain ⟨r, rfl⟩ := Quot.exists_rep w
  let α := yonedaEquiv.symm p.value
  let q := FieldValuedPoint.map B S hS _ (pullback.snd f α) r
  let x := pointsMap B S hS (pullback f α) (pullback.fst f α) r.class
  have hq : pointsMap B S hS (yoneda.obj (p.siteObject B S hS Y)) α q.class = p.class :=
    pointsMap_yoneda_eq_class B S hS p q
  have hcomp : pointsMap B S hS X f x =
      pointsMap B S hS (yoneda.obj (p.siteObject B S hS Y)) α
        (pointsMap B S hS (pullback f α) (pullback.snd f α) r.class) := by
    have hh := congrArg (fun k => pointsMap B S hS (pullback f α) k r.class)
      pullback.condition
    simpa [x, pointsMap_comp,
      FieldValuedPoint.siteObject] using hh
  exact ⟨x, by simpa [setFibre] using hcomp.trans hq⟩


/-- A finite set of points of an algebraic space over `S` is covered by a quasi-compact open
subspace: the point space has a basis of open quasi-compact neighbourhoods, and the union of
one such neighbourhood of each of the finitely many points is open and compact, hence of the
form `|U|` for a quasi-compact open subspace `U`. -/
public theorem exists_quasiCompact_openSubspace_covering_finite
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (A : Set (points B S hS X)) (hA : A.Finite) :
    ∃ U : Subfunctor X,
      IsOpenSubspace B S hS U ∧
      IsQuasiCompactSpace B S hS U.toFunctor ∧
      A ⊆ Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  let N : ∀ x : points B S hS X, Set (points B S hS X) :=
    fun x => Classical.choose
      ((hasBasis_nhds_isOpen_isCompact B S hS X hX x).mem_iff.mp
        (Filter.univ_mem : (Set.univ : Set (points B S hS X)) ∈ nhds x))
  have hN : ∀ x, IsOpen (N x) ∧ IsCompact (N x) ∧ x ∈ N x := by
    intro x; exact (Classical.choose_spec
      ((hasBasis_nhds_isOpen_isCompact B S hS X hX x).mem_iff.mp
        (Filter.univ_mem : (Set.univ : Set (points B S hS X)) ∈ nhds x))).1
  let W : Set (points B S hS X) := ⋃ x ∈ A, N x
  have hWopen : IsOpen W := isOpen_iUnion fun x => isOpen_iUnion fun _ => (hN x).1
  have hWcompact : IsCompact W := hA.isCompact_biUnion fun x hx => (hN x).2.1
  have hAinW : A ⊆ W := by
    intro x hx; exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, (hN x).2.2⟩⟩
  let e := openSubspacesOrderIso B S hS X hX
  let Z := e.symm ⟨W, hWopen⟩
  let U : Subfunctor X := Z.1
  have hU : IsOpenSubspace B S hS U := Z.2
  have hUrange : Set.range (pointsMap B S hS U.toFunctor U.ι) = W := by
    have hinv : e ⟨U, hU⟩ = ⟨W, hWopen⟩ := e.apply_symm_apply ⟨W, hWopen⟩
    calc
      Set.range (pointsMap B S hS U.toFunctor U.ι) =
          ((e ⟨U, hU⟩ : TopologicalSpace.Opens (points B S hS X)) : Set _) :=
        (openSubspacesOrderIso_apply B S hS X hX ⟨U, hU⟩).symm
      _ = W := congrArg (fun O : TopologicalSpace.Opens (points B S hS X) => O.carrier) hinv
  have hUqc : IsQuasiCompactSpace B S hS U.toFunctor := by
    let : TopologicalSpace (points B S hS U.toFunctor) :=
      pointTopology B S hS U.toFunctor
    have hImm : IsImmersion B S hS U.ι := by
      have hopen : IsOpenImmersion B S hS U.ι := hU.2
      change (MorphismProperty.presheaf
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) U.ι at hopen
      show (MorphismProperty.presheaf
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) U.ι
      refine ⟨hopen.1, ?_⟩
      intro A' B' g fst snd hpull
      have ho := hopen.2 g fst snd hpull
      change AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map snd) at ho
      let : AlgebraicGeometry.IsOpenImmersion
          ((BigFppfOver.toScheme B S hS).map snd) := ho
      show AlgebraicGeometry.IsImmersion
        ((BigFppfOver.toScheme B S hS).map snd)
      exact inferInstance
    have hEmb : @Topology.IsEmbedding _ _
        (pointTopology B S hS U.toFunctor)
        (pointTopology B S hS X)
        (pointsMap B S hS U.toFunctor U.ι) :=
      isEmbedding_pointsMap_of_isImmersion B S hS hX U.ι hImm
    have himage : IsCompact
        (pointsMap B S hS U.toFunctor U.ι ''
          (Set.univ : Set (points B S hS U.toFunctor))) := by
      rw [Set.image_univ, hUrange]; exact hWcompact
    have hcomp : @CompactSpace (points B S hS U.toFunctor)
        (pointTopology B S hS U.toFunctor) :=
      ⟨hEmb.isCompact_iff.mpr himage⟩
    exact (isQuasiCompactSpace_iff_compactSpace_points B S hS _ hU.1).2 hcomp
  refine ⟨U, hU, hUqc, ?_⟩
  intro x hx; rw [hUrange]; exact hAinW hx

/-- An open immersion of algebraic spaces over `S` is locally of finite type: an open
immersion of schemes is locally of finite type, so the relative property ascends, and being
locally of finite type is the every-étale-chart condition by Stacks 03MJ. -/
public theorem locallyOfFiniteType_of_openImmersion
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G)
    (i : F ⟶ G) (hi : IsOpenImmersion B S hS i) :
    IsLocallyOfFiniteType B S hS i := by
  let T := BigFppfOver.toScheme B S hS
  have hle :
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) T) ≤
      (MorphismProperty.inverseImage
        (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) T) := by
    intro A' B' f hf
    change AlgebraicGeometry.IsOpenImmersion (T.map f) at hf
    let : AlgebraicGeometry.IsOpenImmersion (T.map f) := hf
    show LocallyOfFiniteType (T.map f)
    infer_instance
  have hi' :
      ((MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) T).relative
        yoneda) i := hi
  have hrel := MorphismProperty.relative_monotone (F := yoneda) hle i hi'
  let : MorphismProperty.IsLocalAtTarget
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage :=
    Stacks.Descent.locallyOfFiniteType_isLocalAtTarget_fpqc
  let : MorphismProperty.IsLocalAtTarget
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact (holdsOnEveryEtaleChart_iff_relative B S hS
    (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
    hF hG i hrel.1).2 hrel

private theorem isFinite_of_source_iso
    {A A' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : A ≅ A') (f : A ⟶ Y)
    (hf : IsFinite B S hS f) :
    IsFinite B S hS (e.inv ≫ f) := by
  intro T hT ξ
  obtain ⟨P, p, i, hP, hp, hpb⟩ := hf T hT ξ
  refine ⟨P, p, i ≫ e.hom, hP, hp, ?_⟩
  exact hpb.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)


/-- **Stacks 0AD0, conditions (1) and (2) imply condition (3).** Let `f : X ⟶ Y` be a
quasi-separated morphism of algebraic spaces over `S` which is locally of finite type, let `Y`
be a quasi-separated algebraic space and let `y` be a point of `|Y|` whose local ring has
dimension zero. If the set-theoretic fibre `f^{-1}({y}) ⊂ |X|` is finite then there are open
subspaces `U ⊂ X` and `V ⊂ Y` and a morphism `g : U ⟶ V` restricting `f`, with `y ∈ |V|`,
with `f^{-1}({y}) ⊂ |U|`, and with `g` finite.

A finite set of points of an algebraic space is covered by a quasi-compact open subspace, so
`X` may be shrunk to a quasi-compact open `U₀` containing the fibre. Quasi-separatedness of
`Y` makes the restriction `U₀ ⟶ Y` quasi-compact (Stacks 073B) and hence of finite type, and
its fibre over `y` is still finite, so the field fibre is finite as well. Condition (3) of
Stacks 0ACZ then supplies an open `V ⊂ Y` containing `y` over which `U₀` becomes finite, and
the base change `U₀ ×_Y V` is an open subspace of `X` because `U₀` is. -/
@[stacks 0AD0 "conditions (1) and (2) imply condition (3)"]
theorem exists_isOpenSubspace_isFinite_openRestriction_of_finite_setFibre
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hqs : IsQuasiSeparated B S hS f)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (y : points B S hS Y)
    (hy : localRingDimension B S hS y = 0) :
    Set.Finite {x : points B S hS X |
      pointsMap B S hS X f x = y} →
      ∃ (U : Subfunctor X) (V : Subfunctor Y)
        (g : U.toFunctor ⟶ V.toFunctor),
        IsOpenSubspace B S hS U ∧
        IsOpenSubspace B S hS V ∧
        g ≫ V.ι = U.ι ≫ f ∧
        y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) ∧
        {x : points B S hS X |
          pointsMap B S hS X f x = y} ⊆
          Set.range (pointsMap B S hS U.toFunctor U.ι) ∧
        IsFinite B S hS g := by
  classical
  intro hfinite
  obtain ⟨U₀, hU₀, hU₀qc, hcover₀⟩ :=
    exists_quasiCompact_openSubspace_covering_finite B S hS hX
      {x : points B S hS X |
        pointsMap B S hS X f x = y} hfinite
  let f₀ := U₀.ι ≫ f
  let hU₀alg := hU₀.1
  have hU₀lft : IsLocallyOfFiniteType B S hS U₀.ι :=
    locallyOfFiniteType_of_openImmersion B S hS hU₀alg hX U₀.ι hU₀.2
  have hU₀qs : IsQuasiSeparated B S hS U₀.ι :=
    isQuasiSeparated_of_mono B S hS U₀.ι inferInstance
  have hf₀qs : IsQuasiSeparated B S hS f₀ :=
    isQuasiSeparated_comp
      B S hS hU₀alg hX U₀.ι f hU₀qs hqs
  have hf₀lft : IsLocallyOfFiniteType B S hS f₀ :=
    isLocallyOfFiniteType_comp B S hS hU₀alg hX hY U₀.ι f hU₀lft hft
  have hf₀qc : IsQuasiCompact B S hS f₀ :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal hY hYqs hU₀qc f₀
  have hf₀type : IsFiniteType B S hS f₀ := ⟨hf₀lft, hf₀qc⟩
  obtain ⟨p, hp⟩ := Quot.exists_rep y
  let F₀ : Set (points B S hS U₀.toFunctor) :=
    {x | pointsMap B S hS U₀.toFunctor f₀ x = y}
  let F : Set (points B S hS X) :=
    {x | pointsMap B S hS X f x = y}
  have hf₀pt : ∀ x, pointsMap B S hS U₀.toFunctor f₀ x =
      pointsMap B S hS X f (pointsMap B S hS U₀.toFunctor U₀.ι x) := fun x =>
    congrFun (pointsMap_comp B S hS _ U₀.ι f) x
  have hfinite₀ : F₀.Finite :=
    hfinite.preimage (pointsMap_injective_of_mono B S hS U₀.ι).injOn |>.subset fun x hx => by
      simpa only [F₀, F, Set.mem_ofPred_eq, Set.mem_preimage, hf₀pt] using hx
  have hfield₀ : Set.Finite (Set.univ : Set (points B S hS
      (pullback f₀ (yonedaEquiv.symm p.value)))) :=
    (finite_setFibre_iff_finite_fieldFibre_of_isAbsolutelyQuasiSeparated B S hS hU₀alg hY f₀
      hf₀qs hf₀lft hYqs y hy p hp).mp hfinite₀
  obtain ⟨V, hV, hyV, hVfinite⟩ :=
    (exists_isOpenSubspace_isFinite_pullback_snd_of_finite_fieldFiber B S hS hU₀alg hY f₀
      hf₀qs hf₀type y p hp hy) hfield₀
  let P := pullback f₀ V.ι
  let hP : IsAlgebraicSpace B S hS P :=
    isAlgebraicSpace_pullback B S hS f₀ V.ι hU₀alg hV.1 hY
  let p₀ := pullback.fst f₀ V.ι
  let q₀ := pullback.snd f₀ V.ι
  let e := p₀ ≫ U₀.ι
  let Popen : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
  let : Popen.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange Popen
  let O := Popen.presheaf
  have hp₀open : IsOpenImmersion B S hS p₀ := by
    show O p₀
    exact MorphismProperty.pullback_fst f₀ V.ι hV.2
  have heopen : IsOpenImmersion B S hS e := by
    show O e
    exact MorphismProperty.comp_mem O p₀ U₀.ι hp₀open hU₀.2
  have : Mono e := by
    have : Mono V.ι := inferInstance
    have : Mono p₀ := by
      dsimp [p₀]
      infer_instance
    exact mono_comp p₀ U₀.ι
  let U : Subfunctor X := Subfunctor.range e
  let r := Subfunctor.toRange e
  let eIso : P ≅ U.toFunctor := asIso r
  have hUalg : IsAlgebraicSpace B S hS U.toFunctor :=
    algebraicSpace_of_iso B S hS eIso hP
  have hincl : eIso.inv ≫ e = U.ι := by
    calc
      eIso.inv ≫ e = eIso.inv ≫ (r ≫ U.ι) := by rw [Subfunctor.toRange_ι]
      _ = U.ι := by simp [eIso, r]
  have hUopen : IsOpenSubspace B S hS U := by
    refine ⟨hUalg, ?_⟩
    show O U.ι
    rw [← hincl]
    exact MorphismProperty.RespectsIso.precomp O eIso.inv e heopen
  let g₀ := q₀
  let g := eIso.inv ≫ g₀
  have hgcomm : g ≫ V.ι = U.ι ≫ f := by
    have heq : q₀ ≫ V.ι = e ≫ f := by
      calc
        q₀ ≫ V.ι = p₀ ≫ f₀ := pullback.condition.symm
        _ = p₀ ≫ U₀.ι ≫ f := by simp [f₀]
        _ = e ≫ f := rfl
    calc
      g ≫ V.ι = eIso.inv ≫ (q₀ ≫ V.ι) := by simp [g, g₀, Category.assoc]
      _ = eIso.inv ≫ (e ≫ f) := by rw [heq]
      _ = (eIso.inv ≫ e) ≫ f := (Category.assoc _ _ _).symm
      _ = U.ι ≫ f := by rw [hincl]
  have hgfinite : IsFinite B S hS g :=
    isFinite_of_source_iso B S hS eIso g₀ hVfinite
  let U₀R : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨U₀.toFunctor, hU₀alg⟩
  let VR : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨V.toFunctor, hV.1⟩
  let YR : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let PR : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨P, hP⟩
  let f₀R : U₀R ⟶ YR := ObjectProperty.homMk f₀
  let vR : VR ⟶ YR := ObjectProperty.homMk V.ι
  let pR : PR ⟶ U₀R := ObjectProperty.homMk p₀
  let qR : PR ⟶ VR := ObjectProperty.homMk q₀
  have hpullR : IsPullback pR qR f₀R vR :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (IsPullback.of_hasPullback f₀ V.ι)
  refine ⟨U, V, g, hUopen, hV, hgcomm, hyV, ?_, hgfinite⟩
  intro x hx
  obtain ⟨x₀, hx₀⟩ := hcover₀ hx
  obtain ⟨v, hv⟩ := hyV
  have hcompat : pointsMap B S hS U₀.toFunctor f₀ x₀ =
      pointsMap B S hS V.toFunctor V.ι v := by
    rw [hf₀pt, hx₀, hx, hv]
  obtain ⟨w, hw₁, -⟩ := exists_point_of_isPullback B S hS hpullR
    x₀ v hcompat
  have hw₁' : pointsMap B S hS P p₀ w = x₀ := by
    simpa [pR] using hw₁
  let z := pointsMap B S hS P r w
  have hxe : pointsMap B S hS P e w = x := by
    calc
      pointsMap B S hS P e w =
          pointsMap B S hS U₀.toFunctor U₀.ι
            (pointsMap B S hS P p₀ w) :=
              congrFun (pointsMap_comp B S hS _ p₀ U₀.ι) w
      _ = pointsMap B S hS U₀.toFunctor U₀.ι x₀ :=
        congrArg (pointsMap B S hS U₀.toFunctor U₀.ι) hw₁'
      _ = x := hx₀
  refine ⟨z, ?_⟩
  calc
    pointsMap B S hS U.toFunctor U.ι z =
        pointsMap B S hS P e w := by
          dsimp [z]
          calc
            _ = pointsMap B S hS P (r ≫ U.ι) w :=
              (congrFun (pointsMap_comp B S hS _ r U.ι) w).symm
            _ = pointsMap B S hS P e w := by rw [Subfunctor.toRange_ι]
    _ = x := hxe


end FiniteRestriction

end AlgebraicGeometry.Space

end
