module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresFiniteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableDenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.Impurities
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Smallness
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence

/-!
# Relatively pure modules on an algebraic space

In the standing situation of Stacks 0CV6 — a finite type decent morphism `f : X ⟶ Y` of
algebraic spaces, a finite type quasi-coherent `𝒪_X`-module `F` and a point `y` of `Y` — the
module is *pure above `y`* when no impurity of `F` above `y` has its structure morphism
`T ⟶ Y` quasi-finite at `t`, and *universally pure above `y`* when there is no impurity at all.

Universal purity above `y` is the same as purity above `y'` for every base change along a
morphism `(Y', y') ⟶ (Y, y)` of pointed algebraic spaces — equivalently, universal purity
relative to `Y` is purity of every base change `F_{Y'}` relative to `Y'` — and purity above `y`
passes to a base change whose morphism of bases is quasi-finite at `y'`.

## Main definitions

* `AlgebraicGeometry.Space.IsPureAbove` and
  `AlgebraicGeometry.Space.IsUniversallyPureAbove`: parts (1) and (2) of Stacks 0CVD, with
  `AlgebraicGeometry.Space.IsUniversallyPureRelative` and
  `AlgebraicGeometry.Space.IsPureRelative` parts (4) and (5).
* `AlgebraicGeometry.Space.PointedOver`: a morphism of pointed algebraic spaces into the base
  of the situation, with `AlgebraicGeometry.Space.PointedOver.baseChange` the situation it
  induces on the fibre product `X' = Y' ×_Y X`.
* `AlgebraicGeometry.Space.PointedOver.alongBaseChange`: an impurity diagram of the
  base-changed situation, read as an impurity diagram of the original one.
* `AlgebraicGeometry.Space.PrePureSituation.baseChangeAlong`: the situation induced on
  `X' = Y' ×_Y X` by an unpointed morphism `Y' ⟶ Y` of bases together with a point of `Y'`,
  with `AlgebraicGeometry.Space.PrePureSituation.IsPureRelativeAlong` the purity of that base
  change relative to `Y'`.

## Main results

* `AlgebraicGeometry.Space.isQuasiFiniteAt_comp`: quasi-finiteness at a point is preserved by
  composition with a morphism quasi-finite at the image point.
* `AlgebraicGeometry.Space.exists_isImpurity_isQuasiFiniteAt_of_exists_isImpurity_isEtale`:
  condition (3) of Stacks 0CVB implies condition (4).
* `AlgebraicGeometry.Space.PointedOver.isImpurity_alongBaseChange_iff`: an impurity of the
  base-changed module above `y'` is exactly an impurity of the module above `y`.
* `AlgebraicGeometry.Space.isUniversallyPureAbove_iff_forall_baseChange_isPureAbove`:
  **Stacks 0CVE**, the equivalence above a point.
* `AlgebraicGeometry.Space.isUniversallyPureRelative_iff_forall_baseChange_isPureRelative`:
  **Stacks 0CVE**, the closing "in particular" clause, relative to the whole base.
* `AlgebraicGeometry.Space.isPureAbove_baseChange_of_isQuasiFiniteAt`: **Stacks 0CVF.**

## Implementation notes

Purity above `y` is stated as the failure of condition (4) of Stacks 0CVB, the condition on
impurities whose structure morphism is quasi-finite at `t`; that is the condition the proof of
Stacks 0CVF uses, and the one for which the composition of quasi-finite morphisms is the whole
argument. Of the four conditions of Stacks 0CVB only the implication from condition (3) to
condition (4) is recorded here; the implications (1) ⟹ (3) and (1) ⟹ (4), for a test scheme
realizing the strict henselization of an étale chart, are in
`StacksFrontier/AlgebraicGeometry/Spaces/Flat/StrictHenselizationImpurity.lean`.

The base change of the situation along `(Y', y') ⟶ (Y, y)` is taken on the chosen fibre
product `Limits.pullback`, so that the decency of the base-changed morphism is available on the
nose from `AlgebraicGeometry.Space.isDecent_baseChange`, matching the convention of
`AlgebraicGeometry.Space.ImpurityDiagram.baseChange`. The base change is a situation of
Stacks 0CV6 outright, with nothing assumed: quasi-coherence of the base-changed module is
Stacks 03GA in the form
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`, which
holds along an arbitrary morphism of algebraic spaces, and finiteness of its type is the clause
03DL(5) of Stacks 03DO in the form
`AlgebraicGeometry.Space.isFiniteTypeOnSite_modulePullback`.

Because both the base change of the situation and the base change inside an impurity diagram
are chosen fibre products, an impurity diagram of the base-changed situation has total space
`T ×_{Y'} (Y' ×_Y X)` where the corresponding diagram of the original situation has
`T ×_Y X`. The two are compared by `CategoryTheory.Limits.pullbackRightPullbackFstIso`, whose
two compatibilities with the projections are exactly what is needed to carry the distinguished
point, the closure condition and the relative weak assassin condition across. The last of
these uses Stacks 0CUU in the form
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_modulePullback_iff` for the induced
isomorphism of fibres, which is étale, together with
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_congr` and
`AlgebraicGeometry.Space.modulePullbackCompIso` for the comparison of the two pulled-back
modules.

The relative notions of Stacks 0CVD quantify over every point of the base, so they are stated
on a situation by varying its chosen point. For a base change along an unpointed morphism
`Y' ⟶ Y` there is no chosen point of `Y'` to start from, so one is supplied and then varied;
`AlgebraicGeometry.Space.isPureRelative_baseChangeAlong_iff` says that this recovers relative
purity of the base change whichever point was supplied. Parts (3) and (6), which read the
purity of the algebraic space `X` itself as the purity of its structure sheaf, are stated in
`StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityProper`, where the situation carrying `𝒪_X`
is available.

## References

* [Stacks Project, Tag 0CVD](https://stacks.math.columbia.edu/tag/0CVD)
* [Stacks Project, Tag 0CVE](https://stacks.math.columbia.edu/tag/0CVE)
* [Stacks Project, Tag 0CVF](https://stacks.math.columbia.edu/tag/0CVF)
* [Stacks Project, Tag 0CVB](https://stacks.math.columbia.edu/tag/0CVB)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03XK](https://stacks.math.columbia.edu/tag/03XK)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Quasi-finiteness at a point and composition -/

/-- **Quasi-finiteness at a point composes.** If `f` is quasi-finite at `x` and `g` is
quasi-finite at the image of `x`, then `f ≫ g` is quasi-finite at `x`.

The witness is the open subspace of `X` swept out by the part of the witness for `f` lying over
the witness for `g`; it is locally quasi-finite over the latter by Stacks 03XN and hence over
the target by Stacks 03XK. -/
theorem isQuasiFiniteAt_comp (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : points B S hS X)
    (hf : IsQuasiFiniteAt B S hS f x)
    (hg : IsQuasiFiniteAt B S hS g (pointsMap B S hS X f x)) :
    IsQuasiFiniteAt B S hS (f ≫ g) x := by
  obtain ⟨U, hU, x', hx', hUf⟩ := hf
  obtain ⟨V, hV, y', hy', hVg⟩ := hg
  -- `L` is the part of `U` lying over `V`.
  set L : Subfunctor U.toFunctor := V.preimage (U.ι ≫ f) with hLdef
  have hL : IsOpenSubspace B S hS L :=
    isOpenSubspace_preimage B S hS (U.ι ≫ f) V hY hU.1 hV
  have hsq : IsPullback (V.fromPreimage (U.ι ≫ f)) L.ι V.ι (U.ι ≫ f) :=
    Subfunctor.isPullback_preimage (U.ι ≫ f) V
  have hcompat : pointsMap B S hS V.toFunctor V.ι y' =
      pointsMap B S hS U.toFunctor (U.ι ≫ f) x' := by
    rw [hy', pointsMap_comp, Function.comp_apply, hx']
  obtain ⟨w, _, hw2⟩ := exists_points_of_isPullback B S hS hsq y' x' hcompat
  -- `W` is `L`, read as an open subspace of `X`.
  set W : Subfunctor X := Subfunctor.range (L.ι ≫ U.ι) with hWdef
  have hW : IsOpenSubspace B S hS W := isOpenSubspace_range_ι_comp_ι B S hS hU hL
  refine ⟨W, hW, ?_⟩
  have hmem : x ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) := by
    rw [hWdef, range_pointsMap_ι_range_ι_comp_ι]
    exact ⟨w, by rw [pointsMap_comp, Function.comp_apply, hw2, hx']⟩
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, hz, ?_⟩
  -- The comparison of `W` with `L`.
  have hmono : Mono (L.ι ≫ U.ι) := mono_comp _ _
  set e : L.toFunctor ≅ W.toFunctor := asIso (Subfunctor.toRange (L.ι ≫ U.ι)) with hedef
  have hehom : e.hom ≫ W.ι = L.ι ≫ U.ι := Subfunctor.toRange_ι (L.ι ≫ U.ι)
  have hWι : W.ι = e.inv ≫ L.ι ≫ U.ι := by
    rw [← hehom, Iso.inv_hom_id_assoc]
  -- `L.ι` is locally quasi-finite, hence so is `L.ι ≫ U.ι ≫ f`.
  have hLι : IsLocallyQuasiFinite B S hS L.ι :=
    isLocallyQuasiFinite_of_isImmersion B S hS L.ι
      (isImmersion_of_isOpenImmersion B S hS hL.2)
  have hLf : IsLocallyQuasiFinite B S hS (L.ι ≫ U.ι ≫ f) :=
    isLocallyQuasiFinite_comp B S hS hL.1 hU.1 hY L.ι (U.ι ≫ f) hLι hUf
  -- The projection `L ⟶ V` is locally quasi-finite by cancellation.
  have hfp : V.fromPreimage (U.ι ≫ f) ≫ V.ι = L.ι ≫ U.ι ≫ f := hsq.w
  have hfromLqf : IsLocallyQuasiFinite B S hS (V.fromPreimage (U.ι ≫ f)) := by
    refine isLocallyQuasiFinite_of_comp B S hS hL.1 hV.1 hY
      (V.fromPreimage (U.ι ≫ f)) V.ι ?_
    rw [hfp]
    exact hLf
  have hLg : IsLocallyQuasiFinite B S hS (V.fromPreimage (U.ι ≫ f) ≫ V.ι ≫ g) :=
    isLocallyQuasiFinite_comp B S hS hL.1 hV.1 hZ _ _ hfromLqf hVg
  have hesym : IsEtale B S hS e.inv :=
    isEtale_of_isIso B S hS e.inv
  have heinv : IsLocallyQuasiFinite B S hS e.inv :=
    isLocallyQuasiFinite_of_isEtale' B S hS hesym
  have hfinal : IsLocallyQuasiFinite B S hS
      (e.inv ≫ V.fromPreimage (U.ι ≫ f) ≫ V.ι ≫ g) :=
    isLocallyQuasiFinite_comp B S hS hW.1 hL.1 hZ _ _ heinv hLg
  have hfp2 : L.ι ≫ U.ι ≫ f ≫ g = V.fromPreimage (U.ι ≫ f) ≫ V.ι ≫ g := by
    have haux : (L.ι ≫ U.ι ≫ f) ≫ g = (V.fromPreimage (U.ι ≫ f) ≫ V.ι) ≫ g := by
      rw [hfp]
    simpa only [Category.assoc] using haux
  have hrw : W.ι ≫ f ≫ g = e.inv ≫ V.fromPreimage (U.ι ≫ f) ≫ V.ι ≫ g := by
    rw [hWι]
    simp only [Category.assoc]
    rw [hfp2]
  rw [hrw]
  exact hfinal

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-- The map on points of an isomorphism undoes the map on points of its inverse. -/
private theorem pointsMap_hom_inv_apply {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (z : points B S hS G) : pointsMap B S hS F e.hom (pointsMap B S hS G e.inv z) = z := by
  rw [← pointsMap_comp_apply, Iso.inv_hom_id, pointsMap_id, id_eq]

/-! ### Purity above a point -/

/-- **Stacks 0CVD, part (1).** The module is *pure above `y`* when no impurity of `F` above `y`
has its structure morphism `T ⟶ Y` quasi-finite at `t`.

This is the failure of condition (4) of Stacks 0CVB, which is the condition the proof of
Stacks 0CVF works with. -/
@[stacks 0CVD "part (1), as the failure of condition (4) of Stacks 0CVB"]
def IsPureAbove (P : PrePureSituation.{u, u} B S hS) : Prop :=
  ∀ D : ImpurityDiagram P, IsQuasiFiniteAt B S hS D.g D.t → ¬ D.IsImpurity

/-- **Stacks 0CVD, part (2).** The module is *universally pure above `y`* when there is no
impurity of `F` above `y` at all. -/
@[stacks 0CVD "part (2)"]
def IsUniversallyPureAbove (P : PrePureSituation.{u, u} B S hS) : Prop :=
  ∀ D : ImpurityDiagram P, ¬ D.IsImpurity

/-- A module universally pure above `y` is pure above `y`. -/
theorem IsPureAbove.of_isUniversallyPureAbove {P : PrePureSituation.{u, u} B S hS}
    (h : IsUniversallyPureAbove P) : IsPureAbove P := fun D _ => h D

/-- **Stacks 0CVD, part (4).** The module is *universally pure relative to `Y`* when it is
universally pure above every point of `Y`.

The chosen point of the situation is irrelevant: the condition varies it over all of `|Y|`. -/
@[stacks 0CVD "part (4)"]
def IsUniversallyPureRelative (P : PrePureSituation.{u, u} B S hS) : Prop :=
  ∀ y : points B S hS P.Y, IsUniversallyPureAbove { P with y := y }

/-- **Stacks 0CVD, part (5).** The module is *pure relative to `Y`* when it is pure above every
point of `Y`.

The chosen point of the situation is irrelevant: the condition varies it over all of `|Y|`. -/
@[stacks 0CVD "part (5)"]
def IsPureRelative (P : PrePureSituation.{u, u} B S hS) : Prop :=
  ∀ y : points B S hS P.Y, IsPureAbove { P with y := y }

/-- A module universally pure relative to `Y` is pure relative to `Y`. -/
theorem IsPureRelative.of_isUniversallyPureRelative {P : PrePureSituation.{u, u} B S hS}
    (h : IsUniversallyPureRelative P) : IsPureRelative P :=
  fun y => IsPureAbove.of_isUniversallyPureAbove (h y)

/-- **Stacks 0CVB, condition (3) implies condition (4).** An impurity of `F` above `y` whose
structure morphism `T ⟶ Y` is étale, so that `(T, t) ⟶ (Y, y)` is an étale neighbourhood, is an
impurity whose structure morphism is quasi-finite at `t`: an étale morphism of algebraic spaces
is locally quasi-finite by Stacks 03XU.

The implications (1) ⟹ (3) and (1) ⟹ (4) are
`AlgebraicGeometry.Space.exists_isImpurity_isEtale_of_isImpurity_strictHenselization` and
`AlgebraicGeometry.Space.exists_isImpurity_isQuasiFiniteAt_of_isImpurity_strictHenselization`. -/
@[stacks 0CVB "condition (3) implies condition (4)"]
theorem exists_isImpurity_isQuasiFiniteAt_of_exists_isImpurity_isEtale
    (P : PrePureSituation.{u, u} B S hS)
    (h : ∃ D : ImpurityDiagram P, IsEtale B S hS D.g ∧ D.IsImpurity) :
    ∃ D : ImpurityDiagram P, IsQuasiFiniteAt B S hS D.g D.t ∧ D.IsImpurity := by
  obtain ⟨D, hetale, himp⟩ := h
  exact ⟨D, isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS
    (isAlgebraicSpace_yoneda B S hS D.T)
    (isLocallyQuasiFinite_of_isEtale B S hS P.hY hetale) D.t, himp⟩

/-! ### Pointed base changes of the situation -/

/-- A morphism of pointed algebraic spaces `(Y', y') ⟶ (Y, y)` into the base of a pre-pure
situation. -/
structure PointedOver (P : PrePureSituation.{u, u} B S hS) where
  /-- The new base. -/
  Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- It is an algebraic space. -/
  hY' : IsAlgebraicSpace B S hS Y'
  /-- The morphism of bases. -/
  g : Y' ⟶ P.Y
  /-- The chosen point of the new base. -/
  y' : points B S hS Y'
  /-- It lies above the chosen point of the old base. -/
  mapsPoint : pointsMap B S hS Y' g y' = P.y

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_RelativelyPureModules
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace PointedOver

variable {P : PrePureSituation.{u, u} B S hS} (c : PointedOver P)

/-- The fibre product `X' = Y' ×_Y X`, as an object of the category of algebraic spaces. -/
noncomputable abbrev source : AlgebraicSpaces B S hS :=
  ⟨pullback c.g P.f, isAlgebraicSpace_pullback B S hS c.g P.f c.hY' P.hX P.hY⟩

/-- The projection `X' ⟶ X`, as a morphism of algebraic spaces. -/
noncomputable abbrev proj : c.source ⟶ (⟨P.X, P.hX⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (pullback.snd c.g P.f)

/-- The base change `F_{Y'}` of the module `F` to `X' = Y' ×_Y X`. -/
noncomputable abbrev «module» : Modules.{u, u} B S hS c.source.1 c.source.2 :=
  (modulePullback B S hS c.proj).obj P.F

/-- The pre-pure situation obtained by base change along a morphism of pointed algebraic
spaces: the fibre product `X' = Y' ×_Y X` over `Y'`, with the pullback of `F` and the chosen
point `y'`.

All of the data Stacks 0CV6 asks for is available: the projection `X' ⟶ Y'` is of finite type
and decent by base change, the pulled-back module is of finite type by the clause 03DL(5) of
Stacks 03DO and quasi-coherent by Stacks 03GA. -/
@[reducible] noncomputable def baseChange : PrePureSituation.{u, u} B S hS where
  X := pullback c.g P.f
  hX := isAlgebraicSpace_pullback B S hS c.g P.f c.hY' P.hX P.hY
  Y := c.Y'
  hY := c.hY'
  f := pullback.fst c.g P.f
  finiteType := IsFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback c.g P.f)
    P.hX P.hY P.finiteType
  decent := isDecent_baseChange B S hS P.f c.g P.decent
  F := c.module
  moduleFiniteType :=
    isFiniteTypeOnSite_modulePullback B S hS c.proj P.F P.moduleFiniteType
  moduleQuasicoherent :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS c.proj P.F
      P.moduleQuasicoherent
  y := c.y'

/-- The comparison `T ×_{Y'} (Y' ×_Y X) ≅ T ×_Y X` between the total space of an impurity
diagram of the base-changed situation and that of the corresponding diagram of the original
situation. -/
noncomputable abbrev compare (E : ImpurityDiagram c.baseChange) :
    E.baseChange ≅ pullback (E.g ≫ c.g) P.f :=
  pullbackRightPullbackFstIso c.g P.f E.g

/-- An impurity diagram of the base-changed situation, read as an impurity diagram of the
original situation: its structure morphism is composed with the morphism of bases, and its
distinguished point is carried across the comparison of total spaces. -/
@[reducible] noncomputable def alongBaseChange (E : ImpurityDiagram c.baseChange) :
    ImpurityDiagram P where
  T := E.T
  g := E.g ≫ c.g
  t' := E.t'
  t := E.t
  specializes := E.specializes
  mapsToChosenPoint := by
    rw [pointsMap_comp, Function.comp_apply, E.mapsToChosenPoint]
    exact c.mapsPoint
  xi := pointsMap B S hS E.baseChange (c.compare E).hom E.xi
  xi_liesOver := by
    rw [← Function.comp_apply (f := pointsMap B S hS (pullback (E.g ≫ c.g) P.f)
      (pullback.fst (E.g ≫ c.g) P.f)), ← pointsMap_comp,
      pullbackRightPullbackFstIso_hom_fst]
    exact E.xi_liesOver

/-- The comparison of total spaces is compatible with the projections to `T`. -/
theorem compare_hom_toT (E : ImpurityDiagram c.baseChange) :
    (c.compare E).hom ≫
        (c.alongBaseChange E).toT = E.toT :=
  pullbackRightPullbackFstIso_hom_fst c.g P.f E.g

/-- The comparison of total spaces is compatible with the projections to `X`. -/
theorem compare_hom_toX (E : ImpurityDiagram c.baseChange) :
    (c.compare E).hom ≫
        (c.alongBaseChange E).toX = E.toX ≫ c.proj.hom :=
  pullbackRightPullbackFstIso_hom_snd c.g P.f E.g

/-- The comparison of total spaces carries the distinguished point of the diagram read along
the base change back to the distinguished point of `E`. -/
theorem pointsMap_compare_inv_xi (E : ImpurityDiagram c.baseChange) :
    pointsMap B S hS (c.alongBaseChange E).baseChange (c.compare E).inv
      (c.alongBaseChange E).xi = E.xi := by
  have hxi : (c.alongBaseChange E).xi = pointsMap B S hS E.baseChange (c.compare E).hom E.xi :=
    rfl
  rw [hxi, ← pointsMap_comp_apply, Iso.hom_inv_id, pointsMap_id, id_eq]

/-- The image in `T` of the closure of the distinguished point is the same for `E` and for the
diagram read along the base change. -/
theorem image_toT_closure_alongBaseChange (E : ImpurityDiagram c.baseChange) :
    pointsMap B S hS (c.alongBaseChange E).baseChange (c.alongBaseChange E).toT ''
        closure {(c.alongBaseChange E).xi} =
      pointsMap B S hS E.baseChange E.toT '' closure {E.xi} := by
  set D := c.alongBaseChange E
  set φ := c.compare E
  have hφT : φ.hom ≫ D.toT = E.toT := c.compare_hom_toT E
  have hxi : D.xi = pointsMap B S hS E.baseChange φ.hom E.xi := rfl
  have hinvxi : pointsMap B S hS D.baseChange φ.inv D.xi = E.xi := c.pointsMap_compare_inv_xi E
  have hcl : closure {D.xi} = pointsMap B S hS E.baseChange φ.hom '' closure {E.xi} := by
    refine Set.Subset.antisymm ?_ ?_
    · intro z hz
      refine ⟨pointsMap B S hS D.baseChange φ.inv z, ?_, ?_⟩
      · have hsub := image_closure_subset_closure_image (s := {D.xi})
          (continuous_pointsMap B S hS (F := D.baseChange) φ.inv)
        have h2 := hsub ⟨z, hz, rfl⟩
        rwa [Set.image_singleton, hinvxi] at h2
      · exact pointsMap_hom_inv_apply φ z
    · have hsub := image_closure_subset_closure_image (s := {E.xi})
        (continuous_pointsMap B S hS (F := E.baseChange) φ.hom)
      rwa [Set.image_singleton, ← hxi] at hsub
  rw [hcl, ← Set.image_comp, ← pointsMap_comp, hφT]

/-- The fibres over a field-valued point of `T` of `E` and of the diagram read along the base
change are identified, compatibly with the comparison of total spaces. -/
theorem exists_fibreAt_iso_alongBaseChange (E : ImpurityDiagram c.baseChange)
    (p : FieldValuedPoint B S hS (yoneda.obj E.T)) :
    ∃ ψ : (E.fibreAt p).1 ≅ ((c.alongBaseChange E).fibreAt p).1,
      ψ.hom ≫ ((c.alongBaseChange E).fibreProjection p).hom =
        (E.fibreProjection p).hom ≫ (c.compare E).hom := by
  set D := c.alongBaseChange E
  set φ := c.compare E
  have hφT : φ.hom ≫ D.toT = E.toT := c.compare_hom_toT E
  have sqφ : IsPullback φ.hom E.toT D.toT (𝟙 (yoneda.obj E.T)) :=
    IsPullback.of_horiz_isIso ⟨by rwa [Category.comp_id]⟩
  have sqfib : IsPullback
      ((E.fibreProjection p).hom ≫ φ.hom)
      (pullback.snd E.toT (fieldMorphism B S hS (yoneda.obj E.T) p)) D.toT
      (fieldMorphism B S hS (yoneda.obj E.T) p) := by
    simpa using
      (IsPullback.of_hasPullback E.toT (fieldMorphism B S hS (yoneda.obj E.T) p)).paste_horiz
        sqφ
  exact ⟨sqfib.isoPullback, sqfib.isoPullback_hom_fst⟩

/-- Under an identification of fibres compatible with the comparison of total spaces, a point of
the fibre of `E` is weakly associated to the restriction of `F_T` exactly when its image is
weakly associated to the restriction of the module of the diagram read along the base change. -/
theorem isWeaklyAssociatedPoint_fibreAt_alongBaseChange_iff (E : ImpurityDiagram c.baseChange)
    (p : FieldValuedPoint B S hS (yoneda.obj E.T))
    (ψ : (E.fibreAt p).1 ≅ ((c.alongBaseChange E).fibreAt p).1)
    (hψ : ψ.hom ≫ ((c.alongBaseChange E).fibreProjection p).hom =
      (E.fibreProjection p).hom ≫ (c.compare E).hom)
    (θ : points B S hS (E.fibreAt p).1) :
    IsWeaklyAssociatedPoint B S hS ((c.alongBaseChange E).fibreAt p)
        ((modulePullback B S hS ((c.alongBaseChange E).fibreProjection p)).obj
          (c.alongBaseChange E).baseChangeModule)
        (pointsMap B S hS (E.fibreAt p).1 ψ.hom θ) ↔
      IsWeaklyAssociatedPoint B S hS (E.fibreAt p)
        ((modulePullback B S hS (E.fibreProjection p)).obj E.baseChangeModule) θ := by
  have hψEtale : IsEtale B S hS ψ.hom := isEtale_of_isIso B S hS ψ.hom
  set D := c.alongBaseChange E
  set φ := c.compare E
  have hφX : φ.hom ≫ D.toX = E.toX ≫ c.proj.hom := c.compare_hom_toX E
  set ψSpace : E.fibreAt p ⟶ D.fibreAt p := ObjectProperty.homMk ψ.hom
  have hpath : ψSpace ≫ D.fibreProjection p ≫ D.toXSpace =
      E.fibreProjection p ≫ E.toXSpace ≫ c.proj := by
    refine ObjectProperty.hom_ext _ ?_
    have h1 : (ψSpace ≫ D.fibreProjection p ≫ D.toXSpace).hom =
        ψ.hom ≫ (D.fibreProjection p).hom ≫ D.toX := rfl
    have h2 : (E.fibreProjection p ≫ E.toXSpace ≫ c.proj).hom =
        (E.fibreProjection p).hom ≫ E.toX ≫ c.proj.hom := rfl
    rw [h1, h2, ← Category.assoc ψ.hom, hψ, Category.assoc, hφX]
  have α1 : (modulePullback B S hS ψSpace).obj
        ((modulePullback B S hS (D.fibreProjection p)).obj D.baseChangeModule) ≅
      (modulePullback B S hS ψSpace).obj
        ((modulePullback B S hS (D.fibreProjection p ≫ D.toXSpace)).obj P.F) :=
    (modulePullback B S hS ψSpace).mapIso
      ((modulePullbackCompIso B S hS (D.fibreProjection p) D.toXSpace).app P.F)
  have α2 : (modulePullback B S hS ψSpace).obj
        ((modulePullback B S hS (D.fibreProjection p ≫ D.toXSpace)).obj P.F) ≅
      (modulePullback B S hS (ψSpace ≫ D.fibreProjection p ≫ D.toXSpace)).obj P.F :=
    (modulePullbackCompIso B S hS ψSpace (D.fibreProjection p ≫ D.toXSpace)).app P.F
  have α3 : (modulePullback B S hS (ψSpace ≫ D.fibreProjection p ≫ D.toXSpace)).obj P.F ≅
      (modulePullback B S hS (E.fibreProjection p ≫ E.toXSpace ≫ c.proj)).obj P.F :=
    eqToIso (congrArg (fun k : E.fibreAt p ⟶ (⟨P.X, P.hX⟩ : AlgebraicSpaces B S hS) =>
      (modulePullback B S hS k).obj P.F) hpath)
  have α4 : (modulePullback B S hS (E.fibreProjection p ≫ E.toXSpace ≫ c.proj)).obj P.F ≅
      (modulePullback B S hS (E.fibreProjection p)).obj
        ((modulePullback B S hS (E.toXSpace ≫ c.proj)).obj P.F) :=
    ((modulePullbackCompIso B S hS (E.fibreProjection p) (E.toXSpace ≫ c.proj)).app P.F).symm
  have α5 : (modulePullback B S hS (E.fibreProjection p)).obj
        ((modulePullback B S hS (E.toXSpace ≫ c.proj)).obj P.F) ≅
      (modulePullback B S hS (E.fibreProjection p)).obj E.baseChangeModule :=
    (modulePullback B S hS (E.fibreProjection p)).mapIso
      ((modulePullbackCompIso B S hS E.toXSpace c.proj).app P.F).symm
  exact (isWeaklyAssociatedPoint_modulePullback_iff B S hS ψSpace hψEtale _ θ).symm.trans
    (isWeaklyAssociatedPoint_congr B S hS (α1 ≪≫ α2 ≪≫ α3 ≪≫ α4 ≪≫ α5) θ)

/-- **An impurity of the base-changed module above `y'` is exactly an impurity of the module
above `y`.** The total spaces `T ×_{Y'} (Y' ×_Y X)` and `T ×_Y X` correspond under
`CategoryTheory.Limits.pullbackRightPullbackFstIso`, and so do the pulled-back modules and the
fibres of the two projections to `T`. -/
theorem isImpurity_alongBaseChange_iff (E : ImpurityDiagram c.baseChange) :
    (c.alongBaseChange E).IsImpurity ↔ E.IsImpurity := by
  set D := c.alongBaseChange E
  set φ := c.compare E
  have hφT : φ.hom ≫ D.toT = E.toT := c.compare_hom_toT E
  have hxi : D.xi = pointsMap B S hS E.baseChange φ.hom E.xi := rfl
  have hinvxi : pointsMap B S hS D.baseChange φ.inv D.xi = E.xi := c.pointsMap_compare_inv_xi E
  have hassT : pointsMap B S hS D.baseChange D.toT D.xi =
      pointsMap B S hS E.baseChange E.toT E.xi := by
    rw [hxi, ← pointsMap_comp_apply, hφT]
  have hass : D.IsRelativeWeakAssassinPoint D.xi ↔ E.IsRelativeWeakAssassinPoint E.xi := by
    refine exists_congr fun p => ?_
    obtain ⟨ψ, hψ⟩ : ∃ ψ : (E.fibreAt p).1 ≅ (D.fibreAt p).1,
        ψ.hom ≫ (D.fibreProjection p).hom = (E.fibreProjection p).hom ≫ φ.hom :=
      c.exists_fibreAt_iso_alongBaseChange E p
    have hψinv : ψ.inv ≫ (E.fibreProjection p).hom =
        (D.fibreProjection p).hom ≫ φ.inv := by
      rw [← Iso.eq_inv_comp] at hψ
      rw [hψ]
      simp
    have hwa := c.isWeaklyAssociatedPoint_fibreAt_alongBaseChange_iff E p ψ hψ
    rw [hassT]
    refine and_congr_right fun _ => ?_
    constructor
    · rintro ⟨θ, hθ, hwaD⟩
      refine ⟨pointsMap B S hS (D.fibreAt p).1 ψ.inv θ, ?_, (hwa _).mp ?_⟩
      · rw [← pointsMap_comp_apply, hψinv, pointsMap_comp_apply, hθ, hinvxi]
      · rwa [pointsMap_hom_inv_apply]
    · rintro ⟨θ, hθ, hwaE⟩
      refine ⟨pointsMap B S hS (E.fibreAt p).1 ψ.hom θ, ?_, (hwa θ).mpr hwaE⟩
      rw [← pointsMap_comp_apply, hψ, pointsMap_comp_apply, hθ, ← hxi]
  unfold ImpurityDiagram.IsImpurity
  rw [hass, c.image_toT_closure_alongBaseChange E]

end PointedOver

/-! ### The two lemmas -/

/-- An impurity of `F` above `y` is an impurity of the base change along `(T, t) ⟶ (Y, y)`
itself, whose structure morphism is the identity and hence quasi-finite at `t`. -/
theorem ImpurityDiagram.exists_pointedOver_isImpurity_baseChange
    {P : PrePureSituation.{u, u} B S hS} (D : ImpurityDiagram P) (hD : D.IsImpurity) :
    ∃ (c : PointedOver P) (E : ImpurityDiagram c.baseChange),
      IsQuasiFiniteAt B S hS E.g E.t ∧ E.IsImpurity := by
  set c : PointedOver P :=
    { Y' := yoneda.obj D.T
      hY' := isAlgebraicSpace_yoneda B S hS D.T
      g := D.g
      y' := D.t
      mapsPoint := D.mapsToChosenPoint }
  have hidEtale : IsEtale B S hS (𝟙 (yoneda.obj D.T)) := isEtale_of_isIso B S hS _
  set E : ImpurityDiagram c.baseChange :=
    { T := D.T
      g := 𝟙 (yoneda.obj D.T)
      t' := D.t'
      t := D.t
      specializes := D.specializes
      mapsToChosenPoint := by
        rw [pointsMap_id]
        rfl
      xi := pointsMap B S hS D.baseChange
        (pullbackRightPullbackFstIso D.g P.f (𝟙 (yoneda.obj D.T))).inv D.xi
      xi_liesOver := by
        rw [← pointsMap_comp_apply]
        rw [show (pullbackRightPullbackFstIso D.g P.f (𝟙 (yoneda.obj D.T))).inv ≫
            pullback.fst (𝟙 (yoneda.obj D.T)) (pullback.fst D.g P.f) =
            pullback.fst (𝟙 (yoneda.obj D.T) ≫ D.g) P.f by
          rw [Iso.inv_comp_eq, pullbackRightPullbackFstIso_hom_fst]]
        exact D.xi_liesOver }
  have hqfE : IsQuasiFiniteAt B S hS E.g E.t :=
    isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS (isAlgebraicSpace_yoneda B S hS D.T)
      (isLocallyQuasiFinite_of_isEtale' B S hS hidEtale) E.t
  refine ⟨c, E, hqfE, (c.isImpurity_alongBaseChange_iff E).mp ?_⟩
  have hxieq : (c.alongBaseChange E).xi = D.xi := by
    exact pointsMap_hom_inv_apply (pullbackRightPullbackFstIso D.g P.f (𝟙 (yoneda.obj D.T)))
      D.xi
  unfold ImpurityDiagram.IsImpurity at hD ⊢
  rwa [hxieq]

/-- **Stacks 0CVE.** A finite type quasi-coherent module is universally pure above `y` exactly
when, for every morphism `(Y', y') ⟶ (Y, y)` of pointed algebraic spaces, its base change
`F_{Y'}` is pure above `y'`.

The source lists the two conditions without the connective; they are equivalent, as the
statement of the analogous Stacks 05J6 for schemes makes explicit. The consequence the source
draws for purity relative to the whole base is
`isUniversallyPureRelative_iff_forall_baseChange_isPureRelative`.

Both directions are formal, as the source says: an impurity of a base change is an impurity of
`F` by `isImpurity_alongBaseChange_iff`, and conversely an impurity diagram `(T, t' ⤳ t, ξ)` of
`F` is an impurity of the base change along `(T, t) ⟶ (Y, y)` itself, whose structure morphism
is the identity and hence quasi-finite at `t`. -/
@[stacks 0CVE "the equivalence left implicit by the source"]
theorem isUniversallyPureAbove_iff_forall_baseChange_isPureAbove
    (P : PrePureSituation.{u, u} B S hS) :
    IsUniversallyPureAbove P ↔ ∀ c : PointedOver P, IsPureAbove c.baseChange :=
  ⟨fun hP c E _ hE => hP _ ((c.isImpurity_alongBaseChange_iff E).mpr hE), fun hAll D hD => by
    obtain ⟨c, E, hqf, hE⟩ := D.exists_pointedOver_isImpurity_baseChange hD
    exact hAll c E hqf hE⟩

/-- **Stacks 0CVF.** If `(Y', y') ⟶ (Y, y)` is a morphism of pointed algebraic spaces with
`Y' ⟶ Y` quasi-finite at `y'`, and the module is pure above `y`, then its base change `F_{Y'}`
is pure above `y'`.

An impurity of `F_{Y'}` above `y'` whose structure morphism is quasi-finite at `t` is an
impurity of `F` above `y` whose structure morphism is quasi-finite at `t`, by
`isQuasiFiniteAt_comp`, the pointwise form of Stacks 03XK that the source appeals to.

Purity above `y` is written out in the hypothesis rather than named: the condition stated there
is `AlgebraicGeometry.Space.IsPureAbove` of Stacks 0CVD part (1), definitionally and on the
nose, so a consumer holding that predicate may pass it directly. -/
@[stacks 0CVF]
theorem isPureAbove_baseChange_of_isQuasiFiniteAt (P : PrePureSituation.{u, u} B S hS)
    (c : PointedOver P)
    (hqf : IsQuasiFiniteAt B S hS c.g c.y')
    (hP : ∀ D : ImpurityDiagram P, IsQuasiFiniteAt B S hS D.g D.t → ¬ D.IsImpurity) :
    IsPureAbove c.baseChange := by
  intro E hqfE hE
  refine hP _ ?_ ((c.isImpurity_alongBaseChange_iff E).mpr hE)
  refine isQuasiFiniteAt_comp B S hS c.hY' P.hY E.g c.g E.t hqfE ?_
  rw [E.mapsToChosenPoint]
  exact hqf

/-! ### Base change along an unpointed morphism of bases, and the relative form of Stacks 0CVE

The closing clause of Stacks 0CVE compares universal purity relative to `Y` with purity of
*every* base change `F_{Y'}` relative to `Y'`, so the base change is taken along a morphism
`Y' ⟶ Y` carrying no point. The construction is the pointed one with the requirement on the
point dropped: a point `y'` of `Y'` is always a point above its own image, so moving the chosen
point of the situation to `g(y')` turns `(Y', y')` into a pointed algebraic space over it.
-/

/-- **The base change of the situation along an unpointed morphism of bases.** For a morphism
`g : Y' ⟶ Y` of algebraic spaces and a point `y'` of `Y'`, this is the situation of Stacks 0CV6
on the fibre product `X' = Y' ×_Y X` over `Y'`, with the pullback of `F` and chosen point `y'`.

A situation carries a chosen point, so one has to be supplied; `y'` lies above `g(y')` by
construction, so this is `AlgebraicGeometry.Space.PointedOver.baseChange` for the situation
whose chosen point has been moved to `g(y')`, and nothing new. The notions of Stacks 0CVD that
quantify over all points of the base do not see which point was supplied, by
`AlgebraicGeometry.Space.isPureRelative_baseChangeAlong_iff`. -/
@[reducible] noncomputable def PrePureSituation.baseChangeAlong
    (P : PrePureSituation.{u, u} B S hS) {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY' : IsAlgebraicSpace B S hS Y') (g : Y' ⟶ P.Y) (y' : points B S hS Y') :
    PrePureSituation.{u, u} B S hS :=
  PointedOver.baseChange (P := { P with y := pointsMap B S hS Y' g y' })
    { Y' := Y'
      hY' := hY'
      g := g
      y' := y'
      mapsPoint := rfl }

/-- **The base change along a morphism of pointed algebraic spaces is the base change along its
underlying morphism of bases**, taken at the chosen point of `Y'`. Both are the same situation
on `X' = Y' ×_Y X`: no field of
`AlgebraicGeometry.Space.PointedOver.baseChange` reads the chosen point of `Y` or the
compatibility of `y'` with it. -/
theorem PointedOver.baseChange_eq_baseChangeAlong {P : PrePureSituation.{u, u} B S hS}
    (c : PointedOver P) : c.baseChange = P.baseChangeAlong c.hY' c.g c.y' :=
  rfl

/-- **Stacks 0CVD, part (5), for a base change along an unpointed morphism `g : Y' ⟶ Y`.** The
base change `F_{Y'}` is *pure relative to `Y'`* when it is pure above every point of `Y'`.

Each point of `Y'` is at once the point at which the base change is formed and the point above
which purity is asserted; that this is `AlgebraicGeometry.Space.IsPureRelative` of the base
change is `AlgebraicGeometry.Space.isPureRelative_baseChangeAlong_iff`. -/
def PrePureSituation.IsPureRelativeAlong (P : PrePureSituation.{u, u} B S hS)
    {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY' : IsAlgebraicSpace B S hS Y')
    (g : Y' ⟶ P.Y) : Prop :=
  ∀ y' : points B S hS Y', IsPureAbove (P.baseChangeAlong hY' g y')

/-- **Relative purity of the base change does not depend on the point at which the base change
was formed, and is purity of the base change relative to `Y'`.** The two sides are the same
family of conditions: `AlgebraicGeometry.Space.IsPureRelative` varies the chosen point of the
base over all of `|Y'|`, and the chosen point is the only field of the base change that the
supplied point occupies. -/
theorem isPureRelative_baseChangeAlong_iff (P : PrePureSituation.{u, u} B S hS)
    {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY' : IsAlgebraicSpace B S hS Y')
    (g : Y' ⟶ P.Y) (y' : points B S hS Y') :
    IsPureRelative (P.baseChangeAlong hY' g y') ↔ P.IsPureRelativeAlong hY' g :=
  Iff.rfl

/-- **Stacks 0CVE, the closing clause.** The module is universally pure relative to `Y` exactly
when, for every morphism `Y' ⟶ Y` of algebraic spaces, its base change `F_{Y'}` is pure
relative to `Y'`.

This is formal, as the source says, and is the pointwise equivalence
`AlgebraicGeometry.Space.isUniversallyPureAbove_iff_forall_baseChange_isPureAbove` read at every
point of the base at once: a pointed morphism `(Y', y') ⟶ (Y, y)` is a morphism `Y' ⟶ Y`
together with a point `y'` of `Y'` whose image is `y`, and the two sides quantify over all `y`
and all such `y'` in the two possible orders. -/
@[stacks 0CVE "the 'in particular' clause: universally pure relative to Y iff every base \
change is pure relative to Y'"]
theorem isUniversallyPureRelative_iff_forall_baseChange_isPureRelative
    (P : PrePureSituation.{u, u} B S hS) :
    IsUniversallyPureRelative P ↔
      ∀ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY' : IsAlgebraicSpace B S hS Y')
        (g : Y' ⟶ P.Y), P.IsPureRelativeAlong hY' g :=
  ⟨fun hP Y' hY' g y' => (isUniversallyPureAbove_iff_forall_baseChange_isPureAbove
      { P with y := pointsMap B S hS Y' g y' }).mp (hP _)
      { Y' := Y', hY' := hY', g := g, y' := y', mapsPoint := rfl },
    fun hAll y => (isUniversallyPureAbove_iff_forall_baseChange_isPureAbove
      { P with y := y }).mpr fun c => hAll c.Y' c.hY' c.g c.y'⟩

end AlgebraicGeometry.Space

end
