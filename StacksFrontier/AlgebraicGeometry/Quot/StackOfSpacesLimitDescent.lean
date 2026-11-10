module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatFamilyCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineSystemSiteConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SiteConventionDescentInputs
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent

/-!
# Descent of finitely presented, flat and proper families along limits of affine schemes

Let `T = lim Tᵢ` be the limit, in schemes, of a cofiltered inverse system of affine objects of the
big fppf site of `S`, with `T` in the site: the situation of Stacks 07XL. This file proves, for the
category `Spaces'_{fp, flat, proper}` of Stacks 0D1D, the three stage-descent conditions
`Deformation.Artin.DescentObj`, `Deformation.Artin.DescentHom` and `Deformation.Artin.DescentEq`,
which together make the comparison functor `colim Spaces'_{Tᵢ} ⥤ Spaces'_T` of Stacks 07XL an
equivalence.

The argument is that of Stacks 0D1I. The represented presheaves `yoneda Tᵢ` form an
inverse system of quasi-compact, quasi-separated algebraic spaces with affine transition morphisms
whose limit is `yoneda T`, and which satisfies the convention of Section 70.2 (tag 07SD) by
`AlgebraicGeometry.Space.siteContainsBaseChangeLimits_of_isLimit`. Stacks 07SK then says that the
category of algebraic spaces of finite presentation over `T` is the colimit of those over the
`Tᵢ`, and flatness and properness descend through the limit by Stacks 08K0 and 08K1.

Those three results enter in the form in which they hold under the convention, with no bound on
the index: the propositions `AlgebraicGeometry.Space.ModelsDescendUnderConvention`,
`AlgebraicGeometry.Space.MorphismsDescendUnderConvention`,
`AlgebraicGeometry.Space.EqualitiesDescendUnderConvention` and
`AlgebraicGeometry.Space.PropertyDescendsUnderConvention`, taken here as arguments.

## Main results

* `AlgebraicGeometry.StackOfSpacesLimit.descentObj`: descent of objects of
  `Spaces'_{fp, flat, proper}` to a stage.
* `AlgebraicGeometry.StackOfSpacesLimit.descentHom`: descent of morphisms to a stage.
* `AlgebraicGeometry.StackOfSpacesLimit.descentEq`: descent of equalities of morphisms to a stage.

## Implementation notes

All the bookkeeping is done with explicit pullbacks of presheaves. For a family `X ⟶ Tᵢ` and a
morphism `q : Z ⟶ Tᵢ`, the base change is `pullback f q`; a morphism `q' : Z' ⟶ Z` over `Tᵢ`
induces the transition `pullback f (q' ≫ q) ⟶ pullback f q`, which is
`CategoryTheory.Limits.pullback.map` with identities, and exhibits the first as a base change of
the second. A morphism between two base changes along `q` restricts along `q'`.

## References

* [Stacks Project, Tag 0D1I](https://stacks.math.columbia.edu/tag/0D1I)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.StackOfSpacesLimit

/-! ### Transitions between base changes -/

section PullbackAlgebra

variable {C : Type*} [Category* C] [HasPullbacks C]

/-- The transition `pullback f q'' ⟶ pullback f q` induced by `q' : Z' ⟶ Z` with
`q' ≫ q = q''`. -/
abbrev trans {X A Z Z' : C} (f : X ⟶ A) {q : Z ⟶ A} {q'' : Z' ⟶ A} (q' : Z' ⟶ Z)
    (h : q' ≫ q = q'') : pullback f q'' ⟶ pullback f q :=
  pullback.map f q'' f q (𝟙 X) q' (𝟙 A) (by simp) (by simp [h])

/-- The transition commutes with the first projections. -/
@[reassoc (attr := simp)]
theorem trans_fst {X A Z Z' : C} (f : X ⟶ A) {q : Z ⟶ A} {q'' : Z' ⟶ A} (q' : Z' ⟶ Z)
    (h : q' ≫ q = q'') : trans f q' h ≫ pullback.fst f q = pullback.fst f q'' := by
  simp [trans]

/-- The second projection of the transition is the second projection followed by `q'`. -/
@[reassoc (attr := simp)]
theorem trans_snd {X A Z Z' : C} (f : X ⟶ A) {q : Z ⟶ A} {q'' : Z' ⟶ A} (q' : Z' ⟶ Z)
    (h : q' ≫ q = q'') : trans f q' h ≫ pullback.snd f q = pullback.snd f q'' ≫ q' := by
  simp [trans]

/-- The transition exhibits `pullback f q''` as the base change of `pullback f q` along `q'`. -/
theorem isPullback_trans {X A Z Z' : C} (f : X ⟶ A) {q : Z ⟶ A} {q'' : Z' ⟶ A} (q' : Z' ⟶ Z)
    (h : q' ≫ q = q'') :
    IsPullback (trans f q' h) (pullback.snd f q'') (pullback.snd f q) q' :=
  IsPullback.of_right (h₁₂ := pullback.fst f q) (h₂₂ := q) (v₁₃ := f)
    (by rw [trans_fst, h]; exact IsPullback.of_hasPullback f q'') (trans_snd f q' h)
    (IsPullback.of_hasPullback f q)

/-- The transition along `b` followed by the transition along `a` is the transition along
`b ≫ a`. -/
theorem trans_trans {X A Z Z' Z'' : C} (f : X ⟶ A) {q : Z ⟶ A} {q' : Z' ⟶ A} {q'' : Z'' ⟶ A}
    (a : Z' ⟶ Z) (b : Z'' ⟶ Z') (ha : a ≫ q = q') (hb : b ≫ q' = q'') :
    trans f b hb ≫ trans f a ha = trans f (b ≫ a) (by rw [Category.assoc, ha, hb]) := by
  apply pullback.hom_ext <;> simp

/-- Transitions along equal morphisms are equal. -/
theorem trans_congr {X A Z Z' : C} (f : X ⟶ A) {q : Z ⟶ A} {q'' : Z' ⟶ A} {a b : Z' ⟶ Z}
    (hab : a = b) (ha : a ≫ q = q'') (hb : b ≫ q = q'') : trans f a ha = trans f b hb := by
  subst hab
  rfl

/-- A morphism between two base changes along `q`, over `Z`, restricted along `q'`. -/
def restr {X Y A Z Z' : C} {f : X ⟶ A} {g : Y ⟶ A} {q : Z ⟶ A} {q'' : Z' ⟶ A}
    (v : pullback f q ⟶ pullback g q) (hv : v ≫ pullback.snd g q = pullback.snd f q)
    (q' : Z' ⟶ Z) (h : q' ≫ q = q'') : pullback f q'' ⟶ pullback g q'' :=
  pullback.lift (trans f q' h ≫ v ≫ pullback.fst g q) (pullback.snd f q'') (by
    rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hv, trans_snd_assoc, h])

/-- The restriction is a morphism over `Z'`. -/
@[reassoc (attr := simp)]
theorem restr_snd {X Y A Z Z' : C} {f : X ⟶ A} {g : Y ⟶ A} {q : Z ⟶ A} {q'' : Z' ⟶ A}
    (v : pullback f q ⟶ pullback g q) (hv : v ≫ pullback.snd g q = pullback.snd f q)
    (q' : Z' ⟶ Z) (h : q' ≫ q = q'') : restr v hv q' h ≫ pullback.snd g q'' = pullback.snd f q'' :=
  pullback.lift_snd _ _ _

/-- The first projection of the restriction is the transition followed by the morphism and the
first projection. -/
@[reassoc (attr := simp)]
theorem restr_fst {X Y A Z Z' : C} {f : X ⟶ A} {g : Y ⟶ A} {q : Z ⟶ A} {q'' : Z' ⟶ A}
    (v : pullback f q ⟶ pullback g q) (hv : v ≫ pullback.snd g q = pullback.snd f q)
    (q' : Z' ⟶ Z) (h : q' ≫ q = q'') :
    restr v hv q' h ≫ pullback.fst g q'' = trans f q' h ≫ v ≫ pullback.fst g q :=
  pullback.lift_fst _ _ _

/-- The restriction commutes with the transitions. -/
@[reassoc]
theorem restr_trans {X Y A Z Z' : C} {f : X ⟶ A} {g : Y ⟶ A} {q : Z ⟶ A} {q'' : Z' ⟶ A}
    (v : pullback f q ⟶ pullback g q) (hv : v ≫ pullback.snd g q = pullback.snd f q)
    (q' : Z' ⟶ Z) (h : q' ≫ q = q'') :
    restr v hv q' h ≫ trans g q' h = trans f q' h ≫ v := by
  apply pullback.hom_ext
  · simp
  · simp [hv]

/-- A morphism of base changes along `q''` over `Z'` commuting with the transitions is the
restriction. -/
theorem eq_restr {X Y A Z Z' : C} {f : X ⟶ A} {g : Y ⟶ A} {q : Z ⟶ A} {q'' : Z' ⟶ A}
    (v : pullback f q ⟶ pullback g q) (hv : v ≫ pullback.snd g q = pullback.snd f q)
    (q' : Z' ⟶ Z) (h : q' ≫ q = q'') (w : pullback f q'' ⟶ pullback g q'')
    (hw : w ≫ pullback.snd g q'' = pullback.snd f q'')
    (hwt : w ≫ trans g q' h = trans f q' h ≫ v) : w = restr v hv q' h := by
  apply pullback.hom_ext
  · rw [restr_fst, ← reassoc_of% hwt, trans_fst]
  · rw [hw, restr_snd]

/-- Two morphisms of base changes along `q` that agree after the transition have the same
restriction. -/
theorem restr_congr {X Y A Z Z' : C} {f : X ⟶ A} {g : Y ⟶ A} {q : Z ⟶ A} {q'' : Z' ⟶ A}
    {v v' : pullback f q ⟶ pullback g q} (hv : v ≫ pullback.snd g q = pullback.snd f q)
    (hv' : v' ≫ pullback.snd g q = pullback.snd f q)
    (q' : Z' ⟶ Z) (h : q' ≫ q = q'') (H : trans f q' h ≫ v = trans f q' h ≫ v') :
    restr v hv q' h = restr v' hv' q' h := by
  apply pullback.hom_ext
  · rw [restr_fst, restr_fst, reassoc_of% H]
  · rw [restr_snd, restr_snd]

/-- Restriction along `q'` is compatible with composition. -/
theorem restr_comp {X Y W A Z Z' : C} {f : X ⟶ A} {g : Y ⟶ A} {k : W ⟶ A} {q : Z ⟶ A}
    {q'' : Z' ⟶ A}
    (v : pullback f q ⟶ pullback g q) (hv : v ≫ pullback.snd g q = pullback.snd f q)
    (v' : pullback g q ⟶ pullback k q) (hv' : v' ≫ pullback.snd k q = pullback.snd g q)
    (q' : Z' ⟶ Z) (h : q' ≫ q = q'') :
    restr v hv q' h ≫ restr v' hv' q' h =
      restr (v ≫ v') (by rw [Category.assoc, hv', hv]) q' h :=
  eq_restr _ _ _ _ _ (by simp) (by rw [Category.assoc, restr_trans, restr_trans_assoc])

/-- The restriction of the identity is the identity. -/
theorem restr_id {X A Z Z' : C} {f : X ⟶ A} {q : Z ⟶ A} {q'' : Z' ⟶ A}
    (q' : Z' ⟶ Z) (h : q' ≫ q = q'') :
    restr (𝟙 (pullback f q)) (Category.id_comp _) q' h = 𝟙 _ :=
  (eq_restr _ _ _ _ _ (Category.id_comp _) (by simp)).symm

/-- A morphism `v` of base changes along `πi`, compatible with `g'` after the transition along `πj`,
is compatible with the restriction of `g'` along `a` after the transition along `πk`. -/
private theorem comp_trans_eq_trans_restr {X Y A L Zj Zk : C} {f : X ⟶ A} {g : Y ⟶ A}
    {ε : Zj ⟶ A} {qs : Zk ⟶ A} {πi : L ⟶ A} {πj : L ⟶ Zj} {πk : L ⟶ Zk} (a : Zk ⟶ Zj)
    (hj : πj ≫ ε = πi) (hk : πk ≫ a = πj) (hs : a ≫ ε = qs) (hi : πk ≫ qs = πi)
    (v : pullback f πi ⟶ pullback g πi) (hv : v ≫ pullback.snd g πi = pullback.snd f πi)
    (g' : pullback f ε ⟶ pullback g ε) (hg' : g' ≫ pullback.snd g ε = pullback.snd f ε)
    (hr : v ≫ trans g πj hj = trans f πj hj ≫ g') :
    v ≫ trans g πk hi = trans f πk hi ≫ restr g' hg' a hs := by
  have ht : trans f πk hi ≫ trans f a hs = trans f πj hj := by
    rw [trans_trans f a πk hs hi]
    exact trans_congr f hk _ _
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, trans_fst, restr_fst, reassoc_of% ht, ← reassoc_of% hr,
      trans_fst]
  · rw [Category.assoc, trans_snd, reassoc_of% hv, Category.assoc, restr_snd, trans_snd]

/-- The canonical comparison of `AlgebraicGeometry.Space.MorphismsDescendUnderConvention` is
pinned down by its inverse: composed with the first projection it is the transition. -/
theorem inv_left_fst {L Aj A : C} (Y : Over A) {πi : L ⟶ A} (πj : L ⟶ Aj) {ε : Aj ⟶ A}
    (h : πj ≫ ε = πi)
    (α : (Over.pullback πj).obj ((Over.pullback ε).obj Y) ≅ (Over.pullback πi).obj Y)
    (hα : α.hom.left ≫ pullback.fst Y.hom πi =
      pullback.fst ((Over.pullback ε).obj Y).hom πj ≫ pullback.fst Y.hom ε) :
    α.inv.left ≫ pullback.fst ((Over.pullback ε).obj Y).hom πj = trans Y.hom πj h := by
  apply pullback.hom_ext
  · rw [Category.assoc, trans_fst, ← hα, ← Category.assoc, ← Over.comp_left, α.inv_hom_id]
    simp
  · have hc : pullback.fst ((Over.pullback ε).obj Y).hom πj ≫ ((Over.pullback ε).obj Y).hom =
        pullback.snd ((Over.pullback ε).obj Y).hom πj ≫ πj := pullback.condition
    have hw : α.inv.left ≫ pullback.snd ((Over.pullback ε).obj Y).hom πj =
        pullback.snd Y.hom πi := Over.w α.inv
    rw [Category.assoc]
    calc α.inv.left ≫ pullback.fst ((Over.pullback ε).obj Y).hom πj ≫ pullback.snd Y.hom ε
        = α.inv.left ≫ pullback.snd ((Over.pullback ε).obj Y).hom πj ≫ πj :=
          congrArg (α.inv.left ≫ ·) hc
      _ = pullback.snd Y.hom πi ≫ πj := by rw [← Category.assoc, hw]
      _ = trans Y.hom πj h ≫ pullback.snd Y.hom ε := (trans_snd _ _ _).symm

end PullbackAlgebra

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits in presheaves on the big fppf site
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_StackOfSpacesLimitDescent {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_StackOfSpacesLimitDescent
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits in presheaves on the big fppf site
/-- Discrete limits of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_StackOfSpacesLimitDescent
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (K : Type) :
    HasLimitsOfShape (Discrete K) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-! ### The system of represented presheaves of a system of affine schemes -/

section Setting

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {J : Type u} [Category.{u} J] [IsCofiltered J]
  (D : J ⥤ BigAffineFppf B S hS) {c : Cone D}
  (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))

/-- The system of presheaves represented by the stages. -/
abbrev sys : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  D ⋙ BigAffineFppf.inclusion B S hS ⋙ yoneda

include hc in
/-- The cone is a limit cone in the big fppf site. -/
def isLimitInclusion : IsLimit ((BigAffineFppf.inclusion B S hS).mapCone c) := by
  haveI : IsConnected J := IsCofiltered.isConnected J
  exact isLimitOfReflects (Over.forget (B.obj hS))
    (isLimitOfReflects B.inclusion hc)

/-- The represented presheaf of the limit is the limit of the represented presheaves. -/
def limitIso : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj c.pt) ≅ limit (sys D) :=
  (isLimitOfPreserves yoneda (isLimitInclusion D hc)).conePointUniqueUpToIso (limit.isLimit _)

/-- The comparison `limitIso` followed by a limit projection is the represented cone
projection. -/
@[reassoc (attr := simp)]
theorem limitIso_hom_π (i : J) :
    (limitIso D hc).hom ≫ limit.π (sys D) i =
      yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ i

variable (B S hS) in
/-- The presheaf represented by an affine object of the site is an algebraic space. -/
theorem isAlgebraicSpace_yoneda_affine (V : BigAffineFppf B S hS) :
    IsAlgebraicSpace B S hS (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V)) :=
  isAlgebraicSpace_yoneda B S hS _

omit [IsCofiltered J] in
/-- The transition morphisms of the system of represented presheaves are affine. -/
theorem isAffineHom_sys {i j : J} (f : i ⟶ j) : Space.IsAffineHom B S hS ((sys D).map f) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) := (D.obj i).property
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj (D.obj j))) := (D.obj j).property
  exact Space.isAffineHom_yoneda_map B S hS _

variable (B S hS) in
/-- The presheaf represented by an affine object of the site is quasi-compact. -/
theorem isQuasiCompactSpace_yoneda_affine (V : BigAffineFppf B S hS) :
    Space.IsQuasiCompactSpace B S hS (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V)) :=
  Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS _ V.property

variable (B S hS) in
/-- The presheaf represented by an affine object of the site is quasi-separated over
`Spec ℤ`. -/
theorem isAbsolutelyQuasiSeparated_yoneda_affine (hZ : B.Contains (⊤_ Scheme.{u}))
    (V : BigAffineFppf B S hS) :
    Space.IsAbsolutelyQuasiSeparated B S hS hZ
      (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V)) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj V)) := V.property
  exact Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS _ hZ
    ⟨_, inferInstance, ⟨Functor.RepresentableBy.yoneda _⟩⟩

include hc in
/-- The limit of the system of represented presheaves is an algebraic space. -/
theorem isAlgebraicSpace_limit_sys : IsAlgebraicSpace B S hS (limit (sys D)) :=
  (isAlgebraicSpace_yoneda B S hS _).of_iso (limitIso D hc)

/-- The represented cone projections are compatible with the transitions of the system. -/
private theorem yoneda_map_π_comp_sys_map {J : Type u} [Category.{u} J]
    (D : J ⥤ BigAffineFppf B S hS) (c : Cone D) {i k : J} (s : k ⟶ i) :
    yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app k)) ≫ (sys D).map s =
      yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) := by
  change yoneda.map _ ≫ yoneda.map ((BigAffineFppf.inclusion B S hS).map (D.map s)) = _
  rw [← Functor.map_comp, ← Functor.map_comp, c.w s]

/-- The base change of an algebraic space along a map of stages is an algebraic space. -/
private theorem isAlgebraicSpace_pullback_sys {J : Type u} [Category.{u} J]
    (D : J ⥤ BigAffineFppf B S hS) {i k : J} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ (sys D).obj i) (q : (sys D).obj k ⟶ (sys D).obj i) (hX : IsAlgebraicSpace B S hS X) :
    IsAlgebraicSpace B S hS (pullback f q) :=
  isAlgebraicSpace_pullback B S hS _ _ hX (isAlgebraicSpace_yoneda_affine B S hS _)
    (isAlgebraicSpace_yoneda_affine B S hS _)

/-- The base change of a finitely presented morphism along a map of stages is finitely presented. -/
private theorem isFinitePresentation_snd_sys {J : Type u} [Category.{u} J]
    (D : J ⥤ BigAffineFppf B S hS) {i k : J} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ (sys D).obj i} (q : (sys D).obj k ⟶ (sys D).obj i) (hX : IsAlgebraicSpace B S hS X)
    (hf : Space.IsFinitePresentation B S hS f) :
    Space.IsFinitePresentation B S hS (pullback.snd f q) :=
  Space.IsFinitePresentation.of_isPullback B S hS (isAlgebraicSpace_pullback_sys D f q hX) hX
    (isAlgebraicSpace_yoneda_affine B S hS _) (isAlgebraicSpace_yoneda_affine B S hS _)
    (IsPullback.of_hasPullback f q) hf

end Setting

/-! ### The descent results, read for the system of represented presheaves -/

section Inputs

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))
  {J : Type u} [Category.{u} J] [IsCofiltered J]
  (D : J ⥤ BigAffineFppf B S hS) {c : Cone D}
  (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))

include hc in
/-- Stacks 07SK, essential surjectivity, for the system of represented presheaves. -/
theorem exists_model (hM : Space.ModelsDescendUnderConvention B S hS hZ)
    (Y : Over (limit (sys D))) (hY : IsAlgebraicSpace B S hS Y.left)
    (hFp : Space.IsFinitePresentation B S hS Y.hom) :
    ∃ (i : J) (Yᵢ : Over ((sys D).obj i)),
      IsAlgebraicSpace B S hS Yᵢ.left ∧ Space.IsFinitePresentation B S hS Yᵢ.hom ∧
        Nonempty (Y ≅ (Over.pullback (limit.π (sys D) i)).obj Yᵢ) :=
  hM J (sys D) (fun i => isAlgebraicSpace_yoneda_affine B S hS (D.obj i))
    (fun f => isAffineHom_sys D f) (fun i => isQuasiCompactSpace_yoneda_affine B S hS (D.obj i))
    (fun i => isAbsolutelyQuasiSeparated_yoneda_affine B S hS hZ (D.obj i))
    (Space.siteContainsBaseChangeLimits_of_isLimit D hc) Y hY hFp

include hc in
/-- Stacks 07SK, fullness, for the system of represented presheaves, read with explicit
pullbacks: a morphism over the limit between base changes of two families at a stage `i`
is, after the transitions, a morphism over a later stage. -/
theorem exists_stage_hom (hF : Space.MorphismsDescendUnderConvention B S hS hZ) (i : J)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (fX : X ⟶ (sys D).obj i) (fY : Y ⟶ (sys D).obj i)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXfp : Space.IsFinitePresentation B S hS fX) (hYfp : Space.IsFinitePresentation B S hS fY)
    (v : pullback fX (limit.π (sys D) i) ⟶ pullback fY (limit.π (sys D) i))
    (hv : v ≫ pullback.snd fY _ = pullback.snd fX _) :
    ∃ (j : J) (e : j ⟶ i) (w : pullback fX ((sys D).map e) ⟶ pullback fY ((sys D).map e)),
      w ≫ pullback.snd fY _ = pullback.snd fX _ ∧
        v ≫ trans fY (limit.π (sys D) j) (limit.w (sys D) e) =
          trans fX (limit.π (sys D) j) (limit.w (sys D) e) ≫ w := by
  obtain ⟨j, e, g, α, β, hα, hβ, hrel⟩ := hF J (sys D)
    (fun i => isAlgebraicSpace_yoneda_affine B S hS (D.obj i))
    (fun f => isAffineHom_sys D f) (fun i => isQuasiCompactSpace_yoneda_affine B S hS (D.obj i))
    (fun i => isAbsolutelyQuasiSeparated_yoneda_affine B S hS hZ (D.obj i))
    (Space.siteContainsBaseChangeLimits_of_isLimit D hc) i (Over.mk fX) (Over.mk fY)
    hX hY hXfp hYfp (Over.homMk (V := (Over.pullback (limit.π (sys D) i)).obj (Over.mk fY)) v hv)
  refine ⟨j, e, g.left, Over.w g, ?_⟩
  have hαinv := inv_left_fst (Over.mk fX) (limit.π (sys D) j) (limit.w (sys D) e) α hα
  have hβinv := inv_left_fst (Over.mk fY) (limit.π (sys D) j) (limit.w (sys D) e) β hβ
  have hrel' : (Over.homMk (V := (Over.pullback (limit.π (sys D) i)).obj (Over.mk fY)) v hv) ≫
      β.inv = α.inv ≫ (Over.pullback (limit.π (sys D) j)).map g := by
    rw [Iso.comp_inv_eq, Category.assoc, ← hrel, Iso.inv_hom_id_assoc]
  have h := congrArg (fun φ => φ.left ≫ pullback.fst
    ((Over.pullback ((sys D).map e)).obj (Over.mk fY)).hom (limit.π (sys D) j)) hrel'
  simp only [Over.comp_left, Over.homMk_left, Category.assoc, Over.pullback_map_left,
    pullback.lift_fst] at h
  rwa [hβinv, ← Category.assoc, hαinv] at h

include hc in
/-- Stacks 07SK, faithfulness, for the system of represented presheaves, read with explicit
pullbacks. -/
theorem exists_stage_eq (hE : Space.EqualitiesDescendUnderConvention B S hS hZ) (i : J)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (fX : X ⟶ (sys D).obj i) (fY : Y ⟶ (sys D).obj i)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXfp : Space.IsFinitePresentation B S hS fX) (hYfp : Space.IsFinitePresentation B S hS fY)
    (ψ ψ' : X ⟶ Y) (hψ : ψ ≫ fY = fX) (hψ' : ψ' ≫ fY = fX)
    (heq : pullback.fst fX (limit.π (sys D) i) ≫ ψ = pullback.fst fX (limit.π (sys D) i) ≫ ψ') :
    ∃ (j : J) (e : j ⟶ i),
      pullback.fst fX ((sys D).map e) ≫ ψ = pullback.fst fX ((sys D).map e) ≫ ψ' := by
  obtain ⟨j, e, h⟩ := hE J (sys D)
    (fun i => isAlgebraicSpace_yoneda_affine B S hS (D.obj i))
    (fun f => isAffineHom_sys D f) (fun i => isQuasiCompactSpace_yoneda_affine B S hS (D.obj i))
    (fun i => isAbsolutelyQuasiSeparated_yoneda_affine B S hS hZ (D.obj i))
    (Space.siteContainsBaseChangeLimits_of_isLimit D hc) i (Over.mk fX) (Over.mk fY)
    hX hY hXfp hYfp (Over.homMk ψ hψ) (Over.homMk ψ' hψ') (by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · simp only [Over.pullback_map_left, pullback.lift_fst]
        exact heq
      · exact (Over.w ((Over.pullback (limit.π (sys D) i)).map
          (Over.homMk (U := Over.mk fX) (V := Over.mk fY) ψ hψ))).trans
          (Over.w ((Over.pullback (limit.π (sys D) i)).map
            (Over.homMk (U := Over.mk fX) (V := Over.mk fY) ψ' hψ'))).symm)
  refine ⟨j, e, ?_⟩
  have h' := congrArg (fun φ => φ.left ≫ pullback.fst (Over.mk fY).hom ((sys D).map e)) h
  simp only [Over.pullback_map_left, pullback.lift_fst, Over.homMk_left] at h'
  exact h'

end Inputs

/-! ### Descent of a property of morphisms to a stage -/

section PropertyDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))
  {J : Type u} [Category.{u} J] [IsCofiltered J]
  (D : J ⥤ BigAffineFppf B S hS) {c : Cone D}
  (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))

/-- A property of morphisms of presheaves which passes to base changes between algebraic
spaces. -/
def BaseChangeStable (P : ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, (X ⟶ Y) → Prop) : Prop :=
  ∀ {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
    {g : Y' ⟶ Y}, IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS X →
    IsAlgebraicSpace B S hS Y' → IsAlgebraicSpace B S hS Y → IsPullback g' f' f g → P f → P f'

omit [IsCofiltered J] in
/-- Two base changes of the same morphism along the same morphism share every base-change stable
property. -/
theorem of_isPullback_same {P : ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, (X ⟶ Y) → Prop}
    (hP : BaseChangeStable P) {X₁ X₂ X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a₁ : X₁ ⟶ X} {f₁ : X₁ ⟶ Y'} {a₂ : X₂ ⟶ X} {f₂ : X₂ ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h₁ : IsPullback a₁ f₁ f g) (h₂ : IsPullback a₂ f₂ f g)
    (hX₂ : IsAlgebraicSpace B S hS X₂) (hX₁ : IsAlgebraicSpace B S hS X₁)
    (hY' : IsAlgebraicSpace B S hS Y') (hP₁ : P f₁) : P f₂ := by
  let e := h₂.isoIsPullback _ _ h₁
  refine hP hX₂ hX₁ hY' hY' (g' := e.hom) (g := 𝟙 Y') ?_ hP₁
  refine IsPullback.of_horiz_isIso ⟨?_⟩
  rw [Category.comp_id]
  exact h₂.isoIsPullback_hom_snd _ _ h₁

include hc in
/-- **Descent of a property to a stage.** If the propositions
`AlgebraicGeometry.Space.PropertyDescendsUnderConvention P H` hold, then for a finitely presented
morphism `fX : X ⟶ Tᵢ` from an algebraic space with `H fX` whose base change to the limit has `P`,
the base change to some later stage has `P`. -/
theorem exists_stage_prop {P H : ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, (X ⟶ Y) → Prop}
    (hdesc : Space.PropertyDescendsUnderConvention B S hS hZ P H)
    (hP : BaseChangeStable P) (hH : BaseChangeStable H)
    (i : J) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (fX : X ⟶ (sys D).obj i)
    (hX : IsAlgebraicSpace B S hS X) (hXfp : Space.IsFinitePresentation B S hS fX)
    (hHX : H fX) (hPL : P (pullback.snd fX (limit.π (sys D) i))) :
    ∃ (j : J) (e : j ⟶ i), P (pullback.snd fX ((sys D).map e)) := by
  classical
  obtain ⟨α, hαOrder, hαDirected, hαNonempty, F, hF⟩ := IsFiltered.exists_directed ((Over i)ᵒᵖ)
  let _ : PartialOrder α := hαOrder
  have _ : IsDirected α (· ≤ ·) := hαDirected
  have _ : Nonempty α := hαNonempty
  let G : αᵒᵖ ⥤ Over i := F.leftOp
  let Dα : αᵒᵖ ⥤ BigAffineFppf B S hS := G ⋙ Over.forget i ⋙ D
  let cα : Cone Dα := c.whisker (G ⋙ Over.forget i)
  have hcα : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone cα) :=
    (Functor.Initial.isLimitWhiskerEquiv (G ⋙ Over.forget i) _).symm hc
  let E := sys D
  let a₀ : α := Classical.arbitrary α
  let k₀ : Over i := G.obj (op a₀)
  let q := E.map k₀.hom
  have halg : ∀ V : BigAffineFppf B S hS,
      IsAlgebraicSpace B S hS (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V)) :=
    isAlgebraicSpace_yoneda_affine B S hS
  have hX₀ : IsAlgebraicSpace B S hS (pullback fX q) := isAlgebraicSpace_pullback_sys D _ _ hX
  have hf₀fp := isFinitePresentation_snd_sys D q hX hXfp
  have hLα := isAlgebraicSpace_limit_sys Dα hcα
  have hL := isAlgebraicSpace_limit_sys D hc
  let φ : limit (sys Dα) ⟶ limit E := (limitIso Dα hcα).inv ≫ (limitIso D hc).hom
  have hφ : limit.π (sys Dα) (op a₀) ≫ q = φ ≫ limit.π E i := by
    have h1 : limit.π (sys Dα) (op a₀) =
        (limitIso Dα hcα).inv ≫ yoneda.map ((BigAffineFppf.inclusion B S hS).map
          (c.π.app k₀.left)) := by
      rw [Iso.eq_inv_comp, limitIso_hom_π]
      rfl
    rw [h1, Category.assoc, Category.assoc, limitIso_hom_π]
    congr 1
    exact yoneda_map_π_comp_sys_map D c k₀.hom
  have hPlim : P (pullback.fst (limit.π (sys Dα) (op a₀)) (pullback.snd fX q)) := by
    have h₁ : P (pullback.snd fX (φ ≫ limit.π E i)) :=
      hP (isAlgebraicSpace_pullback B S hS _ _ hX hLα (halg _))
        (isAlgebraicSpace_pullback B S hS _ _ hX hL (halg _)) hLα hL
        (isPullback_trans fX φ rfl) hPL
    exact of_isPullback_same hP (isPullback_trans fX (limit.π (sys Dα) (op a₀)) hφ)
      (IsPullback.of_hasPullback (limit.π (sys Dα) (op a₀)) (pullback.snd fX q)).flip
      (isAlgebraicSpace_pullback B S hS _ _ hLα hX₀ (halg _))
      (isAlgebraicSpace_pullback B S hS _ _ hX hLα (halg _)) hLα h₁
  obtain ⟨a, ha, hPa⟩ := hdesc α (sys Dα) (fun a => halg _) (fun f => isAffineHom_sys Dα f) hLα
    (Space.siteContainsBaseChangeLimits_of_isLimit Dα hcα) a₀ (pullback fX q) (pullback.snd fX q)
    hX₀ (isQuasiCompactSpace_yoneda_affine B S hS _)
    (isAbsolutelyQuasiSeparated_yoneda_affine B S hS hZ _)
    (Space.isQuasiCompactSpace_of_isFinitePresentation B S hS _ (halg _)
      (isQuasiCompactSpace_yoneda_affine B S hS _) hf₀fp)
    (Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hX₀
      (isAbsolutelyQuasiSeparated_yoneda_affine B S hS hZ _) hf₀fp.2.2)
    hPlim (hH hX₀ hX (halg _) (halg _) (IsPullback.of_hasPullback fX q) hHX)
  let k := G.obj (op a)
  let w : k ⟶ k₀ := G.map (homOfLE ha).op
  have hw : E.map w.left ≫ q = E.map k.hom := by
    simp only [q, ← Functor.map_comp, Over.w w]
  exact ⟨k.left, k.hom, of_isPullback_same hP
    (IsPullback.of_hasPullback ((sys Dα).map (homOfLE ha).op) (pullback.snd fX q)).flip
    (isPullback_trans fX (E.map w.left) hw)
    (isAlgebraicSpace_pullback_sys D _ _ hX)
    (isAlgebraicSpace_pullback B S hS _ _ (halg _) hX₀ (halg _)) (halg _) hPa⟩

end PropertyDescent

/-! ### The base-change stable properties used -/

section Stable

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Flatness is stable under base change between algebraic spaces. -/
theorem baseChangeStable_isFlat :
    BaseChangeStable (B := B) (S := S) (hS := hS) (fun f => Space.IsFlat B S hS f) :=
  fun hX' hX hY' hY sq hf => CartesianProperFlatSpaces.isFlat_of_isPullback' hX' hX hY' hY sq hf

/-- Properness is stable under base change between algebraic spaces. -/
theorem baseChangeStable_isProper :
    BaseChangeStable (B := B) (S := S) (hS := hS) (fun f => Space.IsProper B S hS f) :=
  fun hX' hX hY' hY sq hf =>
    CartesianProperFlatSpaces.isProper_of_isPullback' hX' hX hY' hY sq hf

/-- Being locally of finite presentation is stable under base change between algebraic
spaces. -/
theorem baseChangeStable_isLocallyOfFinitePresentation :
    BaseChangeStable (B := B) (S := S) (hS := hS)
      (fun f => Space.IsLocallyOfFinitePresentation B S hS f) :=
  fun hX' hX hY' hY sq hf =>
    (Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
      (Space.isPullback_homMk B S hS hX hY' hY hX' sq) hf

/-- Being locally of finite type is stable under base change between algebraic spaces. -/
theorem baseChangeStable_isLocallyOfFiniteType :
    BaseChangeStable (B := B) (S := S) (hS := hS)
      (fun f => Space.IsLocallyOfFiniteType B S hS f) :=
  fun hX' hX hY' hY sq hf =>
    (Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (Space.isPullback_homMk B S hS hX hY' hY hX' sq) hf

end Stable

/-! ### Descent of families -/

section FamilyDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))
  {J : Type u} [Category.{u} J] [IsCofiltered J]
  (D : J ⥤ BigAffineFppf B S hS) {c : Cone D}
  (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))

include hc in
/-- A cartesian square over a cone projection, read over the limit of the represented
presheaves. -/
theorem isPullback_limit {i : J} {X Xi : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : X ⟶ Xi} {h : X ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj c.pt)}
    {fi : Xi ⟶ (sys D).obj i}
    (sq : IsPullback a h fi (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i)))) :
    IsPullback a (h ≫ (limitIso D hc).hom) fi (limit.π (sys D) i) :=
  sq.of_iso (Iso.refl _) (Iso.refl _) (limitIso D hc) (Iso.refl _) (by simp) (by simp)
    (by simp) (by simp)

include hc in
/-- **Descent of a finitely presented, flat and proper family to a stage** (Stacks 07SK, 08K0,
08K1). Every finitely presented, flat and proper morphism from an algebraic space to `T` is the
base change, along a cone projection, of a finitely presented, flat and proper morphism to a
stage. -/
theorem exists_stage_family (hM : Space.ModelsDescendUnderConvention B S hS hZ)
    (hflat : Space.PropertyDescendsUnderConvention B S hS hZ (fun f => Space.IsFlat B S hS f)
      (fun f => Space.IsLocallyOfFinitePresentation B S hS f))
    (hproper : Space.PropertyDescendsUnderConvention B S hS hZ
      (fun f => Space.IsProper B S hS f) (fun f => Space.IsLocallyOfFiniteType B S hS f))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (h : X ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj c.pt))
    (hfp : Space.IsFinitePresentation B S hS h) (hfl : Space.IsFlat B S hS h)
    (hpr : Space.IsProper B S hS h) :
    ∃ (k : J) (Xk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (fk : Xk ⟶ (sys D).obj k) (a : X ⟶ Xk),
      IsAlgebraicSpace B S hS Xk ∧ Space.IsFinitePresentation B S hS fk ∧
        Space.IsFlat B S hS fk ∧ Space.IsProper B S hS fk ∧
          IsPullback a h fk (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app k))) := by
  classical
  let E := sys D
  let eT := limitIso D hc
  have halg : ∀ V : BigAffineFppf B S hS,
      IsAlgebraicSpace B S hS (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V)) :=
    isAlgebraicSpace_yoneda_affine B S hS
  have hT := isAlgebraicSpace_yoneda B S hS ((BigAffineFppf.inclusion B S hS).obj c.pt)
  have hL := isAlgebraicSpace_limit_sys D hc
  have hsq₀ : IsPullback (𝟙 X) (h ≫ eT.hom) h eT.inv :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have hYfp : Space.IsFinitePresentation B S hS (h ≫ eT.hom) :=
    Space.IsFinitePresentation.of_isPullback B S hS hX hX hL hT hsq₀ hfp
  obtain ⟨i, Yi, hYi, hYifp, ⟨eY⟩⟩ := exists_model hZ D hc hM (Over.mk (h ≫ eT.hom)) hX hYfp
  let eYl : X ≅ pullback Yi.hom (limit.π E i) := (Over.forget _).mapIso eY
  have heYl : eYl.hom ≫ pullback.snd Yi.hom (limit.π E i) = h ≫ eT.hom := Over.w eY.hom
  have hsqL : IsPullback eYl.inv (pullback.snd Yi.hom (limit.π E i)) h eT.inv :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Iso.inv_comp_eq, ← Category.assoc, heYl, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]⟩
  have hpbL : ∀ {P : ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, (X ⟶ Y) → Prop},
      BaseChangeStable P → P h → P (pullback.snd Yi.hom (limit.π E i)) := fun hP hPh =>
    hP (isAlgebraicSpace_pullback B S hS _ _ hYi hL (halg _)) hX hL hT hsqL hPh
  have hsqi : IsPullback (eYl.hom ≫ pullback.fst Yi.hom (limit.π E i)) h Yi.hom
      (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) := by
    refine (IsPullback.of_hasPullback Yi.hom (limit.π E i)).of_iso eYl.symm (Iso.refl _)
      eT.symm (Iso.refl _) (by simp) ?_ (by simp) ?_
    · simp only [Iso.symm_hom]
      rw [Iso.eq_inv_comp, ← Category.assoc, heYl, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      rw [Iso.eq_inv_comp, limitIso_hom_π]
  obtain ⟨j₁, e₁, hfl₁⟩ := exists_stage_prop hZ D hc hflat baseChangeStable_isFlat
    baseChangeStable_isLocallyOfFinitePresentation i Yi.hom hYi hYifp hYifp.1
    (hpbL baseChangeStable_isFlat hfl)
  obtain ⟨j₂, e₂, hpr₂⟩ := exists_stage_prop hZ D hc hproper baseChangeStable_isProper
    baseChangeStable_isLocallyOfFiniteType i Yi.hom hYi hYifp
    (Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hYifp.1)
    (hpbL baseChangeStable_isProper hpr)
  obtain ⟨k, b₁, b₂, hb⟩ := IsCofiltered.cospan e₁ e₂
  let s := b₁ ≫ e₁
  have hs₁ : E.map b₁ ≫ E.map e₁ = E.map s := (E.map_comp _ _).symm
  have hs₂ : E.map b₂ ≫ E.map e₂ = E.map s := by
    rw [← E.map_comp, ← hb]
  have hYk : IsAlgebraicSpace B S hS (pullback Yi.hom (E.map s)) :=
    isAlgebraicSpace_pullback_sys D _ _ hYi
  refine ⟨k, pullback Yi.hom (E.map s), pullback.snd Yi.hom (E.map s),
    pullback.lift (eYl.hom ≫ pullback.fst Yi.hom (limit.π E i))
      (h ≫ yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app k))) ?_,
    hYk, ?_, ?_, ?_, ?_⟩
  · rw [hsqi.w, Category.assoc, yoneda_map_π_comp_sys_map D c s]
  · exact isFinitePresentation_snd_sys D _ hYi hYifp
  · exact baseChangeStable_isFlat hYk (isAlgebraicSpace_pullback_sys D _ _ hYi) (halg _) (halg _)
      (isPullback_trans Yi.hom (E.map b₁) hs₁) hfl₁
  · exact baseChangeStable_isProper hYk (isAlgebraicSpace_pullback_sys D _ _ hYi) (halg _) (halg _)
      (isPullback_trans Yi.hom (E.map b₂) hs₂) hpr₂
  · refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rwa [pullback.lift_fst, yoneda_map_π_comp_sys_map D c s]

end FamilyDescent

/-! ### Descent of isomorphisms -/

section IsoDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))
  {J : Type u} [Category.{u} J] [IsCofiltered J]
  (D : J ⥤ BigAffineFppf B S hS) {c : Cone D}
  (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))

include hc in
/-- **Descent of isomorphisms** (Stacks 07SK, fullness and faithfulness). An isomorphism over the
limit between the base changes of two finitely presented families at a stage `i` is, after the
transitions, an isomorphism over a later stage. -/
theorem exists_stage_iso (hF : Space.MorphismsDescendUnderConvention B S hS hZ)
    (hE : Space.EqualitiesDescendUnderConvention B S hS hZ) (i : J)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (fX : X ⟶ (sys D).obj i) (fY : Y ⟶ (sys D).obj i)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXfp : Space.IsFinitePresentation B S hS fX) (hYfp : Space.IsFinitePresentation B S hS fY)
    (u : pullback fX (limit.π (sys D) i) ≅ pullback fY (limit.π (sys D) i))
    (hu : u.hom ≫ pullback.snd fY _ = pullback.snd fX _) :
    ∃ (k : J) (s : k ⟶ i) (G : pullback fX ((sys D).map s) ≅ pullback fY ((sys D).map s)),
      G.hom ≫ pullback.snd fY _ = pullback.snd fX _ ∧
        u.hom ≫ trans fY (limit.π (sys D) k) (limit.w (sys D) s) =
          trans fX (limit.π (sys D) k) (limit.w (sys D) s) ≫ G.hom := by
  classical
  have halg : ∀ V : BigAffineFppf B S hS,
      IsAlgebraicSpace B S hS (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V)) :=
    isAlgebraicSpace_yoneda_affine B S hS
  have hu' : u.inv ≫ pullback.snd fX _ = pullback.snd fY _ := by
    rw [Iso.inv_comp_eq, hu]
  obtain ⟨j₁, e₁, g₁, hg₁, hr₁⟩ := exists_stage_hom hZ D hc hF i fX fY hX hY hXfp hYfp u.hom hu
  obtain ⟨j₂, e₂, g₂, hg₂, hr₂⟩ := exists_stage_hom hZ D hc hF i fY fX hY hX hYfp hXfp u.inv hu'
  obtain ⟨k, a₁, a₂, ha⟩ := IsCofiltered.cospan e₁ e₂
  let s := a₁ ≫ e₁
  have h₁ : (sys D).map a₁ ≫ (sys D).map e₁ = (sys D).map s := ((sys D).map_comp _ _).symm
  have h₂ : (sys D).map a₂ ≫ (sys D).map e₂ = (sys D).map s := by rw [← (sys D).map_comp, ← ha]
  let g₁' := restr g₁ hg₁ ((sys D).map a₁) h₁
  let g₂' := restr g₂ hg₂ ((sys D).map a₂) h₂
  let rX := trans fX (limit.π (sys D) k) (limit.w (sys D) s)
  let rY := trans fY (limit.π (sys D) k) (limit.w (sys D) s)
  have key₁ : u.hom ≫ rY = rX ≫ g₁' :=
    comp_trans_eq_trans_restr _ _ (limit.w (sys D) a₁) _ _ u.hom hu g₁ hg₁ hr₁
  have key₂ : u.inv ≫ rX = rY ≫ g₂' :=
    comp_trans_eq_trans_restr _ _ (limit.w (sys D) a₂) _ _ u.inv hu' g₂ hg₂ hr₂
  have hg₁'s : g₁' ≫ pullback.snd fY ((sys D).map s) = pullback.snd fX ((sys D).map s) :=
    restr_snd _ _ _ _
  have hg₂'s : g₂' ≫ pullback.snd fX ((sys D).map s) = pullback.snd fY ((sys D).map s) :=
    restr_snd _ _ _ _
  have hXs := isAlgebraicSpace_pullback_sys D fX ((sys D).map s) hX
  have hYs := isAlgebraicSpace_pullback_sys D fY ((sys D).map s) hY
  have hXsfp := isFinitePresentation_snd_sys D ((sys D).map s) hX hXfp
  have hYsfp := isFinitePresentation_snd_sys D ((sys D).map s) hY hYfp
  have hid₁ : rX ≫ g₁' ≫ g₂' = rX := by
    rw [← reassoc_of% key₁, ← key₂, Iso.hom_inv_id_assoc]
  have hid₂ : rY ≫ g₂' ≫ g₁' = rY := by
    rw [← reassoc_of% key₂, ← key₁, Iso.inv_hom_id_assoc]
  have hfstX : pullback.fst (pullback.snd fX ((sys D).map s)) (limit.π (sys D) k) ≫ (g₁' ≫ g₂') =
      pullback.fst (pullback.snd fX ((sys D).map s)) (limit.π (sys D) k) ≫ 𝟙 _ := by
    rw [← (isPullback_trans fX (limit.π (sys D) k) (limit.w (sys D) s)).isoPullback_inv_fst,
      Category.assoc, hid₁, Category.comp_id]
  have hfstY : pullback.fst (pullback.snd fY ((sys D).map s)) (limit.π (sys D) k) ≫ (g₂' ≫ g₁') =
      pullback.fst (pullback.snd fY ((sys D).map s)) (limit.π (sys D) k) ≫ 𝟙 _ := by
    rw [← (isPullback_trans fY (limit.π (sys D) k) (limit.w (sys D) s)).isoPullback_inv_fst,
      Category.assoc, hid₂, Category.comp_id]
  obtain ⟨m₁, b₁, hb₁⟩ := exists_stage_eq hZ D hc hE k (pullback.snd fX ((sys D).map s))
    (pullback.snd fX ((sys D).map s)) hXs hXs hXsfp hXsfp (g₁' ≫ g₂') (𝟙 _)
    (by rw [Category.assoc, hg₂'s, hg₁'s]) (Category.id_comp _) hfstX
  obtain ⟨m₂, b₂, hb₂⟩ := exists_stage_eq hZ D hc hE k (pullback.snd fY ((sys D).map s))
    (pullback.snd fY ((sys D).map s)) hYs hYs hYsfp hYsfp (g₂' ≫ g₁') (𝟙 _)
    (by rw [Category.assoc, hg₁'s, hg₂'s]) (Category.id_comp _) hfstY
  obtain ⟨m, c₁, c₂, hcc⟩ := IsCofiltered.cospan b₁ b₂
  let b := c₁ ≫ b₁
  let s' := b ≫ s
  have hb : (sys D).map b ≫ (sys D).map s = (sys D).map s' := ((sys D).map_comp _ _).symm
  have hbX : trans fX ((sys D).map b) hb ≫ (g₁' ≫ g₂') = trans fX ((sys D).map b) hb ≫ 𝟙 _ := by
    have hν : trans fX ((sys D).map b) hb ≫ pullback.snd fX ((sys D).map s) =
        (pullback.snd fX ((sys D).map s') ≫ (sys D).map c₁) ≫ (sys D).map b₁ := by
      rw [trans_snd, Category.assoc, ← (sys D).map_comp]
    rw [← pullback.lift_fst _ _ hν, Category.assoc, hb₁]
    exact (Category.assoc _ _ _).symm
  have hbY : trans fY ((sys D).map b) hb ≫ (g₂' ≫ g₁') = trans fY ((sys D).map b) hb ≫ 𝟙 _ := by
    have hν : trans fY ((sys D).map b) hb ≫ pullback.snd fY ((sys D).map s) =
        (pullback.snd fY ((sys D).map s') ≫ (sys D).map c₂) ≫ (sys D).map b₂ := by
      rw [trans_snd, Category.assoc, ← (sys D).map_comp, ← hcc]
    rw [← pullback.lift_fst _ _ hν, Category.assoc, hb₂]
    exact (Category.assoc _ _ _).symm
  let G : pullback fX ((sys D).map s') ≅ pullback fY ((sys D).map s') :=
    { hom := restr g₁' hg₁'s ((sys D).map b) hb
      inv := restr g₂' hg₂'s ((sys D).map b) hb
      hom_inv_id := by
        rw [restr_comp, restr_congr _ (Category.id_comp _) _ hb hbX, restr_id]
      inv_hom_id := by
        rw [restr_comp, restr_congr _ (Category.id_comp _) _ hb hbY, restr_id] }
  exact ⟨m, s', G, restr_snd g₁' hg₁'s _ hb,
    comp_trans_eq_trans_restr _ _ (limit.w (sys D) b) _ _ u.hom hu g₁' hg₁'s key₁⟩

end IsoDescent

/-! ### The three stage-descent conditions for `Spaces'_{fp, flat, proper}` -/

section StageDescent

open CartesianProperFlatSpaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))
  {J : Type u} [Category.{u} J] [IsCofiltered J]
  (D : J ⥤ BigAffineFppf B S hS) {c : Cone D}
  (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))

/-- A morphism of families lying over `f` is cartesian over `yoneda.map f`. -/
private theorem isPullback_hom_of_isHomLift {x y : CartesianProperFlatSpaces B S hS}
    (f : x.base ⟶ y.base) (φ : x ⟶ y)
    (hφ : (cartesianProperFlatProjection B S hS).IsHomLift f φ) :
    IsPullback φ.hom.hom.left.hom x.toBase y.toBase (yoneda.map f) := by
  simpa only [@hom_right_eq _ _ _ _ _ f φ hφ] using isPullback_hom φ

include hc in
/-- **Descent of objects** (`Deformation.Artin.DescentObj`) for `Spaces'_{fp, flat, proper}`:
every finitely presented, flat and proper family over the limit is the pullback of one over a
stage (Stacks 07SK, 08K0, 08K1). -/
theorem descentObj (hM : Space.ModelsDescendUnderConvention B S hS hZ)
    (hflat : Space.PropertyDescendsUnderConvention B S hS hZ (fun f => Space.IsFlat B S hS f)
      (fun f => Space.IsLocallyOfFinitePresentation B S hS f))
    (hproper : Space.PropertyDescendsUnderConvention B S hS hZ
      (fun f => Space.IsProper B S hS f) (fun f => Space.IsLocallyOfFiniteType B S hS f)) :
    Deformation.Artin.DescentObj (cartesianProperFlatProjection B S hS)
      (D ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c) := by
  intro x
  obtain ⟨⟨⟨⟨⟨X, hX⟩, V, h⟩, ⟨hfp, hfl, hpr⟩⟩⟩, hV⟩ := x
  change V = (BigAffineFppf.inclusion B S hS).obj c.pt at hV
  subst hV
  obtain ⟨k, Xk, fk, a, hXk, hfk, hflk, hprk, sq⟩ :=
    exists_stage_family hZ D hc hM hflat hproper hX h hfp hfl hpr
  exact ⟨k, ⟨mk' _ Xk hXk fk hfk hflk hprk, rfl⟩,
    homOfIsPullback (x := mk' _ X hX h hfp hfl hpr) (y := mk' _ Xk hXk fk hfk hflk hprk) a _ sq,
    isHomLift_homOfIsPullback _ _ _⟩

include hc in
/-- **Descent of equalities** (`Deformation.Artin.DescentEq`) for `Spaces'_{fp, flat, proper}`
(Stacks 07SK, faithfulness). -/
theorem descentEq (hE : Space.EqualitiesDescendUnderConvention B S hS hZ) :
    Deformation.Artin.DescentEq (cartesianProperFlatProjection B S hS)
      (D ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c) := by
  intro i xi yi x δ hδ ψ ψ' hψ hψ' hδψ
  obtain ⟨⟨⟨⟨⟨Xi, hXi⟩, Vi, fi⟩, ⟨hfpi, hfli, hpri⟩⟩⟩, hVi⟩ := xi
  change Vi = _ at hVi
  subst hVi
  obtain ⟨⟨⟨⟨⟨Yi, hYi⟩, Wi, gi⟩, ⟨hfpY, hflY, hprY⟩⟩⟩, hWi⟩ := yi
  change Wi = _ at hWi
  subst hWi
  obtain ⟨⟨⟨⟨⟨X, hX⟩, V, h⟩, hPx⟩⟩, hV⟩ := x
  change V = _ at hV
  subst hV
  have hδr : δ.hom.hom.right = (BigAffineFppf.inclusion B S hS).map (c.π.app i) :=
    @hom_right_eq _ _ _ _ _ _ δ hδ
  have hψr : ψ.hom.hom.right = 𝟙 _ := @hom_right_eq _ _ _ _ _ _ ψ hψ
  have hψ'r : ψ'.hom.hom.right = 𝟙 _ := @hom_right_eq _ _ _ _ _ _ ψ' hψ'
  have sqδ : IsPullback δ.hom.hom.left.hom h fi
      (yoneda.map ((BigAffineFppf.inclusion B S hS).map (c.π.app i))) :=
    isPullback_hom_of_isHomLift _ δ hδ
  have hψw : ψ.hom.hom.left.hom ≫ gi = fi := by
    simpa using (isPullback_hom_of_isHomLift _ ψ hψ).w
  have hψ'w : ψ'.hom.hom.left.hom ≫ gi = fi := by
    simpa using (isPullback_hom_of_isHomLift _ ψ' hψ').w
  have hδψl : δ.hom.hom.left.hom ≫ ψ.hom.hom.left.hom =
      δ.hom.hom.left.hom ≫ ψ'.hom.hom.left.hom :=
    congrArg (fun φ => φ.hom.hom.left.hom) hδψ
  have sq' := isPullback_limit D hc sqδ
  have heq : pullback.fst fi (limit.π (sys D) i) ≫ ψ.hom.hom.left.hom =
      pullback.fst fi (limit.π (sys D) i) ≫ ψ'.hom.hom.left.hom := by
    rw [← sq'.isoPullback_inv_fst, Category.assoc, Category.assoc, hδψl]
  obtain ⟨j, e, hj⟩ := exists_stage_eq hZ D hc hE i fi gi hXi hYi hfpi hfpY _ _ hψw hψ'w heq
  let xi₀ := mk' _ Xi hXi fi hfpi hfli hpri
  refine ⟨j, e, ⟨baseChange xi₀ ((BigAffineFppf.inclusion B S hS).map (D.map e)),
    projection_obj_baseChange _ _⟩,
    baseChangeHom xi₀ ((BigAffineFppf.inclusion B S hS).map (D.map e)),
    isHomLift_baseChangeHom _ _, ?_⟩
  apply hom_ext'
  · exact hj
  · change (BigAffineFppf.inclusion B S hS).map (D.map e) ≫ ψ.hom.hom.right =
      (BigAffineFppf.inclusion B S hS).map (D.map e) ≫ ψ'.hom.hom.right
    rw [hψr, hψ'r]

include hc in
/-- **Descent of morphisms** (`Deformation.Artin.DescentHom`) for `Spaces'_{fp, flat, proper}`
(Stacks 07SK, fullness and faithfulness): a morphism over the identity of the limit between the
pullbacks of two families at a stage is, at a later stage, a cartesian morphism lying over the
transition. -/
theorem descentHom (hF : Space.MorphismsDescendUnderConvention B S hS hZ)
    (hE : Space.EqualitiesDescendUnderConvention B S hS hZ) :
    Deformation.Artin.DescentHom (cartesianProperFlatProjection B S hS)
      (D ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c) := by
  intro i xi yi x y δ ε hδ hε φ hφ
  obtain ⟨⟨⟨⟨⟨Xi, hXi⟩, Vi, fi⟩, hPi⟩⟩, hVi⟩ := xi
  change Vi = _ at hVi
  subst hVi
  obtain ⟨⟨⟨⟨⟨Yi, hYi⟩, Wi, gi⟩, hPYi⟩⟩, hWi⟩ := yi
  change Wi = _ at hWi
  subst hWi
  obtain ⟨⟨⟨⟨⟨X, hX⟩, V, h⟩, hPx⟩⟩, hV⟩ := x
  change V = _ at hV
  subst hV
  obtain ⟨⟨⟨⟨⟨Y, hY⟩, V', h'⟩, hPy⟩⟩, hV'⟩ := y
  change V' = _ at hV'
  subst hV'
  let ι := BigAffineFppf.inclusion B S hS
  have hδr : δ.hom.hom.right = ι.map (c.π.app i) := @hom_right_eq _ _ _ _ _ _ δ hδ
  have hεr : ε.hom.hom.right = ι.map (c.π.app i) := @hom_right_eq _ _ _ _ _ _ ε hε
  have hφr : φ.hom.hom.right = 𝟙 _ := @hom_right_eq _ _ _ _ _ _ φ hφ
  have sqδ : IsPullback δ.hom.hom.left.hom h fi (yoneda.map (ι.map (c.π.app i))) :=
    isPullback_hom_of_isHomLift _ δ hδ
  have sqε : IsPullback ε.hom.hom.left.hom h' gi (yoneda.map (ι.map (c.π.app i))) :=
    isPullback_hom_of_isHomLift _ ε hε
  have sqφ : IsPullback φ.hom.hom.left.hom h h' (yoneda.map (𝟙 _)) :=
    isPullback_hom_of_isHomLift _ φ hφ
  have hφw : φ.hom.hom.left.hom ≫ h' = h := by simpa using sqφ.w
  have : IsIso φ.hom.hom.left.hom := sqφ.isIso_fst_of_isIso
  let sX := isPullback_limit D hc sqδ
  let sY := isPullback_limit D hc sqε
  let u : pullback fi (limit.π (sys D) i) ≅ pullback gi (limit.π (sys D) i) :=
    sX.isoPullback.symm ≪≫ asIso φ.hom.hom.left.hom ≪≫ sY.isoPullback
  have hu : u.hom ≫ pullback.snd gi (limit.π (sys D) i) =
      pullback.snd fi (limit.π (sys D) i) := by
    change (sX.isoPullback.inv ≫ φ.hom.hom.left.hom ≫ sY.isoPullback.hom) ≫ _ = _
    rw [Category.assoc, Category.assoc, sY.isoPullback_hom_snd, reassoc_of% hφw,
      sX.isoPullback_inv_snd]
  obtain ⟨k, s, G, hG, hrel⟩ := exists_stage_iso hZ D hc hF hE i fi gi hXi hYi hPi.1 hPYi.1 u hu
  let xi₀ : CartesianProperFlatSpaces B S hS := ⟨⟨⟨⟨Xi, hXi⟩, _, fi⟩, hPi⟩⟩
  let yi₀ : CartesianProperFlatSpaces B S hS := ⟨⟨⟨⟨Yi, hYi⟩, _, gi⟩, hPYi⟩⟩
  let xk := baseChange xi₀ (ι.map (D.map s))
  have hGinv : G.inv ≫ pullback.snd fi ((sys D).map s) = pullback.snd gi ((sys D).map s) := by
    rw [Iso.inv_comp_eq, hG]
  have sqχ : IsPullback (G.hom ≫ pullback.fst gi ((sys D).map s))
      (pullback.snd fi ((sys D).map s)) gi (yoneda.map (ι.map (D.map s))) :=
    (IsPullback.of_hasPullback gi ((sys D).map s)).of_iso G.symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simpa using hGinv.symm) (by simp)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
  let χ : xk ⟶ yi₀ := homOfIsPullback (x := xk) (y := yi₀)
    (G.hom ≫ pullback.fst gi ((sys D).map s)) (ι.map (D.map s)) sqχ
  have hcs := yoneda_map_π_comp_sys_map D c s
  have hlift : δ.hom.hom.left.hom ≫ fi = (h ≫ yoneda.map (ι.map (c.π.app k))) ≫ (sys D).map s := by
    rw [sqδ.w, Category.assoc, hcs]
  let δkl : X ⟶ pullback fi ((sys D).map s) :=
    pullback.lift δ.hom.hom.left.hom (h ≫ yoneda.map (ι.map (c.π.app k))) hlift
  have sqk : IsPullback δkl h (pullback.snd fi ((sys D).map s))
      (yoneda.map (ι.map (c.π.app k))) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rwa [pullback.lift_fst, hcs]
  let x₀ : CartesianProperFlatSpaces B S hS := ⟨⟨⟨⟨X, hX⟩, _, h⟩, hPx⟩⟩
  let δk : x₀ ⟶ xk := homOfIsPullback (x := x₀) (y := xk) δkl (ι.map (c.π.app k)) sqk
  have hδk : δkl = sX.isoPullback.hom ≫ trans fi (limit.π (sys D) k) (limit.w (sys D) s) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, trans_fst, sX.isoPullback_hom_fst]
    · rw [pullback.lift_snd, Category.assoc, trans_snd, sX.isoPullback_hom_snd_assoc,
        Category.assoc, limitIso_hom_π]
  have hcompat : δkl ≫ G.hom ≫ pullback.fst gi ((sys D).map s) =
      φ.hom.hom.left.hom ≫ ε.hom.hom.left.hom := by
    rw [hδk, Category.assoc]
    calc sX.isoPullback.hom ≫ trans fi (limit.π (sys D) k) (limit.w (sys D) s) ≫ G.hom ≫
          pullback.fst gi ((sys D).map s)
        = sX.isoPullback.hom ≫ u.hom ≫ trans gi (limit.π (sys D) k) (limit.w (sys D) s) ≫
          pullback.fst gi ((sys D).map s) :=
          congrArg (sX.isoPullback.hom ≫ ·) ((reassoc_of% hrel) _).symm
      _ = sX.isoPullback.hom ≫ u.hom ≫ pullback.fst gi (limit.π (sys D) i) := by
          rw [trans_fst]
      _ = _ := by
          change sX.isoPullback.hom ≫ (sX.isoPullback.inv ≫ φ.hom.hom.left.hom ≫
            sY.isoPullback.hom) ≫ _ = _
          rw [Category.assoc, Iso.hom_inv_id_assoc, Category.assoc, sY.isoPullback_hom_fst]
  refine ⟨k, s, ⟨xk, projection_obj_baseChange _ _⟩, ⟨xk, projection_obj_baseChange _ _⟩,
    baseChangeHom xi₀ (ι.map (D.map s)), χ, δk, 𝟙 xk,
    isHomLift_baseChangeHom _ _, isHomLift_homOfIsPullback _ _ _,
    isHomLift_homOfIsPullback _ _ _, IsHomLift.id (projection_obj_baseChange _ _), ?_, ?_⟩
  · apply hom_ext'
    · change δkl ≫ pullback.fst fi ((sys D).map s) = δ.hom.hom.left.hom
      exact pullback.lift_fst _ _ _
    · change ι.map (c.π.app k) ≫ ι.map (D.map s) = δ.hom.hom.right
      rw [hδr, ← Functor.map_comp, c.w s]
  · apply hom_ext'
    · change δkl ≫ 𝟙 _ ≫ (G.hom ≫ pullback.fst gi ((sys D).map s)) =
        φ.hom.hom.left.hom ≫ ε.hom.hom.left.hom
      rw [Category.id_comp, hcompat]
    · change ι.map (c.π.app k) ≫ 𝟙 _ ≫ ι.map (D.map s) = φ.hom.hom.right ≫ ε.hom.hom.right
      rw [hφr, hεr, Category.id_comp, Category.id_comp, ← Functor.map_comp, c.w s]

end StageDescent

end AlgebraicGeometry.StackOfSpacesLimit

end
