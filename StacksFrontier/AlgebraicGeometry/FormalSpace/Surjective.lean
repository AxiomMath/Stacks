module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.CategoryTheory.Sites.JointlyLocallySurjective

/-!
# Surjective morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A morphism `f : X ⟶ Y` of formal
algebraic spaces over `S` is *surjective* when the induced map on points is surjective. This is
the condition of Stacks 0GHP, that the induced morphism `X_red ⟶ Y_red` of underlying reduced
algebraic spaces be surjective, because the inclusion of a reduction is bijective on points.

Surjectivity is stable under base change and can be tested on base changes: it is equivalent to
surjectivity of every base change along a scheme over `S` in the site mapping to the target, to
the same for the affine such schemes alone, to surjectivity of the base changes along the
members of a covering of the target as in Definition 0AIM, and to the existence of a single
surjective morphism of formal algebraic spaces onto the target along which the base change is
surjective.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsSurjective`: a morphism of fppf sheaves is surjective when
  it is surjective on points.
* `AlgebraicGeometry.FormalSpace.IsSurjectiveOnSchemeBaseChanges`,
  `AlgebraicGeometry.FormalSpace.IsSurjectiveOnAffineBaseChanges`,
  `AlgebraicGeometry.FormalSpace.HasSurjectiveFormalAtlas`,
  `AlgebraicGeometry.FormalSpace.HasSurjectiveFormalCover`: conditions (2), (3), (4) and (5) of
  **Stacks 0GHS**.

## Main results

* `AlgebraicGeometry.FormalSpace.isSurjective_iff_isSurjectiveULift_red`: surjectivity on
  points is the condition of Stacks 0GHP on the morphism of reduced algebraic spaces.
* `AlgebraicGeometry.FormalSpace.IsSurjective.of_isPullback`: a base change of a surjective
  morphism is surjective.
* `AlgebraicGeometry.FormalSpace.isSurjective_tfae`: **Stacks 0GHS** for its conditions (1),
  (2), (3), (4) and (5).
* `AlgebraicGeometry.FormalSpace.IsSurjective.hasSurjectiveFormalAtlas` and
  `AlgebraicGeometry.FormalSpace.isSurjective_of_hasSurjectiveFormalAtlas`: the implications
  (1) ⇒ (4) and (4) ⇒ (1) of **Stacks 0GHS**.
* `AlgebraicGeometry.FormalSpace.isSurjective_of_isLocallySurjective`: a surjection of fppf
  sheaves is surjective on points.
* `AlgebraicGeometry.FormalSpace.exists_pointsMapULift_eq_of_isLocallySurjective_sigmaDesc`: a
  family of morphisms of fppf sheaves whose induced morphism out of the coproduct is a
  surjection of sheaves is jointly surjective on points.

## Implementation notes

`AlgebraicGeometry.FormalSpace.IsSurjective` is surjectivity of the map on points of
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPoints` rather than a condition on a chosen
reduction; `AlgebraicGeometry.FormalSpace.isSurjective_iff_isSurjectiveULift_red` identifies it
with the condition of Stacks 0GHP for any reductions of the source and target and any compatible
morphism between them. The definition and the conditions of Stacks 0GHS are stated for arbitrary
morphisms of fppf sheaves, as `AlgebraicGeometry.FormalSpace.IsProper` is.

Conditions (2), (3) and (5) of Stacks 0GHS quantify over every cartesian square `X ×_Y T` rather
than over the chosen `CategoryTheory.Limits.pullback`, as the conditions of Stacks 0ART do.
Condition (4) spells out the covering of Stacks 0AIM. Condition (6) of the source is the
placeholder "add more here" and asserts nothing.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0GB8](https://stacks.math.columbia.edu/tag/0GB8)
* [Stacks Project, Tag 0GHP](https://stacks.math.columbia.edu/tag/0GHP)
* [Stacks Project, Tag 0GHS](https://stacks.math.columbia.edu/tag/0GHS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of fppf sheaves on the big fppf site of `S` is *surjective* when the induced map
on their sets of points is surjective. For a morphism of formal algebraic spaces over `S` this
is the condition of Stacks 0GHP, that the induced morphism of underlying reduced algebraic
spaces be surjective. -/
abbrev IsSurjective {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  Space.IsSurjectiveULift.{u + 1} B S hS f.hom

/-- Surjectivity on points of a morphism of formal algebraic spaces over `S` is the condition
of Stacks 0GHP on it: the morphism between any two reductions of its source and target
compatible with it is a surjective morphism of algebraic spaces exactly when the morphism
itself is surjective on points. -/
@[stacks 0GHP "the definition, identified with the source's condition on the morphism \
of underlying reduced algebraic spaces"]
theorem isSurjective_iff_isSurjectiveULift_red {X Y Xred Yred : FppfSheaf B S hS}
    {iX : Xred ⟶ X} {iY : Yred ⟶ Y}
    (hiX : IsReduction B S hS X Xred iX) (hiY : IsReduction B S hS Y Yred iY)
    {f : X ⟶ Y} {fred : Xred ⟶ Yred} (hfred : fred ≫ iY = iX ≫ f) :
    IsSurjective B S hS f ↔ Space.IsSurjectiveULift.{u + 1} B S hS fred.hom := by
  have hXbij := hiX.bijective_pointsMapULift
  have hYbij := hiY.bijective_pointsMapULift
  have hhom : fred.hom ≫ iY.hom = iX.hom ≫ f.hom := congrArg (·.hom) hfred
  have hcomm : ∀ pt, Space.pointsMapULift.{u + 1} B S hS Yred.obj iY.hom
        (Space.pointsMapULift.{u + 1} B S hS Xred.obj fred.hom pt)
      = Space.pointsMapULift.{u + 1} B S hS X.obj f.hom
        (Space.pointsMapULift.{u + 1} B S hS Xred.obj iX.hom pt) := fun pt => by
    simpa only [Space.pointsMapULift_comp, Function.comp_apply] using
      congrFun (congrArg (Space.pointsMapULift.{u + 1} B S hS Xred.obj) hhom) pt
  constructor
  · intro hsurj pt
    obtain ⟨pre, hpre⟩ := hsurj (Space.pointsMapULift.{u + 1} B S hS Yred.obj iY.hom pt)
    obtain ⟨rpre, hrpre⟩ := hXbij.2 pre
    refine ⟨rpre, hYbij.1 ?_⟩
    rw [hcomm, hrpre, hpre]
  · intro hsurj pt
    obtain ⟨rpt, hrpt⟩ := hYbij.2 pt
    obtain ⟨pre, hpre⟩ := hsurj rpt
    refine ⟨Space.pointsMapULift.{u + 1} B S hS Xred.obj iX.hom pre, ?_⟩
    rw [← hcomm, hpre, hrpt]

/-! ### Composition -/

/-- The composition of two surjective morphisms of fppf sheaves on the big fppf site of `S` is
surjective. -/
@[stacks 0GHQ]
theorem IsSurjective.comp {X Y Z : FppfSheaf B S hS} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsSurjective B S hS f) (hg : IsSurjective B S hS g) :
    IsSurjective B S hS (f ≫ g) := by
  intro z
  obtain ⟨y, hy⟩ := hg z
  obtain ⟨x, hx⟩ := hf y
  refine ⟨x, ?_⟩
  have hhom : (f ≫ g).hom = f.hom ≫ g.hom := rfl
  rw [hhom, Space.pointsMapULift_comp, Function.comp_apply, hx, hy]

/-! ### Base change -/

/-- A base change of a surjective morphism of fppf sheaves on the big fppf site of `S` is
surjective. -/
@[stacks 0GHR]
theorem IsSurjective.of_isPullback {W X Z Y : FppfSheaf B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hf : IsSurjective B S hS f) : IsSurjective B S hS p := by
  intro z
  obtain ⟨x, hx⟩ := hf (Space.pointsMapULift.{u + 1} B S hS Z.obj g.hom z)
  obtain ⟨v, hv, -⟩ := Space.exists_point_of_isPullbackULift B S hS
    (sq.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) z x hx.symm
  exact ⟨v, hv⟩

/-- If a base change of `f : X ⟶ Y` along `g : Z ⟶ Y` is surjective then for every point of `Z`
there is a point of `X` with the same image in `Y`. -/
theorem exists_pointsMapULift_eq_of_isSurjective {W X Z Y : FppfSheaf B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hp : IsSurjective B S hS p) (z : Space.pointsULift.{u + 1} B S hS Z.obj) :
    ∃ x, Space.pointsMapULift.{u + 1} B S hS X.obj f.hom x
      = Space.pointsMapULift.{u + 1} B S hS Z.obj g.hom z := by
  obtain ⟨v, rfl⟩ := hp z
  have hw : q.hom ≫ f.hom = p.hom ≫ g.hom := congrArg (·.hom) sq.w.symm
  refine ⟨Space.pointsMapULift.{u + 1} B S hS W.obj q.hom v, ?_⟩
  simpa only [Space.pointsMapULift_comp, Function.comp_apply] using
    congrFun (congrArg (Space.pointsMapULift.{u + 1} B S hS W.obj) hw) v

/-- If every base change of `f : X ⟶ Y` along `g : Z ⟶ Y` is surjective, then a point of `Y`
in the image of a point of `Z` is in the image of a point of `X`. -/
private theorem exists_pointsMapULift_eq_of_forall_isPullback {X Y Z : FppfSheaf B S hS}
    (f : X ⟶ Y) (g : Z ⟶ Y)
    (hbase : ∀ (W : FppfSheaf B S hS) (p : W ⟶ Z) (q : W ⟶ X),
      IsPullback p q g f → IsSurjective B S hS p)
    {y : Space.pointsULift.{u + 1} B S hS Y.obj} {z : Space.pointsULift.{u + 1} B S hS Z.obj}
    (hz : Space.pointsMapULift.{u + 1} B S hS Z.obj g.hom z = y) :
    ∃ x, Space.pointsMapULift.{u + 1} B S hS X.obj f.hom x = y := by
  obtain ⟨x, hx⟩ := exists_pointsMapULift_eq_of_isSurjective B S hS
    (IsPullback.of_hasPullback f g).flip
    (hbase _ _ _ (IsPullback.of_hasPullback f g).flip) z
  exact ⟨x, hx.trans hz⟩

/-! ### The conditions of Stacks 0GHS -/

/-- **Stacks 0GHS, condition (2).** Every base change of a morphism of fppf sheaves on the big
fppf site of `S` along a scheme over `S` in the site mapping to its target is surjective. -/
abbrev IsSurjectiveOnSchemeBaseChanges {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (T : BigFppfOver B S hS) (g : yonedaSheaf B S hS T ⟶ Y) (W : FppfSheaf B S hS)
    (p : W ⟶ yonedaSheaf B S hS T) (q : W ⟶ X), IsPullback p q g f → IsSurjective B S hS p

/-- **Stacks 0GHS, condition (3).** Every base change of a morphism of fppf sheaves on the big
fppf site of `S` along an affine scheme over `S` in the site mapping to its target is
surjective. -/
abbrev IsSurjectiveOnAffineBaseChanges {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
    ∀ (g : yonedaSheaf B S hS T ⟶ Y) (W : FppfSheaf B S hS)
      (p : W ⟶ yonedaSheaf B S hS T) (q : W ⟶ X), IsPullback p q g f → IsSurjective B S hS p

/-- **Stacks 0GHS, condition (4).** There is a covering of the target of a morphism of fppf
sheaves on the big fppf site of `S` as in Definition 0AIM — by affine formal algebraic spaces,
along morphisms representable by algebraic spaces and étale, jointly surjective as a map of
sheaves — each of whose base changes of the morphism is surjective. -/
abbrev HasSurjectiveFormalAtlas {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  ∃ (I : Type (u + 1)) (Yi : I → FppfSheaf B S hS) (c : ∀ i, Yi i ⟶ Y),
    (∀ i, IsAffineFormalAlgebraicSpace B S hS (Yi i)) ∧
    (∀ i, ∃ hci : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (c i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (c i).hom hci) ∧
    Sheaf.IsLocallySurjective (Sigma.desc c) ∧
    ∀ (i : I) (W : FppfSheaf B S hS) (p : W ⟶ Yi i) (q : W ⟶ X),
      IsPullback p q (c i) f → IsSurjective B S hS p

/-- **Stacks 0GHS, condition (5).** There is a surjective morphism of formal algebraic spaces
onto the target of a morphism of fppf sheaves on the big fppf site of `S` along which the base
change of that morphism is surjective. -/
abbrev HasSurjectiveFormalCover {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ (Z : FppfSheaf B S hS) (g : Z ⟶ Y), IsFormalAlgebraicSpace B S hS Z ∧
    IsSurjective B S hS g ∧
    ∀ (W : FppfSheaf B S hS) (p : W ⟶ Z) (q : W ⟶ X),
      IsPullback p q g f → IsSurjective B S hS p

/-! ### Local surjectivity -/

/-- A family of morphisms of fppf sheaves on the big fppf site of `S` whose induced morphism out
of the coproduct is a surjection of sheaves is jointly surjective on points: every point of the
target is the image of a point of one of the sources. -/
theorem exists_pointsMapULift_eq_of_isLocallySurjective_sigmaDesc {I : Type (u + 1)}
    {Yi : I → FppfSheaf B S hS} {Y : FppfSheaf B S hS} (c : ∀ i, Yi i ⟶ Y)
    (hc : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc c))
    (y : Space.pointsULift.{u + 1} B S hS Y.obj) :
    ∃ (i : I) (z : Space.pointsULift.{u + 1} B S hS (Yi i).obj),
      Space.pointsMapULift.{u + 1} B S hS (Yi i).obj (c i).hom z = y := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  induction y using Quot.ind with
  | _ p => ?_
  obtain ⟨T, hT, hTmem⟩ :=
    Sheaf.exists_sieve_of_isLocallySurjective_sigmaDesc c hc p.value
  obtain ⟨V, g, hg, z, -⟩ := BigFppfOver.exists_mem_range_of_mem_topology B S hS hT
    (IsLocalRing.closedPoint p.carrier)
  obtain ⟨i, t, ht⟩ := hTmem g hg
  obtain ⟨K, instK, hK, ρ, -⟩ := Space.exists_fieldSpec_at_point B V.left.2 z
  let r : B.obj hK ⟶ V.left := B.inclusion.preimage (X := B.obj hK) (Y := V.left) ρ
  let m : (Over.mk (r ≫ V.hom) : BigFppfOver B S hS) ⟶ V := Over.homMk r
  refine ⟨i, Quot.mk _ ⟨K, hK, B.inclusion.map (r ≫ V.hom), (Yi i).obj.map m.op t⟩, ?_⟩
  refine Quot.sound ⟨_, Space.FieldValuedPointULift.dominates_refl B S hS Y.obj _, m ≫ g, ?_⟩
  show Y.obj.map (m ≫ g).op p.value = (c i).hom.app _ ((Yi i).obj.map m.op t)
  rw [op_comp, Y.obj.map_comp, types_comp_apply, ← ht]
  exact (congrArg (fun k => k t) ((c i).hom.naturality m.op)).symm

/-- A surjection of fppf sheaves on the big fppf site of `S` is surjective on points. -/
theorem isSurjective_of_isLocallySurjective {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (hf : Sheaf.IsLocallySurjective f) : IsSurjective B S hS f := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have hdesc : Sheaf.IsLocallySurjective (Sigma.desc (fun _ : PUnit.{u + 2} ↦ f)) := by
    have := hf
    refine Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
      (f₁ := (Sigma.ι (fun _ : PUnit.{u + 2} ↦ X) PUnit.unit).hom) (f₃ := f.hom) ?_
    exact congrArg (·.hom) (Sigma.ι_desc (fun _ : PUnit.{u + 2} ↦ f) PUnit.unit)
  intro y
  obtain ⟨-, z, hz⟩ := exists_pointsMapULift_eq_of_isLocallySurjective_sigmaDesc B S hS
    (fun _ : PUnit.{u + 2} ↦ f) hdesc y
  exact ⟨z, hz⟩

/-! ### The criteria -/

/-- **Stacks 0GHS, condition (3) implies condition (1).** A morphism of fppf sheaves on the big
fppf site of `S` whose base change along every affine scheme over `S` in the site mapping to
its target is surjective is itself surjective. -/
theorem isSurjective_of_isSurjectiveOnAffineBaseChanges {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (h : IsSurjectiveOnAffineBaseChanges B S hS f) : IsSurjective B S hS f := by
  intro y
  induction y using Quot.ind with | _ point => ?_
  let T := point.siteObject B S hS Y.obj
  have hTaff : IsAffine ((BigFppfOver.toScheme B S hS).obj T) :=
    inferInstanceAs (IsAffine (Spec (.of point.carrier)))
  let g : yonedaSheaf B S hS T ⟶ Y := ⟨uliftYonedaEquiv.{u + 1}.symm point.value⟩
  let q : Space.FieldValuedPointULift.{u + 1} B S hS (yonedaSheaf B S hS T).obj :=
    ⟨point.carrier, point.contained, point.toBase, ULift.up (𝟙 T)⟩
  have hval : (uliftYonedaEquiv.{u + 1}.symm point.value).app (Opposite.op T)
      (ULift.up (𝟙 T)) = point.value :=
    uliftYonedaEquiv.{u + 1}.apply_symm_apply point.value
  have hg : Space.pointsMapULift.{u + 1} B S hS (yonedaSheaf B S hS T).obj g.hom
      (Quot.mk _ q) = Quot.mk _ point := by
    refine Quot.sound ⟨point, ⟨𝟙 _, ?_⟩,
      ⟨𝟙 _, Functor.map_id_apply Y.obj (Opposite.op T) point.value⟩⟩
    show Y.obj.map (𝟙 T).op ((uliftYonedaEquiv.{u + 1}.symm point.value).app
      (Opposite.op T) (ULift.up (𝟙 T))) = point.value
    rw [hval]
    exact Functor.map_id_apply Y.obj (Opposite.op T) point.value
  exact exists_pointsMapULift_eq_of_forall_isPullback B S hS f g (h T hTaff g) hg

/-- **Stacks 0GHS, condition (5) implies condition (1).** A morphism of fppf sheaves on the big
fppf site of `S` whose base change along one surjective morphism onto its target is surjective
is itself surjective. -/
theorem isSurjective_of_hasSurjectiveFormalCover {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : HasSurjectiveFormalCover B S hS f) : IsSurjective B S hS f := by
  obtain ⟨Z, g, -, hg, hbase⟩ := h
  intro y
  obtain ⟨z, hz⟩ := hg y
  exact exists_pointsMapULift_eq_of_forall_isPullback B S hS f g hbase hz

/-- **Stacks 0GHS, condition (1) implies condition (4).** If `f : X ⟶ Y` is surjective and `Y`
is a formal algebraic space over `S`, then the atlas of `Y` furnished by Stacks 0AIM is a
covering `{Y_j ⟶ Y}` as in Definition 0AIM along which every base change of `f` is
surjective. -/
@[stacks 0GHS "condition (1) implies condition (4)"]
theorem IsSurjective.hasSurjectiveFormalAtlas {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (hY : IsFormalAlgebraicSpace B S hS Y) (hf : IsSurjective B S hS f) :
    HasSurjectiveFormalAtlas B S hS f := by
  obtain ⟨-, I, Yi, c, haffine, hetale, hsurjective⟩ := hY
  exact ⟨I, Yi, c, haffine, hetale, hsurjective,
    fun _ _ _ _ sq => IsSurjective.of_isPullback B S hS sq hf⟩

/-- **Stacks 0GHS, condition (4) implies condition (1).** If a morphism `f : X ⟶ Y` of fppf
sheaves on the big fppf site of `S` admits a covering `{Y_j ⟶ Y}` of its target as in
Definition 0AIM along which every base change of `f` is surjective, then `f` is surjective. -/
@[stacks 0GHS "condition (4) implies condition (1)"]
theorem isSurjective_of_hasSurjectiveFormalAtlas {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : HasSurjectiveFormalAtlas B S hS f) : IsSurjective B S hS f := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨I, Yi, c, -, -, hcov, hbase⟩ := h
  intro y
  obtain ⟨i, z, hz⟩ :=
    exists_pointsMapULift_eq_of_isLocallySurjective_sigmaDesc B S hS c hcov y
  exact exists_pointsMapULift_eq_of_forall_isPullback B S hS f (c i) (hbase i) hz

/-- For a morphism `f : X ⟶ Y` of formal algebraic spaces over `S` the following are
equivalent:

1. `f` is surjective;
2. for every scheme `T` over `S` in the site and every `T ⟶ Y` the projection
   `X ×_Y T ⟶ T` is surjective;
3. the same for every affine scheme `T` over `S` in the site;
4. there is a covering `{Y_j ⟶ Y}` as in Definition 0AIM such that each projection
   `X ×_Y Y_j ⟶ Y_j` is surjective;
5. there is a surjective morphism `Z ⟶ Y` of formal algebraic spaces over `S` such that
   `X ×_Y Z ⟶ Z` is surjective. -/
@[stacks 0GHS "conditions (1), (2), (3), (4) and (5)"]
theorem isSurjective_tfae {X Y : FppfSheaf B S hS} (hY : IsFormalAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) :
    List.TFAE
      [IsSurjective B S hS f,
        IsSurjectiveOnSchemeBaseChanges B S hS f,
        IsSurjectiveOnAffineBaseChanges B S hS f,
        HasSurjectiveFormalAtlas B S hS f,
        HasSurjectiveFormalCover B S hS f] := by
  tfae_have 1 → 2 := fun hf _ _ _ _ _ sq => IsSurjective.of_isPullback B S hS sq hf
  tfae_have 2 → 3 := fun h T _ g => h T g
  tfae_have 3 → 1 := isSurjective_of_isSurjectiveOnAffineBaseChanges B S hS f
  tfae_have 1 → 4 := fun hf => IsSurjective.hasSurjectiveFormalAtlas B S hS hY hf
  tfae_have 4 → 1 := fun h => isSurjective_of_hasSurjectiveFormalAtlas B S hS h
  tfae_have 1 → 5 := fun hf => ⟨Y, 𝟙 Y, hY,
    fun y => ⟨y, congrFun (Space.pointsMapULift_id B S hS Y.obj) y⟩,
    fun _ _ _ sq => IsSurjective.of_isPullback B S hS sq hf⟩
  tfae_have 5 → 1 := fun h => isSurjective_of_hasSurjectiveFormalCover B S hS h
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
