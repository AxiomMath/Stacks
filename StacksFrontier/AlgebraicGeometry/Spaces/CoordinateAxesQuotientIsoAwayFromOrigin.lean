module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.CoordinateAxesQuotientSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteLocalSurjectivity
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves

/-!
# The coordinate-axes quotient is the affine line away from the origin

Let `k` be a field, `U = Spec (k[x, y]/(xy))`, `R = Δ(U) ⨿ Δ'(U ∖ {0_U})` and `X = U/R`. The
morphism `X ⟶ 𝔸¹_k` descended from `(x, y) ↦ x + y` is, by **Stacks 0ENU**, an isomorphism
over `𝔸¹_k ∖ {0}`. This file proves that assertion, in the form
`IsIso (pullback.snd π i)` for `i` the inclusion of the punctured affine line, the form in which
the same assertion is stated for the squaring map of Stacks 05VS.

## Main results

* `AlgebraicGeometry.CoordinateAxesQuotient.toQuotientSheaf_swap_eq`: the quotient projection
  identifies a point of the punctured axes with its image under the swap.
* `AlgebraicGeometry.CoordinateAxesQuotient.toQuotientSheaf_eq_axesPoint_sum`: a point of `U`
  whose coordinate sum `s` is invertible has the same image in `X` as the point `(s, 0)`.
* `AlgebraicGeometry.CoordinateAxesQuotient.isIso_sumMap_pullback_puncturedAffineLine`:
  **Stacks 0ENU**, the sum map is an isomorphism over `𝔸¹_k ∖ {0}`.

## Implementation notes

The base change is shown to be locally bijective, hence an isomorphism of sheaves: the
projection `U ⟶ X` is locally surjective, so is its composite with the sum map (which is even
surjective on points, through the first axis), and two points of `U` over the same point of the
punctured line have the same image in `X` because both have the image of the point `(s, 0)` of
the first axis.
That last fact is local on the test object: where the first coordinate is invertible the
second vanishes, and where the second is invertible the first vanishes and the point is the
swap of `(s, 0)`. No hypothesis on the characteristic is used.

## References

* [Stacks Project, Tag 0ENU](https://stacks.math.columbia.edu/tag/0ENU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedChangeOfRings

universe u

namespace AlgebraicGeometry.CoordinateAxesQuotient

open AffineLineInvolution

variable (B : BigFppfSite.{u}) (S : Setup.{u}) (hS : B.Contains (Spec (.of S.k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of S.k)) hS) (Type u)]

/-- The quotient projection identifies a point of the punctured coordinate axes with its image
under the coordinate swap: the two are the two legs of the relation at the second summand. -/
theorem toQuotientSheaf_swap_eq (T : BigFppfOver B (Spec (.of S.k)) hS)
    (a a' : (Over.post (X := B.obj hS) B.inclusion).obj T ⟶ axesOver S)
    (hp : a.left ⁻¹ᵁ puncturedCoordinateAxes S = ⊤)
    (ha' : a'.left = a.left ≫ coordinateSwap S) :
    (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of S.k)) hS)
        (Over.post (X := B.obj hS) B.inclusion) (relationPreRelation S)).app (Opposite.op T) a' =
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of S.k)) hS)
        (Over.post (X := B.obj hS) B.inclusion) (relationPreRelation S)).app (Opposite.op T) a := by
  let F := Over.post (X := B.obj hS) B.inclusion
  have hr : Set.range a.left ⊆ Set.range (puncturedCoordinateAxes S).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    show x ∈ a.left ⁻¹ᵁ puncturedCoordinateAxes S
    rw [hp]
    trivial
  let l := IsOpenImmersion.lift (puncturedCoordinateAxes S).ι a.left hr
  have hl : l ≫ (puncturedCoordinateAxes S).ι = a.left := IsOpenImmersion.lift_fac _ _ _
  let r : F.obj T ⟶ relationOver S := Over.homMk (l ≫ coprod.inr) (by
    show (l ≫ coprod.inr) ≫ relationLeft S ≫ baseMap S = (F.obj T).hom
    rw [Category.assoc, ← Category.assoc coprod.inr, inr_relationLeft, ← Category.assoc, hl]
    exact Over.w a)
  have h := congrArg (fun e => e.app (Opposite.op T) r)
    (Stacks.Groupoids.sourceMap_toQuotientSheaf (BigFppfOver.topology B (Spec (.of S.k)) hS)
      F (relationPreRelation S))
  change (Stacks.Groupoids.toQuotientSheaf _ F (relationPreRelation S)).app (Opposite.op T)
      (r ≫ (relationPreRelation S).source) =
    (Stacks.Groupoids.toQuotientSheaf _ F (relationPreRelation S)).app (Opposite.op T)
      (r ≫ (relationPreRelation S).target) at h
  have hs : r ≫ (relationPreRelation S).source = a' := by
    rw [relationPreRelation_source]
    refine Over.OverMorphism.ext ?_
    rw [Over.comp_left, relationRightOver_left, ha']
    show (l ≫ coprod.inr) ≫ relationRight S = _
    rw [Category.assoc, inr_relationRight, ← Category.assoc, hl]
  have ht : r ≫ (relationPreRelation S).target = a := by
    rw [relationPreRelation_target]
    refine Over.OverMorphism.ext ?_
    rw [Over.comp_left, relationLeftOver_left]
    show (l ≫ coprod.inr) ≫ relationLeft S = _
    rw [Category.assoc, inr_relationLeft, hl]
  rwa [hs, ht] at h

/-- The global section `s` of a scheme becomes a unit on its basic open. -/
private theorem _root_.AlgebraicGeometry.Scheme.isUnit_basicOpen_ι_appTop (X : Scheme.{u})
    (s : Γ(X, ⊤)) : IsUnit ((X.basicOpen s).ι.appTop s) := by
  apply (X.basicOpen s).toScheme.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  apply (Scheme.mem_basicOpen _ _ _ hx).mp
  rw [← Scheme.preimage_basicOpen_top]
  exact x.property

/-- If `f * g = 0` and `f + g` is a unit, every point has an open neighbourhood on which one of
`f`, `g` is a unit and the other vanishes. -/
private theorem _root_.AlgebraicGeometry.Scheme.exists_mem_isUnit_of_mul_eq_zero {X : Scheme.{u}}
    {f g : Γ(X, ⊤)} (hfg : f * g = 0) (hs : IsUnit (f + g)) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ((IsUnit (U.ι.appTop f) ∧ U.ι.appTop g = 0) ∨
      (IsUnit (U.ι.appTop g) ∧ U.ι.appTop f = 0)) := by
  have hx : x ∈ X.basicOpen f ⊔ X.basicOpen g :=
    X.basicOpen_add_le f g (by rw [X.basicOpen_of_isUnit hs]; trivial)
  rcases TopologicalSpace.Opens.mem_sup.mp hx with hx | hx
  · refine ⟨_, hx, Or.inl ⟨X.isUnit_basicOpen_ι_appTop f, ?_⟩⟩
    have he := congrArg (X.basicOpen f).ι.appTop hfg
    rwa [map_mul, map_zero, (X.isUnit_basicOpen_ι_appTop f).mul_right_eq_zero] at he
  · refine ⟨_, hx, Or.inr ⟨X.isUnit_basicOpen_ι_appTop g, ?_⟩⟩
    have he := congrArg (X.basicOpen g).ι.appTop hfg
    rwa [map_mul, map_zero, (X.isUnit_basicOpen_ι_appTop g).mul_left_eq_zero] at he

/-- The coordinate swap as an automorphism of the coordinate axes over the ground field. -/
noncomputable def swapOver : axesOver S ⟶ axesOver S :=
  Over.homMk (coordinateSwap S) (coordinateSwap_comp_baseMap S)

/-- A point of the coordinate axes whose first coordinate is invertible and second vanishes, or
the other way round, has the same image in the quotient as the point `(s, 0)` of the first axis,
for `s` its coordinate sum. -/
private theorem toQuotientSheaf_eq_axesPoint_of_isUnit (T : BigFppfOver B (Spec (.of S.k)) hS)
    (a : (Over.post (X := B.obj hS) B.inclusion).obj T ⟶ axesOver S)
    {s : Γ(((Over.post (X := B.obj hS) B.inclusion).obj T).left, ⊤)}
    (hs : a.left.appTop (xSection S) + a.left.appTop (ySection S) = s)
    (hU : (IsUnit (a.left.appTop (xSection S)) ∧ a.left.appTop (ySection S) = 0) ∨
      (IsUnit (a.left.appTop (ySection S)) ∧ a.left.appTop (xSection S) = 0)) :
    (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of S.k)) hS)
        (Over.post (X := B.obj hS) B.inclusion) (relationPreRelation S)).app (Opposite.op T) a =
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of S.k)) hS)
        (Over.post (X := B.obj hS) B.inclusion) (relationPreRelation S)).app (Opposite.op T)
        (axesPoint S s 0 (mul_zero _)) := by
  subst hs
  rcases hU with ⟨-, hy⟩ | ⟨hyu, hx0⟩
  · congr 1
    exact axes_hom_ext S (by rw [axesPoint_xSection, hy, add_zero])
      (by rw [axesPoint_ySection, hy])
  · have hp : a.left ⁻¹ᵁ puncturedCoordinateAxes S = ⊤ := by
      refine top_le_iff.mp (le_trans ?_ (Scheme.Hom.preimage_mono _ le_sup_right))
      rw [show a.left ⁻¹ᵁ (coordinateAxes S).basicOpen (ySection S) = _ from
        Scheme.preimage_basicOpen_top a.left (ySection S)]
      exact (Scheme.basicOpen_of_isUnit _ hyu).ge
    refine (toQuotientSheaf_swap_eq B S hS T a _ hp ?_).symm
    have hsw : axesPoint S (a.left.appTop (xSection S) + a.left.appTop (ySection S)) 0
        (mul_zero _) = a ≫ swapOver S := by
      refine axes_hom_ext S ?_ ?_
      · rw [comp_appTop_section, axesPoint_xSection]
        show _ = a.left.appTop ((coordinateSwap S).appTop (xSection S))
        rw [coordinateSwap_appTop_xSection, hx0, zero_add]
      · rw [comp_appTop_section, axesPoint_ySection]
        show _ = a.left.appTop ((coordinateSwap S).appTop (ySection S))
        rw [coordinateSwap_appTop_ySection, hx0]
    rw [hsw, Over.comp_left]
    rfl

/-- A point of the coordinate axes whose coordinate sum `s` is invertible has the same image in
the quotient as the point `(s, 0)` of the first axis.

Near a point where the first coordinate is invertible the second one vanishes, so the point is
`(s, 0)` there; near a point where the second coordinate is invertible the first one vanishes,
so the point is the image of `(s, 0)` under the coordinate swap, and it lies in the punctured
axes, where the relation identifies a point with its swap. These opens cover the test object,
since `s` is invertible, and the quotient is a sheaf. -/
theorem toQuotientSheaf_eq_axesPoint_sum (T : BigFppfOver B (Spec (.of S.k)) hS)
    (a : (Over.post (X := B.obj hS) B.inclusion).obj T ⟶ axesOver S)
    (hs : IsUnit (a.left.appTop (xSection S) + a.left.appTop (ySection S))) :
    (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of S.k)) hS)
        (Over.post (X := B.obj hS) B.inclusion) (relationPreRelation S)).app (Opposite.op T) a =
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of S.k)) hS)
        (Over.post (X := B.obj hS) B.inclusion) (relationPreRelation S)).app (Opposite.op T)
        (axesPoint S (a.left.appTop (xSection S) + a.left.appTop (ySection S)) 0
          (mul_zero _)) := by
  let J := BigFppfOver.topology B (Spec (.of S.k)) hS
  let F := Over.post (X := B.obj hS) B.inclusion
  let Q := Stacks.Groupoids.quotientSheaf J F (relationPreRelation S)
  let q := Stacks.Groupoids.toQuotientSheaf J F (relationPreRelation S)
  set ax := a.left.appTop (xSection S)
  set ay := a.left.appTop (ySection S)
  let p := axesPoint S (ax + ay) 0 (mul_zero _)
  let E := Presheaf.equalizerSieve (F := Q.obj) (q.app (Opposite.op T) a)
    (q.app (Opposite.op T) p)
  have hR : ∀ x : B.inclusion.obj T.left, ∃ (W : B.Schemes) (m : W ⟶ T.left),
      Flat (B.inclusion.map m) ∧ LocallyOfFinitePresentation (B.inclusion.map m) ∧
      x ∈ Set.range (B.inclusion.map m) ∧
      E.arrows (Over.homMk m : Over.mk (m ≫ T.hom) ⟶ T) := by
    intro x
    obtain ⟨U, hxU, hU⟩ := Scheme.exists_mem_isUnit_of_mul_eq_zero
      (appTop_xSection_mul_appTop_ySection S a) hs x
    have hsite : B.Contains U.toScheme :=
      Scheme.size_lt_of_isOpenImmersion U.ι T.left.property
    let m : B.obj hsite ⟶ T.left := ObjectProperty.homMk U.ι
    refine ⟨B.obj hsite, m, inferInstanceAs (Flat U.ι),
      inferInstanceAs (LocallyOfFinitePresentation U.ι), ⟨⟨x, hxU⟩, rfl⟩, ?_⟩
    let g : (Over.mk (m ≫ T.hom) : BigFppfOver B (Spec (.of S.k)) hS) ⟶ T := Over.homMk m
    have hres (d : F.obj T ⟶ axesOver S) (t : Γ(coordinateAxes S, ⊤)) :
        (F.map g ≫ d).left.appTop t = U.ι.appTop (d.left.appTop t) := by
      rw [comp_appTop_section]
      rfl
    show Q.obj.map g.op (q.app (Opposite.op T) a) = Q.obj.map g.op (q.app (Opposite.op T) p)
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
    show q.app (Opposite.op _) (F.map g ≫ a) = q.app (Opposite.op _) (F.map g ≫ p)
    rw [show F.map g ≫ p = axesPoint S ((F.map g ≫ a).left.appTop (xSection S) +
        (F.map g ≫ a).left.appTop (ySection S)) 0 (mul_zero _) from
      axes_hom_ext S
        (by rw [axesPoint_xSection, hres, hres, hres, axesPoint_xSection, map_add])
        (by rw [axesPoint_ySection, hres, axesPoint_ySection, map_zero])]
    exact toQuotientSheaf_eq_axesPoint_of_isUnit B S hS _ _ rfl (by rwa [hres, hres])
  have heq : E ∈ J T := by
    choose W m hflat hlfp hrange hmem using hR
    refine J.superset_covering ?_
      (mem_topology_of_family B (Spec (.of S.k)) hS (I := ULift.{u + 1} (B.inclusion.obj T.left))
        (fun i => W i.down) (fun i => m i.down) (fun i => hflat i.down) (fun i => hlfp i.down)
        (fun x => ⟨⟨x⟩, hrange x⟩))
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    exact fun i => hmem i.down
  exact (((isSheaf_iff_isSheaf_of_type J Q.obj).mp Q.property).isSeparated _ heq).ext
    (fun _ _ h => h)

/-- The sum map is surjective on `T`-points already on `U`: a `T`-point `t` of the affine line is
the sum of the coordinates of the point `(t, 0)` of the first axis. -/
theorem axesPoint_coord_zero_comp_coordinateSumMap {T : Over (Spec (.of S.k))}
    (t : T ⟶ affineLine S.k) :
    axesPoint S (t.left.appTop (AffineSpace.coord (Spec (.of S.k)) PUnit.unit)) 0
        (mul_zero _) ≫ coordinateSumMap S = t := by
  refine Over.OverMorphism.ext (AffineSpace.hom_ext ?_ ?_)
  · exact (Over.w (axesPoint S (t.left.appTop (AffineSpace.coord (Spec (.of S.k)) PUnit.unit))
      0 (mul_zero _) ≫ coordinateSumMap S)).trans (Over.w t).symm
  · rintro ⟨⟩
    rw [comp_coordinateSumMap_coord, axesPoint_xSection, axesPoint_ySection, add_zero]

/-- A point of the coordinate axes whose coordinate sum lands in the punctured affine line has
invertible coordinate sum. -/
private theorem isUnit_appTop_add_of_comp_coordinateSumMap_eq {T : Over (Spec (.of S.k))}
    (a : T ⟶ axesOver S) (c : T ⟶ puncturedAffineLine S.k)
    (h : a ≫ coordinateSumMap S = c ≫ puncturedAffineLineInclusion S.k) :
    IsUnit (a.left.appTop (xSection S) + a.left.appTop (ySection S)) := by
  rw [← comp_coordinateSumMap_coord, h, Over.comp_left, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, puncturedAffineLineInclusion_left]
  exact IsUnit.map _ ((affineLine S.k).left.isUnit_basicOpen_ι_appTop _)

/-- Two points of the coordinate axes with the same invertible coordinate sum have the same image
in the quotient. -/
private theorem toQuotientSheaf_eq_of_comp_coordinateSumMap_eq
    (T : BigFppfOver B (Spec (.of S.k)) hS)
    (a b : (Over.post (X := B.obj hS) B.inclusion).obj T ⟶ axesOver S)
    (hab : a ≫ coordinateSumMap S = b ≫ coordinateSumMap S)
    (ha : IsUnit (a.left.appTop (xSection S) + a.left.appTop (ySection S))) :
    (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of S.k)) hS)
        (Over.post (X := B.obj hS) B.inclusion) (relationPreRelation S)).app (Opposite.op T) a =
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of S.k)) hS)
        (Over.post (X := B.obj hS) B.inclusion) (relationPreRelation S)).app (Opposite.op T) b := by
  have hsum : a.left.appTop (xSection S) + a.left.appTop (ySection S) =
      b.left.appTop (xSection S) + b.left.appTop (ySection S) := by
    rw [← comp_coordinateSumMap_coord, ← comp_coordinateSumMap_coord, hab]
  rw [toQuotientSheaf_eq_axesPoint_sum B S hS T a ha,
    toQuotientSheaf_eq_axesPoint_sum B S hS T b (by rwa [← hsum])]
  congr 1
  exact axes_hom_ext S (by rw [axesPoint_xSection, axesPoint_xSection, hsum])
    (by rw [axesPoint_ySection, axesPoint_ySection])

/-- The base change `pullback.snd f g` of a morphism of sheaves of types is an isomorphism when
`f` is hit by a locally surjective `q` with `q ≫ f` locally surjective, and any two sections that
`q ≫ f` sends to the image of one section of `V` have the same image under `q`. -/
private theorem isIso_pullback_snd_of_isLocallySurjective {C : Type*} [Category C]
    {J : GrothendieckTopology C} {P : Cᵒᵖ ⥤ Type u} {X A V : Sheaf J (Type u)}
    (q : P ⟶ X.obj) (f : X ⟶ A) (g : V ⟶ A) [HasPullback f g]
    (hq : Presheaf.IsLocallySurjective J q) (hsq : Presheaf.IsLocallySurjective J (q ≫ f.hom))
    (hrel : ∀ (T : Cᵒᵖ) (a b : P.obj T) (c : V.obj.obj T), f.hom.app T (q.app T a) =
      g.hom.app T c → f.hom.app T (q.app T b) = g.hom.app T c → q.app T a = q.app T b) :
    IsIso (pullback.snd f g) := by
  have hp := IsPullback.of_hasPullback f g
  have hp' (T : Cᵒᵖ) := (hp.map (sheafToPresheaf J (Type u))).map ((evaluation _ (Type u)).obj T)
  apply (Sheaf.isLocallyBijective_iff_isIso (pullback.snd f g)).mp
  constructor
  · apply Presheaf.isLocallyInjective_of_injective
    intro T a b hab
    apply Types.ext_of_isPullback (hp' T) ?_ hab
    apply (((isSheaf_iff_isSheaf_of_type J X.obj).mp X.property).isSeparated _
      (J.intersection_covering (Presheaf.imageSieve_mem J q ((pullback.fst f g).hom.app T a))
        (Presheaf.imageSieve_mem J q ((pullback.fst f g).hom.app T b)))).ext
    intro W l hl
    obtain ⟨a', ha⟩ := hl.1
    obtain ⟨b', hb⟩ := hl.2
    change q.app (Opposite.op W) a' = X.obj.map l.op ((pullback.fst f g).hom.app T a) at ha
    change q.app (Opposite.op W) b' = X.obj.map l.op ((pullback.fst f g).hom.app T b) at hb
    show X.obj.map l.op ((pullback.fst f g).hom.app T a) =
      X.obj.map l.op ((pullback.fst f g).hom.app T b)
    rw [← ha, ← hb]
    apply hrel (Opposite.op W) a' b' (V.obj.map l.op ((pullback.snd f g).hom.app T a))
    · rw [ha, NatTrans.naturality_apply, NatTrans.naturality_apply]
      exact congrArg (A.obj.map l.op) (congrArg (fun z => z.hom.app T a) hp.w)
    · rw [hb, NatTrans.naturality_apply, NatTrans.naturality_apply, hab]
      exact congrArg (A.obj.map l.op) (congrArg (fun z => z.hom.app T b) hp.w)
  · refine ⟨?_⟩
    intro T c
    apply J.superset_covering _
      (Presheaf.imageSieve_mem J (q ≫ f.hom) (g.hom.app (Opposite.op T) c))
    intro W l hl
    obtain ⟨a, ha⟩ := hl
    change f.hom.app (Opposite.op W) (q.app (Opposite.op W) a) =
      A.obj.map l.op (g.hom.app (Opposite.op T) c) at ha
    obtain ⟨b, -, hb₂⟩ := Types.exists_of_isPullback (hp' (Opposite.op W))
      (q.app (Opposite.op W) a) (V.obj.map l.op c)
      (ha.trans (NatTrans.naturality_apply g.hom l.op c).symm)
    exact ⟨b, hb₂⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **Stacks 0ENU.** The morphism `X ⟶ 𝔸¹_k` descended from `(x, y) ↦ x + y` is an isomorphism
over `𝔸¹_k ∖ {0}`: its base change along the inclusion of the punctured affine line is an
isomorphism. No hypothesis on the field is needed. -/
theorem isIso_sumMap_pullback_puncturedAffineLine :
    IsIso (pullback.snd (sumMap S B hS)
      ((Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
        (yoneda.map (puncturedAffineLineInclusion S.k)))) := by
  let J := BigFppfOver.topology B (Spec (.of S.k)) hS
  let F := Over.post (X := B.obj hS) B.inclusion
  let A : Sheaf J (Type u) := pointsAffineLineSheaf B S hS
  let V : Sheaf J (Type u) := ⟨Stacks.Groupoids.points F (puncturedAffineLine S.k),
    BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B (Spec (.of S.k)) hS
      (puncturedAffineLine S.k)⟩
  let f : quotientSpace S B hS ⟶ A := ⟨sumMap S B hS⟩
  let g : V ⟶ A := ⟨F.op.whiskerLeft (yoneda.map (puncturedAffineLineInclusion S.k))⟩
  let q := quotientMap S B hS
  have hsq : Presheaf.IsLocallySurjective J (q ≫ f.hom) := by
    show Presheaf.IsLocallySurjective J (quotientMap S B hS ≫ sumMap S B hS)
    rw [quotientMap_comp_sumMap]
    exact Presheaf.isLocallySurjective_of_surjective _ _ fun T t =>
      ⟨_, axesPoint_coord_zero_comp_coordinateSumMap S t⟩
  have ht : IsIso (pullback.snd f g) :=
    isIso_pullback_snd_of_isLocallySurjective q f g
      (Stacks.Groupoids.toQuotientSheaf_isLocallySurjective J F (relationPreRelation S)) hsq
      fun T a b c ha hb =>
      toQuotientSheaf_eq_of_comp_coordinateSumMap_eq B S hS T.unop a b
        ((sumMap_app_quotientMap S B hS T.unop a).symm.trans
          (ha.trans (hb.symm.trans (sumMap_app_quotientMap S B hS T.unop b))))
        (isUnit_appTop_add_of_comp_coordinateSumMap_eq S a c
          ((sumMap_app_quotientMap S B hS T.unop a).symm.trans ha))
  have he : (PreservesPullback.iso (sheafToPresheaf J (Type u)) f g).inv ≫
      (sheafToPresheaf J (Type u)).map (pullback.snd f g) = pullback.snd f.hom g.hom :=
    PreservesPullback.iso_inv_snd _ _ _
  show IsIso (pullback.snd f.hom g.hom)
  rw [← he]
  infer_instance

end AlgebraicGeometry.CoordinateAxesQuotient

end
