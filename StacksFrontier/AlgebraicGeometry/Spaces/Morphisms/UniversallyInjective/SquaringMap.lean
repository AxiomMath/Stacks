module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Size.Pullback
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolution
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteLocalSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Continuous
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves

/-!
# The squaring map on the involution quotient of the affine line

The endomorphism of the affine line squaring the coordinate, and the morphism
`AlgebraicGeometry.AffineLineInvolution.squaringMap` it descends to on the involution quotient
of Stacks 02Z1 (part (1) of the remark Stacks 05VS), together with a local criterion for an
isomorphism of sheaves and the fppf-local existence of square roots of a coordinate used for
the remaining parts of the remark.

See `StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective` for the overview.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AffineLineInvolution

/-! ### Squaring the coordinate of the affine line -/

variable (k : Type u) [Field k]

/-- The endomorphism of the affine line over `k` which squares the standard coordinate. -/
noncomputable def affineLineSquare : affineLine k ⟶ affineLine k :=
  Over.homMk (AffineSpace.homOfVector (affineLine k).hom
    (fun _ : PUnit.{u + 1} => AffineSpace.coord (Spec (.of k)) PUnit.unit ^ 2))

/-- The underlying morphism of schemes of `affineLineSquare k` is the morphism to affine space
given by the square of the standard coordinate. -/
@[simp]
theorem affineLineSquare_left :
    (affineLineSquare k).left = AffineSpace.homOfVector (affineLine k).hom
      (fun _ : PUnit.{u + 1} => AffineSpace.coord (Spec (.of k)) PUnit.unit ^ 2) :=
  rfl

/-- Squaring the coordinate is unchanged by negating it. -/
theorem affineLineNeg_comp_affineLineSquare :
    affineLineNeg k ≫ affineLineSquare k = affineLineSquare k := by
  ext1
  refine AffineSpace.hom_ext ?_ ?_
  · simp
  · intro i
    rw [Over.comp_left, affineLineSquare_left, affineLineNeg_left, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, AffineSpace.homOfVector_appTop_coord, map_pow,
      AffineSpace.homOfVector_appTop_coord, neg_sq]

/-- Squaring the coordinate identifies the two legs of the involution relation: on the
diagonal summand both are the identity, and on the summand carrying the graph of negation
they differ by negation, which squaring undoes. -/
theorem involutionRelation_source_comp_affineLineSquare :
    (involutionRelation k).source ≫ affineLineSquare k =
      (involutionRelation k).target ≫ affineLineSquare k := by
  rw [involutionRelation_source, involutionRelation_target]
  refine coprod.hom_ext ?_ ?_
  · rw [← Category.assoc, ← Category.assoc, coprod.inl_desc, coprod.inl_desc]
  · rw [← Category.assoc, ← Category.assoc, coprod.inr_desc, coprod.inr_desc,
      Category.assoc, affineLineNeg_comp_affineLineSquare]

/-! ### The squaring map on the quotient -/

/-- The restricted functor of points of the affine line, as a sheaf on the big fppf site
of `k`. -/
noncomputable def affineLinePointsSheaf (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k))) :
    Sheaf (BigFppfOver.topology B (Spec (.of k)) hk) (Type u) :=
  ⟨Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (affineLine k),
    BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B (Spec (.of k)) hk (affineLine k)⟩

/-- Squaring the coordinate, read on the restricted functors of points, identifies related
points. -/
theorem sourceMap_comp_points_affineLineSquare (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k))) :
    Stacks.Groupoids.sourceMap (Over.post (X := B.obj hk) B.inclusion)
          (involutionRelation k) ≫
        (Over.post (X := B.obj hk) B.inclusion).op.whiskerLeft
          (yoneda.map (affineLineSquare k)) =
      Stacks.Groupoids.targetMap (Over.post (X := B.obj hk) B.inclusion)
          (involutionRelation k) ≫
        (Over.post (X := B.obj hk) B.inclusion).op.whiskerLeft
          (yoneda.map (affineLineSquare k)) := by
  rw [Stacks.Groupoids.sourceMap, Stacks.Groupoids.targetMap,
    ← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp, ← yoneda.map_comp,
    ← yoneda.map_comp, involutionRelation_source_comp_affineLineSquare]

/-- **Stacks 05VS, part (1).** The canonical morphism from the involution quotient to the
affine line, descended from squaring the coordinate: the point with coordinate `x` is sent to
the point with coordinate `x ^ 2`. This is the morphism `X ⟶ 𝐀¹_k` of the remark. -/
@[stacks 05VS "part (1): the morphism X ⟶ 𝐀¹_k squaring the coordinate"]
noncomputable def squaringMap (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] :
    (involutionQuotient k B hk).obj ⟶
      Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (affineLine k) :=
  (Stacks.Groupoids.quotientSheafDesc (BigFppfOver.topology B (Spec (.of k)) hk)
    (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k)
    (affineLinePointsSheaf k B hk) _ (sourceMap_comp_points_affineLineSquare k B hk)).hom

/-- The squaring map on the quotient pulls back to squaring the coordinate on the chart.

This is the third assertion of the example of **Stacks 05Z6**: the composite of the two
morphisms `𝐀¹_k ⟶ X ⟶ 𝐀¹_k` is the map `x ↦ x²`. -/
@[simp]
theorem toQuotientSheaf_comp_squaringMap (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] :
    Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
          (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k) ≫
        squaringMap k B hk =
      (Over.post (X := B.obj hk) B.inclusion).op.whiskerLeft
        (yoneda.map (affineLineSquare k)) :=
  Stacks.Groupoids.toQuotientSheaf_quotientSheafDesc _ _ _ _ _ _

/-! ### A local criterion for an isomorphism of sheaves -/

universe v w z

/-- A base change of a morphism of sheaves is an isomorphism as soon as, for a locally
surjective map `q` onto its source which stays locally surjective after composing with the
morphism, any two sections of `q` with the same image in the base agree.

Local surjectivity of `q ≫ f` gives local surjectivity of the base change, and the
hypothesis on `q` gives its local injectivity; a locally bijective morphism of sheaves is an
isomorphism. -/
theorem isIso_of_local_roots {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    {U : Cᵒᵖ ⥤ Type z} {P X Y V : Sheaf J (Type z)}
    (q : U ⟶ X.obj) (f : X ⟶ Y) (g : V ⟶ Y)
    (p : P ⟶ X) (t : P ⟶ V) (hp : IsPullback p t f g)
    [Presheaf.IsLocallySurjective J q]
    [Presheaf.IsLocallySurjective J (q ≫ f.hom)]
    (hrel : ∀ (T : Cᵒᵖ) (a b : U.obj T) (c : V.obj.obj T),
      f.hom.app T (q.app T a) = g.hom.app T c →
      f.hom.app T (q.app T b) = g.hom.app T c → q.app T a = q.app T b) :
    IsIso t := by
  have hp' (T : Cᵒᵖ) := (hp.map (sheafToPresheaf J (Type z))).map
    ((evaluation Cᵒᵖ (Type z)).obj T)
  apply (Sheaf.isLocallyBijective_iff_isIso t).mp
  constructor
  · apply Presheaf.isLocallyInjective_of_injective
    intro T a b hab
    apply Types.ext_of_isPullback (hp' T) ?_ hab
    apply (((isSheaf_iff_isSheaf_of_type J X.obj).mp X.property).isSeparated _
      (J.intersection_covering (Presheaf.imageSieve_mem J q (p.hom.app T a))
        (Presheaf.imageSieve_mem J q (p.hom.app T b)))).ext
    intro W l hl
    obtain ⟨a', ha⟩ := hl.1
    obtain ⟨b', hb⟩ := hl.2
    change q.app (Opposite.op W) a' = X.obj.map l.op (p.hom.app T a) at ha
    change q.app (Opposite.op W) b' = X.obj.map l.op (p.hom.app T b) at hb
    change X.obj.map l.op (p.hom.app T a) = X.obj.map l.op (p.hom.app T b)
    rw [← ha, ← hb]
    apply hrel (Opposite.op W) a' b' (V.obj.map l.op (t.hom.app T a))
    · rw [ha, NatTrans.naturality_apply, NatTrans.naturality_apply]
      exact congrArg (Y.obj.map l.op) (congrArg (fun z => z.hom.app T a) hp.w)
    · rw [hb, NatTrans.naturality_apply, NatTrans.naturality_apply, hab]
      exact congrArg (Y.obj.map l.op) (congrArg (fun z => z.hom.app T b) hp.w)
  · refine ⟨fun {T} c => ?_⟩
    apply J.superset_covering _
      (Presheaf.imageSieve_mem J (q ≫ f.hom) (g.hom.app (Opposite.op T) c))
    intro W l hl
    obtain ⟨a, ha⟩ := hl
    change f.hom.app (Opposite.op W) (q.app (Opposite.op W) a) =
      Y.obj.map l.op (g.hom.app (Opposite.op T) c) at ha
    obtain ⟨b, -, hb₂⟩ := Types.exists_of_isPullback (hp' (Opposite.op W))
      (q.app (Opposite.op W) a) (V.obj.map l.op c)
      (ha.trans (NatTrans.naturality_apply g.hom l.op c).symm)
    exact ⟨b, hb₂⟩

/-! ### Square roots of a coordinate -/

/-- The restriction of a global section to its own basic open is a unit. -/
theorem isUnit_basicOpen_appTop (T : Scheme.{u}) (s : Γ(T, ⊤)) :
    IsUnit ((T.basicOpen s).ι.appTop s) := by
  apply (T.basicOpen s).toScheme.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  apply (Scheme.mem_basicOpen _ _ _ hx).mp
  rw [← Scheme.preimage_basicOpen_top]
  exact x.property

/-- Two sections with the same square and with the first one invertible agree, up to sign, on
a neighbourhood of any point, provided `2` is invertible: the two basic opens of their sum and
of their difference cover, and on each of them the other factor of
`(a - b) * (a + b) = a ^ 2 - b ^ 2 = 0` vanishes. -/
theorem exists_open_square_eq_or_neg (T : Scheme.{u}) (a b : Γ(T, ⊤))
    (hab : a ^ 2 = b ^ 2) (ha : T.basicOpen a = ⊤) (h2 : IsUnit (2 : Γ(T, ⊤)))
    (x : T) : ∃ U : T.Opens, x ∈ U ∧
      (U.ι.appTop a = U.ι.appTop b ∨ U.ι.appTop a = -U.ι.appTop b) := by
  have hcover : T.basicOpen (a + b) ⊔ T.basicOpen (a - b) = ⊤ := by
    have h := T.basicOpen_add_le (a + b) (a - b)
    rw [show a + b + (a - b) = 2 * a by ring,
      T.basicOpen_mul, T.basicOpen_of_isUnit h2, ha, inf_top_eq] at h
    exact top_le_iff.mp h
  have hx : x ∈ T.basicOpen (a + b) ∨ x ∈ T.basicOpen (a - b) := by
    rw [← TopologicalSpace.Opens.mem_sup, hcover]
    trivial
  have hprod : (a - b) * (a + b) = 0 := by linear_combination hab
  rcases hx with hx | hx
  · refine ⟨T.basicOpen (a + b), hx, Or.inl ?_⟩
    have hu := isUnit_basicOpen_appTop T (a + b)
    have he := congrArg (T.basicOpen (a + b)).ι.appTop hprod
    rw [map_mul, map_zero, hu.mul_left_eq_zero] at he
    rwa [map_sub, sub_eq_zero] at he
  · refine ⟨T.basicOpen (a - b), hx, Or.inr ?_⟩
    have hu := isUnit_basicOpen_appTop T (a - b)
    have he := congrArg (T.basicOpen (a - b)).ι.appTop hprod
    rw [map_mul, map_zero, hu.mul_right_eq_zero] at he
    rwa [map_add, add_eq_zero_iff_eq_neg] at he

/-- A sieve on an object of the big fppf site of `S` covers as soon as every point of the
object has a flat, locally finitely presented neighbourhood belonging to the sieve. The
family of all those neighbourhoods is jointly surjective, so
`AlgebraicGeometry.mem_topology_of_family` makes it generate a covering sieve, which the given
sieve contains. -/
theorem sieve_mem_of_fppf_neighborhoods (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {T : BigFppfOver B S hS} (R : Sieve T)
    (hR : ∀ x : B.inclusion.obj T.left, ∃ (W : B.Schemes) (m : W ⟶ T.left),
      Flat (B.inclusion.map m) ∧ LocallyOfFinitePresentation (B.inclusion.map m) ∧
      x ∈ Set.range (B.inclusion.map m) ∧
      R.arrows (Over.homMk m : Over.mk (m ≫ T.hom) ⟶ T)) :
    R ∈ BigFppfOver.topology B S hS T := by
  classical
  choose W m hflat hlfp hrange hmem using hR
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (mem_topology_of_family B S hS (I := ULift.{u + 1} (B.inclusion.obj T.left))
      (fun i => W i.down) (fun i => m i.down) (fun i => hflat i.down) (fun i => hlfp i.down)
      (fun x => ⟨⟨x⟩, hrange x⟩))
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  exact fun i => hmem i.down

end AlgebraicGeometry.AffineLineInvolution

end
