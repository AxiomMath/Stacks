module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Composition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceEtaleLocal
public import StacksFrontier.RingTheory.Branches.CompositionLawMinimalPrimes

/-!
# The two identity sections of the space of composable arrows, and their retractions

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces and write `P = R ×_{s, U, t} R` for the
space of composable pairs of arrows, with projections `pr₁, pr₂ : P ⟶ R`.  The unit `e : U ⟶ R`
produces two sections of `R` in `P`,

```
j₁ : R ⟶ P, a ↦ (e(t a), a),      j₂ : R ⟶ P, a ↦ (a, e(s a)),
```

characterised by `j₁ ≫ pr₁ = t ≫ e`, `j₁ ≫ pr₂ = id`, `j₂ ≫ pr₁ = id`,
`j₂ ≫ pr₂ = s ≫ e`, and — these are the unit axioms of the groupoid — `j₁ ≫ c = id` and
`j₂ ≫ c = id`.

At a geometric point of `R` which is the identity arrow at a geometric point of `U`, the two
sections agree, so they induce two homomorphisms `C ⟶ A` of étale local rings out of the one
étale local ring `C` of `P` at the pair of identity arrows, where `A` is the étale local ring
of `R` at the identity arrow.  Together with the three homomorphisms `A ⟶ C` induced by `pr₁`,
`pr₂` and `c`, these are the retraction data that the ring-theoretic core of [Stacks Project,
Tag 06E4] consumes: `StacksDraft.existsUnique_minimalPrimes_of_retraction_of_bijOn_comap_pair`.

## Main definitions

* `AlgebraicGeometry.Space.etaleLocalRingCongr`: transport of the étale local ring along an
  equality of geometric points.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identitySectionAfterTarget` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identitySectionAfterSource`: the two sections
  `j₁` and `j₂`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityArrowPoint` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityPairPoint`: the geometric point of the
  arrow space given by the identity arrow at a geometric point of the object space, and the
  geometric point of the space of composable pairs it determines.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityPairComp`,
  `...identityPairLeft`, `...identityPairRight`, `...identityPairFst` and `...identityPairSnd`:
  the five homomorphisms of étale local rings.

## Main results

* `AlgebraicGeometry.Space.etaleLocalRingMap_id`: the canonical homomorphism of étale local
  rings induced by the identity is the identity.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityPairFst_comp_identityPairComp` and its
  three siblings: the four retraction identities.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityPairFst_identityPairRight_eq_zero` and
  `...identityPairSnd_identityPairLeft_eq_zero`: the two remaining composites kill the maximal
  ideal, as soon as the étale local ring of the object space at the point is a field — which is
  the case the source is interested in, the object space there being the spectrum of a field.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.flat_identityPairComp`: the homomorphism induced
  by the composition law is flat when the object space is the spectrum of a field, which is
  Tag 06E0 read through Tag 04NG.

## Implementation notes

The two sections are built with `CategoryTheory.Limits.pullback.lift` out of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityAfterTarget` and
`...identityAfterSource` applied to the identity of the arrow space; the unit axioms are then
literally `...groupoidCompose_leftIdentity` and `...groupoidCompose_rightIdentity` at the
identity, because `...groupoidCompose` is by definition a `pullback.lift` followed by the
composition law.

Every homomorphism below is a canonical homomorphism of étale local rings composed with a
transport along an equality of geometric points, which is unavoidable: the geometric point of
`P` cut out by `j₂` is only *propositionally* carried to the identity arrow by `pr₁`, `pr₂`
and `c`, while the source and target of the canonical homomorphism are indexed by the points
themselves.  `AlgebraicGeometry.Space.etaleLocalRingCongr` is that transport and
`AlgebraicGeometry.Space.etaleLocalRingMap_congr` lets a morphism equality be moved through
`AlgebraicGeometry.Space.etaleLocalRingMap` at the cost of one such transport; the proofs are
then uniform, and the two general lemmas
`AlgebraicGeometry.Space.comp_etaleLocalRingMap_eq_id_of_section` and
`...comp_etaleLocalRingMap_eq_zero_of_factors` do all the transport bookkeeping once, over
variables.

## References

* [Stacks Project, Tag 06E4](https://stacks.math.columbia.edu/tag/06E4)
* [Stacks Project, Tag 06E0](https://stacks.math.columbia.edu/tag/06E0)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_identityArrowRetractions
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : AlgebraicGeometry.Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Transport of the étale local ring along an equality of geometric points. -/
def etaleLocalRingCongr {x y : GeometricPoint B S hS F} (h : x = y) :
    etaleLocalRing B S hS F x ≃+* etaleLocalRing B S hS F y :=
  h ▸ RingEquiv.refl _

/-- Transport of the étale local ring along the reflexive equality `x = x` is the identity. -/
@[simp]
theorem etaleLocalRingCongr_rfl (x : GeometricPoint B S hS F) :
    etaleLocalRingCongr (rfl : x = x) = RingEquiv.refl _ := rfl

/-- The maximal ideal of a local ring which is a field is zero. -/
private theorem maximalIdeal_eq_bot_of_isField {R : Type*} [CommRing R] [IsLocalRing R]
    (h : IsField R) : IsLocalRing.maximalIdeal R = ⊥ := by
  refine le_antisymm (fun a ha => ?_) bot_le
  rw [Ideal.mem_bot]
  by_contra hne
  obtain ⟨b, hb⟩ := h.mul_inv_cancel hne
  exact (IsLocalRing.mem_maximalIdeal a).mp ha (isUnit_iff_exists_inv.mpr ⟨b, hb⟩)

/-- The canonical homomorphism of étale local rings induced by the identity morphism is the
identity. -/
theorem etaleLocalRingMap_id_apply (hF : IsAlgebraicSpace B S hS F)
    (x : GeometricPoint B S hS F)
    (a : etaleLocalRing B S hS F (geometricPointMap (𝟙 F) x)) :
    etaleLocalRingMap hF (𝟙 F) x a = a := by
  have key : RingHom.id (etaleLocalRing B S hS F x) = etaleLocalRingMap hF (𝟙 F) x := by
    refine eq_etaleLocalRingMap hF (𝟙 F) x ?_
    intro U V g hc hp
    refine Eq.trans ?_ (RingHom.id_comp _).symm
    exact etaleLocalRingGerm_comp_map B S hS
      (smallEtaleNeighborhoodHom (U := U) (V := V) g
        (hc.symm.trans (Category.comp_id _)) hp)
  exact (DFunLike.congr_fun key a).symm

/-- A morphism equality may be moved through the canonical homomorphism of étale local rings,
at the cost of one transport along the resulting equality of geometric points. -/
theorem etaleLocalRingMap_congr (hF : IsAlgebraicSpace B S hS F) {f g : F ⟶ G} (h : f = g)
    (x : GeometricPoint B S hS F) :
    etaleLocalRingMap hF f x =
      (etaleLocalRingMap hF g x).comp
        (etaleLocalRingCongr (congrArg (fun k => geometricPointMap k x) h)).toRingHom := by
  subst h
  rfl

/-- If `j ≫ p = q`, the induced homomorphisms for `p` then `j` compose to the one for `q`, up to
the transport along the resulting equality of geometric points. -/
private theorem etaleLocalRingMap_comp_apply_of_comp_eq (hF : IsAlgebraicSpace B S hS F)
    (hH : IsAlgebraicSpace B S hS H) (j : F ⟶ H) (p : H ⟶ F) (q : F ⟶ F) (hjp : j ≫ p = q)
    (x : GeometricPoint B S hS F) (v : etaleLocalRing B S hS F (geometricPointMap p
      (geometricPointMap j x))) :
    etaleLocalRingMap hF j x (etaleLocalRingMap hH p (geometricPointMap j x) v) =
      etaleLocalRingMap hF q x
        (etaleLocalRingCongr (congrArg (fun k => geometricPointMap k x) hjp) v) := by
  subst hjp
  exact DFunLike.congr_fun (etaleLocalRingMap_comp hF hH j p x) v

/-- **The retraction identity.** Let `j : F ⟶ H` be a section of `p : H ⟶ F`, let `x` be a
geometric point of `F` and let `y` be the geometric point of `H` it determines.  Then the
homomorphism of étale local rings induced by `p` at `y`, followed by the one induced by `j` at
`x`, is the identity — both read through the transports along the two displayed equalities of
geometric points. -/
theorem comp_etaleLocalRingMap_apply_of_section (hF : IsAlgebraicSpace B S hS F)
    (hH : IsAlgebraicSpace B S hS H) (j : F ⟶ H) (p : H ⟶ F) (hjp : j ≫ p = 𝟙 F)
    (x : GeometricPoint B S hS F) (y : GeometricPoint B S hS H)
    (hy : geometricPointMap j x = y) (h : geometricPointMap p y = x)
    (m : etaleLocalRing B S hS F x) :
    etaleLocalRingMap hF j x ((etaleLocalRingCongr hy).symm
        (etaleLocalRingMap hH p y ((etaleLocalRingCongr h).symm m))) = m := by
  subst hy
  refine Eq.trans ?_ ((etaleLocalRingCongr h).apply_symm_apply m)
  exact (etaleLocalRingMap_comp_apply_of_comp_eq hF hH j p _ hjp x _).trans
    (etaleLocalRingMap_id_apply hF x _)

/-- **The vanishing identity.** In the situation of
`AlgebraicGeometry.Space.comp_etaleLocalRingMap_apply_of_section`, if instead `j ≫ p` factors
as `a ≫ b` through a presheaf `G` whose étale local ring at the image point is a field, then
the same composite kills the maximal ideal. -/
theorem comp_etaleLocalRingMap_apply_eq_zero_of_factors
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H)
    (j : F ⟶ H) (p : H ⟶ F) (a : F ⟶ G) (b : G ⟶ F) (hjp : j ≫ p = a ≫ b)
    (x : GeometricPoint B S hS F) (y : GeometricPoint B S hS H)
    (hy : geometricPointMap j x = y) (h : geometricPointMap p y = x)
    [IsLocalRing (etaleLocalRing B S hS F x)]
    [IsLocalRing (etaleLocalRing B S hS G (geometricPointMap a x))]
    (hfield : IsLocalRing.maximalIdeal
      (etaleLocalRing B S hS G (geometricPointMap a x)) = ⊥)
    (m : etaleLocalRing B S hS F x)
    (hm : m ∈ IsLocalRing.maximalIdeal (etaleLocalRing B S hS F x)) :
    etaleLocalRingMap hF j x ((etaleLocalRingCongr hy).symm
        (etaleLocalRingMap hH p y ((etaleLocalRingCongr h).symm m))) = 0 := by
  subst hy
  let : IsLocalRing (etaleLocalRing B S hS F (geometricPointMap p (geometricPointMap j x))) :=
    isLocalRing_etaleLocalRing B S hS F hF _
  let : IsLocalRing (etaleLocalRing B S hS F (geometricPointMap (j ≫ p) x)) :=
    isLocalRing_etaleLocalRing B S hS F hF _
  let : IsLocalRing (etaleLocalRing B S hS F (geometricPointMap (a ≫ b) x)) :=
    isLocalRing_etaleLocalRing B S hS F hF _
  let : IsLocalRing (etaleLocalRing B S hS F (geometricPointMap b (geometricPointMap a x))) :=
    isLocalRing_etaleLocalRing B S hS F hF _
  let := isLocalHom_etaleLocalRingMap B S hS hG hF b (geometricPointMap a x)
  let := isLocalHom_ringEquiv (etaleLocalRingCongr h).symm
  let := isLocalHom_ringEquiv
    (etaleLocalRingCongr (congrArg (fun k => geometricPointMap k x) hjp))
  set v := (etaleLocalRingCongr h).symm m with hv
  set w := (etaleLocalRingCongr (congrArg (fun k => geometricPointMap k x) hjp)).toRingHom v
    with hw
  have hvmem : v ∈ IsLocalRing.maximalIdeal
      (etaleLocalRing B S hS F (geometricPointMap p (geometricPointMap j x))) :=
    _root_.map_nonunit (etaleLocalRingCongr h).symm.toRingHom m hm
  have hwmem : w ∈ IsLocalRing.maximalIdeal
      (etaleLocalRing B S hS F (geometricPointMap b (geometricPointMap a x))) :=
    _root_.map_nonunit
      (etaleLocalRingCongr (congrArg (fun k => geometricPointMap k x) hjp)).toRingHom v hvmem
  have hzero : etaleLocalRingMap hG b (geometricPointMap a x) w = 0 := by
    have hmem := _root_.map_nonunit (etaleLocalRingMap hG b (geometricPointMap a x)) w hwmem
    rwa [hfield, Ideal.mem_bot] at hmem
  refine (etaleLocalRingMap_comp_apply_of_comp_eq hF hH j p _ hjp x v).trans
    ((DFunLike.congr_fun (etaleLocalRingMap_comp hF hG a b x) w).symm.trans ?_)
  change etaleLocalRingMap hF a x (etaleLocalRingMap hG b (geometricPointMap a x) w) = 0
  rw [hzero, map_zero]

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-! ### The two identity sections -/

/-- The section `j₁ : R ⟶ R ×_{s, U, t} R` of the second projection sending an arrow `a` to the
composable pair `(e(t a), a)`. -/
def identitySectionAfterTarget (G : GroupoidInAlgebraicSpaces C S hS B) :
    G.arrows.obj ⟶ pullback G.source.hom G.target.hom :=
  pullback.lift (identityAfterTarget G (𝟙 _)) (𝟙 _)
    (identityAfterTarget_composable G (𝟙 _))

/-- The section `j₂ : R ⟶ R ×_{s, U, t} R` of the first projection sending an arrow `a` to the
composable pair `(a, e(s a))`. -/
def identitySectionAfterSource (G : GroupoidInAlgebraicSpaces C S hS B) :
    G.arrows.obj ⟶ pullback G.source.hom G.target.hom :=
  pullback.lift (𝟙 _) (identityAfterSource G (𝟙 _))
    (identityAfterSource_composable G (𝟙 _))

/-- Composing `j₁` with the composition law is the identity: the identity arrow at the target
of an arrow is a left unit. -/
theorem identitySectionAfterTarget_comp_comp (G : GroupoidInAlgebraicSpaces C S hS B) :
    identitySectionAfterTarget G ≫ G.comp.hom = 𝟙 G.arrows.obj :=
  groupoidCompose_leftIdentity G (𝟙 _)

/-- Composing `j₂` with the composition law is the identity: the identity arrow at the source
of an arrow is a right unit. -/
theorem identitySectionAfterSource_comp_comp (G : GroupoidInAlgebraicSpaces C S hS B) :
    identitySectionAfterSource G ≫ G.comp.hom = 𝟙 G.arrows.obj :=
  groupoidCompose_rightIdentity G (𝟙 _)

/-- The first component of `j₁` is the identity arrow at the target. -/
theorem identitySectionAfterTarget_comp_fst (G : GroupoidInAlgebraicSpaces C S hS B) :
    identitySectionAfterTarget G ≫ pullback.fst G.source.hom G.target.hom =
      G.target.hom ≫ (identityArrow G).hom := by
  rw [identitySectionAfterTarget, pullback.lift_fst]
  exact Category.id_comp _

/-- The second component of `j₁` is the arrow itself. -/
theorem identitySectionAfterTarget_comp_snd (G : GroupoidInAlgebraicSpaces C S hS B) :
    identitySectionAfterTarget G ≫ pullback.snd G.source.hom G.target.hom =
      𝟙 G.arrows.obj :=
  pullback.lift_snd _ _ _

/-- The first component of `j₂` is the arrow itself. -/
theorem identitySectionAfterSource_comp_fst (G : GroupoidInAlgebraicSpaces C S hS B) :
    identitySectionAfterSource G ≫ pullback.fst G.source.hom G.target.hom =
      𝟙 G.arrows.obj :=
  pullback.lift_fst _ _ _

/-- The second component of `j₂` is the identity arrow at the source. -/
theorem identitySectionAfterSource_comp_snd (G : GroupoidInAlgebraicSpaces C S hS B) :
    identitySectionAfterSource G ≫ pullback.snd G.source.hom G.target.hom =
      G.source.hom ≫ (identityArrow G).hom := by
  rw [identitySectionAfterSource, pullback.lift_snd]
  exact Category.id_comp _

/-- The identity arrow at the source of an identity arrow is that identity arrow. -/
theorem identityArrow_comp_sourceIdentity (G : GroupoidInAlgebraicSpaces C S hS B) :
    (identityArrow G).hom ≫ G.source.hom ≫ (identityArrow G).hom = (identityArrow G).hom := by
  rw [← Category.assoc, identityArrow_hom_comp_source, Category.id_comp]

/-- The identity arrow at the target of an identity arrow is that identity arrow. -/
theorem identityArrow_comp_targetIdentity (G : GroupoidInAlgebraicSpaces C S hS B) :
    (identityArrow G).hom ≫ G.target.hom ≫ (identityArrow G).hom = (identityArrow G).hom := by
  rw [← Category.assoc, identityArrow_hom_comp_target, Category.id_comp]

/-- The two identity sections agree on identity arrows: both send the identity arrow at an
object to the composable pair of that identity arrow with itself. -/
theorem identityArrow_comp_identitySection (G : GroupoidInAlgebraicSpaces C S hS B) :
    (identityArrow G).hom ≫ identitySectionAfterTarget G =
      (identityArrow G).hom ≫ identitySectionAfterSource G := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, identitySectionAfterTarget_comp_fst,
      identitySectionAfterSource_comp_fst, Category.comp_id,
      identityArrow_comp_targetIdentity]
  · rw [Category.assoc, Category.assoc, identitySectionAfterTarget_comp_snd,
      identitySectionAfterSource_comp_snd, Category.comp_id,
      identityArrow_comp_sourceIdentity]


/-! ### The étale local rings at an identity arrow -/

/-- The space of composable pairs of arrows of a groupoid in algebraic spaces is an algebraic
space, in the spelling as a presheaf fibre product. -/
theorem isAlgebraicSpace_composablePairs (G : GroupoidInAlgebraicSpaces C S hS B) :
    IsAlgebraicSpace C S hS (pullback G.source.hom G.target.hom) :=
  (AlgebraicSpaces.fiberProduct C S hS G.source G.target).property

section

variable (G : GroupoidInAlgebraicSpaces C S hS B)
  (z : Space.GeometricPoint C S hS G.objects.obj)

/-- The geometric point of the arrow space given by the identity arrow at a geometric point of
the object space. -/
abbrev identityArrowPoint : Space.GeometricPoint C S hS G.arrows.obj :=
  Space.geometricPointMap (identityArrow G).hom z

/-- The geometric point of the space of composable pairs of arrows given by the pair of
identity arrows at a geometric point of the object space. -/
abbrev identityPairPoint :
    Space.GeometricPoint C S hS (pullback G.source.hom G.target.hom) :=
  Space.geometricPointMap (identitySectionAfterSource G) (identityArrowPoint G z)

/-- The other identity section carries the identity arrow to the same geometric point of the
space of composable pairs. -/
theorem geometricPointMap_identitySectionAfterTarget :
    Space.geometricPointMap (identitySectionAfterTarget G) (identityArrowPoint G z) =
      identityPairPoint G z :=
  congrArg (fun k => Space.geometricPointMap k z) (identityArrow_comp_identitySection G)

/-- The composition law carries the pair of identity arrows to the identity arrow. -/
theorem geometricPointMap_comp_identityPairPoint :
    Space.geometricPointMap G.comp.hom (identityPairPoint G z) = identityArrowPoint G z :=
  congrArg (fun k => Space.geometricPointMap k z)
    (show (identityArrow G).hom ≫ identitySectionAfterSource G ≫ G.comp.hom =
        (identityArrow G).hom by
      rw [identitySectionAfterSource_comp_comp, Category.comp_id])

/-- The first projection carries the pair of identity arrows to the identity arrow. -/
theorem geometricPointMap_fst_identityPairPoint :
    Space.geometricPointMap (pullback.fst G.source.hom G.target.hom) (identityPairPoint G z) =
      identityArrowPoint G z :=
  congrArg (fun k => Space.geometricPointMap k z)
    (show (identityArrow G).hom ≫ identitySectionAfterSource G ≫
        pullback.fst G.source.hom G.target.hom = (identityArrow G).hom by
      rw [identitySectionAfterSource_comp_fst, Category.comp_id])

/-- The second projection carries the pair of identity arrows to the identity arrow. -/
theorem geometricPointMap_snd_identityPairPoint :
    Space.geometricPointMap (pullback.snd G.source.hom G.target.hom) (identityPairPoint G z) =
      identityArrowPoint G z :=
  congrArg (fun k => Space.geometricPointMap k z)
    (show (identityArrow G).hom ≫ identitySectionAfterSource G ≫
        pullback.snd G.source.hom G.target.hom = (identityArrow G).hom by
      rw [identitySectionAfterSource_comp_snd, identityArrow_comp_sourceIdentity])

/-- The source carries the identity arrow at a geometric point of the object space back to that
point. -/
theorem geometricPointMap_source_identityArrowPoint :
    Space.geometricPointMap G.source.hom (identityArrowPoint G z) = z :=
  congrArg (fun k => Space.geometricPointMap k z) (identityArrow_hom_comp_source G)

/-- The target carries the identity arrow at a geometric point of the object space back to that
point. -/
theorem geometricPointMap_target_identityArrowPoint :
    Space.geometricPointMap G.target.hom (identityArrowPoint G z) = z :=
  congrArg (fun k => Space.geometricPointMap k z) (identityArrow_hom_comp_target G)

/-- The homomorphism of étale local rings induced by the composition law at the pair of
identity arrows: the map `c^#` of [Stacks Project, Tag 06E4]. -/
def identityPairComp :
    Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z) →+*
      Space.etaleLocalRing C S hS (pullback G.source.hom G.target.hom)
        (identityPairPoint G z) :=
  (Space.etaleLocalRingMap (isAlgebraicSpace_composablePairs G) G.comp.hom
      (identityPairPoint G z)).comp
    (Space.etaleLocalRingCongr (geometricPointMap_comp_identityPairPoint G z)).symm.toRingHom

/-- The homomorphism of étale local rings induced by the first projection at the pair of
identity arrows. -/
def identityPairLeft :
    Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z) →+*
      Space.etaleLocalRing C S hS (pullback G.source.hom G.target.hom)
        (identityPairPoint G z) :=
  (Space.etaleLocalRingMap (isAlgebraicSpace_composablePairs G)
      (pullback.fst G.source.hom G.target.hom) (identityPairPoint G z)).comp
    (Space.etaleLocalRingCongr (geometricPointMap_fst_identityPairPoint G z)).symm.toRingHom

/-- The homomorphism of étale local rings induced by the second projection at the pair of
identity arrows. -/
def identityPairRight :
    Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z) →+*
      Space.etaleLocalRing C S hS (pullback G.source.hom G.target.hom)
        (identityPairPoint G z) :=
  (Space.etaleLocalRingMap (isAlgebraicSpace_composablePairs G)
      (pullback.snd G.source.hom G.target.hom) (identityPairPoint G z)).comp
    (Space.etaleLocalRingCongr (geometricPointMap_snd_identityPairPoint G z)).symm.toRingHom

/-- The retraction of étale local rings carried by the identity section `j₂`, undoing the
composition law and the first projection. -/
def identityPairFst :
    Space.etaleLocalRing C S hS (pullback G.source.hom G.target.hom)
        (identityPairPoint G z) →+*
      Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z) :=
  Space.etaleLocalRingMap G.arrows.property (identitySectionAfterSource G)
    (identityArrowPoint G z)

/-- The retraction of étale local rings carried by the identity section `j₁`, undoing the
composition law and the second projection. -/
def identityPairSnd :
    Space.etaleLocalRing C S hS (pullback G.source.hom G.target.hom)
        (identityPairPoint G z) →+*
      Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z) :=
  (Space.etaleLocalRingMap G.arrows.property (identitySectionAfterTarget G)
      (identityArrowPoint G z)).comp
    (Space.etaleLocalRingCongr (geometricPointMap_identitySectionAfterTarget G z)).symm.toRingHom

/-- The retraction `j₂^#` undoes the composition law. -/
theorem identityPairFst_comp_identityPairComp :
    (identityPairFst G z).comp (identityPairComp G z) = RingHom.id _ :=
  RingHom.ext fun m =>
    Space.comp_etaleLocalRingMap_apply_of_section G.arrows.property
      (isAlgebraicSpace_composablePairs G) (identitySectionAfterSource G) G.comp.hom
      (identitySectionAfterSource_comp_comp G) (identityArrowPoint G z)
      (identityPairPoint G z) rfl (geometricPointMap_comp_identityPairPoint G z) m

/-- The retraction `j₂^#` undoes the first projection. -/
theorem identityPairFst_comp_identityPairLeft :
    (identityPairFst G z).comp (identityPairLeft G z) = RingHom.id _ :=
  RingHom.ext fun m =>
    Space.comp_etaleLocalRingMap_apply_of_section G.arrows.property
      (isAlgebraicSpace_composablePairs G) (identitySectionAfterSource G)
      (pullback.fst G.source.hom G.target.hom)
      (identitySectionAfterSource_comp_fst G) (identityArrowPoint G z)
      (identityPairPoint G z) rfl (geometricPointMap_fst_identityPairPoint G z) m

/-- The retraction `j₁^#` undoes the composition law. -/
theorem identityPairSnd_comp_identityPairComp :
    (identityPairSnd G z).comp (identityPairComp G z) = RingHom.id _ :=
  RingHom.ext fun m =>
    Space.comp_etaleLocalRingMap_apply_of_section G.arrows.property
      (isAlgebraicSpace_composablePairs G) (identitySectionAfterTarget G) G.comp.hom
      (identitySectionAfterTarget_comp_comp G) (identityArrowPoint G z)
      (identityPairPoint G z) (geometricPointMap_identitySectionAfterTarget G z)
      (geometricPointMap_comp_identityPairPoint G z) m

/-- The retraction `j₁^#` undoes the second projection. -/
theorem identityPairSnd_comp_identityPairRight :
    (identityPairSnd G z).comp (identityPairRight G z) = RingHom.id _ :=
  RingHom.ext fun m =>
    Space.comp_etaleLocalRingMap_apply_of_section G.arrows.property
      (isAlgebraicSpace_composablePairs G) (identitySectionAfterTarget G)
      (pullback.snd G.source.hom G.target.hom)
      (identitySectionAfterTarget_comp_snd G) (identityArrowPoint G z)
      (identityPairPoint G z) (geometricPointMap_identitySectionAfterTarget G z)
      (geometricPointMap_snd_identityPairPoint G z) m

/-- The remaining composite `j₂^# ∘ pr₂^#` kills the maximal ideal: it factors through the
étale local ring of the object space, which is a field. -/
theorem identityPairFst_identityPairRight_eq_zero
    [IsLocalRing (Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z))]
    (hfield : ∀ w : Space.GeometricPoint C S hS G.objects.obj,
      IsField (Space.etaleLocalRing C S hS G.objects.obj w))
    (m : Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z))
    (hm : m ∈ IsLocalRing.maximalIdeal
      (Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z))) :
    identityPairFst G z (identityPairRight G z m) = 0 := by
  let : IsLocalRing (Space.etaleLocalRing C S hS G.objects.obj
      (Space.geometricPointMap G.source.hom (identityArrowPoint G z))) :=
    Space.isLocalRing_etaleLocalRing C S hS G.objects.obj G.objects.property _
  exact Space.comp_etaleLocalRingMap_apply_eq_zero_of_factors G.arrows.property
    G.objects.property (isAlgebraicSpace_composablePairs G) (identitySectionAfterSource G)
    (pullback.snd G.source.hom G.target.hom) G.source.hom (identityArrow G).hom
    (identitySectionAfterSource_comp_snd G) (identityArrowPoint G z) (identityPairPoint G z)
    rfl (geometricPointMap_snd_identityPairPoint G z)
    (Space.maximalIdeal_eq_bot_of_isField (hfield _)) m hm

/-- The remaining composite `j₁^# ∘ pr₁^#` kills the maximal ideal: it factors through the
étale local ring of the object space, which is a field. -/
theorem identityPairSnd_identityPairLeft_eq_zero
    [IsLocalRing (Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z))]
    (hfield : ∀ w : Space.GeometricPoint C S hS G.objects.obj,
      IsField (Space.etaleLocalRing C S hS G.objects.obj w))
    (m : Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z))
    (hm : m ∈ IsLocalRing.maximalIdeal
      (Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z))) :
    identityPairSnd G z (identityPairLeft G z m) = 0 := by
  let : IsLocalRing (Space.etaleLocalRing C S hS G.objects.obj
      (Space.geometricPointMap G.target.hom (identityArrowPoint G z))) :=
    Space.isLocalRing_etaleLocalRing C S hS G.objects.obj G.objects.property _
  exact Space.comp_etaleLocalRingMap_apply_eq_zero_of_factors G.arrows.property
    G.objects.property (isAlgebraicSpace_composablePairs G) (identitySectionAfterTarget G)
    (pullback.fst G.source.hom G.target.hom) G.target.hom (identityArrow G).hom
    (identitySectionAfterTarget_comp_fst G) (identityArrowPoint G z) (identityPairPoint G z)
    (geometricPointMap_identitySectionAfterTarget G z)
    (geometricPointMap_fst_identityPairPoint G z)
    (Space.maximalIdeal_eq_bot_of_isField (hfield _)) m hm

/-- **Flatness of the composition law on étale local rings.** For a groupoid in algebraic
spaces whose object space is the spectrum of a field, the homomorphism of étale local rings
induced by the composition law at the pair of identity arrows is flat.

This is Tag 06E0 — flatness of the composition law — read through Tag 04NG. -/
theorem flat_identityPairComp {k : Type u} [Field k]
    (structureMap : Spec (.of k) ⟶ S) (hk : C.Contains (Spec (.of k)))
    (objects_eq : G.objects =
      schemeSpace (Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS))) :
    (identityPairComp G z).Flat := by
  have hflat : (Space.etaleLocalRingMap (isAlgebraicSpace_composablePairs G) G.comp.hom
      (identityPairPoint G z)).Flat := by
    refine (Space.isFlatAt_iff_etaleLocalRingMap_flat (isAlgebraicSpace_composablePairs G)
      G.arrows.property G.comp.hom (identityPairPoint G z)).mp ?_
    exact (Space.isFlat_iff_forall_isFlatAt C S hS G.comp.hom).mp
      (isFlat_comp_of_objects_eq_spec_field C S hS structureMap hk B G objects_eq).1 _
  exact (RingHom.Flat.comp_iff_of_bijective_right
    (Space.etaleLocalRingCongr
      (geometricPointMap_comp_identityPairPoint G z)).symm.bijective).mpr hflat


/-- **The local computation of Stacks 06E4, reduced to Tag 06DU.** Let `G` be a groupoid in
algebraic spaces whose object space is the spectrum of a field `k`, and let `z` be a geometric
point of the object space.  Write `A` for the étale local ring of the arrow space at the
identity arrow at `z` and `C` for the étale local ring of the space of composable pairs at the
pair of identity arrows.  If contracting a minimal prime of `C` along the two projections is a
bijection onto the pairs of minimal primes of `A`, and each minimal prime of `C` is the
smallest prime containing the images of its two contractions, then `A` has a unique minimal
prime.

The two hypotheses are Tag 06DU for the pair `(A, C)`; everything else is supplied here: the
two retractions carried by the identity sections, their four identities, the vanishing of the
two remaining composites (because the étale local ring of the object space is a field) and
flatness of the composition law (Tag 06E0 through Tag 04NG).

No `@[stacks 06E4]` attribute is claimed: this is the local computation of the tag only.  Tag 06DU
for the pair `(A, C)` is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.minimalPrimesSplitAtIdentityArrow_of_isAlgClosed`,
and the tag is registered in `StacksFrontier.AlgebraicGeometry.Spaces.GroupoidArrowsUnibranch`. -/
theorem existsUnique_minimalPrimes_etaleLocalRing_identityArrow
    [IsLocalRing (Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z))]
    {k : Type u} [Field k] (structureMap : Spec (.of k) ⟶ S)
    (hk : C.Contains (Spec (.of k)))
    (objects_eq : G.objects =
      schemeSpace (Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS)))
    (hfield : ∀ w : Space.GeometricPoint C S hS G.objects.obj,
      IsField (Space.etaleLocalRing C S hS G.objects.obj w))
    (hbij : Set.BijOn
      (fun q : Ideal (Space.etaleLocalRing C S hS (pullback G.source.hom G.target.hom)
          (identityPairPoint G z)) =>
        (q.comap (identityPairLeft G z), q.comap (identityPairRight G z)))
      (minimalPrimes (Space.etaleLocalRing C S hS (pullback G.source.hom G.target.hom)
        (identityPairPoint G z)))
      (minimalPrimes (Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z)) ×ˢ
        minimalPrimes (Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z))))
    (hsmallest : ∀ q ∈ minimalPrimes (Space.etaleLocalRing C S hS
        (pullback G.source.hom G.target.hom) (identityPairPoint G z)),
      ∀ P : Ideal (Space.etaleLocalRing C S hS (pullback G.source.hom G.target.hom)
        (identityPairPoint G z)), P.IsPrime →
      (q.comap (identityPairLeft G z)).map (identityPairLeft G z) ≤ P →
      (q.comap (identityPairRight G z)).map (identityPairRight G z) ≤ P → q ≤ P) :
    ∃! p : Ideal (Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z)),
      p ∈ minimalPrimes (Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z)) :=
  StacksDraft.existsUnique_minimalPrimes_of_retraction_of_bijOn_comap_pair
    (identityPairLeft G z) (identityPairRight G z) (identityPairComp G z)
    (identityPairFst G z) (identityPairSnd G z) hbij hsmallest
    (flat_identityPairComp G z structureMap hk objects_eq)
    (identityPairFst_comp_identityPairComp G z) (identityPairFst_comp_identityPairLeft G z)
    (fun x hx => identityPairFst_identityPairRight_eq_zero G z hfield x hx)
    (identityPairSnd_comp_identityPairComp G z) (identityPairSnd_comp_identityPairRight G z)
    (fun x hx => identityPairSnd_identityPairLeft_eq_zero G z hfield x hx)

end

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
