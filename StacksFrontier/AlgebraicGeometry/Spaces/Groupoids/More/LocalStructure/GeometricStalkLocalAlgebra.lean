module

public import StacksFrontier.AlgebraicGeometry.Groupoids.More.LocalStructure.LocalAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.LocalStructure.GeometricStalkRetractions

/-!
# The local model of a groupoid in algebraic spaces at a geometric identity

Let `(U, R, s, t, c, e, i)` be a groupoid in algebraic spaces and let `ū` be a geometric point of
`U`.  The étale local rings

```
A = 𝒪_{U, ū},   B = 𝒪_{R, e(ū)},   C = 𝒪_{R ×_{s, U, t} R, (e, e)(ū)}
```

carry the eleven homomorphisms of `Stacks.Groupoids.LocalGroupoidAlgebra` and all of its
relations, including the identification `J = I·C + C·I` of the ideal of the pair of identities.
**This file assembles them**: `geometricStalkLocalGroupoidAlgebra`.

The inversion data is what this file adds to
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.sourceStalk` and the other homomorphisms already
available: the endomorphism of `B` induced by `i`, and the retraction of `C` onto `B` carried by
the section `a ↦ (a, i(a))` of the space of composable pairs.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inverseArrowSection`: the section
  `R ⟶ R ×_{s, U, t} R`, `a ↦ (a, i(a))`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inverseStalk`: the endomorphism `i : B ⟶ B`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityPairInverse`: the retraction `C ⟶ B`
  carried by `a ↦ (a, i(a))`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.geometricStalkLocalGroupoidAlgebra`: the local
  model `Stacks.Groupoids.LocalGroupoidAlgebra` assembled from `A`, `B` and `C`.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityArrow_comp_groupoidInverse`: the inverse
  of an identity arrow is that identity arrow.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inverseArrowSection_comp_comp`: an arrow composed
  with its inverse is the identity at its target.
* `AlgebraicGeometry.Space.comp_etaleLocalRingMap_apply_of_eq`: the one-step companion of
  `AlgebraicGeometry.Space.comp_etaleLocalRingMap_apply_of_factors`, for a factorisation
  `j ≫ p = a` of a morphism through a single morphism.

## Implementation notes

That the inverse of an identity arrow is that identity arrow is needed already to *type* the
endomorphism of `B`, whose source and target are indexed by the geometric point `e(ū)` and by
its image under `i`.  It is derived from the groupoid laws themselves rather than pointwise on
the evaluated groupoids: `e ∘ i` has source the target of `e`, which is the object, so the
right unit law leaves `e ∘ i` unchanged when it is composed with the identity at its source,
while the inverse law computes that same composite as `e`.

The three relations the inversion data satisfies come from the three components of
`inverseArrowSection`, read through
`AlgebraicGeometry.Space.comp_etaleLocalRingMap_apply_of_factors` and its one-step companion, so
no transport bookkeeping is done by hand.

The groupoid law `s ∘ c = s ∘ pr₂`, which `Stacks.Groupoids.LocalGroupoidAlgebra` does not carry
among its fields, holds for this instance:
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityPairComp_comp_sourceStalk`.

## References

* [Stacks Project, Tag 0CK9](https://stacks.math.columbia.edu/tag/0CK9)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Two transports of the étale local ring along the same equality of geometric points, one of
them inverted, cancel.  The two proofs need not be the same term: an equality of geometric
points is a proposition. -/
theorem etaleLocalRingCongr_apply_symm {x y : GeometricPoint B S hS F} (h h' : x = y)
    (m : etaleLocalRing B S hS F y) :
    etaleLocalRingCongr h ((etaleLocalRingCongr h').symm m) = m := by
  subst h
  rfl

/-- **One factorisation through a single morphism.**  Let `j ≫ p = a`, let `x` be a geometric
point of `F` and let `y` and `u` be the geometric points its images determine.  Then the
homomorphism of étale local rings induced by `p` after the one induced by `j` is the one induced
by `a`, each read through the transports along the displayed equalities of geometric points. -/
theorem comp_etaleLocalRingMap_apply_of_eq {H K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hH : IsAlgebraicSpace B S hS H)
    (j : F ⟶ H) (p : H ⟶ K) (a : F ⟶ K) (hjp : j ≫ p = a)
    (x : GeometricPoint B S hS F) (y : GeometricPoint B S hS H)
    (hy : geometricPointMap j x = y) (u : GeometricPoint B S hS K)
    (hu : geometricPointMap p y = u) (hv : geometricPointMap a x = u)
    (m : etaleLocalRing B S hS K u) :
    etaleLocalRingMap hF j x ((etaleLocalRingCongr hy).symm
        (etaleLocalRingMap hH p y ((etaleLocalRingCongr hu).symm m))) =
      etaleLocalRingMap hF a x ((etaleLocalRingCongr hv).symm m) := by
  subst hy hv
  have h1 := DFunLike.congr_fun (etaleLocalRingMap_comp hF hH j p x)
    ((etaleLocalRingCongr hu).symm m)
  have h2 := DFunLike.congr_fun (etaleLocalRingMap_congr hF hjp x)
    ((etaleLocalRingCongr hu).symm m)
  exact (h1.trans h2).trans (congrArg (etaleLocalRingMap hF a x)
    (etaleLocalRingCongr_apply_symm (congrArg (fun k => geometricPointMap k x) hjp) hu m))

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-! ### The inverse of an identity arrow -/

/-- The inverse of an identity arrow is that identity arrow: in a groupoid the identity at an
object is its own inverse.  This is forced by the unit law and the inverse law, with no
pointwise reasoning: `e ∘ i` has source the target of `e`, so composing it with the identity at
its source leaves it unchanged, while the inverse law computes that composite as `e`. -/
theorem identityArrow_comp_groupoidInverse (G : GroupoidInAlgebraicSpaces C S hS B) :
    (identityArrow G).hom ≫ groupoidInverse G = (identityArrow G).hom := by
  have hcomp : ((identityArrow G).hom ≫ groupoidInverse G) ≫ G.source.hom =
      (identityArrow G).hom ≫ G.target.hom := by
    rw [Category.assoc, groupoidInverse_source]
  calc (identityArrow G).hom ≫ groupoidInverse G
      = groupoidCompose G ((identityArrow G).hom ≫ groupoidInverse G)
          (identityAfterSource G ((identityArrow G).hom ≫ groupoidInverse G))
          (identityAfterSource_composable G _) :=
        (groupoidCompose_rightIdentity G _).symm
    _ = groupoidCompose G ((identityArrow G).hom ≫ groupoidInverse G)
          (identityArrow G).hom hcomp :=
        groupoidCompose_congr G _ hcomp rfl (by
          simp [identityAfterSource, ← Category.assoc, hcomp, identityArrow_hom_comp_target])
    _ = identityAfterSource G (identityArrow G).hom :=
        groupoidCompose_inverseRight G (identityArrow G).hom
    _ = (identityArrow G).hom := by
        simp [identityAfterSource, ← Category.assoc, identityArrow_hom_comp_source]

/-! ### The section pairing an arrow with its inverse -/

/-- The section `R ⟶ R ×_{s, U, t} R` of the first projection sending an arrow `a` to the
composable pair `(a, i(a))`. -/
def inverseArrowSection (G : GroupoidInAlgebraicSpaces C S hS B) :
    G.arrows.obj ⟶ pullback G.source.hom G.target.hom :=
  pullback.lift (𝟙 G.arrows.obj) (𝟙 G.arrows.obj ≫ groupoidInverse G) (by
    rw [Category.id_comp, Category.id_comp, groupoidInverse_target])

/-- The first component of `a ↦ (a, i(a))` is the arrow itself. -/
theorem inverseArrowSection_comp_fst (G : GroupoidInAlgebraicSpaces C S hS B) :
    inverseArrowSection G ≫ pullback.fst G.source.hom G.target.hom = 𝟙 G.arrows.obj :=
  pullback.lift_fst _ _ _

/-- The second component of `a ↦ (a, i(a))` is the inverse arrow. -/
theorem inverseArrowSection_comp_snd (G : GroupoidInAlgebraicSpaces C S hS B) :
    inverseArrowSection G ≫ pullback.snd G.source.hom G.target.hom = groupoidInverse G :=
  (pullback.lift_snd _ _ _).trans (Category.id_comp _)

/-- Composing `a ↦ (a, i(a))` with the composition law gives the identity at the target: an
arrow composed with its inverse is the identity at its target. -/
theorem inverseArrowSection_comp_comp (G : GroupoidInAlgebraicSpaces C S hS B) :
    inverseArrowSection G ≫ G.comp.hom = G.target.hom ≫ (identityArrow G).hom := by
  refine (groupoidCompose_inverseLeft G (𝟙 G.arrows.obj)).trans ?_
  rw [identityAfterTarget, Category.id_comp]

/-- The two sections `a ↦ (a, e(s a))` and `a ↦ (a, i(a))` agree on identity arrows. -/
theorem identityArrow_comp_inverseArrowSection (G : GroupoidInAlgebraicSpaces C S hS B) :
    (identityArrow G).hom ≫ inverseArrowSection G =
      (identityArrow G).hom ≫ identitySectionAfterSource G := by
  refine pullback.hom_ext ?_ ?_ <;>
    simp [inverseArrowSection_comp_fst, identitySectionAfterSource_comp_fst,
      inverseArrowSection_comp_snd, identitySectionAfterSource_comp_snd,
      identityArrow_comp_groupoidInverse, identityArrow_comp_sourceIdentity]

/-! ### The inversion data on the étale local rings -/

section

variable (G : GroupoidInAlgebraicSpaces C S hS B)
  (z : Space.GeometricPoint C S hS G.objects.obj)

/-- Inversion fixes the geometric point of the arrow space given by an identity arrow. -/
theorem geometricPointMap_groupoidInverse_identityArrowPoint :
    Space.geometricPointMap (groupoidInverse G) (identityArrowPoint G z) =
      identityArrowPoint G z :=
  congrArg (fun k => Space.geometricPointMap k z) (identityArrow_comp_groupoidInverse G)

/-- The section `a ↦ (a, i(a))` carries an identity arrow to the pair of identity arrows. -/
theorem geometricPointMap_inverseArrowSection :
    Space.geometricPointMap (inverseArrowSection G) (identityArrowPoint G z) =
      identityPairPoint G z :=
  congrArg (fun k => Space.geometricPointMap k z) (identityArrow_comp_inverseArrowSection G)

/-- **Stacks 0CK9.**  The endomorphism `i : B ⟶ B` of the étale local ring of the arrow space at
an identity arrow induced by inversion. -/
def inverseStalk :
    Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z) →+*
      Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z) :=
  (Space.etaleLocalRingMap G.arrows.property (groupoidInverse G)
      (identityArrowPoint G z)).comp
    (Space.etaleLocalRingCongr
      (geometricPointMap_groupoidInverse_identityArrowPoint G z)).symm.toRingHom

/-- The retraction `C ⟶ B` of étale local rings carried by the section `a ↦ (a, i(a))`. -/
def identityPairInverse :
    Space.etaleLocalRing C S hS (pullback G.source.hom G.target.hom)
        (identityPairPoint G z) →+*
      Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z) :=
  (Space.etaleLocalRingMap G.arrows.property (inverseArrowSection G)
      (identityArrowPoint G z)).comp
    (Space.etaleLocalRingCongr (geometricPointMap_inverseArrowSection G z)).symm.toRingHom

/-- The retraction carried by `a ↦ (a, i(a))` undoes the first projection. -/
theorem identityPairInverse_comp_identityPairLeft :
    (identityPairInverse G z).comp (identityPairLeft G z) = RingHom.id _ :=
  RingHom.ext fun m =>
    Space.comp_etaleLocalRingMap_apply_of_section G.arrows.property
      (isAlgebraicSpace_composablePairs G) (inverseArrowSection G)
      (pullback.fst G.source.hom G.target.hom) (inverseArrowSection_comp_fst G)
      (identityArrowPoint G z) (identityPairPoint G z)
      (geometricPointMap_inverseArrowSection G z)
      (geometricPointMap_fst_identityPairPoint G z) m

/-- The retraction carried by `a ↦ (a, i(a))` turns the second projection into inversion. -/
theorem identityPairInverse_comp_identityPairRight :
    (identityPairInverse G z).comp (identityPairRight G z) = inverseStalk G z :=
  RingHom.ext fun m =>
    Space.comp_etaleLocalRingMap_apply_of_eq G.arrows.property
      (isAlgebraicSpace_composablePairs G) (inverseArrowSection G)
      (pullback.snd G.source.hom G.target.hom) (groupoidInverse G)
      (inverseArrowSection_comp_snd G) (identityArrowPoint G z) (identityPairPoint G z)
      (geometricPointMap_inverseArrowSection G z) (identityArrowPoint G z)
      (geometricPointMap_snd_identityPairPoint G z)
      (geometricPointMap_groupoidInverse_identityArrowPoint G z) m

/-- The retraction carried by `a ↦ (a, i(a))` turns the composition law into `t ∘ e`: an arrow
composed with its inverse is the identity at its target. -/
theorem identityPairInverse_comp_identityPairComp :
    (identityPairInverse G z).comp (identityPairComp G z) =
      (targetStalk G z).comp (identityStalk G z) :=
  RingHom.ext fun m =>
    Space.comp_etaleLocalRingMap_apply_of_factors G.arrows.property G.objects.property
      (isAlgebraicSpace_composablePairs G) (inverseArrowSection G) G.comp.hom
      G.target.hom (identityArrow G).hom (inverseArrowSection_comp_comp G)
      (identityArrowPoint G z) (identityPairPoint G z)
      (geometricPointMap_inverseArrowSection G z) z
      (geometricPointMap_target_identityArrowPoint G z) (identityArrowPoint G z)
      (geometricPointMap_comp_identityPairPoint G z) rfl m

/-- **Stacks 0CK9.**  Inversion does not change the unit: `e ∘ i = e` on `B`. -/
theorem identityStalk_comp_inverseStalk :
    (identityStalk G z).comp (inverseStalk G z) = identityStalk G z :=
  RingHom.ext fun m =>
    Space.comp_etaleLocalRingMap_apply_of_eq G.objects.property G.arrows.property
      (identityArrow G).hom (groupoidInverse G) (identityArrow G).hom
      (identityArrow_comp_groupoidInverse G) z (identityArrowPoint G z) rfl
      (identityArrowPoint G z)
      (geometricPointMap_groupoidInverse_identityArrowPoint G z) rfl m

/-! ### The local model -/

/-- **Stacks 0CK9.**  The local model of a groupoid in algebraic spaces at a geometric identity:
the étale local rings `A = 𝒪_{U, ū}`, `B = 𝒪_{R, e(ū)}` and
`C = 𝒪_{R ×_{s, U, t} R, (e, e)(ū)}` with the homomorphisms induced by source, target, unit, the
two projections, composition and inversion, the three retractions carried by the identity
sections and by `a ↦ (a, i(a))`, and the identification `J = I·C + C·I` of the ideal of the pair
of identities. -/
def geometricStalkLocalGroupoidAlgebra :
    Stacks.Groupoids.LocalGroupoidAlgebra
      (Space.etaleLocalRing C S hS G.objects.obj z)
      (Space.etaleLocalRing C S hS G.arrows.obj (identityArrowPoint G z))
      (Space.etaleLocalRing C S hS (pullback G.source.hom G.target.hom)
        (identityPairPoint G z)) where
  source := sourceStalk G z
  target := targetStalk G z
  identity := identityStalk G z
  first := identityPairLeft G z
  second := identityPairRight G z
  comp := identityPairComp G z
  inverse := inverseStalk G z
  rightUnit := identityPairFst G z
  leftUnit := identityPairSnd G z
  inversePair := identityPairInverse G z
  identity_source := identityStalk_comp_sourceStalk G z
  identity_target := identityStalk_comp_targetStalk G z
  rightUnit_first := identityPairFst_comp_identityPairLeft G z
  rightUnit_second := identityPairFst_comp_identityPairRight_eq G z
  leftUnit_first := identityPairSnd_comp_identityPairLeft_eq G z
  leftUnit_second := identityPairSnd_comp_identityPairRight G z
  rightUnit_comp := identityPairFst_comp_identityPairComp G z
  leftUnit_comp := identityPairSnd_comp_identityPairComp G z
  inversePair_first := identityPairInverse_comp_identityPairLeft G z
  inversePair_second := identityPairInverse_comp_identityPairRight G z
  inversePair_comp := identityPairInverse_comp_identityPairComp G z
  identity_inverse := identityStalk_comp_inverseStalk G z
  ideal_pairs := geometricPairIdeal_eq_sup G z

end

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
