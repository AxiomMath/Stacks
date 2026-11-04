module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeQuotientTorsor
public import StacksFrontier.Examples.Spaces.NonSeparatedGroupSpace

/-!
# `V/G` as the fppf sheafification of the presheaf of pointwise orbits

Let `S` be a scheme and let an abstract group `G` act by automorphisms over `S` on an object
`V` of a big fppf site over `S`. The Stacks Project forms the quotient `V/G` as the fppf
sheafification of the presheaf `T ↦ V(T)/G` of pointwise orbits. That sheaf is the quotient
sheaf of the graph relation of the action, and for a free action it is therefore an algebraic
space over `S`.

## Main definitions

* `AlgebraicGeometry.Space.orbitQuotientToActionQuotient` is the comparison map from the
  sheafification of the presheaf of pointwise orbits to the quotient sheaf of the graph
  relation, and `AlgebraicGeometry.Space.actionQuotientToOrbitQuotient` is its inverse.

## Main results

* `AlgebraicGeometry.Space.isoOrbitQuotientActionQuotient`: the two descriptions of `V/G`
  agree.
* `AlgebraicGeometry.Space.isAlgebraicSpace_orbitQuotientSheaf_points_of_free`:
  **Stacks 071S** for an action on an object of the site: the fppf sheafification of
  `T ↦ V(T)/G` is an algebraic space over `S` when the action is free.

## Implementation notes

The two quotients are compared by their universal properties alone. In one direction the
projection onto the quotient sheaf of the graph relation is invariant, because a point of `V`
and its translate by a group element are the source and the target of a point of the relation
scheme; that is pointwise. In the other direction the projection onto the sheafification of the
orbit presheaf identifies the source and the target of the graph relation, which is *not*
pointwise: a point of the relation scheme is concentrated in a single group element only
locally on the base. It is
`Stacks.Examples.NonSeparatedGroupSpace.actionRelation_coequalizes_of_invariant` which supplies
that step, the coproduct inclusions of the relation scheme being a covering family. The two
maps are mutually inverse because each of the two quotients is determined by its projection
from the functor of points of `V`.

The action on the functor of points is a hypothesis rather than an instance, since it is read
off a homomorphism `a : G →* Aut V` over `S`, which is not a class;
`AlgebraicGeometry.Space.isNaturalAction_points_of_smul_eq` shows that such an action is
automatically compatible with restriction, so the naturality hypothesis asks nothing new.

## References

* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    (V : BigFppfOver B S hS) (G : Type v) [Group G] [Small.{u} G]
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    [∀ T : (BigFppfOver B S hS)ᵒᵖ, MulAction G ((Stacks.Groupoids.points
      (Over.post B.inclusion) ((Over.post B.inclusion).obj V)).obj T)]
    (a : G →* Aut ((Over.post B.inclusion).obj V))

omit [Small.{u} G] [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  [∀ T : (BigFppfOver B S hS)ᵒᵖ, MulAction G ((Stacks.Groupoids.points
    (Over.post B.inclusion) ((Over.post B.inclusion).obj V)).obj T)] in
/-- The action of `G` on the functor of points of `V` attached to a homomorphism into the
automorphisms of `V` over `S`: a group element translates a point by postcomposition. It is a
left action because the product in an automorphism group is composition in the other order. -/
@[instance_reducible]
def mulActionPoints (T : (BigFppfOver B S hS)ᵒᵖ) :
    MulAction G ((Stacks.Groupoids.points (Over.post B.inclusion)
      ((Over.post B.inclusion).obj V)).obj T) where
  smul g x := x ≫ (a g).hom
  one_smul x := by
    change x ≫ (a (1 : G)).hom = x
    rw [map_one]
    exact Category.comp_id x
  mul_smul g h x := by
    change x ≫ (a (g * h)).hom = (x ≫ (a h).hom) ≫ (a g).hom
    rw [map_mul, Aut.Aut_mul_def]
    exact (Category.assoc _ _ _).symm

omit [Small.{u} G] [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- An action on the functor of points of `V` which is translation by automorphisms of `V` over
`S` is compatible with restriction, restriction being precomposition. -/
theorem isNaturalAction_points_of_smul_eq
    (hsmul : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (g : G)
      (x : (Stacks.Groupoids.points (Over.post B.inclusion)
        ((Over.post B.inclusion).obj V)).obj T),
      g • x = x ≫ (a g).hom) :
    IsNaturalAction B S hS G (Stacks.Groupoids.points (Over.post B.inclusion)
      ((Over.post B.inclusion).obj V)) := by
  intro T W f g x
  rw [hsmul, hsmul]
  show (Over.post B.inclusion).map f.unop ≫ x ≫ (a g).hom =
    ((Over.post B.inclusion).map f.unop ≫ x) ≫ (a g).hom
  exact (Category.assoc _ _ _).symm

omit [∀ T : (BigFppfOver B S hS)ᵒᵖ, MulAction G ((Stacks.Groupoids.points
      (Over.post B.inclusion) ((Over.post B.inclusion).obj V)).obj T)] in
/-- The projection onto the quotient sheaf of the graph relation of an action is invariant: a
point of `V` and its translate by a group element are the source and the target of a point of
the relation scheme, namely of the point in the copy indexed by that group element. -/
theorem toQuotientSheaf_actionRelation_smul (T : (BigFppfOver B S hS)ᵒᵖ)
    (x : (Over.post B.inclusion).obj T.unop ⟶ (Over.post B.inclusion).obj V) (g : G) :
    (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (actionRelation ((Over.post B.inclusion).obj V) G a)).app T (x ≫ (a g).hom) =
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (actionRelation ((Over.post B.inclusion).obj V) G a)).app T x := by
  have happ := NatTrans.congr_app (Stacks.Groupoids.sourceMap_toQuotientSheaf
    (BigFppfOver.topology B S hS) (Over.post B.inclusion)
    (actionRelation ((Over.post B.inclusion).obj V) G a)) T
  have h := ConcreteCategory.congr_hom happ
    (show (Over.post B.inclusion).obj T.unop ⟶
        actionRelationScheme ((Over.post B.inclusion).obj V) G from
      x ≫ Sigma.ι (fun _ : G ↦ (Over.post B.inclusion).obj V) g)
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  have hsrc : (Stacks.Groupoids.sourceMap (Over.post B.inclusion)
      (actionRelation ((Over.post B.inclusion).obj V) G a)).app T
      (x ≫ Sigma.ι (fun _ : G ↦ (Over.post B.inclusion).obj V) g) = x := by
    simp [Stacks.Groupoids.sourceMap, actionRelation, Stacks.Groupoids.PreRelation.source,
      actionRelationSource]
  have htgt : (Stacks.Groupoids.targetMap (Over.post B.inclusion)
      (actionRelation ((Over.post B.inclusion).obj V) G a)).app T
      (x ≫ Sigma.ι (fun _ : G ↦ (Over.post B.inclusion).obj V) g) = x ≫ (a g).hom := by
    simp [Stacks.Groupoids.targetMap, actionRelation, Stacks.Groupoids.PreRelation.target,
      actionRelationTarget]
  rw [hsrc, htgt] at h
  exact h.symm

variable (hnat : IsNaturalAction B S hS G (Stacks.Groupoids.points (Over.post B.inclusion)
      ((Over.post B.inclusion).obj V)))
    (hsmul : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (g : G)
      (x : (Stacks.Groupoids.points (Over.post B.inclusion)
        ((Over.post B.inclusion).obj V)).obj T),
      g • x = x ≫ (a g).hom)

include hsmul in
/-- The projection onto the quotient sheaf of the graph relation is invariant for the induced
action on the functor of points of `V`. -/
theorem toQuotientSheaf_smul_points (T : (BigFppfOver B S hS)ᵒᵖ) (g : G)
    (x : (Stacks.Groupoids.points (Over.post B.inclusion)
      ((Over.post B.inclusion).obj V)).obj T) :
    (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (actionRelation ((Over.post B.inclusion).obj V) G a)).app T (g • x) =
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (actionRelation ((Over.post B.inclusion).obj V) G a)).app T x := by
  rw [hsmul]
  exact toQuotientSheaf_actionRelation_smul B hS V G a T x g

/-- The comparison map from the fppf sheafification of the presheaf of pointwise orbits of `V`
to the quotient sheaf of the graph relation of the action, obtained from the invariance of the
projection onto the latter. -/
noncomputable def orbitQuotientToActionQuotient :
    (orbitQuotientSheaf B S hS G (Stacks.Groupoids.points (Over.post B.inclusion)
        ((Over.post B.inclusion).obj V)) hnat).obj ⟶ actionQuotient G B hS V a :=
  orbitQuotientLift B S hS G _ hnat
    (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
      (actionRelation ((Over.post B.inclusion).obj V) G a))
    (toQuotientSheaf_smul_points B hS V G a hsmul)
    (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
      (actionRelation ((Over.post B.inclusion).obj V) G a)).property

/-- The comparison map carries the projection from the functor of points of `V` onto the
sheafified orbit presheaf to the projection onto the quotient sheaf of the graph relation. -/
theorem toOrbitQuotient_orbitQuotientToActionQuotient :
    toOrbitQuotient B S hS G (Stacks.Groupoids.points (Over.post B.inclusion)
          ((Over.post B.inclusion).obj V)) hnat ≫
        orbitQuotientToActionQuotient B hS V G a hnat hsmul =
      Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (actionRelation ((Over.post B.inclusion).obj V) G a) := by
  show toOrbitPresheaf B S hS G _ hnat ≫ toSheafify _ _ ≫ sheafifyLift _ _ _ = _
  rw [toSheafify_sheafifyLift]
  refine NatTrans.ext (funext fun T => ?_)
  apply ConcreteCategory.hom_ext
  intro x
  rfl

variable (hR : B.Contains (actionRelationScheme ((Over.post B.inclusion).obj V) G).left)

include hsmul in
/-- The comparison map out of the quotient sheaf of the graph relation of the action, obtained
from the fact that the projection onto the sheafified orbit presheaf identifies the source and
the target of the relation. -/
noncomputable def actionQuotientToOrbitQuotient :
    Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (actionRelation ((Over.post B.inclusion).obj V) G a) ⟶
      orbitQuotientSheaf B S hS G (Stacks.Groupoids.points (Over.post B.inclusion)
        ((Over.post B.inclusion).obj V)) hnat :=
  Stacks.Groupoids.quotientSheafDesc (BigFppfOver.topology B S hS) (Over.post B.inclusion)
    (actionRelation ((Over.post B.inclusion).obj V) G a) _
    (toOrbitQuotient B S hS G _ hnat)
    (Stacks.Examples.NonSeparatedGroupSpace.actionRelation_coequalizes_of_invariant B S hS V G a
      hR (orbitQuotientSheaf B S hS G _ hnat).property (toOrbitQuotient B S hS G _ hnat)
      (fun T x g => by
        rw [← hsmul]
        exact toOrbitQuotient_smul B S hS G _ hnat g x))

include hsmul in
/-- The second comparison map carries the projection onto the quotient sheaf of the graph
relation to the projection onto the sheafified orbit presheaf. -/
theorem toQuotientSheaf_actionQuotientToOrbitQuotient :
    Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
          (actionRelation ((Over.post B.inclusion).obj V) G a) ≫
        (actionQuotientToOrbitQuotient B hS V G a hnat hsmul hR).hom =
      toOrbitQuotient B S hS G (Stacks.Groupoids.points (Over.post B.inclusion)
        ((Over.post B.inclusion).obj V)) hnat :=
  Stacks.Groupoids.toQuotientSheaf_quotientSheafDesc _ _ _ _ _ _

include hsmul in
/-- The two descriptions of `V/G` agree as sheaves: the fppf sheafification of the presheaf
`T ↦ V(T)/G` of pointwise orbits is the quotient sheaf of the graph relation of the action. -/
noncomputable def sheafIsoOrbitQuotientActionQuotient :
    orbitQuotientSheaf B S hS G (Stacks.Groupoids.points (Over.post B.inclusion)
        ((Over.post B.inclusion).obj V)) hnat ≅
      Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (actionRelation ((Over.post B.inclusion).obj V) G a) := by
  have h1 := toOrbitQuotient_orbitQuotientToActionQuotient B hS V G a hnat hsmul
  have h2 := toQuotientSheaf_actionQuotientToOrbitQuotient B hS V G a hnat hsmul hR
  refine ⟨⟨orbitQuotientToActionQuotient B hS V G a hnat hsmul⟩,
    actionQuotientToOrbitQuotient B hS V G a hnat hsmul hR, ?_, ?_⟩
  · apply Sheaf.hom_ext
    change orbitQuotientToActionQuotient B hS V G a hnat hsmul ≫
      (actionQuotientToOrbitQuotient B hS V G a hnat hsmul hR).hom = 𝟙 _
    have key : toOrbitQuotient B S hS G (Stacks.Groupoids.points (Over.post B.inclusion)
          ((Over.post B.inclusion).obj V)) hnat ≫
        (orbitQuotientToActionQuotient B hS V G a hnat hsmul ≫
          (actionQuotientToOrbitQuotient B hS V G a hnat hsmul hR).hom) =
        toOrbitQuotient B S hS G (Stacks.Groupoids.points (Over.post B.inclusion)
          ((Over.post B.inclusion).obj V)) hnat := by
      rw [← Category.assoc, h1]
      exact h2
    refine sheafify_hom_ext (BigFppfOver.topology B S hS) _ _
      (orbitQuotientSheaf B S hS G (Stacks.Groupoids.points (Over.post B.inclusion)
        ((Over.post B.inclusion).obj V)) hnat).property ?_
    refine NatTrans.ext (funext fun T => ?_)
    apply ConcreteCategory.hom_ext
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
      have hk := ConcreteCategory.congr_hom (NatTrans.congr_app key T) x
      simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, toOrbitQuotient_app] at hk
      exact hk
  · refine Stacks.Groupoids.quotientSheaf_hom_ext _ _ _ _ _ _ ?_
    change Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (actionRelation ((Over.post B.inclusion).obj V) G a) ≫
        ((actionQuotientToOrbitQuotient B hS V G a hnat hsmul hR).hom ≫
          orbitQuotientToActionQuotient B hS V G a hnat hsmul) = _
    rw [← Category.assoc, h2, h1]
    simp

include hsmul in
/-- The two descriptions of `V/G` agree: the fppf sheafification of the presheaf `T ↦ V(T)/G`
of pointwise orbits is the quotient sheaf of the graph relation of the action. -/
noncomputable def isoOrbitQuotientActionQuotient :
    (orbitQuotientSheaf B S hS G (Stacks.Groupoids.points (Over.post B.inclusion)
        ((Over.post B.inclusion).obj V)) hnat).obj ≅ actionQuotient G B hS V a :=
  (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).mapIso
    (sheafIsoOrbitQuotientActionQuotient B hS V G a hnat hsmul hR)

include hsmul in
/-- **Stacks 071S** for an action on an object of a big fppf site over `S`: the quotient of `V`
by a free action of an abstract group `G`, formed as in the source as the fppf sheafification
of the presheaf `T ↦ V(T)/G` of pointwise orbits, is an algebraic space over `S`.

That quotient is the quotient sheaf of the graph relation of the action, by
`AlgebraicGeometry.Space.isoOrbitQuotientActionQuotient`, so this is
`AlgebraicGeometry.Space.isAlgebraicSpace_actionQuotient_of_actsFreelyOnNonemptyPoints`. -/
@[stacks 071S "for an action of the abstract group on an object of the big fppf site in place \
of an arbitrary algebraic space, and with freeness read on the points over the test schemes \
with nonempty underlying space"]
theorem isAlgebraicSpace_orbitQuotientSheaf_points_of_free
    (ha : ActsFreelyOnNonemptyPoints ((Over.post B.inclusion).obj V) G a) :
    IsAlgebraicSpace B S hS (orbitQuotientSheaf B S hS G
      (Stacks.Groupoids.points (Over.post B.inclusion)
        ((Over.post B.inclusion).obj V)) hnat).obj :=
  isAlgebraicSpace_of_iso B S hS
    (isoOrbitQuotientActionQuotient B hS V G a hnat hsmul
      (contains_actionRelationScheme G B hS V a
        (actsNontriviallyOnFixedResidueFields_of_actsFreelyOnNonemptyPoints _ G a ha))).symm
    (isAlgebraicSpace_actionQuotient_of_actsFreelyOnNonemptyPoints G B hS V a ha)

end AlgebraicGeometry.Space

end
