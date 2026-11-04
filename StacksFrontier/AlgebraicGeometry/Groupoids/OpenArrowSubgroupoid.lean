module

public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantOpenSubgroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SchemeSplittings

/-!
# Open subschemes of the arrow scheme which are subgroupoids

Let `(U, R, s, t, c)` be a groupoid scheme and let `W ⊆ R` be an open subscheme of its arrow
scheme.  If `W` contains every identity arrow, is stable under the inverse, and is stable under
the composition of composable pairs of its own arrows, then `(U, W, s|_W, t|_W, c|_W)` is again
a groupoid scheme, and the open immersion `W ⟶ R` together with the identity of `U` is a
morphism of groupoid schemes into the ambient one.  Adding finiteness of `s|_W` and `t|_W` makes
it an open finite subgroupoid in the sense of conditions (a) and (b) of Stacks 04RK.

The three stability conditions are conditions on *points*: an open immersion is a
monomorphism through which a morphism factors exactly when its image lies in the open, so each
restricted structure morphism is obtained from the ambient one by
`Stacks.Groupoids.openOverLift`, and every groupoid axiom is then an equality of morphisms into
`U` or into `W` which may be tested after composing with a monomorphism.  That last reduction is
`Stacks.Groupoids.GroupoidScheme.MonoSubgroupoid`, so nothing here has to reprove an axiom.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.IsArrowSubgroupoid`: the three stability conditions on an
  open subscheme of the arrow scheme.
* `Stacks.Groupoids.GroupoidScheme.monoSubgroupoidOfOpens`: the subgroupoid presentation it
  carries, with objects the whole object scheme and the identity as its monomorphism of object
  schemes.
* `Stacks.Groupoids.GroupoidScheme.openFiniteSubgroupoidOfOpens`: the resulting open finite
  subgroupoid, once the restricted source and target are finite.

## Implementation notes

The monomorphism of object schemes is the identity of `U`, which is what makes the result an
`Stacks.Groupoids.GroupoidScheme.OpenFiniteSubgroupoid`: that structure asks for a subgroupoid
on the *same* object scheme, recorded as an equality of objects transported by
`CategoryTheory.eqToHom`, and here that equality is `rfl`.

The stability conditions are stated in exactly the form
`Stacks.Groupoids.openOverLift` consumes — pointwise membership of the image of the relevant
composite — rather than in the equivalent form "the range is contained in the open", so that no
rewriting intervenes between the hypothesis and the lift.  For composition the composite in
question is the comparison morphism of schemes of composable pairs followed by the ambient
composition; the comparison is `Stacks.Groupoids.GroupoidScheme.openArrowComposables`, which is
the same `CategoryTheory.Limits.pullback.map` that the `comp_ι` field of
`Stacks.Groupoids.GroupoidScheme.MonoSubgroupoid` names.

Stability under the inverse is not implied by the other two: the ambient inverse of an arrow of
`W` is an arrow with the source and the target exchanged, and nothing about `W` forces it to lie
in `W` again.  It is needed because a groupoid scheme carries its inverse as data.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} {G : GroupoidScheme S} (W : G.arrows.left.Opens)

/-! ### The restricted source and target -/

/-- The source morphism of a groupoid scheme, restricted to an open subscheme of its arrow
scheme. -/
abbrev openArrowSource : openOver G.arrows W ⟶ G.objects := openOverι G.arrows W ≫ G.source

/-- The target morphism of a groupoid scheme, restricted to an open subscheme of its arrow
scheme. -/
abbrev openArrowTarget : openOver G.arrows W ⟶ G.objects := openOverι G.arrows W ≫ G.target

theorem openArrowSource_ι :
    openArrowSource W ≫ 𝟙 G.objects = openOverι G.arrows W ≫ G.source :=
  Category.comp_id _

theorem openArrowTarget_ι :
    openArrowTarget W ≫ 𝟙 G.objects = openOverι G.arrows W ≫ G.target :=
  Category.comp_id _

/-- The comparison of the scheme of composable pairs of arrows of an open subscheme of the arrow
scheme with that of the ambient groupoid. -/
def openArrowComposables :
    pullback (openArrowSource W) (openArrowTarget W) ⟶ pullback G.source G.target :=
  pullback.map _ _ _ _ (openOverι G.arrows W) (openOverι G.arrows W) (𝟙 G.objects)
    (openArrowSource_ι W) (openArrowTarget_ι W)

/-! ### The stability conditions -/

/-- An open subscheme of the arrow scheme of a groupoid scheme is a *subgroupoid* when it
contains every identity arrow and is stable under the inverse and under the composition of its
own composable pairs. -/
structure IsArrowSubgroupoid : Prop where
  /-- Every identity arrow lies in the open. -/
  mem_identity : ∀ y : G.objects.left, G.identity.left.base y ∈ W
  /-- The inverse of an arrow of the open lies in the open. -/
  mem_inverse : ∀ x, (openOverι G.arrows W ≫ G.inverse).left.base x ∈ W
  /-- The composite of a composable pair of arrows of the open lies in the open. -/
  mem_comp : ∀ z, (openArrowComposables W ≫ G.comp).left.base z ∈ W

/-! ### The subgroupoid presentation -/

/-- **The subgroupoid presentation carried by an open subscheme of the arrow scheme which is
stable under the groupoid operations.**  Its objects are those of the ambient groupoid and its
monomorphism of object schemes is the identity. -/
def monoSubgroupoidOfOpens (h : IsArrowSubgroupoid W) : MonoSubgroupoid G where
  objects := G.objects
  arrows := openOver G.arrows W
  ιObjects := 𝟙 G.objects
  ιArrows := openOverι G.arrows W
  mono_ιObjects := inferInstance
  mono_ιArrows := inferInstance
  source := openArrowSource W
  target := openArrowTarget W
  comp := openOverLift (openArrowComposables W ≫ G.comp) W h.mem_comp
  identity := openOverLift G.identity W h.mem_identity
  inverse := openOverLift (openOverι G.arrows W ≫ G.inverse) W h.mem_inverse
  source_ι := openArrowSource_ι W
  target_ι := openArrowTarget_ι W
  identity_ι := (openOverLift_comp_openOverι _ _ _).trans (Category.id_comp _).symm
  inverse_ι := openOverLift_comp_openOverι _ _ _
  comp_ι := openOverLift_comp_openOverι _ _ _

@[simp]
theorem monoSubgroupoidOfOpens_objects (h : IsArrowSubgroupoid W) :
    (monoSubgroupoidOfOpens W h).objects = G.objects := rfl

@[simp]
theorem monoSubgroupoidOfOpens_arrows (h : IsArrowSubgroupoid W) :
    (monoSubgroupoidOfOpens W h).arrows = openOver G.arrows W := rfl

@[simp]
theorem monoSubgroupoidOfOpens_source (h : IsArrowSubgroupoid W) :
    (monoSubgroupoidOfOpens W h).source = openArrowSource W := rfl

@[simp]
theorem monoSubgroupoidOfOpens_target (h : IsArrowSubgroupoid W) :
    (monoSubgroupoidOfOpens W h).target = openArrowTarget W := rfl

/-! ### The open finite subgroupoid -/

/-- **An open subscheme of the arrow scheme which is stable under the groupoid operations and
whose restricted source and target are finite is an open finite subgroupoid**, that is, it
satisfies conditions (a) and (b) of Stacks 04RK. -/
def openFiniteSubgroupoidOfOpens (h : IsArrowSubgroupoid W)
    (hs : IsFinite (openArrowSource W).left) (ht : IsFinite (openArrowTarget W).left) :
    OpenFiniteSubgroupoid G where
  subgroupoid := (monoSubgroupoidOfOpens W h).toGroupoidScheme
  objects_eq := rfl
  inclusion := (monoSubgroupoidOfOpens W h).hom
  mapObjects_eq := rfl
  arrows_open := isOpenImmersion_openOverι_left G.arrows W
  source_finite := hs
  target_finite := ht

@[simp]
theorem openFiniteSubgroupoidOfOpens_subgroupoid_arrows (h : IsArrowSubgroupoid W)
    (hs : IsFinite (openArrowSource W).left) (ht : IsFinite (openArrowTarget W).left) :
    (openFiniteSubgroupoidOfOpens W h hs ht).subgroupoid.arrows = openOver G.arrows W := rfl

@[simp]
theorem openFiniteSubgroupoidOfOpens_inclusion_mapArrows (h : IsArrowSubgroupoid W)
    (hs : IsFinite (openArrowSource W).left) (ht : IsFinite (openArrowTarget W).left) :
    (openFiniteSubgroupoidOfOpens W h hs ht).inclusion.mapArrows = openOverι G.arrows W := rfl

end Stacks.Groupoids.GroupoidScheme

end

end
