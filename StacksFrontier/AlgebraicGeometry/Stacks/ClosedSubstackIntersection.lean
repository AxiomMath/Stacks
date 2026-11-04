module

public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SubstackSchemeProperty
import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
import StacksFrontier.AlgebraicGeometry.Spaces.ZeroScheme
import StacksFrontier.AlgebraicGeometry.Stacks.ReducedStackClosedSubstack
import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack
import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangeComposite

/-!
# Intersections of closed substacks

Let `𝒳` be an algebraic stack over `S`. An arbitrary intersection of closed substacks of `𝒳`
(Stacks 04YM, part (2)) is again a closed substack. This is the closedness clause of
**Stacks 0CPU**, the existence of scheme theoretic images
(`AlgebraicGeometry.Stack.hasSchemeTheoreticImage`).

## Main results

* `AlgebraicGeometry.Stack.IsClosedSubstack.prop_of_hom`: membership of a closed substack is
  inherited along morphisms of `𝒳`.
* `AlgebraicGeometry.Stack.isClosedSubspace_fullSubcategoryBaseChangeSubfunctor`: the base change
  of the inclusion of a closed substack along a scheme-valued point with values in `W` is a closed
  subspace of `W`.
* `AlgebraicGeometry.Stack.isClosedSubstack_of_forall_isClosedSubspace`: conversely, a property
  inherited along morphisms whose base changes along all scheme-valued points are closed
  subspaces cuts out a closed substack.
* `AlgebraicGeometry.Stack.isClosedSubstack_sInf`: an intersection of closed substacks is a
  closed substack.

## The proof

Write `P` for the intersection of a family of closed substacks `Q`. Each `Q` is inherited along
morphisms, because its full subcategory is fibred in groupoids and every morphism of `𝒳` is
strongly cartesian, so `P` is inherited along morphisms too; in particular its full subcategory is
fibred in groupoids (`AlgebraicGeometry.Stack.isFiberedInGroupoids_fullSubcategoryBased`).

The base change of the inclusion of the full subcategory of such a property along a scheme-valued
point `z` with values in `W` is the category of elements of a subfunctor of `yoneda W`
(`AlgebraicGeometry.Stack.nonempty_equivalenceOver_fullSubcategoryBaseChange`), whose sections
over `T` are present exactly when the property holds at `z T`. For a closed substack `Q` that
subfunctor is an algebraic space, being isomorphic to any algebraic space representing the base
change, and its inclusion into `yoneda W` is a closed immersion: the closed immersion condition of
Stacks 04YL gives that the structural morphism of its lower-shriek extension to `S` is a closed
immersion (`AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff`), and a closed immersion is
inherited from its lower-shriek extension
(`AlgebraicGeometry.Space.isClosedImmersion_of_relocalizeMap`).

For `P` the subfunctor is the intersection of the subfunctors of the members, so it is a closed
subspace of `W` by `AlgebraicGeometry.Space.isClosedSubspace_sInf`. This makes the inclusion of
the full subcategory of `P` representable by algebraic spaces
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion`); that
full subcategory is then an algebraic stack by **Stacks 05UM**, and the inclusion is a closed
immersion because the lower-shriek extension of a closed immersion is one
(`AlgebraicGeometry.Space.isClosedImmersion_relocalize`) and any algebraic space representing the
base change is isomorphic to the subfunctor.

No quasi-coherent ideal sheaf on `𝒳` or on a presentation of it is used, and no correspondence
between closed substacks and invariant closed subspaces of a presentation: the scheme-theoretic
intersection is formed only on the schemes the closed subspaces are base changed to, inside
`AlgebraicGeometry.Space.isClosedImmersion_ι_sInf`.

## References

* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 0CPU](https://stacks.math.columbia.edu/tag/0CPU)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Membership of a closed substack is inherited along morphisms.** If `Q` cuts out a closed
substack of `𝒳` and `φ : a ⟶ b` is a morphism of `𝒳` with `Q b`, then `Q a`: the full subcategory
of `Q` is fibred in groupoids and `φ` is strongly cartesian. -/
theorem IsClosedSubstack.prop_of_hom {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {Q : ObjectProperty 𝒳.val.val.obj} (hQ : IsClosedSubstack 𝒳 Q)
    {a b : 𝒳.val.val.obj} (φ : a ⟶ b) (hb : Q b) : Q a :=
  IsSubstackWith.prop_of_hom (Q := @AlgebraicGeometry.IsClosedImmersion.{u}) hQ φ hb

/-- **The base change of the inclusion of a closed substack is a closed subspace.** Let `Q` cut
out a closed substack of `𝒳` and let `z` be a scheme-valued point of `𝒳` with values in `W`. The
subfunctor of `yoneda W` whose sections over `T` are present exactly when `Q` holds at `z T` is a
closed subspace of `W`.

It is an algebraic space because it is isomorphic to any algebraic space representing the base
change of the inclusion along `z`, and its inclusion is a closed immersion because the lower-shriek
extension of that inclusion is, up to the isomorphism
`AlgebraicGeometry.isIso_relocalizeToYoneda_yonedaId`, the structural morphism that the closed
immersion condition of Stacks 04YL is about. -/
theorem isClosedSubspace_fullSubcategoryBaseChangeSubfunctor
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {Q : ObjectProperty 𝒳.val.val.obj} (hQ : IsClosedSubstack 𝒳 Q)
    (W : BigFppfOver B S hS) (z : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.val.obj)
    (hz : z ⋙ 𝒳.val.val.p = Over.map W.hom) :
    Space.IsClosedSubspace B W.left.1 W.left.2
      (fullSubcategoryBaseChangeSubfunctor 𝒳 (fun φ hb => hQ.prop_of_hom φ hb) z) :=
  isSubspaceWith_fullSubcategoryBaseChangeSubfunctor hQ W z hz

/-- **A property whose base changes along scheme-valued points are closed subspaces cuts out a
closed substack.** Let `Q` be a property of the objects of an algebraic stack `𝒳` over `S` which is
inherited along morphisms. If for every scheme-valued point `z` of `𝒳` with values in `W` the
subfunctor of `yoneda W` whose sections over `T` are present exactly when `Q` holds at `z T` is a
closed subspace of `W`, then `Q` cuts out a closed substack of `𝒳`.

Those subfunctors are algebraic spaces, so the inclusion of the full subcategory is representable
by algebraic spaces
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion`); the
full subcategory is then an algebraic stack by **Stacks 05UM**, and the inclusion is a closed
immersion because the lower-shriek extension of a closed immersion is one
(`AlgebraicGeometry.Space.isClosedImmersion_relocalize`) and any algebraic space representing the
base change is isomorphic to the subfunctor. -/
theorem isClosedSubstack_of_forall_isClosedSubspace (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {Q : ObjectProperty 𝒳.val.val.obj} (hinh : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → Q b → Q a)
    (hsub : ∀ (W : BigFppfOver B S hS) (z : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.val.obj)
      (_hz : z ⋙ 𝒳.val.val.p = Over.map W.hom),
      Space.IsClosedSubspace B W.left.1 W.left.2
        (fullSubcategoryBaseChangeSubfunctor 𝒳 hinh z)) :
    IsClosedSubstack 𝒳 Q :=
  isSubstackWith_of_forall_isSubspaceWith 𝒳 hinh hsub

/-- **An intersection of closed substacks is a closed substack.** Let `𝒮` be a set of properties
of the objects of an algebraic stack `𝒳` over `S`, each cutting out a closed substack of `𝒳`
(Stacks 04YM, part (2)). Then their intersection cuts out a closed substack of `𝒳`.

The base change of its inclusion along a scheme-valued point is the intersection of the base
changes of the inclusions of the members, which are closed subspaces by
`AlgebraicGeometry.Stack.isClosedSubspace_fullSubcategoryBaseChangeSubfunctor`, hence a closed
subspace by `AlgebraicGeometry.Space.isClosedSubspace_sInf`; this is enough by
`AlgebraicGeometry.Stack.isClosedSubstack_of_forall_isClosedSubspace`. For the empty family this
is the whole of `𝒳`. -/
theorem isClosedSubstack_sInf (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (𝒮 : Set (ObjectProperty 𝒳.val.val.obj)) (h𝒮 : ∀ Q ∈ 𝒮, IsClosedSubstack 𝒳 Q) :
    IsClosedSubstack 𝒳 (sInf 𝒮) := by
  have hmem : ∀ x, sInf 𝒮 x ↔ ∀ Q ∈ 𝒮, Q x := fun x => by simp [sInf_apply]
  have hinh : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → sInf 𝒮 b → sInf 𝒮 a := fun φ hb =>
    (hmem _).2 fun Q hQ => (h𝒮 Q hQ).prop_of_hom φ ((hmem _).1 hb Q hQ)
  refine isClosedSubstack_of_forall_isClosedSubspace 𝒳 hinh fun W z hz => ?_
  -- At a scheme-valued point, the base change of the inclusion is the intersection of the base
  -- changes of the inclusions of the members of the family.
  set 𝒯 : Set (Subfunctor (yoneda.obj (Over.mk (𝟙 W.left)) :
      (BigFppfOver B W.left.1 W.left.2)ᵒᵖ ⥤ Type u)) :=
    {Z | ∃ Q, ∃ hQ : Q ∈ 𝒮,
      Z = fullSubcategoryBaseChangeSubfunctor 𝒳 (fun φ hb => (h𝒮 Q hQ).prop_of_hom φ hb) z}
  have heq : fullSubcategoryBaseChangeSubfunctor 𝒳 hinh z = sInf 𝒯 := by
    refine le_antisymm (le_sInf ?_) ?_
    · rintro _ ⟨Q, hQ, rfl⟩ T x hx
      exact (hmem _).1 hx Q hQ
    · intro T x hx
      refine (hmem _).2 fun Q hQ => ?_
      exact sInf_le (α := Subfunctor _) (⟨Q, hQ, rfl⟩ : _ ∈ 𝒯) T hx
  rw [heq]
  exact Space.isClosedSubspace_sInf B W.left.1 W.left.2 (isAlgebraicSpace_yoneda _ _ _ _) 𝒯
    (by
      rintro _ ⟨Q, hQ, rfl⟩
      exact isClosedSubspace_fullSubcategoryBaseChangeSubfunctor (h𝒮 Q hQ) W z hz)

end AlgebraicGeometry.Stack

end
