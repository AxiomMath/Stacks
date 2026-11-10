module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroScheme

/-!
# Properties of a closed immersion of algebraic spaces

A closed immersion of algebraic spaces over a scheme `S` is affine, finite and integral.

For closed subspaces of an algebraic space: a closed subspace is a closed subspace of any
subfunctor containing it; the scheme-theoretic intersection of two closed subspaces is their fibre
product over the ambient space and is a closed subspace of each of them; and each of two closed
subspaces is a closed subspace of their scheme-theoretic union.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_of_isClosedImmersion`: a closed immersion is affine.
* `AlgebraicGeometry.Space.isFinite_of_isClosedImmersion`: a closed immersion is finite.
* `AlgebraicGeometry.Space.isIntegralHom_of_isClosedImmersion`: a closed immersion is
  integral.
* `CategoryTheory.Subfunctor.isPullback_inf`: the intersection of two subfunctors of a functor
  to types is their fibre product over it.
* `AlgebraicGeometry.Space.isClosedImmersion_homOfLe`: a closed subspace is a closed subspace
  of every subfunctor containing it.
* `AlgebraicGeometry.Space.isPullback_schemeTheoreticIntersection`,
  `AlgebraicGeometry.Space.isClosedImmersion_schemeTheoreticIntersection_le_left` and
  `AlgebraicGeometry.Space.isClosedImmersion_schemeTheoreticIntersection_le_right`: the
  scheme-theoretic intersection of two closed subspaces is their fibre product over the
  ambient space, and is a closed subspace of each of them.
* `AlgebraicGeometry.Space.isClosedImmersion_le_schemeTheoreticUnion_left` and
  `AlgebraicGeometry.Space.isClosedImmersion_le_schemeTheoreticUnion_right`: each of two closed
  subspaces is a closed subspace of their scheme-theoretic union.

## Implementation notes

Affineness, finiteness and integrality all read off the same represented base change: the
closed-immersion property supplies, for a test morphism from an affine scheme, a
representing object of the site together with its projection, and that projection is a
closed immersion of schemes with affine target, hence has affine source by
`AlgebraicGeometry.isAffine_of_isAffineHom`. Integrality then follows from finiteness
through Mathlib's instance from `AlgebraicGeometry.IsFinite` to
`AlgebraicGeometry.IsIntegralHom`.

The statements about closed immersions are given for an arbitrary morphism of presheaves on
the big fppf site of `S`: the closed-immersion property already includes representability of
its base changes, so no algebraic-space hypothesis is used.

The Cartesian square of Stacks 0CZ0 is stated in the category of presheaves on the big fppf
site of `S`, which is stronger than the source statement: the morphisms of algebraic spaces over
`S` are the natural transformations of the underlying presheaves, so a Cartesian square of
presheaves whose vertices are algebraic spaces is in particular one of algebraic spaces.

## References

* [Stacks Project, Tag 07U2](https://stacks.math.columbia.edu/tag/07U2)
* [Stacks Project, Tag 081Y](https://stacks.math.columbia.edu/tag/081Y)
* [Stacks Project, Tag 0CYZ](https://stacks.math.columbia.edu/tag/0CYZ)
* [Stacks Project, Tag 0CZ0](https://stacks.math.columbia.edu/tag/0CZ0)
* [Stacks Project, Tag 0CZ1](https://stacks.math.columbia.edu/tag/0CZ1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.Space

/-- The base change of a closed immersion along a map from an affine scheme is a closed immersion
of schemes with affine source. -/
private theorem isAffine_and_isClosedImmersion_pullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} (hf : IsClosedImmersion B S hS f)
    {U : BigFppfOver B S hS} (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (ξ : yoneda.obj U ⟶ Y) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (hf.rep.pullback ξ)) ∧
      AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (hf.rep.snd ξ)) := by
  have h : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (hf.rep.snd ξ)) :=
    hf.property ξ (hf.rep.fst ξ) _ (hf.rep.isPullback ξ)
  exact ⟨AlgebraicGeometry.isAffine_of_isAffineHom
    ((BigFppfOver.toScheme B S hS).map (hf.rep.snd ξ)), h⟩

/-- A closed immersion of algebraic spaces is affine. -/
@[stacks 07U2, ega "II 1.2.2"]
theorem isAffineHom_of_isClosedImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : IsClosedImmersion B S hS f) :
    IsAffineHom B S hS f := by
  intro Z g
  exact ⟨⟨hf.rep.pullback g, (isAffine_and_isClosedImmersion_pullback B S hS hf
    (BigAffineFppf.isAffine_toScheme_obj B S hS Z) g).1⟩, hf.rep.fst g, hf.rep.snd g,
    hf.rep.isPullback g⟩

/-- A closed immersion of algebraic spaces is finite. -/
@[stacks 081Y "finite", ega "II 6.1.5" "(i) finite"]
theorem isFinite_of_isClosedImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f) :
    IsFinite B S hS f := by
  intro U hU ξ
  obtain ⟨hA, _⟩ := isAffine_and_isClosedImmersion_pullback B S hS hf hU ξ
  exact ⟨hf.rep.pullback ξ, hf.rep.snd ξ, hf.rep.fst ξ, hA, inferInstance, hf.rep.isPullback ξ⟩

/-- A closed immersion of algebraic spaces is integral. -/
@[stacks 081Y "integral", ega "II 6.1.5" "(i) integral"]
theorem isIntegralHom_of_isClosedImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f) :
    IsIntegralHom B S hS f := by
  intro U hU ξ
  obtain ⟨V, p, i, hV, hfin, hpb⟩ := isFinite_of_isClosedImmersion B S hS f hf U hU ξ
  have : AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map p) := hfin
  exact ⟨V, p, i, hpb, hV, inferInstance⟩

end AlgebraicGeometry.Space

namespace CategoryTheory.Subfunctor

/-- The intersection of two subfunctors is their fibre product: the square formed by the two
inclusions of `G ⊓ G'` and the inclusions of `G` and `G'` into the ambient functor is Cartesian. -/
theorem isPullback_inf {C : Type u} [Category.{v} C] {F : C ⥤ Type w} (G G' : Subfunctor F) :
    IsPullback (Subfunctor.homOfLe (inf_le_right : G ⊓ G' ≤ G'))
      (Subfunctor.homOfLe (inf_le_left : G ⊓ G' ≤ G)) G'.ι G.ι := by
  have hc : Subfunctor.homOfLe (inf_le_right : G ⊓ G' ≤ G') ≫ G'.ι =
      Subfunctor.homOfLe (inf_le_left : G ⊓ G' ≤ G) ≫ G.ι := by ext A x; rfl
  refine IsPullback.of_isLimit (c := Limits.PullbackCone.mk _ _ hc)
    (Limits.PullbackCone.IsLimit.mk hc (fun s ↦ Subfunctor.lift (s.snd ≫ G.ι) ?_) ?_ ?_ ?_)
  · intro A x hx
    obtain ⟨y, rfl⟩ := hx
    refine ⟨(s.snd.app A y).property, ?_⟩
    have hv : (s.fst.app A y).val = (s.snd.app A y).val := by
      simpa using congrArg (fun g ↦ g y) (congr_app s.condition A)
    change (s.snd.app A y).val ∈ G'.obj A
    rw [← hv]
    exact (s.fst.app A y).property
  · intro s
    refine (cancel_mono G'.ι).mp ?_
    simp only [Category.assoc, Subfunctor.homOfLe_ι]
    exact s.condition.symm
  · intro s
    refine (cancel_mono G.ι).mp ?_
    simpa only [Category.assoc, Subfunctor.homOfLe_ι] using Subfunctor.lift_ι _ _
  · intro s m hm₁ hm₂
    refine (cancel_mono (G ⊓ G').ι).mp ?_
    calc m ≫ (G ⊓ G').ι
        = (m ≫ Subfunctor.homOfLe (inf_le_left : G ⊓ G' ≤ G)) ≫ G.ι := by
          simp [Category.assoc]
      _ = s.snd ≫ G.ι := by rw [hm₂]
      _ = Subfunctor.lift (s.snd ≫ G.ι) _ ≫ (G ⊓ G').ι := (Subfunctor.lift_ι _ _).symm

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Intersections and unions of closed subspaces -/

/-- A closed subspace of an algebraic space is a closed subspace of any subfunctor containing
it. -/
theorem isClosedImmersion_homOfLe (Z : ClosedSubspaces B S hS F) {U : Subfunctor F}
    (h : Z.1 ≤ U) :
    IsClosedImmersion B S hS (Subfunctor.homOfLe h) :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (IsPullback.of_horiz_isIso_mono (fst := 𝟙 Z.1.toFunctor) (snd := Subfunctor.homOfLe h)
      (f := Z.1.ι) (g := U.ι) ⟨by simp⟩) Z.2.2

/-- The scheme-theoretic intersection of two closed subspaces of an algebraic
space over `S` is the fibre product of the two over the ambient space: the square formed by the
four inclusions is Cartesian in the category of presheaves on the big fppf site of `S`. -/
@[stacks 0CZ0 "the intersection square is cartesian"]
theorem isPullback_schemeTheoreticIntersection (hF : IsAlgebraicSpace B S hS F)
    (Z Y : ClosedSubspaces B S hS F) :
    IsPullback
      (Subfunctor.homOfLe (show (schemeTheoreticIntersection B S hS F hF Z Y).1 ≤ Z.1 from
        inf_le_left))
      (Subfunctor.homOfLe (show (schemeTheoreticIntersection B S hS F hF Z Y).1 ≤ Y.1 from
        inf_le_right))
      Z.1.ι Y.1.ι :=
  (Subfunctor.isPullback_inf Z.1 Y.1).flip

/-- The scheme-theoretic intersection of two closed subspaces of an algebraic
space over `S` is a closed subspace of the first of them. -/
@[stacks 0CZ0 "closed immersion into the first factor"]
theorem isClosedImmersion_schemeTheoreticIntersection_le_left
    (hF : IsAlgebraicSpace B S hS F) (Z Y : ClosedSubspaces B S hS F) :
    IsClosedImmersion B S hS
      (Subfunctor.homOfLe (show (schemeTheoreticIntersection B S hS F hF Z Y).1 ≤ Z.1 from
        inf_le_left)) :=
  isClosedImmersion_homOfLe B S hS (schemeTheoreticIntersection B S hS F hF Z Y) _

/-- The scheme-theoretic intersection of two closed subspaces of an algebraic
space over `S` is a closed subspace of the second of them. -/
@[stacks 0CZ0 "closed immersion into the second factor"]
theorem isClosedImmersion_schemeTheoreticIntersection_le_right
    (hF : IsAlgebraicSpace B S hS F) (Z Y : ClosedSubspaces B S hS F) :
    IsClosedImmersion B S hS
      (Subfunctor.homOfLe (show (schemeTheoreticIntersection B S hS F hF Z Y).1 ≤ Y.1 from
        inf_le_right)) :=
  isClosedImmersion_homOfLe B S hS (schemeTheoreticIntersection B S hS F hF Z Y) _

/-- The first of two closed subspaces of an algebraic space over `S` is contained in their
scheme-theoretic union. -/
theorem le_schemeTheoreticUnion_left (hF : IsAlgebraicSpace B S hS F)
    (Y Z : ClosedSubspaces B S hS F) :
    Y.1 ≤ (schemeTheoreticUnion B S hS F hF Y Z).1 :=
  le_sInf fun _ hW ↦ hW.2.1

/-- The second of two closed subspaces of an algebraic space over `S` is contained in their
scheme-theoretic union. -/
theorem le_schemeTheoreticUnion_right (hF : IsAlgebraicSpace B S hS F)
    (Y Z : ClosedSubspaces B S hS F) :
    Z.1 ≤ (schemeTheoreticUnion B S hS F hF Y Z).1 :=
  le_sInf fun _ hW ↦ hW.2.2

/-- The first of two closed subspaces of an algebraic space over `S` is a
closed subspace of their scheme-theoretic union. -/
@[stacks 0CZ1 "closed immersion of the first subspace into the union"]
theorem isClosedImmersion_le_schemeTheoreticUnion_left (hF : IsAlgebraicSpace B S hS F)
    (Y Z : ClosedSubspaces B S hS F) :
    IsClosedImmersion B S hS
      (Subfunctor.homOfLe (le_schemeTheoreticUnion_left B S hS hF Y Z)) :=
  isClosedImmersion_homOfLe B S hS Y _

/-- The second of two closed subspaces of an algebraic space over `S` is a
closed subspace of their scheme-theoretic union. -/
@[stacks 0CZ1 "closed immersion of the second subspace into the union"]
theorem isClosedImmersion_le_schemeTheoreticUnion_right (hF : IsAlgebraicSpace B S hS F)
    (Y Z : ClosedSubspaces B S hS F) :
    IsClosedImmersion B S hS
      (Subfunctor.homOfLe (le_schemeTheoreticUnion_right B S hS hF Y Z)) :=
  isClosedImmersion_homOfLe B S hS Z _

end AlgebraicGeometry.Space

end
