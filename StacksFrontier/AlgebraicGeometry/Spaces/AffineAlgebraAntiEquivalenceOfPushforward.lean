module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentAlgebra

/-!
# Stacks 081V from three properties of the direct-image functor

Stacks 081V asserts that the algebraic spaces affine over an algebraic space `X` are
anti-equivalent to the quasi-coherent sheaves of commutative `𝒪_X`-algebras, *through* the
direct-image functor `f ↦ f_* 𝒪_Y`.  The structure
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` packages an anti-equivalence, a
direct-image functor, two compatibilities of the latter, and an isomorphism between them.

This file constructs that structure from three properties of the direct-image functor
`AlgebraicGeometry.Space.affineQuasicoherentPushforwardAlgebraFunctor`: that it is full, faithful
and essentially surjective.  The anti-equivalence is then the direct-image functor itself, and
its identification with direct image is the identity isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.affineQuasicoherentPushforwardEquivalence` is the anti-equivalence of
  Stacks 081V over a single algebraic space, given that the direct-image functor there is full,
  faithful and essentially surjective.
* `AlgebraicGeometry.Space.affineAlgebraAntiEquivalenceOfPushforwardProperties` assembles the
  whole of `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` from those three properties,
  holding at every algebraic space.

## Main results

* `AlgebraicGeometry.Space.essSurj_affineQuasicoherentPushforwardAlgebraFunctor_iff`: essential
  surjectivity of the direct-image functor over `X` is *exactly* the existence, for every
  quasi-coherent `𝒪_X`-algebra `A`, of an algebraic space affine over `X` whose direct-image
  algebra is `A`.  That existence statement is the object of Stacks 081W, the relative spectrum
  `\underline{Spec}_X(A)`, together with the identification `π_* 𝒪 ≅ A` of its direct image.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Essential surjectivity of the direct-image functor is the existence of the relative
spectrum.**  The functor `f ↦ f_* 𝒪_Y` from the algebraic spaces affine over `X` to the
quasi-coherent `𝒪_X`-algebras is essentially surjective if and only if every quasi-coherent
`𝒪_X`-algebra `A` is the direct-image algebra of some algebraic space affine over `X`. -/
theorem essSurj_affineQuasicoherentPushforwardAlgebraFunctor_iff (X : AlgebraicSpaces B S hS) :
    (affineQuasicoherentPushforwardAlgebraFunctor B S hS X).EssSurj ↔
      ∀ A : QuasicoherentAlgebra B S hS X, ∃ Y : AffineOver B S hS X,
        Nonempty (pushforwardAlgebra B S hS Y.obj ≅ A.obj) := by
  refine ⟨fun h A => ?_, fun h => ⟨fun A => ?_⟩⟩
  · obtain ⟨Y, ⟨e⟩⟩ := h.mem_essImage A
    exact ⟨Y.unop, ⟨(quasicoherentAlgebraInclusion B S hS X).mapIso e⟩⟩
  · obtain ⟨Y, ⟨e⟩⟩ := h A
    exact ⟨op Y, ⟨(quasicoherentAlgebraInclusion B S hS X).preimageIso e⟩⟩

/-- **The anti-equivalence of Stacks 081V over one algebraic space.**  If the direct-image
functor `f ↦ f_* 𝒪_Y` on the algebraic spaces affine over `X` is full, faithful and essentially
surjective, then it *is* the anti-equivalence between those spaces and the quasi-coherent
`𝒪_X`-algebras. -/
def affineQuasicoherentPushforwardEquivalence (X : AlgebraicSpaces B S hS)
    (hfull : (affineQuasicoherentPushforwardAlgebraFunctor B S hS X).Full)
    (hfaithful : (affineQuasicoherentPushforwardAlgebraFunctor B S hS X).Faithful)
    (hessSurj : (affineQuasicoherentPushforwardAlgebraFunctor B S hS X).EssSurj) :
    (AffineOver B S hS X)ᵒᵖ ≌ QuasicoherentAlgebra B S hS X :=
  haveI := hfull
  haveI := hfaithful
  haveI := hessSurj
  haveI : (affineQuasicoherentPushforwardAlgebraFunctor B S hS X).IsEquivalence := { }
  (affineQuasicoherentPushforwardAlgebraFunctor B S hS X).asEquivalence

/-- The functor of `AlgebraicGeometry.Space.affineQuasicoherentPushforwardEquivalence` *is* the
direct-image functor. -/
theorem affineQuasicoherentPushforwardEquivalence_functor (X : AlgebraicSpaces B S hS)
    (hfull : (affineQuasicoherentPushforwardAlgebraFunctor B S hS X).Full)
    (hfaithful : (affineQuasicoherentPushforwardAlgebraFunctor B S hS X).Faithful)
    (hessSurj : (affineQuasicoherentPushforwardAlgebraFunctor B S hS X).EssSurj) :
    (affineQuasicoherentPushforwardEquivalence B S hS X hfull hfaithful hessSurj).functor =
      affineQuasicoherentPushforwardAlgebraFunctor B S hS X :=
  rfl

/-- Bracketing a morphism of algebra sheaves between identities does not change the map it
induces on underlying sheaves of rings. -/
theorem id_comp_comp_id_right {X : AlgebraicSpaces B S hS}
    {A C : AlgebraSheaf.{u, u} B S hS X.1 X.2} (g : A ⟶ C) :
    (𝟙 A ≫ g ≫ 𝟙 C).right = g.right :=
  congrArg (fun k : A ⟶ C => k.right) ((Category.id_comp _).trans (Category.comp_id g))

/-- **Stacks 081V from three properties of the direct-image functor.**  If the direct-image
functor `f ↦ f_* 𝒪_Y` is full, faithful and essentially surjective over every algebraic space,
then `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` is inhabited: the anti-equivalence
is the direct-image functor itself, read as an equivalence, and its identification with direct
image is the identity. -/
def affineAlgebraAntiEquivalenceOfPushforwardProperties
    (hfull : ∀ X : AlgebraicSpaces B S hS,
      (affineQuasicoherentPushforwardAlgebraFunctor B S hS X).Full)
    (hfaithful : ∀ X : AlgebraicSpaces B S hS,
      (affineQuasicoherentPushforwardAlgebraFunctor B S hS X).Faithful)
    (hessSurj : ∀ X : AlgebraicSpaces B S hS,
      (affineQuasicoherentPushforwardAlgebraFunctor B S hS X).EssSurj) :
    AffineAlgebraAntiEquivalence B S hS where
  equivalence X :=
    affineQuasicoherentPushforwardEquivalence B S hS X (hfull X) (hfaithful X) (hessSurj X)
  pushforward X := affineQuasicoherentPushforwardAlgebraFunctor B S hS X
  pushforward_obj _ _ := Iso.refl _
  pushforward_map := fun X {_ _} f =>
    (id_comp_comp_id_right B S hS _).trans
      (affineQuasicoherentPushforwardAlgebraFunctor_map_right B S hS X f)
  pushforwardIso X := Iso.refl (affineQuasicoherentPushforwardAlgebraFunctor B S hS X)

end AlgebraicGeometry.Space

end
