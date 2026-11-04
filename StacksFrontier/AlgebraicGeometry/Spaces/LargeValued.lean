module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentabilityCriteria

/-!
# Algebraic spaces among presheaves with values in a larger universe

An algebraic space over a scheme `S` of a big fppf site `B` is a presheaf on the big fppf
site of `S` with values in `Type u`, the universe of the schemes. Presheaves with values in
a strictly larger universe occur as soon as colimits of such sheaves are taken: a formal
algebraic space is a sheaf of `Type (u + 1)`. This file carries the algebraic-space notions
for a value universe `max w u` with `w` independent of `u`.

Nothing is weakened by the move: the scheme-valued points of a presheaf of `Type (max w u)`
are the morphisms out of `CategoryTheory.uliftYoneda.{w}.obj U`, which is the universe lift
of the Yoneda presheaf of `U`, and each condition is the same condition tested against those
points. `CategoryTheory.uliftYoneda.{u}` and `CategoryTheory.yoneda` are isomorphic, so at
`w = u` the notions below are the ones already in the library.

## Main definitions

* `AlgebraicGeometry.Space.IsAlgebraicSpaceULift` is `AlgebraicGeometry.IsAlgebraicSpace`
  for a presheaf of `Type (max w u)`.
* `AlgebraicGeometry.Space.AlgebraicSpacesULift` is the full subcategory they form, the
  counterpart of `AlgebraicGeometry.AlgebraicSpaces`.
* `AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpacesULift` is
  `AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces` for such presheaves.
* `AlgebraicGeometry.Space.HasPropertyULift` is `AlgebraicGeometry.Space.HasProperty` for
  such presheaves.
* `AlgebraicGeometry.Space.IsEtaleULift` is `AlgebraicGeometry.Space.IsEtale` for such
  presheaves.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpaceULift_of_iso` transports the algebraic-space
  condition along an isomorphism of presheaves.
* `AlgebraicGeometry.Space.isAlgebraicSpaceULift_uliftYoneda`: the universe-lifted Yoneda
  presheaf of a scheme over `S` is an algebraic space, so a scheme-valued point of a
  presheaf of `Type (max w u)` is an object of `AlgebraicSpacesULift`.

## Implementation notes

The predicates are stated with the relative morphism property
`CategoryTheory.MorphismProperty.relative` along `CategoryTheory.uliftYoneda.{w}` rather
than with `CategoryTheory.MorphismProperty.presheaf`, which is by definition that relative
property along `CategoryTheory.yoneda` and therefore only available in the value universe of
the site.

The sheaf condition of a universe-lifted Yoneda presheaf is subcanonicity of the topology of
the big fppf site of `S`, `AlgebraicGeometry.bigFppfOver_subcanonical`;
`CategoryTheory.Functor.IsRepresentable` holds for `CategoryTheory.uliftYoneda.{w}.obj U` just as
it does for `CategoryTheory.yoneda.obj U`, so the same argument applies. The identity serves as
the atlas, which reduces surjectivity and étaleness to the case of an isomorphism of the site.

## References

* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 02YQ](https://stacks.math.columbia.edu/tag/02YQ)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A presheaf on the big fppf site of `S` with values in a universe `max w u` independent of
the universe `u` of the schemes is an *algebraic space* over `S` when it is a sheaf, has
representable diagonal, and admits a surjective étale morphism from a universe-lifted Yoneda
presheaf. This is `AlgebraicGeometry.IsAlgebraicSpace` with the scheme-valued points taken to
be the morphisms out of `CategoryTheory.uliftYoneda.{w}.obj U`. -/
structure IsAlgebraicSpaceULift (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)) : Prop where
  /-- The fppf sheaf condition. -/
  isSheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F
  /-- Representability of the diagonal, relative to the universe-lifted Yoneda embedding. -/
  diagonal_representable :
    (uliftYoneda.{w} (C := BigFppfOver B S hS)).relativelyRepresentable (diag F)
  /-- A scheme atlas, surjective and étale after every representable base change. -/
  exists_atlas : ∃ (U : BigFppfOver B S hS) (f : (uliftYoneda.{w}).obj U ⟶ F),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) f ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) f

/-- The full subcategory of the presheaves on the big fppf site of `S` with values in
`Type (max w u)` whose objects are the algebraic spaces over `S`. This is the counterpart of
`AlgebraicGeometry.AlgebraicSpaces` for a value universe independent of the universe of the
schemes. -/
abbrev AlgebraicSpacesULift :=
  ObjectProperty.FullSubcategory
    (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u) => IsAlgebraicSpaceULift.{w} B S hS F)

/-- The algebraic-space condition on a presheaf with values in a larger universe transports
along an isomorphism of presheaves. -/
theorem isAlgebraicSpaceULift_of_iso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (e : F ≅ G)
    (hF : IsAlgebraicSpaceULift.{w} B S hS F) : IsAlgebraicSpaceULift.{w} B S hS G := by
  refine ⟨(Presheaf.isSheaf_of_iso_iff e).mp hF.isSheaf, ?_, ?_⟩
  · have hnat : diag F ≫ prod.map e.hom e.hom = e.hom ≫ diag G := by
      apply prod.hom_ext <;> simp
    rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := (uliftYoneda.{w} (C := BigFppfOver B S hS)).relativelyRepresentable)
      e.hom (diag G), ← hnat]
    exact MorphismProperty.RespectsIso.postcomp _ (prod.map e.hom e.hom) (diag F)
      hF.diagonal_representable
  · obtain ⟨U, f, hfSurjective, hfEtale⟩ := hF.exists_atlas
    refine ⟨U, f ≫ e.hom, ?_, ?_⟩ <;>
      exact MorphismProperty.RespectsIso.postcomp _ e.hom f (by assumption)

/-- A morphism property holding for isomorphisms holds after every representable base change
of the identity of a universe-lifted Yoneda presheaf. -/
private theorem relative_id_of_iso (P : MorphismProperty Scheme.{u})
    (hP : ∀ ⦃X Y⦄ (f : X ⟶ Y), IsIso f → P f) (T : BigFppfOver B S hS) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w})
      (𝟙 ((uliftYoneda.{w}).obj T)) := by
  refine ⟨Functor.relativelyRepresentable.of_isIso (uliftYoneda.{w}) _, ?_⟩
  intro A C g fst snd hpb
  have : IsIso ((uliftYoneda.{w}).map snd) := hpb.isIso_snd_of_isIso
  have := Functor.FullyFaithful.isIso_of_isIso_map (ULiftYoneda.fullyFaithful _) snd
  exact hP _ (inferInstance)

/-- The universe-lifted Yoneda presheaf of a scheme over `S` is an algebraic space over `S`,
for any value universe `max w u` independent of the universe `u` of the schemes. -/
theorem isAlgebraicSpaceULift_uliftYoneda (T : BigFppfOver B S hS) :
    IsAlgebraicSpaceULift.{w} B S hS ((uliftYoneda.{w}).obj T) := by
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  have hSheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      ((uliftYoneda.{w}).obj T) :=
    (CategoryTheory.isSheaf_iff_isSheaf_of_type
      (J := BigFppfOver.topology B S hS) ((uliftYoneda.{w}).obj T)).2
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
        (J := BigFppfOver.topology B S hS) ((uliftYoneda.{w}).obj T))
  have hDiag : (uliftYoneda.{w} (C := BigFppfOver B S hS)).relativelyRepresentable
      (diag ((uliftYoneda.{w}).obj T)) := by
    apply (Functor.relativelyRepresentable.diag_iff
      (F := uliftYoneda.{w}) (X := (uliftYoneda.{w}).obj T)).2
    intro U g
    simpa using Functor.relativelyRepresentable.map (uliftYoneda.{w})
      ((uliftYoneda.{w}).preimage g)
  refine ⟨hSheaf, hDiag, T, 𝟙 ((uliftYoneda.{w}).obj T), ?_, ?_⟩
  all_goals refine relative_id_of_iso B S hS _ ?_ T; intros; infer_instance

/-- A morphism of presheaves on the big fppf site of `S` with values in a universe
`max w u` independent of the universe `u` of the schemes is *representable by algebraic
spaces* when its base change along every universe-lifted scheme-valued point of its target
is an algebraic space. This is
`AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces` with the scheme-valued points
taken to be the morphisms out of `CategoryTheory.uliftYoneda.{w}.obj U`. -/
abbrev IsRepresentableByAlgebraicSpacesULift
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (a : F ⟶ G) : Prop :=
  ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{w}).obj U ⟶ G),
    IsAlgebraicSpaceULift.{w} B S hS (pullback ξ a)

/-- A morphism of presheaves with values in `Type (max w u)` that is representable by
algebraic spaces *has* a property `P` of morphisms of algebraic spaces when the projection
of its base change along every universe-lifted scheme-valued point of its target has `P`.
This is `AlgebraicGeometry.Space.HasProperty` with the scheme-valued points taken to be the
morphisms out of `CategoryTheory.uliftYoneda.{w}.obj U`. -/
abbrev HasPropertyULift (P : MorphismProperty (AlgebraicSpacesULift.{w} B S hS))
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (a : F ⟶ G)
    (ha : IsRepresentableByAlgebraicSpacesULift.{w} B S hS a) : Prop :=
  ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{w}).obj U ⟶ G),
    P (ObjectProperty.homMk (pullback.fst ξ a) :
      (⟨pullback ξ a, ha U ξ⟩ : AlgebraicSpacesULift.{w} B S hS) ⟶
        (⟨(uliftYoneda.{w}).obj U, isAlgebraicSpaceULift_uliftYoneda.{w} B S hS U⟩ :
          AlgebraicSpacesULift.{w} B S hS))

/-- A morphism of presheaves on the big fppf site of `S` with values in a universe
`max w u` independent of the universe `u` of the schemes is *étale* when its composite with
every étale morphism from a universe-lifted Yoneda presheaf into its source is again étale.
This is `AlgebraicGeometry.Space.IsEtale` with the scheme-valued points taken to be the
morphisms out of `CategoryTheory.uliftYoneda.{w}.obj U`. -/
abbrev IsEtaleULift {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (f : F ⟶ G) : Prop :=
  ∀ (U : BigFppfOver B S hS) (φ : (uliftYoneda.{w}).obj U ⟶ F),
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) φ →
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) (φ ≫ f)

end AlgebraicGeometry.Space

end
