module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasiSplittingEtaleLocalization
public import StacksFrontier.Deformation.Groupoid.Basic

/-!
# The inverse arrow of the realization of a groupoid scheme

Let `(U, R, s, t, c)` be a groupoid scheme over `S`, realized as a groupoid in algebraic spaces
over a big fppf site over `S` containing its object scheme, its arrow scheme and its scheme of
composable pairs.  Evaluating the realization at a test object of the site gives a groupoid whose
arrows are the generalized arrows `T ⟶ R`, and this file identifies the inverse of such an arrow:
it is the generalized arrow obtained by composing with the inverse `i : R ⟶ R` of the groupoid
scheme.

## Main results

* `Stacks.Groupoids.GroupoidScheme.realization_inverse`: the inverse arrow of the realization of
  a groupoid scheme at a generalized arrow is the Yoneda image of the inverse of the groupoid
  scheme, evaluated at that arrow.

## Implementation notes

Inverses in a groupoid are unique, so it suffices to check that the candidate has the endpoints
of an inverse and composes with the given arrow to an identity.  The first is
`Stacks.Groupoids.GroupoidScheme.source_inverse` and
`Stacks.Groupoids.GroupoidScheme.target_inverse` transported through
`AlgebraicGeometry.Space.yonedaSchemePointEquiv_map`, and the second is
`Stacks.Groupoids.GroupoidScheme.left_inverse` transported through
`Stacks.Groupoids.GroupoidScheme.realizationComp_app`, combined with
`Stacks.Groupoids.GroupoidScheme.realization_identity_yonedaMap` to recognize the result as the
identity arrow of the realization.

The uniqueness itself is `Deformation.inverseArrow_eq_of_compose_eq_identity`, which runs the
usual cancellation `i = i ∘ (a ∘ b) = (i ∘ a) ∘ b = b` inside the evaluated groupoid through
`Deformation.GroupoidInFunctors.evaluationArrowEquiv`.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace Deformation

/-- An arrow of a groupoid in functors whose source is the target of a given arrow, whose target
is the source of that arrow, and which composes with it to the identity at its source, is the
inverse arrow of that arrow. -/
private theorem inverseArrow_eq_of_compose_eq_identity {J : Type u} [Category.{v} J]
    (G : GroupoidInFunctors J) (T : J) (a b : G.arrows.obj T)
    (hs : G.source.app T b = G.target.app T a)
    (ht : G.target.app T b = G.source.app T a)
    (hc : G.compose T b a hs = G.identity T (G.source.app T a)) :
    inverseArrow G T a = b := by
  let := G.evaluationGroupoid T
  let x : G.Evaluation T := G.source.app T a
  let y : G.Evaluation T := G.target.app T a
  let E₁ := G.evaluationArrowEquiv T x y
  let E₂ := G.evaluationArrowEquiv T y x
  let E := G.evaluationArrowEquiv T x x
  let α : x ⟶ y := E₁.symm ⟨a, rfl, rfl⟩
  let β : y ⟶ x := E₂.symm ⟨b, hs, ht⟩
  have ha : (E₁ α).1 = a := congrArg Subtype.val (E₁.apply_symm_apply _)
  have hb : (E₂ β).1 = b := congrArg Subtype.val (E₂.apply_symm_apply _)
  have hcongr : ∀ (b' a' : G.arrows.obj T), b' = b → a' = a →
      ∀ h : G.source.app T b' = G.target.app T a',
        G.compose T b' a' h = G.compose T b a hs := by
    intro b' a' hb' ha' h
    subst hb'
    subst ha'
    rfl
  have hαβ : α ≫ β = 𝟙 x := by
    refine E.injective (Subtype.ext ?_)
    exact ((G.evaluationArrowEquiv_comp T α β).trans (hcongr _ _ hb ha _)).trans hc
  have hinv : β = Groupoid.inv α :=
    calc β = 𝟙 y ≫ β := (Category.id_comp β).symm
      _ = (Groupoid.inv α ≫ α) ≫ β := by rw [Groupoid.inv_comp]
      _ = Groupoid.inv α ≫ α ≫ β := Category.assoc _ _ _
      _ = Groupoid.inv α ≫ 𝟙 x := by rw [hαβ]
      _ = Groupoid.inv α := Category.comp_id _
  change (E₂ (Groupoid.inv α)).1 = b
  rw [← hinv]
  exact hb

end Deformation

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- A generalized arrow of a groupoid scheme which is the inverse of another one composes with it
to the identity arrow at its source. -/
private theorem compose_inverse_self {T : Over S} (b f : T ⟶ G.arrows)
    (hb : b = f ≫ G.inverse) (w : b ≫ G.source = f ≫ G.target) :
    G.compose b f w = f ≫ G.source ≫ G.identity := by
  subst hb
  exact G.left_inverse T f w

variable (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
  (hR : C.Contains G.arrows.left) (hP : C.Contains (pullback G.source G.target).left)

open AlgebraicGeometry.Space in
/-- A section of the arrow space of the realization of a groupoid scheme whose generalized point
is the inverse of that of a given section is the inverse arrow of that section. -/
private theorem realization_inverse_aux (T : (BigFppfOver C S hS)ᵒᵖ)
    (a b : (realization G C hS hU hR hP).arrows.obj.obj T)
    (hab : yonedaSchemePointEquiv C hS hR T b =
      yonedaSchemePointEquiv C hS hR T a ≫ G.inverse) :
    Deformation.inverseArrow (realization G C hS hU hR hP).toGroupoidInFunctors T a = b := by
  have key : ∀ p q : G.arrows ⟶ G.objects, G.inverse ≫ p = q →
      (yoneda.map (schemeSiteMap C hS hR hU p)).app T b =
        (yoneda.map (schemeSiteMap C hS hR hU q)).app T a := fun p q h ↦ by
    refine (yonedaSchemePointEquiv C hS hU T).injective ?_
    rw [yonedaSchemePointEquiv_map C hS hR hU p T b,
      yonedaSchemePointEquiv_map C hS hR hU q T a, hab, Category.assoc, h]
  have hs : (realization G C hS hU hR hP).source.hom.app T b =
      (realization G C hS hU hR hP).target.hom.app T a := key _ _ G.source_inverse
  have ht : (realization G C hS hU hR hP).target.hom.app T b =
      (realization G C hS hU hR hP).source.hom.app T a := key _ _ G.target_inverse
  have hw : yonedaSchemePointEquiv C hS hR T b ≫ G.source =
      yonedaSchemePointEquiv C hS hR T a ≫ G.target := by
    rw [hab, Category.assoc, G.source_inverse]
  have hxa : yonedaSchemePointEquiv C hS hU T
        ((realization G C hS hU hR hP).toGroupoidInFunctors.source.app T a) =
      yonedaSchemePointEquiv C hS hR T a ≫ G.source := by
    have h : (realization G C hS hU hR hP).toGroupoidInFunctors.source.app T a =
        (yoneda.map (schemeSiteMap C hS hR hU G.source)).app T a := rfl
    rw [h, yonedaSchemePointEquiv_map C hS hR hU G.source T a]
  have hid : (realization G C hS hU hR hP).toGroupoidInFunctors.identity T
        ((realization G C hS hU hR hP).toGroupoidInFunctors.source.app T a) =
      (yoneda.map (schemeSiteMap C hS hU hR G.identity)).app T
        ((realization G C hS hU hR hP).toGroupoidInFunctors.source.app T a) :=
    realization_identity_yonedaMap G C hS hU hR hP T _
  refine Deformation.inverseArrow_eq_of_compose_eq_identity
    (realization G C hS hU hR hP).toGroupoidInFunctors T a b hs ht ?_
  refine (yonedaSchemePointEquiv C hS hR T).injective ?_
  refine (realizationComp_app G C hS hU hR hP T ⟨(b, a), hs⟩ hw).trans ?_
  refine (compose_inverse_self G (yonedaSchemePointEquiv C hS hR T b)
    (yonedaSchemePointEquiv C hS hR T a) hab hw).trans ?_
  rw [hid, yonedaSchemePointEquiv_map C hS hU hR G.identity T
    ((realization G C hS hU hR hP).toGroupoidInFunctors.source.app T a), hxa, Category.assoc]

open AlgebraicGeometry.Space in
/-- The inverse arrow of the realization of a groupoid scheme at a generalized arrow is the
Yoneda image of the inverse of the groupoid scheme, evaluated at that arrow. -/
theorem realization_inverse (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (realization G C hS hU hR hP).arrows.obj.obj T) :
    Deformation.inverseArrow (realization G C hS hU hR hP).toGroupoidInFunctors T a =
      (yoneda.map (schemeSiteMap C hS hR hR G.inverse)).app T a :=
  realization_inverse_aux G C hS hU hR hP T a _
    (yonedaSchemePointEquiv_map C hS hR hR G.inverse T a)

end Stacks.Groupoids.GroupoidScheme

end
