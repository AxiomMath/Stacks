module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleUniversallyInjectiveOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjectiveSchemeTests
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism

/-!
# An étale morphism with an invertible base change along a surjection

Let `g : G ⟶ A` be an étale morphism of algebraic spaces over a scheme `S` and let `p : A' ⟶ A`
be surjective. If the base change of `g` along `p` is an isomorphism, then `g` itself is an
isomorphism.

This is the descent step on which the topological invariance of the spaces-étale site rests:
applied to the inclusion of a thickening as the surjection `p`, it turns the identification of
an étale space with a candidate *over the thin side* into an identification over the whole
ambient space.

## Main results

* `AlgebraicGeometry.Space.isSurjective_of_isPullback_of_isIso_fst`: the morphism along which an
  invertible base change is taken is itself surjective.
* `AlgebraicGeometry.Space.isIso_of_isEtale_of_isIso_pullback_of_isSurjective`: an étale morphism
  whose base change along a surjection is an isomorphism is an isomorphism.

## Implementation notes

Surjectivity of `g` is read off on points: the inverse of the base change lifts a point of `A'`
into the fibre product, and the two edges of the cartesian square carry it to a point of `G`
over the prescribed point of `A`.

Universal injectivity of `g` is the only step that needs more than the square. It is Stacks
03MX, `AlgebraicGeometry.Space.universallyInjective_tfae`, in the form of its fourth clause: it
suffices to exhibit *one* surjective scheme chart of `A` along which the base change of `g` is
universally injective. The chart is an étale atlas `u` of `A'` followed by `p`, and the base
change of `g` along it is an isomorphism, hence a monomorphism, hence universally injective by
`AlgebraicGeometry.Space.universallyInjective_of_mono`. That the base change along `u ≫ p` is
invertible is the composite of two base changes:
`CategoryTheory.Limits.pullbackRightPullbackFstIso` identifies `U ×_{A'} (A' ×_A G)` with
`G ×_A U`, and the first of those is a base change of an isomorphism.

With universal injectivity available, `g` is an open immersion by Stacks 05W5
(`AlgebraicGeometry.Space.isOpenImmersion_of_isEtale_of_universallyInjective`) and a surjective
open immersion is an isomorphism
(`AlgebraicGeometry.Space.isIso_of_isOpenImmersion_of_surjective_pointsMap`).

## References

* [Stacks Project, Tag 03MX](https://stacks.math.columbia.edu/tag/03MX)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {A A' G P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- If the base change of `g : G ⟶ A` along `p : A' ⟶ A` is an isomorphism and `p` is
surjective on points, then `g` is surjective on points: the inverse of the base change lifts a
point of `A'` into the fibre product, whence into `G`. -/
theorem isSurjective_of_isPullback_of_isIso_fst {p : A' ⟶ A} {g : G ⟶ A} {π : P ⟶ A'} {ρ : P ⟶ G}
    (sq : IsPullback π ρ p g) (hπ : IsIso π) (hp : IsSurjective B S hS p) :
    IsSurjective B S hS g := by
  have _ := hπ
  intro y
  obtain ⟨y', hy'⟩ := hp y
  refine ⟨pointsMap B S hS P ρ (pointsMap B S hS A' (inv π) y'), ?_⟩
  have hfun : pointsMap B S hS P (ρ ≫ g) = pointsMap B S hS P (π ≫ p) := by rw [sq.w]
  have hstep : pointsMap B S hS G g (pointsMap B S hS P ρ (pointsMap B S hS A' (inv π) y')) =
      pointsMap B S hS P (ρ ≫ g) (pointsMap B S hS A' (inv π) y') := by
    rw [pointsMap_comp]
    rfl
  rw [hstep, hfun, pointsMap_comp]
  have : pointsMap B S hS A' (inv π ≫ π) y' = y' := by
    rw [IsIso.inv_hom_id, pointsMap_id, id_eq]
  calc (pointsMap B S hS A' p ∘ pointsMap B S hS P π) (pointsMap B S hS A' (inv π) y')
      = pointsMap B S hS A' p (pointsMap B S hS A' (inv π ≫ π) y') := by
        rw [pointsMap_comp]; rfl
    _ = pointsMap B S hS A' p y' := by rw [this]
    _ = y := hy'

/-- If `e.hom ≫ f` equals an isomorphism `g`, then `f` is an isomorphism. -/
private theorem isIso_of_iso_hom_comp_eq {C : Type*} [Category C] {X Y Z : C} (e : X ≅ Y)
    (f : Y ⟶ Z) (g : X ⟶ Z) (h : e.hom ≫ f = g) [IsIso g] : IsIso f := by
  subst h
  exact IsIso.of_isIso_comp_left e.hom f

/-- **An étale morphism whose base change along a surjection is an isomorphism is an
isomorphism.** Let `g : G ⟶ A` be an étale morphism of algebraic spaces over `S`, let
`p : A' ⟶ A` be surjective, and let the base change of `g` along `p` be invertible. Then `g` is
an isomorphism.

Surjectivity of `g` is `AlgebraicGeometry.Space.isSurjective_of_isPullback_of_isIso_fst` and
universal injectivity is the fourth clause of Stacks 03MX, tested on the étale atlas of `A'`
pushed to `A` along `p`; Stacks 05W5 then makes `g` an open immersion, and a surjective open
immersion is invertible. -/
theorem isIso_of_isEtale_of_isIso_pullback_of_isSurjective
    (hA : IsAlgebraicSpace B S hS A) (hA' : IsAlgebraicSpace B S hS A')
    (hG : IsAlgebraicSpace B S hS G)
    {p : A' ⟶ A} {g : G ⟶ A} {π : P ⟶ A'} {ρ : P ⟶ G}
    (sq : IsPullback π ρ p g) (hπ : IsIso π)
    (hp : IsSurjective B S hS p) (hg : IsEtale B S hS g) :
    IsIso g := by
  have _ := hπ
  have hgsurj : IsSurjective B S hS g :=
    isSurjective_of_isPullback_of_isIso_fst B S hS sq hπ hp
  -- The chosen fibre product `A' ×_A G` is invertible over `A'`.
  have hfst : IsIso (pullback.fst p g) :=
    isIso_of_iso_hom_comp_eq sq.isoPullback _ _ sq.isoPullback_hom_fst
  -- An étale atlas of `A'`, pushed to a surjective scheme chart of `A`.
  obtain ⟨U, u, hu, -⟩ := hA'.exists_atlas
  have huS : IsSurjective B S hS u :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS A' hA' U u).mp hu
  have hchart : IsSurjective B S hS (u ≫ p) := by
    intro y
    obtain ⟨y', hy'⟩ := hp y
    obtain ⟨x, hx⟩ := huS y'
    refine ⟨x, ?_⟩
    rw [pointsMap_comp, Function.comp_apply, hx, hy']
  -- The base change of `g` along that chart is invertible.
  have hiso : IsIso (pullback.snd g (u ≫ p)) := by
    have _ := hfst
    exact isIso_of_iso_hom_comp_eq
      ((pullbackRightPullbackFstIso p g u).trans (pullbackSymmetry (u ≫ p) g)) _
      (pullback.fst u (pullback.fst p g)) (by simp)
  have htfae := (universallyInjective_tfae B S hS hG hA g).out 4 1
  have hui : UniversallyInjective B S hS g := by
    apply htfae.mp
    refine ⟨U, u ≫ p, hchart, ?_⟩
    have _ := hiso
    exact universallyInjective_of_mono B S hS _ inferInstance
  exact isIso_of_isOpenImmersion_of_surjective_pointsMap B S hS g
    (isOpenImmersion_of_isEtale_of_universallyInjective B S hS hG hA g hg hui) hgsurj

end AlgebraicGeometry.Space

end
