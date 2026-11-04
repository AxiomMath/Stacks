module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.QuasiFiniteRepresentableULift
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSitePostcomposition

/-!
# The étale charts of a formal algebraic space are representable by schemes

Let `S` be a scheme contained in a big fppf site `B`. A morphism out of an affine formal algebraic
space which is representable by algebraic spaces and étale is representable by objects of the
site: this is Stacks 0AIG, an étale morphism being locally quasi-finite. In particular each arrow
of an atlas of a formal algebraic space, as in Definition 0AIM, is representable by objects of the
site.

## Main results

* `AlgebraicGeometry.FormalSpace.relativelyRepresentable_of_isEtale_of_isAffineFormal`: a
  morphism out of an affine formal algebraic space which is representable by algebraic spaces and
  étale is representable by objects of the site.
* `AlgebraicGeometry.FormalSpace.exists_atlas_relativelyRepresentable`: every formal algebraic
  space has an atlas as in Definition 0AIM each of whose arrows is representable by objects of
  the site.

## References

* [Stacks Project, Tag 0AIG](https://stacks.math.columbia.edu/tag/0AIG)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 03WS](https://stacks.math.columbia.edu/tag/03WS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism `g : X ⟶ Y` of fppf sheaves on the big fppf site of `S` whose source is an affine
formal algebraic space, which is representable by algebraic spaces and étale, is representable by
objects of the site. -/
@[stacks 0AIG "the case of an etale morphism, at the value universe Type (u+1) where a formal \
algebraic space and the affine formal algebraic spaces of its atlas of Definition 0AIM live. \
Nothing is assumed beyond the tag: an etale morphism of schemes is locally of finite type and \
locally quasi-finite by Stacks 03WS, which is the tag's hypothesis"]
theorem relativelyRepresentable_of_isEtale_of_isAffineFormal {X Y : FppfSheaf B S hS}
    (g : X ⟶ Y) (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) g.hom hrep) :
    uliftYoneda.{u + 1}.relativelyRepresentable g.hom :=
  relativelyRepresentable_of_isAffineFormalAlgebraicSpaceULift B S hS g.hom hX hrep fun T ξ ↦
    holdsOnEveryEtaleChartULift_of_isEtaleULift_over_site B S hS _
      (fun _ hk ↦ have := hk; ⟨inferInstance, inferInstance⟩) (pullback.fst ξ g.hom) (het T ξ)

/-- A formal algebraic space over `S` carries an atlas as in Stacks 0AIM — a family of affine
formal algebraic spaces mapping to it by morphisms which are representable by algebraic spaces and
étale, jointly locally surjective — each of whose morphisms is representable by objects of the
site. -/
theorem exists_atlas_relativelyRepresentable {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ (I : Type (u + 1)) (Xi : I → FppfSheaf B S hS) (g : ∀ i, Xi i ⟶ X),
      (∀ i, IsAffineFormalAlgebraicSpace B S hS (Xi i)) ∧
      (∀ i, uliftYoneda.{u + 1}.relativelyRepresentable (g i).hom) ∧
      Sheaf.IsLocallySurjective (Limits.Sigma.desc g) := by
  obtain ⟨-, I, Xi, g, haff, het, hsurj⟩ := hX
  exact ⟨I, Xi, g, haff, fun i ↦ relativelyRepresentable_of_isEtale_of_isAffineFormal B S hS (g i)
    (haff i) (het i).1 (het i).2, hsurj⟩

end AlgebraicGeometry.FormalSpace

end
