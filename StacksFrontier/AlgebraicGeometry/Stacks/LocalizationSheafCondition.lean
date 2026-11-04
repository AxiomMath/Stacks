module

public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteLocalization
public import StacksFrontier.CategoryTheory.Sites.PresieveSheafTransport

/-!
# The sheaf condition for a presieve, across the localization of Stacks 06W0

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `x` an object of `𝒳` lying
over a scheme `U`.  Stacks 06W0 says that the canonical functor `𝒳/x ⥤ (Sch/U)` is an equivalence
of categories (`AlgebraicGeometry.Stack.isEquivalence_overPost`) carrying the localized associated
topology to the localized base topology
(`AlgebraicGeometry.Stack.inducedTopology_overPost`).

What that identification is used for is to move a *sheaf condition* between the two sites.  Every
transport of sheaves this repository and Mathlib already have — `sheafEquiv` and its relatives —
is an equivalence of sheaf *categories*, so it can only move a sheaf condition that is already
known; it cannot be used to prove one.  This file provides the statement that can: for a presheaf
on `𝒳` and a presieve on `x`, the sheaf condition is *equivalent* to a sheaf condition on the big
site of `U`, for the presieve of images and any presheaf there whose restriction along the
localization functor agrees with the restriction of the presheaf on `𝒳`.

That last agreement is the only input, and it is the honest one: the two sheaf conditions are
conditions on different presheaves on different categories, and nothing but an identification of
the two restricted presheaves can relate them.  Everything else — that the localized categories
agree, that compatible families and amalgamations correspond, that passing between `𝒳` and `𝒳/x`
and between `(Sch/U)` and its slice at the identity changes nothing — is discharged here.

## Main results

* `AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_overPost`: for a family of arrows
  `{x_i → x}` of `𝒳`, the sheaf condition for a presheaf `P` on `𝒳` and that family is the sheaf
  condition, on the big site of `U`, for the family of images `{U_i → U}`.
* `AlgebraicGeometry.Stack.isSheafFor_iff_overPost`: the same for an arbitrary presieve on `x`,
  with the presieve downstairs described as the image presieve on `U`, lifted to the slice at the
  identity of `U`.

## Implementation notes

The three elementary transports the proof is assembled from are in
`StacksFrontier/CategoryTheory/Sites/PresieveSheafTransport.lean`: passage to a slice, an equivalence
of categories, and an isomorphism of the object the presieve lives on.  The last is needed because
the localization functor carries the terminal object `id : x → x` of `𝒳/x` to `Over.mk (p(id_x))`
rather than to `Over.mk (𝟙 U)` on the nose.

The topology plays no part: these are statements about one presieve, so they hold before any
topology is chosen, and in particular for all five of the topologies the source quantifies over.

## References

* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
-/

@[expose] public section

open CategoryTheory Opposite

universe t u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (x : 𝒳) (P : 𝒳ᵒᵖ ⥤ Type t)
  (Q : (Over ((p ⋙ Over.forget (B.obj hS)).obj x))ᵒᵖ ⥤ Type t)

include hp in
/-- **The sheaf condition for a family of arrows, across the localization of Stacks 06W0.**  Let
`p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, `x` an object of `𝒳` lying over a
scheme `U`, and `{φ i : z i ⟶ x}` a family of arrows of `𝒳`, lying over the family of morphisms
`{U_i → U}` of schemes.  Let `P` be a presheaf on `𝒳` and `Q` a presheaf on the big site `Sch/U`
whose restriction along the localization functor of Stacks 06W0 is the restriction of `P` to
`𝒳/x`.  Then `P` satisfies the sheaf condition for `{φ i}` if and only if `Q` satisfies the sheaf
condition for `{U_i → U}`.

This is the identification of the two sheaf conditions that the localization of Stacks 06W0 is
for.  The hypothesis `e` is its whole content: the localization functor is an equivalence of
categories, so once the two restricted presheaves are identified the compatible families and the
amalgamations on the two sides are the same. -/
theorem isSheafFor_ofArrows_iff_overPost {I : Type*} {z : I → 𝒳} (φ : ∀ i, z i ⟶ x)
    (e : (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).op ⋙ Q ≅ (Over.forget x).op ⋙ P) :
    Presieve.IsSheafFor P (Presieve.ofArrows z φ) ↔
      Presieve.IsSheafFor Q (Presieve.ofArrows
        (fun i ↦ Over.mk ((p ⋙ Over.forget (B.obj hS)).map (φ i)))
        (fun i ↦ (Over.homMk ((p ⋙ Over.forget (B.obj hS)).map (φ i)) (by simp) :
          Over.mk ((p ⋙ Over.forget (B.obj hS)).map (φ i)) ⟶
            Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))))) := by
  have _ : (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).IsEquivalence :=
    isEquivalence_overPost B S hS p hp x
  set F := Over.post (X := x) (p ⋙ Over.forget (B.obj hS)) with hF
  set g : ∀ i, Over.mk (φ i) ⟶ Over.mk (𝟙 x) := fun i ↦ Over.homMk (φ i) (by simp) with hg
  have h1 : Presieve.IsSheafFor ((Over.forget x).op ⋙ P) (Presieve.ofArrows _ g) ↔
      Presieve.IsSheafFor P (Presieve.ofArrows z φ) :=
    Presieve.isSheafFor_ofArrows_over_iff P g
  have h2 : Presieve.IsSheafFor (F.op ⋙ Q) (Presieve.ofArrows _ g) ↔
      Presieve.IsSheafFor ((Over.forget x).op ⋙ P) (Presieve.ofArrows _ g) :=
    Presieve.isSheafFor_iff_of_iso e
  have h3 : Presieve.IsSheafFor Q
        (Presieve.ofArrows (fun i ↦ F.obj (Over.mk (φ i))) fun i ↦ F.map (g i)) ↔
      Presieve.IsSheafFor (F.op ⋙ Q) (Presieve.ofArrows _ g) :=
    Presieve.isSheafFor_ofArrows_map_iff_of_isEquivalence F Q g
  let ε : F.obj (Over.mk (𝟙 x)) ≅ Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x)) :=
    Over.isoMk (Iso.refl _) (by
      show 𝟙 _ ≫ 𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x) =
        (p ⋙ Over.forget (B.obj hS)).map (𝟙 x)
      simp)
  have h4 := Presieve.isSheafFor_ofArrows_comp_iso_iff Q ε
    (fun i ↦ F.obj (Over.mk (φ i))) fun i ↦ F.map (g i)
  have hfun : (fun i ↦ F.map (g i) ≫ ε.hom) =
      fun i ↦ (Over.homMk ((p ⋙ Over.forget (B.obj hS)).map (φ i)) (by simp) :
        Over.mk ((p ⋙ Over.forget (B.obj hS)).map (φ i)) ⟶
          Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x))) := by
    funext i
    ext : 1
    show (p ⋙ Over.forget (B.obj hS)).map (φ i) ≫ 𝟙 _ =
      (p ⋙ Over.forget (B.obj hS)).map (φ i)
    simp
  rw [hfun] at h4
  exact h1.symm.trans (h2.symm.trans (h3.symm.trans h4.symm))

include hp in
/-- **The sheaf condition for a presieve, across the localization of Stacks 06W0.**  Let
`p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, `x` an object of `𝒳` lying over a
scheme `U`, and `R` a presieve on `x`.  Let `P` be a presheaf on `𝒳` and `Q` a presheaf on the big
site `Sch/U` whose restriction along the localization functor of Stacks 06W0 is the restriction of
`P` to `𝒳/x`.  Then `P` satisfies the sheaf condition for `R` if and only if `Q` satisfies the
sheaf condition for the presieve of arrows of `Sch/U` lying over the image presieve of `R` on `U`.

This is `AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_overPost` for an arbitrary presieve, the
presieve downstairs being described without a choice of indexing family. -/
theorem isSheafFor_iff_overPost (R : Presieve x)
    (e : (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).op ⋙ Q ≅ (Over.forget x).op ⋙ P) :
    Presieve.IsSheafFor P R ↔
      Presieve.IsSheafFor Q (Presieve.functorPullback
        (X := Over.mk (𝟙 ((p ⋙ Over.forget (B.obj hS)).obj x)))
        (Over.forget ((p ⋙ Over.forget (B.obj hS)).obj x))
        (R.map (p ⋙ Over.forget (B.obj hS)))) := by
  obtain ⟨I, z, φ, rfl⟩ := R.exists_eq_ofArrows
  rw [Presieve.map_ofArrows, Presieve.functorPullback_overForget_ofArrows,
    isSheafFor_ofArrows_iff_overPost B S hS p hp x P Q φ e]
  exact (Presieve.isSheafFor_ofArrows_comp_iff _ fun i ↦ Over.isoMk (Iso.refl _) (by simp)).symm

end AlgebraicGeometry.Stack

end
