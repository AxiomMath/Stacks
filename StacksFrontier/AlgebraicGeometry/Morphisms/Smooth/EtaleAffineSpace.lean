module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.AtPoint
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smooth morphisms are étale-locally affine spaces

At a point where a morphism of schemes is smooth, every affine open neighbourhood of the image
point contains the image of a smaller affine open neighbourhood of the point admitting an étale
morphism to a finite-dimensional affine space over the prescribed neighbourhood.

## Main results

* `AlgebraicGeometry.exists_etale_affineSpace_of_isStandardSmooth`: a morphism of affine
  schemes whose map on global sections is standard smooth factors through an étale morphism to
  an affine space over the target.
* `AlgebraicGeometry.exists_affine_open_etale_affineSpace`: a morphism smooth at a point admits
  an affine-local factorization through an étale morphism to an affine space over any prescribed
  affine open neighbourhood of the image point.

## Implementation notes

The dimension of the affine space is indexed by `ULift.{u} (Fin d)` so that the affine space
lies in the same universe as the schemes. The diagram commutes over the selected affine open
`V`; composing with the canonical immersion of `V` into the base gives the diagram of the
source.

Smoothness at the point produces an affine chart on which the map of coordinate rings is
standard smooth, and a standard smooth ring map factors through a polynomial ring by an étale
map. Taking spectra and transporting along the canonical isomorphisms of affine schemes with
the spectra of their rings of global sections turns that factorization into the geometric one;
that is the content of the first statement, and the second is its chart-wise application.

The polynomial ring produced by `RingHom.IsStandardSmooth.exists_etale_mvPolynomial` is indexed
by `Fin d`, and `MvPolynomial.renameEquiv` identifies it with the `ULift.{u} (Fin d)`-indexed
one. The commuting triangle reduces to the naturality of `AlgebraicGeometry.Scheme.toSpecΓ`
together with `AlgebraicGeometry.AffineSpace.isoOfIsAffine_inv_over`.

## References

* [Stacks Project, Tag 054L](https://stacks.math.columbia.edu/tag/054L)
* [Stacks Project, Tag 01V7](https://stacks.math.columbia.edu/tag/01V7)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of affine schemes whose map on global sections is standard smooth factors as an
étale morphism to an affine space over the target followed by the projection. -/
theorem exists_etale_affineSpace_of_isStandardSmooth
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    (hf : f.appTop.hom.IsStandardSmooth) :
    ∃ (d : ℕ) (π : X ⟶ AffineSpace (ULift.{u} (Fin d)) S),
      Etale π ∧ π ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = f := by
  obtain ⟨d, g, hgC, hgE⟩ := hf.exists_etale_mvPolynomial
  set n := ULift.{u} (Fin d) with hn
  let ρ : MvPolynomial n Γ(S, ⊤) ≃ₐ[Γ(S, ⊤)] MvPolynomial (Fin d) Γ(S, ⊤) :=
    MvPolynomial.renameEquiv _ Equiv.ulift
  let g' : MvPolynomial n Γ(S, ⊤) →+* Γ(X, ⊤) := g.comp ρ.toRingHom
  have hg'E : g'.Etale :=
    RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective ρ.bijective) hgE
  have hg'C : g'.comp MvPolynomial.C = f.appTop.hom := by
    refine .trans ?_ hgC
    ext a
    simp [g', ρ]
  let φ : CommRingCat.of (MvPolynomial n Γ(S, ⊤)) ⟶ Γ(X, ⊤) := CommRingCat.ofHom g'
  refine ⟨d, X.isoSpec.hom ≫ Spec.map φ ≫ (AffineSpace.isoOfIsAffine n S).inv, ?_, ?_⟩
  · have : Etale (Spec.map φ) := HasRingHomProperty.Spec_iff (P := @Etale).mpr hg'E
    infer_instance
  · have hC : CommRingCat.ofHom (MvPolynomial.C (σ := n) (R := Γ(S, ⊤))) ≫ φ = f.appTop :=
      CommRingCat.hom_ext hg'C
    calc X.isoSpec.hom ≫ Spec.map φ ≫ (AffineSpace.isoOfIsAffine n S).inv ≫
          (AffineSpace n S ↘ S)
        = X.isoSpec.hom ≫ (Spec.map φ ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C)) ≫
            S.isoSpec.inv := by
          rw [AffineSpace.isoOfIsAffine_inv_over]; simp only [Category.assoc]
      _ = X.isoSpec.hom ≫ Spec.map f.appTop ≫ S.isoSpec.inv := by
          rw [← Spec.map_comp, hC]
      _ = f := by
          rw [← Category.assoc, Scheme.isoSpec_hom, ← Scheme.toSpecΓ_naturality]
          simp [Scheme.isoSpec]

/-- A morphism of schemes which is smooth at a point is, over any affine open neighbourhood `V`
of the image of that point, étale-locally an affine space over `V`: there is an affine open
neighbourhood `U` of the point mapping into `V` and an étale morphism from `U` to an affine
space over `V` commuting with the morphism. -/
@[stacks 054L,
  stacks 039Q "smooth at a point is étale-locally an affine space",
  ega "IV 17.11.4" "smooth ⇒ étale/A^d"]
theorem exists_affine_open_etale_affineSpace {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (V : Y.Opens) (hV : IsAffineOpen V) (hxV : x ∈ f ⁻¹ᵁ V)
    (hf : InfinitesimalLifting.SmoothAt f x) :
    ∃ (d : ℕ) (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (hUV : U ≤ f ⁻¹ᵁ V)
      (π : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) V.toScheme),
      Etale π ∧
        π ≫ (AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme) =
          f.resLE V U hUV := by
  obtain ⟨U, hU, hxU, hUV, hstd⟩ :=
    (InfinitesimalLifting.smoothAt_iff_exists_affine_isStandardSmooth f x V hV hxV).mp hf
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  obtain ⟨d, π, hπ, hcomp⟩ :=
    exists_etale_affineSpace_of_isStandardSmooth (f.resLE V U hUV) hstd
  exact ⟨d, U, hU, hxU, hUV, π, hπ, hcomp⟩

end AlgebraicGeometry
