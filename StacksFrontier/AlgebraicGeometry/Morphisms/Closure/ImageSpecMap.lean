module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk

/-!
# The scheme-theoretic image of a morphism of affine schemes

Let `φ : A ⟶ B` be a ring map with kernel `I`. The scheme-theoretic image of
`Spec.map φ : Spec B ⟶ Spec A` is the closed subscheme `Spec (A ⧸ I)` of `Spec A`.

Mathlib computes the kernel ideal sheaf of a morphism into an affine scheme from the kernel on
global sections (`AlgebraicGeometry.Scheme.ker_of_isAffine`), and
`AlgebraicGeometry.Scheme.ker_SpecMap` makes this explicit for `Spec.map φ`. Comparing with the
closed immersion `Spec (A ⧸ I) ⟶ Spec A`, whose ring map has the same kernel, shows that the two
closed subschemes have the same ideal sheaf; since closed subschemes are determined by their
ideal sheaves, the scheme-theoretic image is identified with `Spec (A ⧸ I)` over `Spec A`.

## Main definitions

* `AlgebraicGeometry.imageSpecMapIso`: the scheme-theoretic image of `Spec.map φ` is
  isomorphic to `Spec (A ⧸ RingHom.ker φ)`.

## Main results

* `AlgebraicGeometry.ker_SpecMap_eq_ker_SpecMap_quotientMk`: the ideal sheaf of the
  scheme-theoretic image of `Spec.map φ` is that of the closed subscheme `Spec (A ⧸ ker φ)`.
* `AlgebraicGeometry.imageSpecMapIso_hom_comp`: the isomorphism lies over `Spec A`.
* `AlgebraicGeometry.toImage_comp_imageSpecMapIso_hom`: it carries the factorization of
  `Spec.map φ` through its image to `Spec` of the induced map `A ⧸ ker φ ⟶ B`.

## References

* [Stacks Project, Tag 056A](https://stacks.math.columbia.edu/tag/056A)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {A B : CommRingCat.{u}} (φ : A ⟶ B)

/-- The scheme-theoretic image of `Spec B ⟶ Spec A` and the closed subscheme
`Spec (A ⧸ ker φ)` of `Spec A` are cut out by the same ideal sheaf. -/
@[stacks 056A "equal closed subschemes"]
theorem ker_SpecMap_eq_ker_SpecMap_quotientMk :
    (Spec.map φ).ker =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ.hom)))).ker := by
  rw [Scheme.ker_SpecMap, Scheme.ker_SpecMap, CommRingCat.hom_ofHom, Ideal.mk_ker]
  rfl

/-- The scheme-theoretic image of `Spec B ⟶ Spec A` is `Spec (A ⧸ ker φ)`. -/
@[stacks 056A]
noncomputable def imageSpecMapIso :
    (Spec.map φ).image ≅ Spec (.of (A ⧸ RingHom.ker φ.hom)) :=
  have h : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ.hom)))).ker =
      (Spec.map φ).imageι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact (ker_SpecMap_eq_ker_SpecMap_quotientMk φ).symm
  have := IsClosedImmersion.isIso_lift _ _ h
  asIso (IsClosedImmersion.lift _ _ h.le)

/-- The isomorphism `imageSpecMapIso` lies over `Spec A`. -/
@[stacks 056A "over Spec A", reassoc (attr := simp)]
theorem imageSpecMapIso_hom_comp :
    (imageSpecMapIso φ).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ.hom))) =
      (Spec.map φ).imageι :=
  IsClosedImmersion.lift_fac _ _ _

/-- Under `imageSpecMapIso`, the factorization of `Spec B ⟶ Spec A` through its image becomes
`Spec` of the induced map `A ⧸ ker φ ⟶ B`. -/
@[reassoc (attr := simp)]
theorem toImage_comp_imageSpecMapIso_hom :
    (Spec.map φ).toImage ≫ (imageSpecMapIso φ).hom =
      Spec.map (CommRingCat.ofHom (RingHom.kerLift φ.hom)) := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ.hom)))),
    Category.assoc, imageSpecMapIso_hom_comp, Scheme.Hom.toImage_imageι, ← Spec.map_comp]
  congr 1

end AlgebraicGeometry

end
