module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Size.UniversallyClosedCutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Affine space over an affine object of a big fppf site

Step 2 of the proof of Stacks 0F9U assembles a glueing triple out of affine spaces: from the
bundles `T₁ → V` and `T' → Y'` of Stacks 0F82 it builds the triple whose outer components are
`A^{n'}_{T₁}` and `A^{n₁}_{T'}`. Those are components of a triple over the big fppf site, so
they must be *objects of the site*, over the same base and with the projection to `T₁`
respectively `T'` a morphism of the site.

Exactly as for the bundle itself
(`AlgebraicGeometry.exists_contains_affine_pullback_iso_affineSpace`), the obstruction is the
size bound: `AlgebraicGeometry.BigFppfSite.Contains` is a bound on `Scheme.size`, and nothing
about `AlgebraicGeometry.AffineSpace` mentions it. The bound holds for the same reason it holds
there, and more cheaply: `A^n_T → T` is locally of finite presentation for a finite index type,
hence locally of finite type, and `A^n_T` is affine when `T` is, hence quasi-compact, so
Stacks 04T7 bounds its size by that of `T`. No appeal to Stacks 0F82 is needed — this is a
property of affine space, not of the bundle.

The second thing step 2 needs of these components is that they are *cartesian*: the base change
of `A^n_T` along a morphism of bases is `A^n` over the base change of `T`. At the level of
schemes that is `AlgebraicGeometry.AffineSpace.isPullback_map` pasted onto the square defining
the base change of `T`, which is recorded here as
`AlgebraicGeometry.isPullback_affineSpace_paste`: it says that `A^n_P → A^n_T` and the structure
morphism of `A^n_P` to the smaller base exhibit `A^n_P` as the fibre product of `A^n_T` with the
smaller base. That is the form the cartesian condition on a
`BeauvilleLaszlo.Space.GlueingData` reduces to, because the structure morphism of the site
object built here is by construction the *composite* of the affine-space projection with the
structure morphism of `T`, which is the vertical composite the pasting lemma produces.

## Main results

* `AlgebraicGeometry.BigFppfOver.affineSpace`: affine `n`-space over an object of the big
  fppf category over `S`, as an object of that category.
* `AlgebraicGeometry.BigFppfOver.isAffine_affineSpace` and
  `AlgebraicGeometry.BigFppfOver.affineSpaceProj`: it is affine when the base is, and the
  projection to `T` is a morphism of the site.
* `AlgebraicGeometry.isPullback_affineSpace_paste`: affine `n`-space is cartesian over its base
  — the square exhibiting `A^n_P` over the base change `P` of `T` is a fibre product square over
  the composite structure morphism of `A^n_T`.

## Implementation notes

The index type is `ULift (Fin n)`, as in
`AlgebraicGeometry.exists_contains_affine_pullback_iso_affineSpace`, so that the statements here
compose with the conclusion of Stacks 0F82 without a reindexing.

The site object and its projection are defined over any object `T`: the size bound needs no
affineness. Affineness of the base is assumed only by
`AlgebraicGeometry.BigFppfOver.isAffine_affineSpace`, where it is carried as an explicit
argument rather than as an instance, because the object it is about,
`(AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T`, is not a variable.

Both `AlgebraicGeometry.BigFppfOver.toScheme_obj_affineSpace` and
`AlgebraicGeometry.BigFppfOver.toScheme_map_affineSpaceProj` hold by `rfl`: the underlying
scheme of the site object *is* `A^n` over the underlying scheme of `T`, and the underlying
morphism of the projection *is* the structure morphism of affine space. This is what lets the
identifications of Stacks 0F82, which are statements about morphisms of schemes, be applied to
the site object directly rather than transported.

## References

* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
* [Stacks Project, Tag 0F82](https://stacks.math.columbia.edu/tag/0F82)
* [Stacks Project, Tag 0F9U](https://stacks.math.columbia.edu/tag/0F9U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Affine `n`-space over an object of the big fppf category over `S`**, as an object of
that category. Its structure morphism to `S` is the projection to `T` followed by the structure
morphism of `T`, which is what makes it cartesian over `T`. -/
noncomputable def BigFppfOver.affineSpace (n : ℕ) (T : BigFppfOver B S hS) :
    BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (B.contains_affineSpace T.left.2 n)
    ((𝔸(ULift.{u} (Fin n); (BigFppfOver.toScheme B S hS).obj T) ↘
      (BigFppfOver.toScheme B S hS).obj T) ≫ B.inclusion.map T.hom)

/-- The underlying scheme of `AlgebraicGeometry.BigFppfOver.affineSpace` is affine `n`-space
over the underlying scheme of `T`, on the nose. -/
theorem BigFppfOver.toScheme_obj_affineSpace (n : ℕ) (T : BigFppfOver B S hS) :
    (BigFppfOver.toScheme B S hS).obj (BigFppfOver.affineSpace B S hS n T) =
      𝔸(ULift.{u} (Fin n); (BigFppfOver.toScheme B S hS).obj T) :=
  rfl

/-- Affine space over an affine object of the site is affine. -/
theorem BigFppfOver.isAffine_affineSpace (n : ℕ) (T : BigFppfOver B S hS)
    (hTaff : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      (BigFppfOver.affineSpace B S hS n T)) :=
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hTaff
  inferInstanceAs (IsAffine 𝔸(ULift.{u} (Fin n); (BigFppfOver.toScheme B S hS).obj T))

/-- **The projection of affine space over an object of the site**, as a morphism of the site.
The triangle over `S` holds by `rfl`, because the structure morphism of
`AlgebraicGeometry.BigFppfOver.affineSpace` is by construction the composite of this projection
with the structure morphism of `T`. -/
noncomputable def BigFppfOver.affineSpaceProj (n : ℕ) (T : BigFppfOver B S hS) :
    BigFppfOver.affineSpace B S hS n T ⟶ T :=
  Over.homMk (ObjectProperty.homMk
      (𝔸(ULift.{u} (Fin n); (BigFppfOver.toScheme B S hS).obj T) ↘
        (BigFppfOver.toScheme B S hS).obj T))
    (by apply ObjectProperty.hom_ext; rfl)

/-- The morphism of schemes underlying
`AlgebraicGeometry.BigFppfOver.affineSpaceProj` is the structure morphism of affine space, on the
nose. This is what lets the identifications of Stacks 0F82 be applied to it directly. -/
theorem BigFppfOver.toScheme_map_affineSpaceProj (n : ℕ) (T : BigFppfOver B S hS) :
    (BigFppfOver.toScheme B S hS).map (BigFppfOver.affineSpaceProj B S hS n T) =
      (𝔸(ULift.{u} (Fin n); (BigFppfOver.toScheme B S hS).obj T) ↘
        (BigFppfOver.toScheme B S hS).obj T) :=
  rfl

/-- **Affine space is cartesian over its base.** If `P` is the fibre product of `T` with a
smaller base `S'` over `Sb`, then `A^n_P` is the fibre product of `A^n_T` with `S'` over `Sb`,
the structure morphism of `A^n_P` to `S'` being its projection to `P` followed by `P → S'`.

This is `AlgebraicGeometry.AffineSpace.isPullback_map` pasted vertically onto the square
defining `P`. The composite vertical arrows are exactly the structure morphisms that
`AlgebraicGeometry.BigFppfOver.affineSpace` gives its site objects, which is why this is the
cartesian condition those components satisfy. -/
theorem isPullback_affineSpace_paste {n : Type u} {P T Sb S' : Scheme.{u}}
    (a : P ⟶ T) (b : P ⟶ S') (t : T ⟶ Sb) (s : S' ⟶ Sb) (h : IsPullback a b t s) :
    IsPullback (AffineSpace.map n a) ((𝔸(n; P) ↘ P) ≫ b) ((𝔸(n; T) ↘ T) ≫ t) s :=
  (AffineSpace.isPullback_map (n := n) a).paste_vert h

end AlgebraicGeometry

end
