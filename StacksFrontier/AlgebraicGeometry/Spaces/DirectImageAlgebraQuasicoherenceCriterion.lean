module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentOverAlgebraIff

/-!
# The quasi-coherence criterion for modules over the direct-image algebra

Let `f : Y ⟶ X` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `𝒜 = f_*𝒪_Y` be the direct image of the structure sheaf of `Y`, a sheaf of
rings on the small étale site of `X`.  The **second assertion of Stacks 08AI** says that an
`𝒜`-module is quasi-coherent as an `𝒪_X`-module if and only if it is quasi-coherent as an
`𝒜`-module.  This file proves it, in both directions, by instantiating the criterion for an
arbitrary quasi-coherent algebra at `𝒜 = f_*𝒪_Y`, whose quasi-coherence as an `𝒪_X`-module is the
first assertion of Stacks 07U8.

The first consequence is that direct image over `𝒜` carries quasi-coherent `𝒪_Y`-modules to
quasi-coherent `𝒜`-modules, which is
`AlgebraicGeometry.Space.DirectImagePreservesQuasicoherence`: the direct image read over `𝒪_X` is
quasi-coherent by Stacks 07U8, and over `𝒪_X` it is the restriction of scalars along
`f♯ : 𝒪_X ⟶ 𝒜` of the direct image over `𝒜`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_restrictScalars_structureSharp_iff` — **the
  second assertion of Stacks 08AI**: an `f_*𝒪_Y`-module is quasi-coherent as an `𝒪_X`-module if
  and only if it is quasi-coherent as an `f_*𝒪_Y`-module.
* `AlgebraicGeometry.Space.directImagePreservesQuasicoherence` —
  `AlgebraicGeometry.Space.DirectImagePreservesQuasicoherence` for an affine morphism, so that
  `AlgebraicGeometry.Space.quasicoherentDirectImage` applies to every affine morphism of
  algebraic spaces.
* `AlgebraicGeometry.Space.affineQuasicoherentDirectImage` — **the functor of the tag's first
  sentence**, under the hypotheses of the source: for an affine morphism, and with no other
  hypothesis, direct image is a functor from the quasi-coherent `𝒪_Y`-modules to the
  quasi-coherent `𝒜`-modules.
* `AlgebraicGeometry.Space.affineQuasicoherentDirectImage_comp_ι` — that functor is `f_*` on the
  nose.

## Implementation notes

The passage from the direct image over `𝒜` to the direct image read over `𝒪_X` is the
definitional identity `AlgebraicGeometry.Space.restrictScalars_moduleDirectImage`, so the
instantiation needs no comparison of the two readings of `f_*`.

The first assertion of the tag, that `AlgebraicGeometry.Space.affineQuasicoherentDirectImage` is
an equivalence of categories, is
`AlgebraicGeometry.Space.isEquivalence_affineQuasicoherentDirectImage`.

The functor is defined here rather than reusing `AlgebraicGeometry.Space.quasicoherentDirectImage`
with a hypothesis, because that declaration takes
`AlgebraicGeometry.Space.DirectImagePreservesQuasicoherence` as an input, and that preservation is
part of the tag's first sentence; here it is derived.

## References

* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
-/

@[expose] public section

universe u

open CategoryTheory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : AlgebraicSpaces B S hS}

/-- **Stacks 08AI, second assertion.**  Let `f : Y ⟶ X` be an affine morphism of algebraic spaces
over `S` and let `𝒜 = f_*𝒪_Y`.  An `𝒜`-module is quasi-coherent as an `𝒪_X`-module — that is,
after restriction of scalars along the structure map `f♯ : 𝒪_X ⟶ 𝒜` of Stacks 03G8 — if and only
if it is quasi-coherent as an `𝒜`-module.

This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_restrictScalars_iff` at `A = f_*𝒪_Y`,
whose quasi-coherence as an `𝒪_X`-module is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_restrictScalars_structureRingSheafDirectImage`,
the first assertion of Stacks 07U8 at the structure sheaf. -/
@[stacks 08AI "an 𝒜-module is quasi-coherent as an 𝒪_X-module if and only if it is \
quasi-coherent as an 𝒜-module"]
theorem isQuasicoherentOnSite_restrictScalars_structureSharp_iff (f : Y ⟶ X)
    (hf : IsAffineHom B S hS f.hom)
    (M : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f)) :
    ((SheafOfModules.restrictScalars.{u} (structureSharp B S hS f)).obj
        M).IsQuasicoherentOnSite ↔ M.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_restrictScalars_iff B S hS (structureSharp B S hS f)
    (isQuasicoherentOnSite_restrictScalars_structureRingSheafDirectImage B S hS f hf) M

/-- **Direct image along an affine morphism of algebraic spaces carries quasi-coherent
`𝒪_Y`-modules to quasi-coherent `𝒜`-modules**, for `𝒜 = f_*𝒪_Y`: this is
`AlgebraicGeometry.Space.DirectImagePreservesQuasicoherence`.

The direct image of a quasi-coherent `𝒪_Y`-module, read as an `𝒪_X`-module, is quasi-coherent by
the first assertion of Stacks 07U8, and that reading is the restriction of scalars along `f♯` of
the direct image over `𝒜`; the second assertion of Stacks 08AI turns the one into the other. -/
theorem directImagePreservesQuasicoherence (f : Y ⟶ X) (hf : IsAffineHom B S hS f.hom) :
    DirectImagePreservesQuasicoherence B S hS f := fun M hM ↦
  (isQuasicoherentOnSite_restrictScalars_structureSharp_iff B S hS f hf
      ((moduleDirectImage B S hS f).obj M)).1
    (isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS f hf M hM)

/-- **Stacks 08AI, the functor of the first sentence, under the hypotheses of the source.**  For
an affine morphism `f : Y ⟶ X` of algebraic spaces over `S` and `𝒜 = f_*𝒪_Y`, direct image
`ℱ ↦ f_*ℱ` is a functor from the quasi-coherent `𝒪_Y`-modules to the quasi-coherent
`𝒜`-modules.

This takes the affineness of `f` and nothing else.  It is
`AlgebraicGeometry.Space.quasicoherentDirectImage` with its preservation hypothesis discharged by
`AlgebraicGeometry.Space.directImagePreservesQuasicoherence`: that preservation is part of what
the tag asserts, so it is derived here rather than assumed. -/
noncomputable def affineQuasicoherentDirectImage (f : Y ⟶ X) (hf : IsAffineHom B S hS f.hom) :
    QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2 ⥤
      (SheafOfModules.isQuasicoherentOnSite
        (affineDirectImageAlgebra B S hS f)).FullSubcategory :=
  quasicoherentDirectImage B S hS f (directImagePreservesQuasicoherence B S hS f hf)

/-- The functor of `AlgebraicGeometry.Space.affineQuasicoherentDirectImage` is the direct image
over `𝒜` of Stacks 03D1 on the nose: composing it with the inclusion of the quasi-coherent
`𝒜`-modules into all `𝒜`-modules recovers `AlgebraicGeometry.Space.moduleDirectImage`. -/
theorem affineQuasicoherentDirectImage_comp_ι (f : Y ⟶ X) (hf : IsAffineHom B S hS f.hom) :
    affineQuasicoherentDirectImage B S hS f hf ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙ moduleDirectImage B S hS f := rfl

end AlgebraicGeometry.Space

end
