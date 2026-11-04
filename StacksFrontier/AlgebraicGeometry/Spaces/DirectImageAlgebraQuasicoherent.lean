module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFree
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDirectImageAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf

/-!
# The direct-image algebra of an affine morphism is quasi-coherent

Let `f : Y ⟶ X` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `A = f_*𝒪_Y` be the direct image of the structure sheaf of `Y`, a sheaf of
rings on the small étale site of `X`.  This file proves that `A`, read as an `𝒪_X`-module by
restriction of scalars along the structure map `f♯ : 𝒪_X ⟶ f_*𝒪_Y` of Stacks 03G8, is
quasi-coherent.

This is the hypothesis `hA` consumed by Stacks 0H88 instantiated at `𝒜 = f_*𝒪_Y`, and a required
input of the second assertion of Stacks 08AI — the assertion that an `A`-module is quasi-coherent
as an `𝒪_X`-module exactly when it is quasi-coherent as an `A`-module.

The proof is a composition of three facts.  The `𝒪_X`-module
underlying the unit `A`-module is the direct image of the unit `𝒪_Y`-module: on the inverse-image
side this is `Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso`, which is `Iso.refl`, and
restricting scalars along `f♯` turns the direct image over `A` into the direct image read over
`𝒪_X`, which is `AlgebraicGeometry.Space.restrictScalars_moduleDirectImage` and holds by `rfl`.
The structure sheaf `𝒪_Y` is quasi-coherent by `SheafOfModules.isQuasicoherentOnSite_unit`, and
quasi-coherence is preserved by direct image along an affine morphism by the first assertion of
Stacks 07U8.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_restrictScalars_structureRingSheafDirectImage`:
  **for an affine morphism `f : Y ⟶ X` of algebraic spaces the direct-image algebra `f_*𝒪_Y` is
  quasi-coherent as an `𝒪_X`-module.**

## Implementation notes

The identification of the unit `A`-module with the direct image of the unit `𝒪_Y`-module is used
as an isomorphism rather than an equality, through
`SheafOfModules.IsQuasicoherentOnSite.of_iso`, even though
`Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso` is the identity: the transport is what the
statement needs, and nothing is gained by committing to the stronger equality.  The passage from
the direct image over `A` to the direct image over `𝒪_X` is, by contrast, taken as the
definitional identity it is, so the two readings of `f_*` need no comparison at all.

## References

* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
* [Stacks Project, Tag 0H88](https://stacks.math.columbia.edu/tag/0H88)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : AlgebraicSpaces B S hS}

/-- **The direct-image algebra of an affine morphism is quasi-coherent as a module on the
target.**  For an affine morphism `f : Y ⟶ X` of algebraic spaces, the algebra `A = f_*𝒪_Y`, read
as an `𝒪_X`-module by restriction of scalars along the structure map `f♯` of Stacks 03G8, is a
quasi-coherent `𝒪_X`-module.

This is the hypothesis `hA` of Stacks 0H88 at `𝒜 = f_*𝒪_Y`, and a required input of the second
assertion of Stacks 08AI. -/
theorem isQuasicoherentOnSite_restrictScalars_structureRingSheafDirectImage
    (f : Y ⟶ X) (hf : IsAffineHom B S hS f.hom) :
    ((SheafOfModules.restrictScalars.{u} (structureSharp B S hS f)).obj
      (SheafOfModules.unit (structureRingSheafDirectImage B S hS f))).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((SheafOfModules.restrictScalars.{u} (structureSharp B S hS f)).mapIso
      (Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso
        (SmallEtale.topology B S hS X.1) (smallEtaleDirectImage B S hS f)
        (structureRingSheaf B S hS Y))).symm
    (isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS f hf
      (SheafOfModules.unit (structureRingSheaf B S hS Y))
      (SheafOfModules.isQuasicoherentOnSite_unit _))

end AlgebraicGeometry.Space

end
