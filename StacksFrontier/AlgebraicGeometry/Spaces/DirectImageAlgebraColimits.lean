module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsReflectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDirectImageAffine
public import StacksFrontier.CategoryTheory.Sites.Modules.RestrictScalarsSheafification

/-!
# The direct image over `f_*𝒪_Y` commutes with colimits of quasi-coherent modules

Let `f : Y ⟶ X` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `𝒜 = f_*𝒪_Y`.  `AlgebraicGeometry.Space.moduleDirectImage` is the direct
image of `𝒪_Y`-modules taken **over `𝒜`**, which is Stacks 03D1 for the small étale sites, and it
is the right adjoint of
`AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction`, the adjunction whose unit and
counit the first assertion of Stacks 08AI is about.  This file carries the colimit statement of
`StacksFrontier/AlgebraicGeometry/Spaces/AffinePushforwardColimits.lean` from
`AlgebraicGeometry.Space.modulePushforward` — the same direct image read over `𝒪_X` — up to `𝒜`.

The two functors differ only by restriction of scalars along the structure map `f♯ : 𝒪_X ⟶ 𝒜` of
Stacks 03G8, and on the nose:
`AlgebraicGeometry.Space.restrictScalars_moduleDirectImage`.  Restriction of scalars preserves
colimits and reflects isomorphisms, so it reflects the colimits it preserves, and the statement
over `𝒜` follows from the statement over `𝒪_X` with no new geometry.

## Main results

* `AlgebraicGeometry.Space.preservesColimit_moduleDirectImage_of_schemeTarget`: **for an affine
  morphism of algebraic spaces with representable target, the direct image of Stacks 03D1 over
  `f_*𝒪_Y` preserves the colimit of a diagram of quasi-coherent modules.**

## Implementation notes

The target is representable for the same reason as in
`AlgebraicGeometry.Space.preservesColimit_modulePushforward_of_schemeTarget`: preservation of a
colimit is not local on the base, and the representable case is the one the chartwise reduction
of Stacks 08AI needs, an étale chart of an algebraic space being representable by construction.

Two instance binders beyond those of the statement over `𝒪_X` are carried, and both are about the
*shape* of the diagram rather than about `f`: that `𝒜`-modules have colimits of that shape, and
that restriction of scalars preserves them.  Both are automatic for the shapes of interest — a
discrete shape on a type in the module universe, or a finite shape — where
`AlgebraicGeometry.SheafOfModules.restrictScalars_preservesColimits` supplies the second; they
appear as binders only because the diagram shape here is left in arbitrary universes, exactly as
it is in the statement over `𝒪_X`.

## References

* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₂ u₂ u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {K : Type u₂} [Category.{v₂} K] [HasColimitsOfShape K AddCommGrpCat.{u}]
  [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
  [∀ W : Scheme.{u}, HasColimitsOfShape K W.Modules]

/-- **The direct image over `𝒜 = f_*𝒪_Y` along an affine morphism of algebraic spaces with
representable target preserves colimits of quasi-coherent modules.**

This is `AlgebraicGeometry.Space.preservesColimit_modulePushforward_of_schemeTarget` read over
`𝒜` instead of over `𝒪_X`.  The two functors differ by restriction of scalars along the structure
map of Stacks 03G8 and by nothing else
(`AlgebraicGeometry.Space.restrictScalars_moduleDirectImage`), and restriction of scalars both
preserves colimits and reflects isomorphisms, hence reflects the colimits it preserves. -/
theorem preservesColimit_moduleDirectImage_of_schemeTarget (V : BigFppfOver B S hS)
    {Y : AlgebraicSpaces B S hS} (f : Y ⟶ schemeSpace V) (hf : IsAffineHom B S hS f.hom)
    {D : K ⥤ Modules.{u, u} B S hS Y.1 Y.2} (hD : ∀ k, (D.obj k).IsQuasicoherentOnSite)
    [HasColimitsOfShape K
      (SheafOfModules.{u} (structureRingSheafDirectImage B S hS f))]
    [PreservesColimitsOfShape K
      (SheafOfModules.restrictScalars.{u} (structureSharp B S hS f))] :
    PreservesColimit D (moduleDirectImage B S hS f) := by
  have h1 : PreservesColimit D (moduleDirectImage B S hS f ⋙
      SheafOfModules.restrictScalars.{u} (structureSharp B S hS f)) := by
    rw [restrictScalars_moduleDirectImage B S hS f]
    exact preservesColimit_modulePushforward_of_schemeTarget B S hS V f hf hD
  have : ReflectsColimit (D ⋙ moduleDirectImage B S hS f)
      (SheafOfModules.restrictScalars.{u} (structureSharp B S hS f)) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  exact preservesColimit_of_reflects_of_preserves (moduleDirectImage B S hS f)
    (SheafOfModules.restrictScalars.{u} (structureSharp B S hS f))

end AlgebraicGeometry.Space

end
