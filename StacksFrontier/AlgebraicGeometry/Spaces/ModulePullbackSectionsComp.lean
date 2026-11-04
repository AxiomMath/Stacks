module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGlobalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemePullback

/-!
# The inverse image of a global section along a composite

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces and let `σ` be a global
section of an `𝒪_Z`-module `M`. The inverse image of `σ` along `f ≫ g` is the inverse image along
`f` of its inverse image along `g`, read through the comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU:

`(f^*g^*M ≅ (f ≫ g)^*M) (f^*(g^*σ)) = (f ≫ g)^*σ`.

A global section is a morphism out of the unit `𝒪`, so this is the naturality of the comparison
together with its compatibility with the identifications `h^*𝒪 ≅ 𝒪`
(`AlgebraicGeometry.Space.modulePullbackGlobalSection_modulePullbackGlobalSection`).

## Main results

* `AlgebraicGeometry.Space.sectionsMap_modulePullbackCompIso_inv_modulePullbackSections`: the
  identity above, read backwards; the identity itself is
  `AlgebraicGeometry.Space.sectionsMap_modulePullbackCompIso_modulePullbackSections`, in
  `StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemePullback`.
* `AlgebraicGeometry.Space.sectionsMap_modulePullbackCompComparison_modulePullbackSections`: the
  same through the comparison with the inverse image along a morphism equal to `f ≫ g`.
* `AlgebraicGeometry.Space.sectionsMap_eqToHom_modulePullbackSections`: along equal morphisms.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Modules.{u, u} B S hS Z.obj Z.property)

/-- **The inverse image of a global section along a composite, read backwards.** The inverse of
the comparison `f^*g^*M ≅ (f ≫ g)^*M` of Stacks 03LU carries `(f ≫ g)^*σ` to `f^*(g^*σ)`. -/
theorem sectionsMap_modulePullbackCompIso_inv_modulePullbackSections (σ : M.sections) :
    SheafOfModules.sectionsMap ((modulePullbackCompIso B S hS f g).inv.app M)
        (modulePullbackSections B S hS (f ≫ g) M σ) =
      modulePullbackSections B S hS f ((modulePullback B S hS g).obj M)
        (modulePullbackSections B S hS g M σ) := by
  rw [← sectionsMap_modulePullbackCompIso_modulePullbackSections B S hS f g M σ,
    ← SheafOfModules.sectionsMap_comp, Iso.hom_inv_id_app]
  exact SheafOfModules.sectionsMap_id _

/-- **The inverse image of a global section along a morphism equal to a composite.** For
`f ≫ g = k`, the comparison `f^*g^*M ≅ k^*M` of
`AlgebraicGeometry.Space.modulePullbackCompComparison` carries `f^*(g^*σ)` to `k^*σ`. -/
theorem sectionsMap_modulePullbackCompComparison_modulePullbackSections (k : X ⟶ Z)
    (w : f ≫ g = k) (σ : M.sections) :
    SheafOfModules.sectionsMap (modulePullbackCompComparison B S hS f g k w M)
        (modulePullbackSections B S hS f ((modulePullback B S hS g).obj M)
          (modulePullbackSections B S hS g M σ)) =
      modulePullbackSections B S hS k M σ := by
  subst w
  rw [modulePullbackCompComparison, eqToHom_refl, Category.comp_id]
  exact sectionsMap_modulePullbackCompIso_modulePullbackSections B S hS f g M σ

/-- **The inverse image of a global section along equal morphisms.** For `a = b`, the
identification `a^*M = b^*M` carries `a^*σ` to `b^*σ`. -/
theorem sectionsMap_eqToHom_modulePullbackSections {a b : X ⟶ Z} (h : a = b)
    (e : (modulePullback B S hS a).obj M = (modulePullback B S hS b).obj M) (σ : M.sections) :
    SheafOfModules.sectionsMap (eqToHom e) (modulePullbackSections B S hS a M σ) =
      modulePullbackSections B S hS b M σ := by
  subst h
  rfl

end AlgebraicGeometry.Space

end
