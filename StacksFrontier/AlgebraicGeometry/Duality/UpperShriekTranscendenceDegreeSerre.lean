module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekTranscendenceDegreeCharts
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekTranscendenceDegreeVanishing

/-!
# Tag 0E9V

For a morphism `f : X ⟶ Y` of `FTS S` and a point `x ∈ X` with `𝒪_{Y, f x}` Cohen–Macaulay and
residue transcendence degree at most `r` at the generic points of the components of `X` through
`x`, the stalk `H^i(f^!𝒪_Y)_x` vanishes for `i < -r`, and the stalk `H^{-r}(f^!𝒪_Y)_x` is `(S₂)`
as an `𝒪_{X,x}`-module.

## Main results

* `Stacks.Duality.neg_le_and_propertySkModule_stalk_homology_upperShriek_of_residueTrdeg_le`:
  [Stacks, Tag 0E9V], both conclusions.

## References

* [Stacks Project, Tag 0E9V](https://stacks.math.columbia.edu/tag/0E9V)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Duality

section Shriek

open DerivedPushforward

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- **Stacks Project, Tag 0E9V (Lemma 48.21.5).** In Situation [Stacks, Tag 0F42], let
`f : X ⟶ Y` be a morphism of `FTS S` and let `x ∈ X` with image `y = f x`.  Assume `𝒪_{Y, y}` is
Cohen–Macaulay and `trdeg_{κ(f ξ)} κ(ξ) ≤ r` for every generic point `ξ` of an irreducible
component of `X` containing `x`.  Then `H^i(f^!𝒪_Y)_x ≠ 0` implies `-r ≤ i`, and the stalk
`H^{-r}(f^!𝒪_Y)_x` is `(S₂)` as an `𝒪_{X,x}`-module (it is a finite `𝒪_{X,x}`-module by
`module_finite_modulesStalk_homology_upperShriek`).  Here `f^!` is `upperShriek f j` for any
compactification `j`. -/
@[stacks 0E9V "both conclusions: the vanishing H^i(f^! O_Y)_x nonzero implies -r <= i, and the
(S_2) property of the stalk H^{-r}(f^! O_Y)_x as an O_{X,x}-module"]
theorem neg_le_and_propertySkModule_stalk_homology_upperShriek_of_residueTrdeg_le
    (x : X.left) (r : ℕ)
    (hCM : IsCohenMacaulayLocalRing (Y.left.presheaf.stalk (f.left.base x)))
    (htrdeg : ∀ ξ : X.left, closure {ξ} ∈ irreducibleComponents X.left → x ∈ closure {ξ} →
      Stacks.Chow.residueTrdeg f.left ξ ≤ (r : Cardinal)) :
    (∀ i : ℤ, Nontrivial (((DerivedCategory.homologyFunctor X.left.Modules i).obj
        (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj)).presheaf.stalk x) →
        -(r : ℤ) ≤ i) ∧
    letI := module_finite_modulesStalk_homology_upperShriek f j x (-(r : ℤ))
    PropertySkModule (X.left.presheaf.stalk x) ((modulesStalkFunctor x).obj
      ((DerivedCategory.homologyFunctor X.left.Modules (-(r : ℤ))).obj
        (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj))) 2 :=
  ⟨neg_le_of_nontrivial_stalk_homology_upperShriek_of_residueTrdeg_le_unconditional f j x r hCM
      htrdeg,
    propertySkModule_modulesStalk_homology_upperShriek_of_residueTrdeg_le f j x r hCM htrdeg⟩

end Shriek

end Stacks.Duality
