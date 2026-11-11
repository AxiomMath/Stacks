module

public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeNoetherian
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimensionCharts
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekStructureSheafCharts
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekTranscendenceDegree
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingCohenMacaulay

/-!
# The vanishing bound of Tag 0E9V

For a morphism `f : X ⟶ Y` of `FTS S`, a point `x ∈ X` with `𝒪_{Y, f x}` Cohen–Macaulay and
residue transcendence degree at most `r` at the generic points of the components of `X` through
`x`, the stalk `H^i(f^!𝒪_Y)_x` vanishes for `i < -r`.  Together with the `(S₂)` clause this is
[Stacks, Tag 0E9V], stated in
`StacksFrontier.AlgebraicGeometry.Duality.UpperShriekTranscendenceDegreeSerre`.

## Main results

* `Stacks.Duality.relativeDualizingVanishesBelow`: clause (1) of [Stacks, Tag 0E9R] at the
  sharp bound.
* `Stacks.Duality.neg_le_of_nontrivial_stalk_homology_upperShriek_of_residueTrdeg_le_unconditional`:
  the vanishing.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Duality

/-- Clause (1) of [Stacks, Tag 0E9R] at the sharp bound `r`: for a finite type map of Noetherian
rings, `H^i(ω^•_{A/R})` localized at a Cohen–Macaulay prime of `R` vanishes for `i < -r`. -/
theorem relativeDualizingVanishesBelow (r : ℕ) : RelativeDualizingVanishesBelow.{u} r := by
  intro R A φ _ _ p 𝔭 _ hCM htr i hi
  let : Algebra R A := φ.hom.toAlgebra
  refine not_nontrivial_iff_subsingleton.mp fun hnt => ?_
  have h := Dualizing.le_of_nontrivial_localizedModule_homology_relativeDualizingComplex
    (R := R) (A := A) p 𝔭 hCM r
    (fun q _ hq => (trdeg_le_residueTrdeg_spec R A φ ⟨q, inferInstance⟩).trans
      (htr ⟨q, inferInstance⟩ hq)) i hnt
  omega

section Shriek

open DerivedPushforward

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- **The vanishing of [Stacks, Tag 0E9V].** If `𝒪_{Y, f x}` is
Cohen–Macaulay and the residue transcendence degree of `f` is at most `r` at every generic point
of a component of `X` through `x`, then `H^i(f^!𝒪_Y)_x ≠ 0` implies `-r ≤ i`, for every `j`. -/
theorem neg_le_of_nontrivial_stalk_homology_upperShriek_of_residueTrdeg_le_unconditional
    (x : X.left) (r : ℕ)
    (hCM : IsCohenMacaulayLocalRing (Y.left.presheaf.stalk (f.left.base x)))
    (htrdeg : ∀ ξ : X.left, closure {ξ} ∈ irreducibleComponents X.left → x ∈ closure {ξ} →
      Stacks.Chow.residueTrdeg f.left ξ ≤ (r : Cardinal))
    (i : ℤ)
    (hi : Nontrivial (((DerivedCategory.homologyFunctor X.left.Modules i).obj
      (((upperShriek f j).obj
        (derivedStructureSheaf Y.left)).obj)).presheaf.stalk x)) :
    -(r : ℤ) ≤ i :=
  neg_le_of_nontrivial_stalk_homology_upperShriek_of_residueTrdeg_le f j x r
    (fun W hxW => exists_chart_of_upperShriekStructureSheafCharts f j
      (upperShriekStructureSheafCharts f j) x W hxW)
    (relativeDualizingVanishesBelow r) hCM htrdeg i hi

end Shriek

end Stacks.Duality
