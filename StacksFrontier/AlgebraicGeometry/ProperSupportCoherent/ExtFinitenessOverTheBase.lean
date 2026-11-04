module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic

/-!
# Orthogonality of the canonical truncations: vanishing of `Ext`

Let `𝒜` be an abelian category with a derived category. If an object `K` of `D(𝒜)` has no
cohomology above `d` and an object `L` none below `b`, then

`Ext^n_𝒜(K, L) = Hom_{D(𝒜)}(K, L⟦n⟧) = 0`  for `n < b - d`,

because `L⟦n⟧` then lies in degrees `≥ b - n > d` and the canonical `t`-structure of `D(𝒜)` has
no nonzero morphisms from `D^{≤d}` to `D^{≥d+1}`.

This is the vanishing half of the picture completed by [Stacks, Tag 0D0D]: for `X` proper over a
Noetherian ring `A`, `K` in `D^-_Coh(𝒪_X)` and `L` in `D^+_Coh(𝒪_X)`, *every* `Ext^n_{𝒪_X}(K, L)`
is a finite `A`-module, and that is
`Stacks.AlgebraicGeometry.ProperSupportCoherent.moduleFinite_ext_of_proper` of
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/ExtFinitenessUnconditional.lean`. The
statement below is not a weaker form of it: it asserts vanishing, not finiteness, and it needs no
geometry at all.

## Main results

* `Stacks.AlgebraicGeometry.ProperSupportCoherent.subsingleton_ext_of_isLE_of_isGE`:
  `Ext^n(K, L) = 0` whenever `K` lies in degrees `≤ d`, `L` in degrees `≥ b` and `n < b - d`. It
  is stated over an arbitrary abelian category with a derived category, since nothing geometric
  enters.

## Implementation notes

The derived category is the standard model, `CategoryTheory.HasDerivedCategory.standard`,
activated as a local instance at a priority high enough to displace the locally small model that
arrives with the imports; that is the model the rest of this directory is baked at.

## References

* [Stacks Project, Tag 0D0D](https://stacks.math.columbia.edu/tag/0D0D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

attribute [local instance 2000] HasDerivedCategory.standard

/-- **Ext vanishes between a complex concentrated in low degrees and one in high degrees.** If
`K` has no cohomology above `d` and `L` none below `b`, then `Ext^n(K, L) = Hom(K, L⟦n⟧)` is zero
for `n < b - d`: the shift `L⟦n⟧` lies in degrees `≥ b - n`, and `b - n > d`, so the two objects
are orthogonal for the canonical `t`-structure. -/
public theorem subsingleton_ext_of_isLE_of_isGE {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K L : DerivedCategory C) (d b n : ℤ)
    (hK : K.IsLE d) (hL : L.IsGE b) (hn : n < b - d) :
    Subsingleton (DerivedCategory.Ext K L n) := by
  have := hK
  have := hL
  have hshift : (L⟦n⟧).IsGE (b - n) :=
    DerivedCategory.TStructure.t.isGE_shift L b n (b - n) (by omega)
  have := hshift
  exact ⟨fun f g => (DerivedCategory.TStructure.t.zero f d (b - n) (by omega)).trans
    (DerivedCategory.TStructure.t.zero g d (b - n) (by omega)).symm⟩

end Stacks.AlgebraicGeometry.ProperSupportCoherent

end
