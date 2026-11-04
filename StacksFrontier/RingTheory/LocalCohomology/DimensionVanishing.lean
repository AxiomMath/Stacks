module

public import StacksFrontier.RingTheory.Dualizing.PowerTorsionComparison.LocalCohomologyFunctor
public import StacksFrontier.RingTheory.LocalCohomology.DimensionVanishing.HgroupOfSheafCohomology
public import StacksFrontier.RingTheory.LocalCohomology.DimensionVanishing.PuncturedDimension

/-!
# Towards the vanishing of local cohomology above the dimension of the support

Stacks 0DXC asserts that `H^i_{V(I)}(M) = 0` for `i > dim (Supp M)` when `M` is a finite module
over a ring `A` and `I ⊆ A` is finitely generated, and deduces that the cohomological dimension
of `I` is at most `dim A`. Its proof runs as follows: localize at a prime to reduce to a local
ring; there the closed point lies in `V(I)`, so `Spec A ∖ V(I)` has strictly smaller dimension
and the vanishing of sheaf cohomology above the dimension of a spectral space applies; then
translate that geometric vanishing back into local cohomology, and finally reduce an arbitrary
finite module to the regular module over `A / ann(M)`.

This file collects the parts of that argument which depend only on results already in the
library. The two steps still missing are named in the module docstrings of the imported files
and in the implementation note below.

## Main results

* `Stacks.LocalCohomology.topologicalKrullDim_lt_of_open_avoids_specializingPoint` and
  `Stacks.LocalCohomology.specOpenComplement_toScheme_dim_lt`
  (`.DimensionVanishing.PuncturedDimension`) — removing a closed point to which everything
  specializes drops the dimension, which is the geometric input of the argument.
* `Stacks.LocalCohomology.isZero_Hgroup_of_subsingleton_sheafCohomology`
  (`.DimensionVanishing.HgroupOfSheafCohomology`) — the comparison that turns the abelian-sheaf
  vanishing theorem of Stacks 0A3G into vanishing of the cohomology computed in `Mod(𝒪_X)`.
* `Stacks.LocalCohomology.isZero_homology_localCohomology_of_subsingleton` — local cohomology
  of the zero module vanishes in every degree. This is the degenerate case which the main
  argument has to dispose of separately, because the dimension of an empty support is `⊥`.

## Implementation notes

The statement of Stacks 0DXC itself is not formalized here. Its proof needs two results which
are stated but unproved everywhere available: the equivalence of the three vanishing conditions
of Stacks 0DX7 (which converts the geometric vanishing on `Spec A ∖ V(I)` into vanishing of
local cohomology), and the compatibility of local cohomology with restriction of scalars along
`A → A / ann(M)` of Stacks 0BJB, together with its base-change companion Stacks 0ALZ used by
Stacks 0DXB to reduce to the local case.

## References

* [Stacks Project, Tag 0DXC](https://stacks.math.columbia.edu/tag/0DXC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- Local cohomology with support in `V(I)` of the zero module vanishes in every degree: the
zero object of `D(A)` is terminal, local cohomology is a right adjoint and so preserves
terminal objects, and the subcategory of objects with `I`-power-torsion cohomology contains a
zero object. -/
theorem isZero_homology_localCohomology_of_subsingleton
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{max u v} A) [Subsingleton M] (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
      ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
        ((Dualizing.localCohomologyFunctor A I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)))) := by
  have hsingle : IsZero ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) :=
    Functor.map_isZero (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0)
      (ModuleCat.isZero_of_subsingleton M)
  let LC := Dualizing.localCohomologyFunctor.{u, max u v} A I hI
  have : PreservesLimitsOfSize.{0, 0} LC :=
    (Dualizing.localCohomologyAdjunction A I hI).rightAdjoint_preservesLimits
  let P := Dualizing.derivedPowerTorsionProperty.{u, max u v} A I hI
  have : P.ContainsZero :=
    ⟨_, hsingle, fun j _ ↦ ⟨1, Nat.zero_lt_one, fun _ _ ↦
      (ModuleCat.isZero_iff_subsingleton.mp
        (Functor.map_isZero (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) j)
          hsingle)).elim _ _⟩⟩
  have hLC : IsZero (LC.obj ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) :=
    (isZero_zero P.FullSubcategory).of_iso
      ((IsTerminal.isTerminalObj LC _ hsingle.isTerminal).uniqueUpToIso
        (isZero_zero P.FullSubcategory).isTerminal)
  exact Functor.map_isZero (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i)
    (Functor.map_isZero P.ι hLC)

end Stacks.LocalCohomology

end
