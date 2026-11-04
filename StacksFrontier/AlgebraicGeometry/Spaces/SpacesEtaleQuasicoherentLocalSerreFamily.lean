module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleQuasicoherentLocalSerre
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleQuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleSliceAffineVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleAffineCoverings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.QuasicoherenceSliceLocality
import StacksCore.Tactic.StacksAttribute

/-!
# The quasi-coherent modules on the spaces-étale site satisfy the conditions of Stacks 0DC1

Let `S` be a scheme, `X` an algebraic space over `S` and `C = X_{spaces, étale}` the étale site on
the algebraic spaces étale over `X` (Stacks 03G0), with its structure sheaf
`U ↦ Γ(U, 𝒪_U)`.  For an object `U` of `C` let `A_U` be the quasi-coherent `𝒪_U`-modules on the
slice `C/U`.  Stacks 0DC5 asserts that this family is an instance of the situation of the
unbounded cohomological descent of Stacks 0DC1, with `B = Ob(C)`, `d_V = 0` and `Cov_V` the
coverings of `V` by affine objects.  This file proves all of it:

* each `A_U` is a weak Serre subcategory
  (`AlgebraicGeometry.Space.isWeakSerreClass_spacesEtaleQuasicoherentSlices`, Stacks 03M1 read on
  the slice, which is the spaces-étale site of `U` by Stacks 04LY and corresponds to the small
  étale site of `U` by Stacks 03G1);
* condition (1), Stacks 0DC2: restriction along a morphism of `C` preserves quasi-coherence
  (`AlgebraicGeometry.Space.isStableUnderRestriction_spacesEtaleQuasicoherentSlices`);
* condition (2), Stacks 0DC3: quasi-coherence on `C/U` is local on coverings of `U`
  (`AlgebraicGeometry.Space.isLocalOnCoverings_spacesEtaleQuasicoherentSlices`);
* condition (3), Stacks 0DC4, with `B = Ob(C)`, `d_V = 0` and `Cov_V` the coverings of `V` whose
  members have affine underlying algebraic space: these coverings are cofinal
  (`AlgebraicGeometry.Space.SpacesEtale.affineCoverings`), and `H^p(V_i, F) = 0` for `p > 0`
  and `F` quasi-coherent on `C/V`
  (`AlgebraicGeometry.Space.SpacesEtale.isZero_moduleCohomology_of_isAffineSpace`), the vanishing
  the source takes from Stacks 01XB and the discussion of Stacks 071Y.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleQuasicoherentBound`: the data of condition (3).
* `AlgebraicGeometry.Space.spacesEtaleQuasicoherentLocalSerreFamily`: the family `A_U` packaged as
  a `Stacks.Cohomology.CohomologicalDescent.LocalSerreFamily`.

## Main results

* `AlgebraicGeometry.Space.spacesEtaleQuasicoherent_localSerre`: **Stacks 0DC5**, all of its
  assertions at once.

## Implementation notes

The vanishing is the module cohomology `Stacks.Cohomology.moduleCohomology` of
`Stacks.Cohomology.CohomologicalDescent.LocalCohomologicalBound`, the right derived functors of
sections over `V_i` on the slice `C/V`; it is deduced from the abelian cohomology of the iterated
slice `(C/V)/V_i`, which is the spaces-étale site of the affine algebraic space `V_i`.

## References

* [Stacks Project, Tag 0DC5](https://stacks.math.columbia.edu/tag/0DC5)
* [Stacks Project, Tag 0DC1](https://stacks.math.columbia.edu/tag/0DC1)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 071Y](https://stacks.math.columbia.edu/tag/071Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.CohomologicalDescent

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **Condition (2) of Stacks 0DC1 for the family of Stacks 0DC5**: a module on the slice of the
spaces-étale site at `U` is quasi-coherent if and only if its restrictions to the members of a
covering of `U` are. -/
theorem isLocalOnCoverings_spacesEtaleQuasicoherentSlices :
    IsLocalOnCoverings (spacesEtaleRingedSite B S hS X) (spacesEtaleQuasicoherentSlices B S hS X) :=
  fun _ 𝒰 h𝒰 F ↦ Stacks.SheafOfModules.isQuasicoherentOnSite_iff_forall_overMap _ 𝒰 h𝒰 F

/-- **Condition (3) of Stacks 0DC1 for the family of Stacks 0DC5**, with the data of the source:
the set `B` is all of `Ob(C)`, the bound `d_V` is `0`, and `Cov_V` is the system of coverings of
`V` whose members have affine underlying algebraic space. -/
def spacesEtaleQuasicoherentBound :
    LocalCohomologicalBound (spacesEtaleRingedSite B S hS X)
      (spacesEtaleQuasicoherentSlices B S hS X) where
  B := Set.univ
  basisCover U := ⟨SpacesEtale.affineSchemeCover B S hS X U,
    SpacesEtale.affineSchemeCover_mem B S hS X U, fun _ ↦ trivial⟩
  degreeBound _ _ := 0
  coverings V _ := SpacesEtale.affineCoverings B S hS X V
  vanishing V _ 𝒰 h𝒰 := by
    intro i p hp F hF
    exact SpacesEtale.isZero_moduleCohomology_of_isAffineSpace V F hF (Over.mk (𝒰.f i))
      (h𝒰.2 i) p (by exact_mod_cast hp)

/-- The family of quasi-coherent modules on the slices of the spaces-étale site, as a family of
weak Serre subcategories subject to the three conditions of Stacks 0DC1. -/
def spacesEtaleQuasicoherentLocalSerreFamily :
    LocalSerreFamily (spacesEtaleRingedSite B S hS X) where
  A := spacesEtaleQuasicoherentSlices B S hS X
  weakSerre := isWeakSerreClass_spacesEtaleQuasicoherentSlices B S hS X
  restriction := isStableUnderRestriction_spacesEtaleQuasicoherentSlices B S hS X
  locality := isLocalOnCoverings_spacesEtaleQuasicoherentSlices B S hS X
  bound := spacesEtaleQuasicoherentBound B S hS X

/-- **Stacks 0DC5.**  Let `S` be a scheme, `X` an algebraic space over `S`,
`C = X_{spaces, étale}` with its structure sheaf, and `A_U` the quasi-coherent `𝒪_U`-modules on
the slice `C/U`.  Then each `A_U` is a weak Serre subcategory, and the three conditions of
Stacks 0DC1 hold: restriction along a morphism `U ⟶ V` of `C` sends `A_V` into `A_U`
(Stacks 0DC2); membership in `A_U` is local on coverings of `U` (Stacks 0DC3); and condition
(3) (Stacks 0DC4) holds with `B = Ob(C)`, `d_V = 0` and `Cov_V` the coverings `{V_i ⟶ V}` with
every `V_i` affine, that is, for such a covering, every `p > 0` and every `F` in `A_V`,
`H^p(V_i, F) = 0`. -/
@[stacks 0DC5]
theorem spacesEtaleQuasicoherent_localSerre :
    (∀ U, (spacesEtaleQuasicoherentSlices B S hS X U).IsWeakSerreClass) ∧
      IsStableUnderRestriction (spacesEtaleRingedSite B S hS X)
        (spacesEtaleQuasicoherentSlices B S hS X) ∧
      IsLocalOnCoverings (spacesEtaleRingedSite B S hS X)
        (spacesEtaleQuasicoherentSlices B S hS X) ∧
      ∃ b : LocalCohomologicalBound (spacesEtaleRingedSite B S hS X)
          (spacesEtaleQuasicoherentSlices B S hS X),
        b.B = Set.univ ∧ (∀ V hV, b.degreeBound V hV = 0) ∧
          ∀ V hV (𝒰 : PreZeroHypercover.{u + 1} V), (b.coverings V hV).cov 𝒰 ↔
            𝒰.sieve₀ ∈ (spacesEtaleRingedSite B S hS X).J V ∧
              ∀ i, IsAffineSpace B S hS (𝒰.X i).obj.left.1 :=
  ⟨isWeakSerreClass_spacesEtaleQuasicoherentSlices B S hS X,
    isStableUnderRestriction_spacesEtaleQuasicoherentSlices B S hS X,
    isLocalOnCoverings_spacesEtaleQuasicoherentSlices B S hS X,
    spacesEtaleQuasicoherentBound B S hS X, rfl, fun _ _ ↦ rfl, fun _ _ _ ↦ Iff.rfl⟩

end AlgebraicGeometry.Space
