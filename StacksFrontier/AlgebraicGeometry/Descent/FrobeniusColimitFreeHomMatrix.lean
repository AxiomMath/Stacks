module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeHomMatrix
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitSectionsComparison

/-!
# Hom-sets of free Frobenius-colimit bundles are matrices of Frobenius colimits of functions

Let `p` be a prime and let `X` be a scheme in characteristic `p`. A morphism

`(colim_F 𝒪_X)^{⊕I} ⟶ (colim_F 𝒪_X)^{⊕K}`

of free modules over the sheaf of rings `colim_F 𝒪_X` of Stacks Tag 0EXB, with `K` finite, is a
matrix of global sections of `colim_F 𝒪_X` — the top open being the terminal object of the site
of opens of `X` — and when `X` is quasi-compact and quasi-separated those global sections are
the Frobenius colimit `colim_F Γ(X, 𝒪)` of the global functions of `X`.

This is the Hom-level input to the full faithfulness half of Stacks Tag 0EXD: on a trivialising
open the Hom-sets of `AlgebraicGeometry.frobeniusColimitVectorBundles` are matrices over those
rings, and the square of those rings attached to the almost blowup square of Example 0EVH is
cartesian by `AlgebraicGeometry.isPullback_frobeniusColimitSections_twoGenerator`.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitFreeHomMatrixEquiv`: **a morphism of free
  `colim_F 𝒪_X`-modules is a matrix of global sections of `colim_F 𝒪_X`.**
* `AlgebraicGeometry.frobeniusColimitFreeHomColimitEquiv`: **over a quasi-compact
  quasi-separated scheme it is a matrix of Frobenius colimits of global functions of `X`.**

## Implementation notes

Both are instances of `Stacks.SheafOfModules.freeHomMatrixEquiv` at the terminal object `⊤` of
the site of opens of `X`, the second composed with
`AlgebraicGeometry.bijective_frobeniusColimitSectionsComparison` entrywise.

The compatibility of these matrix descriptions with the transition functors
`AlgebraicGeometry.frobeniusColimitVectorBundlesPullback` of Stacks Tag 0EXE is
`AlgebraicGeometry.frobeniusColimitFreeHomMatrixEquiv_pullbackFreeHom`: a transition functor
carries a free module to a free module by `SheafOfModules.pullbackObjFreeIso`, and conjugated by
that isomorphism it acts on a matrix entrywise by
`AlgebraicGeometry.frobeniusColimitSectionsRestrict`. Read entrywise,
`AlgebraicGeometry.isPullback_frobeniusColimitSections_twoGenerator` therefore gives the
cartesian square of Hom-sets of free modules, and
`AlgebraicGeometry.isPullback_squareComparison_homSquare_free_twoGenerator` is the full
faithfulness of `AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison` at *free* modules
that it yields.

## References

* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- **A morphism of free `colim_F 𝒪_X`-modules is a matrix of global sections of
`colim_F 𝒪_X`.** -/
noncomputable def frobeniusColimitFreeHomMatrixEquiv (I K : Type u) [Fintype K]
    [DecidableEq K] :
    (SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) I ⟶
        SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) K) ≃
      (I → K → ToType ((frobeniusColimitRingSheaf X p hX).obj.obj (op ⊤))) :=
  Stacks.SheafOfModules.freeHomMatrixEquiv (isTerminalTop (α := X.Opens)) I K

/-- **Over a quasi-compact quasi-separated scheme, a morphism of free `colim_F 𝒪_X`-modules is a
matrix of Frobenius colimits of global functions of `X`.** This is the Hom-level form in which
the proof of Stacks Tag 0EXD uses the cartesianness of Stacks 0EVK: the square of
`colim_F Γ(-, 𝒪)` at the almost blowup square of Example 0EVH is cartesian, hence so is the
square of matrices over it. -/
noncomputable def frobeniusColimitFreeHomColimitEquiv [CompactSpace X]
    [QuasiSeparatedSpace X] (I K : Type u) [Fintype K] [DecidableEq K] :
    (SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) I ⟶
        SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) K) ≃
      (I → K → (frobeniusColimitGlobalSections.{u} p).obj (op X)) :=
  (frobeniusColimitFreeHomMatrixEquiv X p hX I K).trans
    (Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ =>
      (Equiv.ofBijective _ (bijective_frobeniusColimitSectionsComparison X p hX)).symm)

end AlgebraicGeometry

end
