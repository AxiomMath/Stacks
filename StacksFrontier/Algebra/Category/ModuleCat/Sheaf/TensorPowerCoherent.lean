module

public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras
import StacksCore.Tactic.StacksAttribute

/-!
# Coherence of the tensor powers of a sheaf of modules

Let `(X, 𝒪_X)` be a ringed space and `F` a coherent sheaf of `𝒪_X`-modules. Then `Tⁿ F` is
coherent for every `n > 0`. This is clause (4) of Stacks Tag 01CK for the tensor powers; as in the
source, it follows from clause (6) of Lemma 01CE,
`AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent`: a tensor product of two coherent
sheaves of modules is coherent.

The induction starts at degree one rather than at degree zero, as the hypothesis `n > 0` requires:
`T⁰ F` is the structure sheaf, which on a general ringed space need not be coherent. In degree one
the power is `F` itself, and `Tⁿ⁺²(F)` is `F ⊗ Tⁿ⁺¹(F)` by definition, so 01CE (6) applies with
both factors coherent.

## Main results

* `Stacks.SheafOfModules.isCoherent_tensorPower_succ`: every tensor power of positive degree of a
  coherent sheaf of modules is coherent, for `SheafOfModules.tensorPower`.
* `Stacks.SheafOfModules.isCoherent_tensorPower`: **clause (4) of Tag 01CK for the tensor
  powers**, for the degree-`n` piece of the tensor algebra of Section 17.21. The symmetric part
  of the same clause is `Stacks.SheafOfModules.isCoherent_symmetricPower` of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerCoherent`.

## Implementation notes

**Two spellings of the tensor product.**
`AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent` is stated for the tensor product
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, whereas `SheafOfModules.tensorPower`
is built from `Stacks.SheafOfModules.Tensor.sheafTensor`, both over `structureSheafRing X`. These
agree by `rfl` (the identifications are recorded in the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBifunctorStalk`), but `structureSheafRing` is
a plain `def`, so instance search, which runs at reducible transparency, does not cross it. Each
coherence hypothesis is therefore restated at the spelling `tensorSheaf_isCoherent` uses by
`assumption`, which checks the two against each other at default transparency, as
`StacksFrontier.AlgebraicGeometry.TensorFiniteness.RingedSpace` does for the finiteness clauses of
the same tag.

**The transport to the homogeneous piece.** The clause is about the degree-`n` piece of the
tensor algebra, which `SheafOfModules.TensorExteriorSymmetricAlgebras.tensorPieceIso` identifies
with the degree-`n` tensor power. Coherence is closed under isomorphism as the object property
`Stacks.SheafOfModules.coherentModules`, and `Stacks.SheafOfModules.TensorOver.isCoherent_iff`
converts between that class and the root-level `SheafOfModules.IsCoherent` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation`; the two are the same
two fields under different names.

## References

* [Stacks Project, Tag 00DP](https://stacks.math.columbia.edu/tag/00DP)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf AlgebraicGeometry
  TopologicalSpace

universe u

namespace Stacks.SheafOfModules

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}
  (F : _root_.SheafOfModules.{u} (structureSheafRing X))

/-- **Every tensor power of positive degree of a coherent sheaf of modules on a ringed space is
coherent.** The induction is on the degree: in degree one the power is `F`, and the step is
clause (6) of Stacks 01CE, `AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent`, since
`Tⁿ⁺²(F)` is `F ⊗ Tⁿ⁺¹(F)` by definition. -/
theorem isCoherent_tensorPower_succ [_root_.SheafOfModules.IsCoherent F] (m : ℕ) :
    _root_.SheafOfModules.IsCoherent
      (_root_.SheafOfModules.tensorPower (Opens.grothendieckTopology X.carrier)
        (Osharp := X.sheaf) F (m + 1)) := by
  induction m with
  | zero => assumption
  | succ k ih =>
    have hF : _root_.SheafOfModules.IsCoherent
        (R := structureSheafRing X) F := by
      assumption
    have hT : _root_.SheafOfModules.IsCoherent
        (R := structureSheafRing X)
        (_root_.SheafOfModules.tensorPower (Opens.grothendieckTopology X.carrier)
          (Osharp := X.sheaf) F (k + 1)) := ih
    exact AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent X F
      (_root_.SheafOfModules.tensorPower (Opens.grothendieckTopology X.carrier)
        (Osharp := X.sheaf) F (k + 1))

/-- **Each tensor power of positive degree of a coherent sheaf of modules on a ringed space is
coherent.** This is clause (4) of [Stacks, Tag 01CK] for the tensor powers. -/
@[stacks 01CK "tensor powers of a coherent module, in positive degree"]
theorem isCoherent_tensorPower [_root_.SheafOfModules.IsCoherent F]
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) F) (n : ℕ) (hn : 0 < n) :
    _root_.SheafOfModules.IsCoherent (A.tensor.piece (n : ℤ)) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  have h : IsCoherent
      (_root_.SheafOfModules.tensorPower (Opens.grothendieckTopology X.carrier)
        (Osharp := X.sheaf) F (m + 1)) :=
    (TensorOver.isCoherent_iff _).1 (isCoherent_tensorPower_succ F m)
  exact (TensorOver.isCoherent_iff _).2
    ((coherentModules (structureSheafRing X)).prop_of_iso
      (A.tensorPieceIso (m + 1)).symm h)

end Stacks.SheafOfModules

end
