module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesTensorQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalConeOfImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleQuasicoherentClosure

/-!
# The symmetric algebra of a quasi-coherent module on an algebraic space

Let `W` be an algebraic space and `ℱ` an `𝒪_W`-module on its small étale site, with symmetric
algebra `Sym(ℱ)` (`AlgebraicGeometry.Space.symmetricAlgebra`).  When `ℱ` is quasi-coherent every
piece `Symⁿ(ℱ)` is quasi-coherent, which is the input that
`StacksFrontier/AlgebraicGeometry/Spaces/SymmetricAlgebraSheafQuasicoherence.lean` records as owed:
it is the cokernel of the sheafified slot-wise relator map `⊕_{p < n - 1} Tⁿ(ℱ) ⟶ Tⁿ(ℱ)`, whose
source and target are quasi-coherent because tensor products and finite direct sums of
quasi-coherent modules are.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_tensorPower`: the tensor powers of a
  quasi-coherent module are quasi-coherent.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_symmetricAlgebra_piece_natCast` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_symmetricAlgebra_piece_of_isQuasicoherentOnSite`:
  every piece of the symmetric algebra of a quasi-coherent module is quasi-coherent.

## References

* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)


variable (W : AlgebraicSpaces B S hS) (F : SheafOfModules.{u} (structureRingSheaf B S hS W))

/-- Quasi-coherence of a module over the structure sheaf of an algebraic space, read with the
topology of its small étale site, is quasi-coherence of the same module read as an `𝒪_W`-module on
the small étale ringed site; the two topologies are the same by definition. -/
theorem isQuasicoherentOnSite_modules_iff (M : SheafOfModules.{u} (structureRingSheaf B S hS W)) :
    M.IsQuasicoherentOnSite ↔ (M : Modules.{u, u} B S hS W.1 W.2).IsQuasicoherentOnSite :=
  Iff.rfl

/-- **The tensor powers of a quasi-coherent module on an algebraic space are quasi-coherent.** -/
theorem isQuasicoherentOnSite_tensorPower (hF : F.IsQuasicoherentOnSite) (n : ℕ) :
    (SheafOfModules.tensorPower (SmallEtale.topology B S hS W.1)
      (Osharp := (smallEtaleRingedSite B S hS W.1 W.2).O) F n).IsQuasicoherentOnSite := by
  obtain _ | n := n
  · exact SheafOfModules.isQuasicoherentOnSite_unit _
  induction n with
  | zero => exact hF
  | succ n ih =>
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      (modulesTensorObjIso B S hS W.1 W.2 F
        (SheafOfModules.tensorPower (SmallEtale.topology B S hS W.1)
          (Osharp := (smallEtaleRingedSite B S hS W.1 W.2).O) F (n + 1)))
      (@isQuasicoherentOnSite_tensorObj B S hS W.1 W.2 F
        (SheafOfModules.tensorPower (SmallEtale.topology B S hS W.1)
          (Osharp := (smallEtaleRingedSite B S hS W.1 W.2).O) F (n + 1)) hF ih)

/-- A finite direct sum of quasi-coherent `𝒪_W`-modules is quasi-coherent, whichever choice of
coproduct is used. -/
theorem isQuasicoherentOnSite_sigma {ι : Type} [Finite ι] (M : ι → Modules.{u, u} B S hS W.1 W.2)
    (h : ∀ i, (M i).IsQuasicoherentOnSite) (inst : HasCoproduct M) :
    (@sigmaObj _ _ _ M inst).IsQuasicoherentOnSite :=
  let : Abelian (Modules.{u, u} B S hS W.1 W.2) :=
    @SheafOfModules.instAbelian _ _ _ _ (smallEtaleRingedSite_hasSheafify B S hS W.1 W.2)
      (smallEtaleRingedSite_wEqualsLocallyBijective B S hS W.1 W.2)
  have : HasZeroObject (Modules.{u, u} B S hS W.1 W.2) := Abelian.hasZeroObject
  have : HasFiniteCoproducts (Modules.{u, u} B S hS W.1 W.2) :=
    Limits.hasFiniteCoproducts_of_hasFiniteBiproducts _
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((coproductIsCoproduct M).coconePointUniqueUpToIso (@coproductIsCoproduct _ _ _ M inst))
    (ObjectProperty.prop_coproduct (SheafOfModules.isQuasicoherentOnSite _) h)

/-- **Every piece of the symmetric algebra of a quasi-coherent module on an algebraic space is
quasi-coherent**, in non-negative degrees: the piece of degree `n` is the cokernel of the
sheafified slot-wise relator map `⊕_{p < n - 1} Tⁿ(ℱ) ⟶ Tⁿ(ℱ)`
(`SheafOfModules.symmetricPowerCokernelIso`). -/
theorem isQuasicoherentOnSite_symmetricAlgebra_piece_natCast (hF : F.IsQuasicoherentOnSite)
    (k : ℕ) : ((symmetricAlgebra B S hS W F).piece (k : ℤ)).IsQuasicoherentOnSite := by
  let J := SmallEtale.topology B S hS W.1
  let A := SheafOfModules.sheafifiedAlgebras J
    (Osharp := (smallEtaleRingedSite B S hS W.1 W.2).O) F
  have hT := SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((A.tensorPieceIso k).symm ≪≫ SheafOfModules.tensorPieceSheafifyIso J A k)
    (isQuasicoherentOnSite_tensorPower B S hS W F hF k)
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((SheafOfModules.symmetricPowerCokernelIso J F A k).symm ≪≫
      ((isSymmetricAlgebra_symmetricAlgebra B S hS W F).pieceIso
        A.symmetric_isSymmetricAlgebra k).symm)
    (@isQuasicoherentOnSite_cokernel_unconditional B S hS W.1 W.2 _ _
      (SheafOfModules.IsQuasicoherentOnSite.of_iso (SheafOfModules.sheafifyRelSourceIso J F k).symm
        (isQuasicoherentOnSite_sigma B S hS W _ (fun _ => hT) _)) hT _)

/-- **Every piece of the symmetric algebra of a quasi-coherent module on an algebraic space is
quasi-coherent**, in every integer degree; the negative pieces vanish. -/
theorem isQuasicoherentOnSite_symmetricAlgebra_piece_of_isQuasicoherentOnSite
    (hF : F.IsQuasicoherentOnSite) (n : ℤ) :
    ((symmetricAlgebra B S hS W F).piece n).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_symmetricAlgebra_piece B S hS W F
    (isQuasicoherentOnSite_symmetricAlgebra_piece_natCast B S hS W F hF) n

end AlgebraicGeometry.Space

end
