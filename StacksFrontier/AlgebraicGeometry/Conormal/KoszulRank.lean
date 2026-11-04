module

public import StacksFrontier.AlgebraicGeometry.Conormal.Stalk
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.ShortExact
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Germ
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Regular
public import StacksFrontier.RingTheory.Koszul.Quasiregular
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.CotangentRank

/-!
# The length of a Koszul-regular presentation is the rank of the conormal sheaf

Let `j : Z ⟶ X` be an immersion of schemes whose conormal sheaf is finite locally free of rank
`r`. If the defining ideal sheaf of `j` in its coborder neighbourhood is generated, on an open
containing the image of a point `z`, by a sequence of `c` sections whose Koszul complex is acyclic
in positive degrees, then `c = r`: at `z` the germs form a quasi-regular sequence generating the
kernel `I` of `𝒪_{X,z} ⟶ 𝒪_{Z,z}`, so `I/I²` is free of rank `c`, and `I/I²` is the stalk of the
conormal sheaf.

## Main results

* `Stacks.Conormal.eq_rank_of_isKoszulSequenceExactOn`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}} (j : Z ⟶ X) [IsImmersion j]

/-- **The length of a Koszul-regular generating sequence of the defining ideal sheaf of an
immersion is the rank of its conormal sheaf.** -/
theorem eq_rank_of_isKoszulSequenceExactOn (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := Z.ringCatSheaf)
      (conormalSheaf j) r]
    (z : Z) (U : (j.coborderRange.toScheme).Opens) (hzU : j.liftCoborder.base z ∈ U) {c : ℕ}
    (f : Fin c → (j.coborderRange.toScheme).presheaf.obj (op U))
    (hK : IsKoszulSequenceExactOn j.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace U f
      (fun k => 0 < k))
    (hG : IsGeneratedByOn j.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace
      (definingIdealOfHom j.liftCoborder) U f) : c = r := by
  have hspan : RingHom.ker (j.liftCoborder.stalkMap z).hom = Ideal.span (Set.range
      (germFamily j.coborderRange.toScheme.toLocallyRingedSpace.toRingedSpace U f _ hzU)) :=
    (stalkIdeal_definingIdealOfHom_eq_ker j.liftCoborder z).symm.trans
      (stalkIdeal_eq_Jid_germFamily (definingIdealOfHom j.liftCoborder) U f hG _ hzU)
  have hqr := Koszul.isQuasiRegular_of_isH1RegularOn ((Koszul.isH1RegularOn_self_iff _).mpr
    ((isKoszulSequenceExactOn_iff_forall_germ_isKoszulRegular _ U f).mp hK _ hzU).isH1Regular)
  obtain ⟨e₂⟩ := AlgebraicGeometry.SheafOfModules.nonempty_stalkLinearEquiv_fin
    (conormalSheaf j) r z
  let := stalkMapAlgebra j z
  let := cotangentStalkModule j z
  let := conormalSheafStalkModule j z
  exact Stacks.RingTheory.QuasiRegular.eq_of_basis_cotangent_ker _
    (j.liftCoborder.stalkMap_surjective z) _ hspan hqr
    (Module.Basis.ofRepr ((conormalSheafStalkEquivCotangent j z).symm.trans e₂))

end Stacks.Conormal
