module

public import
 StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ReducedExtensionByZeroStatements
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lemma 03SD: statements (1) -- (8) for `j_! G`, `G` finite locally constant over `F_ℓ`

Lemma 03SD of the source: in Situation 0A52 assume `X` is reduced. Let `j : U ⟶ X` be an open
immersion with `U` connected, `ℓ` a prime and `G` a finite locally constant sheaf of
`F_ℓ`-vector spaces on `U_étale`. Then statements (1) -- (8) of Situation 0A52 hold for
`F = j_! G`.

## Main results

* `Stacks.EtaleCohomology.curveStatements_extensionByZero_forget₂_of_isFiniteLocallyConstant`:
  **Lemma 03SD**, at every coefficient universe and every `Ext` universe.

## Implementation notes

**The proof.** The source's proof (a finite étale cover of degree prime to `ℓ` trivializing `G`
up to a filtration, Lemma 0A3R, then the trace, Zariski's Main Theorem and Lemma 0A5D) is in the
library as `Stacks.EtaleCohomology.curveStatements_extensionByZero_of_isFiniteLocallyConstant`,
which takes Lemma 0A5B on smooth curves as its hypothesis `hbase` and is stated at the
coefficients `AddCommGrpCat.{u + 1}`. Here the statement is proved at every coefficient universe
`max (u + 1) v` and every `Ext` universe `w`, as Lemmas 0A5B and 0A3Q are: the abelian sheaf
underlying `G` is killed by `ℓ`, and so is `j_! G`, hence it is a torsion sheaf
(`Stacks.Torsion.torsionSheafProperty_of_nsmul_id_eq_zero`), and the reduction theorem
`Stacks.EtaleCohomology.curveStatements_of_torsionSheafProperty_max` gives the eight statements
for every torsion sheaf, its only input being Lemma 0A5B for `𝐙/ℓ𝐙` on smooth curves,
`Stacks.EtaleCohomology.curveStatementsConstantOnSmoothCurves_of_prime`. The reducedness of `X`,
the connectedness of `U` and the finiteness and local constancy of `G` are therefore not used;
the statement keeps them because the source does.

## References

* [Stacks Project, Tag 03SD](https://stacks.math.columbia.edu/tag/03SD)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe w v u

namespace Stacks.EtaleCohomology

/-- **Stacks Project, Lemma 03SD.** In Situation 0A52 — `k` algebraically closed, `X` separated,
of finite type and of dimension at most one over `k` — assume `X` is reduced. Let `j : U ⟶ X` be
an open immersion with `U` connected, `ℓ` a prime and `G` a finite locally constant sheaf of
`F_ℓ`-vector spaces (`ZMod ℓ`-modules) on `U_étale`. Then statements (1) -- (8) of Situation
0A52 (`Stacks.EtaleCohomology.CurveStatements`) hold for the abelian sheaf `F = j_! G`, at every
coefficient universe and every `Ext` universe.

`j_! G` is killed by `ℓ`, hence torsion, so this is the reduction theorem
`curveStatements_of_torsionSheafProperty_max` applied with Lemma 0A5B on smooth curves
(`curveStatementsConstantOnSmoothCurves_of_prime`). The hypotheses that `X` is reduced, that `U`
is connected and that `G` is finite locally constant are those of the source; the proof does not
use them. -/
@[stacks 03SD, sga "4 XVI 5.2" "partial"]
theorem curveStatements_extensionByZero_forget₂_of_isFiniteLocallyConstant {k : Type u}
    [Field k] [IsAlgClosed k] {X U : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsSeparated π]
    [LocallyOfFiniteType π] [QuasiCompact π] [IsReduced X] (hdim : topologicalKrullDim X ≤ 1)
    (j : U ⟶ X) [IsOpenImmersion j] [ConnectedSpace U] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{max (u + 1) v} (ZMod ℓ)))
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant U.smallEtaleTopology G]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    CurveStatements.{u, v, w} π ((extensionByZero.{u, v} j).obj
      ((sheafCompose U.smallEtaleTopology
        (forget₂ (ModuleCat.{max (u + 1) v} (ZMod ℓ)) AddCommGrpCat.{max (u + 1) v})).obj G)) := by
  have hG : ℓ • 𝟙 G = 0 := by
    ext V x
    show (ℓ : ℕ) • x = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), ZMod.natCast_self, zero_smul]
  exact curveStatements_of_torsionSheafProperty_max π hdim
    (fun p hp ↦ curveStatementsConstantOnSmoothCurves_of_prime k hp _ ⟨AddEquiv.ulift⟩) _
    (Stacks.Torsion.torsionSheafProperty_of_nsmul_id_eq_zero hℓ.pos
      (nsmul_id_eq_zero_map (extensionByZero.{u, v} j) (nsmul_id_eq_zero_map
        (sheafCompose U.smallEtaleTopology
          (forget₂ (ModuleCat.{max (u + 1) v} (ZMod ℓ)) AddCommGrpCat.{max (u + 1) v})) hG)))

end Stacks.EtaleCohomology

end
