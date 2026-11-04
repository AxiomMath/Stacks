module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionOfConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstantCharacteristicCurveStatements
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsAllUniverses
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtensionConstantSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lemma 0A5B: statements (1) -- (8) of Situation 0A52 for `𝐙/ℓ𝐙` on a smooth `X`

Let `k` be an algebraically closed field, `X` a smooth separated scheme of finite type and
dimension at most one over `k`, `ℓ` a prime and `F = 𝐙/ℓ𝐙` the constant sheaf on `X_étale`.
Lemma 0A5B of the source says that statements (1) -- (8) of Situation 0A52 hold for `F`.

The source's proof reduces to `X` a smooth curve and splits into two cases:

* **Case I**, `ℓ` invertible in `k`: the Kummer sequence and the Picard group of the smooth
  projective model (Tags 03RQ and 03RR), with invariance of the genus and of the number of
  punctures under extension of the algebraically closed ground field. In the library this is
  `Stacks.EtaleCohomology.curveStatementsConstantOnSmoothCurves_of_isUnit`.
* **Case II**, `ℓ = char(k)`: the Artin–Schreier sequence (Tags 0A3N and 0A3P), which is
  `Stacks.EtaleCohomology.curveStatementsConstantOnSmoothCurves_of_charP`.

## Main results

* `Stacks.EtaleCohomology.curveStatementsConstantOnSmoothCurves_of_prime`: the two cases
  combined, in the form `CurveStatementsConstantOnSmoothCurves k E` for every abelian group `E`
  cyclic of prime order. This is exactly the hypothesis `hbase` of the reductions of Lemmas
  03SG, 0A3Q and 03SD (for instance
  `Stacks.EtaleCohomology.curveStatements_extensionByZero_constantSheaf_of_smooth`), which it
  discharges.
* `Stacks.EtaleCohomology.curveStatements_constantSheaf_of_smooth`: **Lemma 0A5B**, in
  Situation 0A52 with `X` smooth, at every coefficient universe and every `Ext` universe.

## Implementation notes

**From curves to smooth `X`.** A smooth `X` of dimension at most one is a finite disjoint union of
smooth curves and points, and on a point every sheaf satisfies the statements. The passage from
the curve components to `X`, and from the coefficients `AddCommGrpCat.{u + 1}` at which the curve
case is proved to `AddCommGrpCat.{max (u + 1) v}`, is done by the reduction theorem
`Stacks.EtaleCohomology.curveStatements_of_torsionSheafProperty_max`, which takes as its only
geometric input the curve case for `𝐙/ℓ𝐙` at every prime `ℓ`, supplied here by
`curveStatementsConstantOnSmoothCurves_of_prime`. That reduction applies to every torsion sheaf on
every `X` of Situation 0A52, so the smoothness of `X` is not used past the curve case; the
statement keeps it because the source does.

**The coefficients.** The constant sheaf is taken with value any abelian group `E` cyclic of order
`ℓ` (`Nonempty (E ≃+ ZMod ℓ)`), the form in which the reductions of 03SG and its successors
quantify over it; `ULift (ZMod ℓ)` is one such group.

## References

* [Stacks Project, Tag 0A5B](https://stacks.math.columbia.edu/tag/0A5B)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 03SG](https://stacks.math.columbia.edu/tag/03SG)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe w v u

namespace Stacks.EtaleCohomology

/-- **Lemma 0A5B on smooth curves, both cases.** For an algebraically closed field `k`, a prime
`ℓ` and an abelian group `E` cyclic of order `ℓ`, statements (1) -- (8) of Situation 0A52 hold for
the constant sheaf `E` on every smooth curve over `k`. If `ℓ` is invertible in `k` this is Case I
of the source (Kummer theory, `curveStatementsConstantOnSmoothCurves_of_isUnit`); otherwise `ℓ` is
the characteristic of `k` and it is Case II (Artin–Schreier theory,
`curveStatementsConstantOnSmoothCurves_of_charP`).

This is the hypothesis `CurveStatementsConstantOnSmoothCurves k E` of the reductions of Lemmas
03SG, 0A3Q and 03SD. -/
@[sga "4½ Arcata 4.4" "special case"]
theorem curveStatementsConstantOnSmoothCurves_of_prime (k : Type u) [Field k] [IsAlgClosed k]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (E : AddCommGrpCat.{u + 1}) (hE : Nonempty (E ≃+ ZMod ℓ)) :
    CurveStatementsConstantOnSmoothCurves k E := by
  by_cases h : IsUnit (ℓ : k)
  · exact curveStatementsConstantOnSmoothCurves_of_isUnit k h E hE
  · have h0 : (ℓ : k) = 0 := by simpa [isUnit_iff_ne_zero] using h
    have : CharP k ℓ := (CharP.charP_iff_prime_eq_zero hℓ).2 h0
    exact curveStatementsConstantOnSmoothCurves_of_charP hℓ E hE

/-- **Stacks Project, Lemma 0A5B.** In Situation 0A52 — `k` algebraically closed, `X` separated,
of finite type and of dimension at most one over `k` — assume `X` is smooth over `k` and let
`F = 𝐙/ℓ𝐙` be the constant sheaf on `X_étale` for a prime `ℓ`, with value any abelian group `E`
cyclic of order `ℓ`. Then statements (1) -- (8) of Situation 0A52 hold for `F`, in the sense of
`Stacks.EtaleCohomology.CurveStatements`, at every coefficient universe and every `Ext`
universe.

On the smooth curve components of `X` this is `curveStatementsConstantOnSmoothCurves_of_prime`
(Cases I and II of the source); the reduction theorem
`curveStatements_of_torsionSheafProperty_max` carries it to `X` and to the coefficients
`AddCommGrpCat.{max (u + 1) v}`, the constant sheaf with finite value being torsion. -/
@[stacks 0A5B]
theorem curveStatements_constantSheaf_of_smooth {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsSeparated π] [LocallyOfFiniteType π]
    [QuasiCompact π] [Smooth π] (hdim : topologicalKrullDim X ≤ 1) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (E : AddCommGrpCat.{max (u + 1) v}) (hE : Nonempty (E ≃+ ZMod ℓ))
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    CurveStatements.{u, v, w} π
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E) := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : Finite E := by obtain ⟨e⟩ := hE; exact Finite.of_equiv _ e.toEquiv.symm
  exact curveStatements_of_torsionSheafProperty_max π hdim
    (fun p hp ↦ curveStatementsConstantOnSmoothCurves_of_prime k hp _ ⟨AddEquiv.ulift⟩) _
    (Stacks.Torsion.torsionSheafProperty_constantSheaf _ E)

end Stacks.EtaleCohomology

end
