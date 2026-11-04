module

public import
 StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ReducedExtensionByZeroStatements
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Lemma 03SG: statements (1) -- (8) of Situation 0A52 for `j_! 𝐙/ℓ𝐙` on a smooth `X`

Let `k` be an algebraically closed field, `X` a smooth separated scheme of finite type and
dimension at most one over `k`, `j : U ⟶ X` an open immersion, `ℓ` a prime and
`F = j_! 𝐙/ℓ𝐙`. Lemma 03SG of the source says that statements (1) -- (8) of Situation 0A52 hold
for `F`.

## Main results

* `Stacks.EtaleCohomology.curveStatements_extensionByZero_zmod_of_smooth`: **Lemma 03SG**, at
  every coefficient universe and every `Ext` universe.

## Implementation notes

The source's proof writes `X` as a finite disjoint union of smooth curves and points; on a curve
`U` is empty or dense, and Lemmas 0A5B and 0GJA apply. That argument is in the library as
`Stacks.EtaleCohomology.curveStatements_extensionByZero_constantSheaf_of_smooth`, stated at the
coefficients `AddCommGrpCat.{u + 1}` with `Ext` in universe `u + 1`.

Here the statement is proved at every coefficient universe `max (u + 1) v` and every `Ext`
universe `w`. A smooth scheme over a field is reduced
(`AlgebraicGeometry.isReduced_of_smooth_of_isAffine`), so Lemma 0A3Q
(`Stacks.EtaleCohomology.curveStatements_extensionByZero_constantSheaf_of_prime`) applies: there
`j_! 𝐙/ℓ𝐙` is killed by `ℓ`, hence torsion, and the reduction theorem
`Stacks.EtaleCohomology.curveStatements_of_torsionSheafProperty_max` gives the eight statements
from Lemma 0A5B for `𝐙/ℓ𝐙` on smooth curves
(`Stacks.EtaleCohomology.curveStatementsConstantOnSmoothCurves_of_prime`).

The constant sheaf is taken with value any abelian group `E` cyclic of order `ℓ`
(`Nonempty (E ≃+ ZMod ℓ)`), as in Lemmas 0A5B and 0A3Q; `ULift (ZMod ℓ)` is one such group.

## References

* [Stacks Project, Tag 03SG](https://stacks.math.columbia.edu/tag/03SG)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 0A5B](https://stacks.math.columbia.edu/tag/0A5B)
* [Stacks Project, Tag 0A3Q](https://stacks.math.columbia.edu/tag/0A3Q)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe w v u

namespace Stacks.EtaleCohomology

/-- **Stacks Project, Lemma 03SG.** In Situation 0A52 — `k` algebraically closed, `X` separated,
of finite type and of dimension at most one over `k` — assume `X` is smooth over `k`. Let
`j : U ⟶ X` be an open immersion, `ℓ` a prime and `F = j_! 𝐙/ℓ𝐙` the extension by zero of the
constant sheaf on `U_étale` with value an abelian group `E` cyclic of order `ℓ`. Then statements
(1) -- (8) of Situation 0A52 hold for `F`, in the sense of
`Stacks.EtaleCohomology.CurveStatements`, at every coefficient universe and every `Ext`
universe.

A smooth `X` over a field is reduced, so this is Lemma 0A3Q,
`curveStatements_extensionByZero_constantSheaf_of_prime`. -/
@[stacks 03SG]
theorem curveStatements_extensionByZero_zmod_of_smooth {k : Type u} [Field k] [IsAlgClosed k]
    {X U : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsSeparated π] [LocallyOfFiniteType π]
    [QuasiCompact π] [Smooth π] (hdim : topologicalKrullDim X ≤ 1) (j : U ⟶ X)
    [IsOpenImmersion j] {ℓ : ℕ} (hℓ : ℓ.Prime) (E : AddCommGrpCat.{max (u + 1) v})
    (hE : Nonempty (E ≃+ ZMod ℓ))
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    CurveStatements.{u, v, w} π ((extensionByZero.{u, v} j).obj
      ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj E)) :=
  have : IsReduced X := isReduced_of_smooth_of_isAffine π
  curveStatements_extensionByZero_constantSheaf_of_prime π hdim j hℓ E hE

end Stacks.EtaleCohomology

end
