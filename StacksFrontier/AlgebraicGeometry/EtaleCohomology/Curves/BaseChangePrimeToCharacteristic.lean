module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.TorsionSheafSituation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleLocallyBijective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.TorsionExponent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.PrimeToCharacteristicFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension

/-!
# Statement (6) of Situation 0A52: prime-to-characteristic base change on a curve

Situation 0A52 fixes an algebraically closed field `k`, a separated scheme `X` of finite type and
of dimension at most one over `k`, and a torsion abelian sheaf `F` on the small étale site of `X`;
it is `Stacks.EtaleCohomology.TorsionSheafSituation`. Statement (6) of that situation reads:

> `H^q_étale(X, F) → H^q_étale(X_{k'}, F|_{X_{k'}})` is an isomorphism for any extension `k'/k`
> of algebraically closed fields if `F` is torsion prime to `char(k)`.

## Main definitions

* `Stacks.EtaleCohomology.TorsionSheafSituation.BaseChangePrimeToCharacteristic` is statement
  (6) for a situation: if the situation's sheaf is torsion prime to the characteristic then
  restriction to `X_{k'}` is bijective on étale cohomology in every degree, for every
  algebraically closed extension `k'` of the ground field.

## Main results

* `Stacks.EtaleCohomology.TorsionSheafSituation.baseChangePrimeToCharacteristic_of_forall`:
  bijectivity of the restriction maps, without the torsion side condition, gives statement (6).
* `Stacks.EtaleCohomology.TorsionSheafSituation`'s
  `baseChangePrimeToCharacteristic_iff_of_ringExpChar_eq_one`: when the exponential characteristic
  is `1`, statement (6) is equivalent to its unconditional conclusion.

## References

* [Stacks Project, Tag 0A58](https://stacks.math.columbia.edu/tag/0A58)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

/-- Statement (6) of the list of statements of Situation 0A52: if the torsion of the situation's
abelian sheaf `F` is prime to the characteristic of the algebraically closed ground field `k`,
then for every algebraically closed extension `k'/k` and every degree `q` the restriction map
`H^q_étale(X, F) → H^q_étale(X_{k'}, F|_{X_{k'}})` is bijective.

"Torsion prime to the characteristic" is taken at the exponential characteristic, so that in
characteristic zero it is the torsion condition the situation already carries. -/
@[stacks 0A58 "statement (6) of Situation 0A52, as a predicate on the situation"]
def TorsionSheafSituation.BaseChangePrimeToCharacteristic
    (S : TorsionSheafSituation.{u, v}) : Prop :=
  Stacks.Torsion.IsPrimeToCharacteristicTorsion S.X.smallEtaleTopology (ringExpChar S.k) S.F →
    ∀ (k' : Type u) [Field k'] [Algebra S.k k'] [IsAlgClosed k']
      [HasExt.{w} (Sheaf S.X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
      [HasExt.{w} (Sheaf (scalarExtension S.k k' S.structureMorphism).smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v})] (q : ℕ),
      Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w}
        (scalarExtensionFst S.k k' S.structureMorphism) S.F q)

/-- Statement (6) follows from its conclusion alone. -/
theorem TorsionSheafSituation.baseChangePrimeToCharacteristic_of_forall
    {S : TorsionSheafSituation.{u, v}}
    (h : ∀ (k' : Type u) [Field k'] [Algebra S.k k'] [IsAlgClosed k']
      [HasExt.{w} (Sheaf S.X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
      [HasExt.{w} (Sheaf (scalarExtension S.k k' S.structureMorphism).smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v})] (q : ℕ),
      Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w}
        (scalarExtensionFst S.k k' S.structureMorphism) S.F q)) :
    S.BaseChangePrimeToCharacteristic.{u, v, w} :=
  fun _ ↦ h

/-- When the exponential characteristic of the ground field is `1`, which is to say in
characteristic zero, the side condition of statement (6) is automatic, so statement (6) is exactly
its unconditional conclusion. -/
theorem TorsionSheafSituation.baseChangePrimeToCharacteristic_iff_of_ringExpChar_eq_one
    {S : TorsionSheafSituation.{u, v}} (hchar : ringExpChar S.k = 1) :
    S.BaseChangePrimeToCharacteristic.{u, v, w} ↔
      ∀ (k' : Type u) [Field k'] [Algebra S.k k'] [IsAlgClosed k']
        [HasExt.{w} (Sheaf S.X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
        [HasExt.{w} (Sheaf (scalarExtension S.k k' S.structureMorphism).smallEtaleTopology
          AddCommGrpCat.{max (u + 1) v})] (q : ℕ),
        Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w}
          (scalarExtensionFst S.k k' S.structureMorphism) S.F q) :=
  ⟨fun h ↦ h (S.isPrimeToCharacteristicTorsion_of_ringExpChar_eq_one hchar),
    TorsionSheafSituation.baseChangePrimeToCharacteristic_of_forall⟩

end Stacks.EtaleCohomology

end
