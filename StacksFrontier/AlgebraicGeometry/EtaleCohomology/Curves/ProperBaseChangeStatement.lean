module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.TorsionSheafSituation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Proper

/-!
# Statement (7) of Situation 0A52: base change to an extension of algebraically closed fields

Situation 0A52 fixes an algebraically closed field `k`, a separated finite-type scheme `X` of
dimension at most one over `k` and a torsion abelian sheaf `F` on the small étale site of `X`.
Statement (7) of that situation is

> `H^q_ét(X, F) → H^q_ét(X_{k'}, F|_{X_{k'}})` is an isomorphism for any extension `k'/k` of
> algebraically closed fields if `X` is proper.

This file states that condition for a term of `Stacks.EtaleCohomology.TorsionSheafSituation` and
identifies it with `Stacks.EtaleCohomology.ProperBaseChangeOverAlgClosed`.

## Main definitions

* `Stacks.EtaleCohomology.TorsionSheafSituation.ProperBaseChangeStatement` is statement (7) for
  one situation: if the structure morphism is proper then, for every extension of the base field
  by an algebraically closed field, restriction along the projection of the scalar extension is
  bijective on étale cohomology in every degree.

## Main results

* `TorsionSheafSituation.properBaseChangeStatement_of_properBaseChangeOverAlgClosed`: proper base
  change over algebraically closed fields gives statement (7) for every situation.
* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_scalarExtensionFst_of_forall`:
  conversely, statement (7) for every situation gives bijectivity of the restriction map for
  every proper scheme of dimension at most one over an algebraically closed field.

## References

* [Stacks Project, Tag 0A59](https://stacks.math.columbia.edu/tag/0A59)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 0A5E](https://stacks.math.columbia.edu/tag/0A5E)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Stacks.EtaleCohomology

universe u v w

/-- Statement (7) of Situation 0A52. For an algebraically closed field `k`, a separated
finite-type scheme `X` of dimension at most one over `k` and a torsion abelian sheaf `F` on the
small étale site of `X`: if the structure morphism of `X` is proper then
`H^q_étale(X, F) → H^q_étale(X_{k'}, F|_{X_{k'}})` is an isomorphism in every degree, for every
extension `k'/k` of algebraically closed fields. -/
@[stacks 0A59 "item (7) of Situation 0A52, as a predicate on the situation"]
def TorsionSheafSituation.ProperBaseChangeStatement (S : TorsionSheafSituation.{u, v}) : Prop :=
  IsProper S.structureMorphism →
    ∀ (k' : Type u) [Field k'] [Algebra S.k k'] [IsAlgClosed k']
      [HasExt.{w} (Sheaf S.X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
      [HasExt.{w} (Sheaf (scalarExtension S.k k' S.structureMorphism).smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v})] (q : ℕ),
      Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w}
        (scalarExtensionFst S.k k' S.structureMorphism) S.F q)

/-- Proper base change over algebraically closed fields gives statement (7) of Situation 0A52
for every situation. -/
theorem TorsionSheafSituation.properBaseChangeStatement_of_properBaseChangeOverAlgClosed
    (habc : ProperBaseChangeOverAlgClosed.{u, v}) (S : TorsionSheafSituation.{u, v}) :
    S.ProperBaseChangeStatement.{u, v, w} := fun _ k' _ _ _ _ _ q ↦
  (etaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt.{u, v, w}
      (scalarExtensionFst S.k k' S.structureMorphism) S.F q).mpr
    (habc S.k k' S.structureMorphism S.dimension_le_one S.F S.isTorsion q)

/-- Conversely, statement (7) of Situation 0A52 for every situation gives bijectivity of the
restriction map to a scalar extension for every proper scheme of dimension at most one over an
algebraically closed field and every torsion abelian sheaf on it. -/
theorem bijective_etaleCohomologyRestrictionMap_scalarExtensionFst_of_forall
    (h : ∀ S : TorsionSheafSituation.{u, v}, S.ProperBaseChangeStatement.{u, v, w})
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsAlgClosed k] [IsAlgClosed k']
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf (scalarExtension k k' f).smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty.{max (u + 1) v} X.smallEtaleTopology F) (q : ℕ) :
    Function.Bijective
      (etaleCohomologyRestrictionMap.{u, v, w} (scalarExtensionFst k k' f) F q) :=
  h { k := k, X := X, structureMorphism := f, dimension_le_one := hdim, F := F, isTorsion := hF }
    inferInstance k' q

end Stacks.EtaleCohomology

end
