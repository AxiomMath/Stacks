module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DerivedPushforwardStalkStrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ProperBaseChangeStatement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveCohomologyTheorem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeFromAlgClosed
import StacksCore.Tactic.StacksAttribute

/-!
# The proper base change theorem (Tags 0A5E, 095T, 095U), unconditionally

Statement (7) of Situation 0A52 (Tag 0A59) holds for every torsion sheaf on a proper scheme of
dimension at most one over an algebraically closed field. This is
`Stacks.EtaleCohomology.TorsionSheafSituation.properBaseChangeStatement`. It is the input
`ProperBaseChangeOverAlgClosed` that the reduction of Tag 0A5E to algebraically closed fields
(`Stacks.EtaleCohomology.etaleCohomologyBaseChangeMap_bijective_of_isSepClosed_of`) takes.
Statement (1) (Tag 0A53) gives the vanishing above degree two that the curve case of Tag 095U
consumes.

## Main results

* `Stacks.EtaleCohomology.properBaseChangeOverAlgClosed`: `ProperBaseChangeOverAlgClosed`, from
  Tag 0A59.
* `Stacks.EtaleCohomology.etaleCohomologyBaseChangeMap_bijective_of_isSepClosed`: **Tag 0A5E.**
* `Stacks.EtaleCohomology.subsingleton_sheafH_of_isProper_of_topologicalKrullDim_le_one`:
  `H^q(X, F) = 0` for `q > 2`, for every torsion sheaf on a proper scheme of dimension at most
  one over an algebraically closed field (Tag 0A53).
* `Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isProper`: **Tag 095T**,
  the proper base change theorem (also as `cohomologyCommutesWithBaseChange_of_isProper`).
* `Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_isProper`: **Tag 095U**
  (also as the statement `properDirectImageVanishingStatement`).

## References

* [Stacks Project, Tag 0A5E](https://stacks.math.columbia.edu/tag/0A5E)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **Statement (7) of Situation 0A52 in the `Ext` form `ProperBaseChangeOverAlgClosed`.** For
`k ⊆ k'` algebraically closed, `X` proper over `k` of dimension at most one and `F` a torsion
abelian sheaf on `X_étale`, restriction to `X_{k'}` is bijective on `Ext^q(ℤ, -)`, in every
degree. This is Tag 0A59 (`TorsionSheafSituation.properBaseChangeStatement`), read through
`bijective_etaleCohomologyRestrictionMap_scalarExtensionFst_of_forall` at the standard `Ext`
universe and transported by `properBaseChangeOverAlgClosed_iff`. -/
@[sga "4 XII 5.2" "special case"]
theorem properBaseChangeOverAlgClosed : ProperBaseChangeOverAlgClosed.{u, v} := by
  intro k k' _ _ _ _ _ X f _ hdim F hF q
  let := HasExt.standard (Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v})
  let := HasExt.standard (Sheaf (smallEtaleTopology (scalarExtension k k' f))
    AddCommGrpCat.{max (u + 1) v})
  exact (properBaseChangeOverAlgClosed_iff k k' f F q).2
    (bijective_etaleCohomologyRestrictionMap_scalarExtensionFst_of_forall
      (fun S ↦ S.properBaseChangeStatement) k k' f hdim F hF q)

/-- **Stacks Project, Tag 0A5E.** Let `k ⊆ k'` be an extension of separably closed fields, `X` a
proper scheme over `k` of dimension at most one, and `F` a torsion abelian sheaf on `X_étale`.
Then the base change map `H^q(X, F) ⟶ H^q(X_{k'}, F|_{X_{k'}})` is bijective for every `q`.

This is `etaleCohomologyBaseChangeMap_bijective_of_isSepClosed_of`, the reduction of the
separably closed case to the algebraically closed one through topological invariance of the
étale site, with its input `ProperBaseChangeOverAlgClosed` supplied by Tag 0A59
(`properBaseChangeOverAlgClosed`). -/
@[sga "4 XII 5.4" "special case",
  sga "4 XVI 1.6" "Abelian clause",
  sga "4 XVI 1.7" "(iii), special case",
  sga "4½ Arcata 5.3.3" "special case"]
theorem etaleCohomologyBaseChangeMap_bijective_of_isSepClosed
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsSepClosed k] [IsSepClosed k'] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    [HasExt.{w} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf (smallEtaleTopology (scalarExtension k k' f))
      AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty.{max (u + 1) v} (smallEtaleTopology X) F)
    (q : ℕ) :
    Function.Bijective
      (etaleCohomologyRestrictionMap.{u, v, w} (scalarExtensionFst k k' f) F q) :=
  etaleCohomologyBaseChangeMap_bijective_of_isSepClosed_of properBaseChangeOverAlgClosed
    k k' f hdim F hF q

/-- **Vanishing above degree two on curves (Tag 0A53).** For `X` proper over an algebraically
closed field with `dim X ≤ 1` and `G` a torsion abelian sheaf on `X_étale`, `H^q(X, G) = 0` for
every `q > 2`. `X` need not be smooth, reduced or irreducible. This is statement (1) of
Situation 0A52, `TorsionSheafSituation.isVanishingAboveDegreeTwo`, for the situation `(X, G)`,
with `Ext` computed in the Grothendieck abelian category of abelian sheaves. It is the curve
input `hcurve` of `properDirectImageVanishingStatement_of_algClosed` (Tag 095U). -/
@[sga "4½ Arcata 4.4" "H^q(X_0, special case"]
theorem subsingleton_sheafH_of_isProper_of_topologicalKrullDim_le_one
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    (π : X ⟶ Spec (.of k)) [IsProper π] (hdim : topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G) (q : ℕ) (hq : 2 * 1 < q) :
    letI := isGrothendieckAbelian_sheaf_smallEtale.{u, 0} X
    letI := IsGrothendieckAbelian.hasExt.{u + 1}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    Subsingleton (Sheaf.H.{u + 1} G q) := by
  let := isGrothendieckAbelian_sheaf_smallEtale.{u, 0} X
  let := IsGrothendieckAbelian.hasExt.{u + 1}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  let S : TorsionSheafSituation.{u, 0} :=
    { k := k, X := X, structureMorphism := π, dimension_le_one := hdim, F := G, isTorsion := hG }
  exact S.isVanishingAboveDegreeTwo q (by omega)

/-- **Proper base change, as `CohomologyCommutesWithBaseChange`.** Let `f : X ⟶ Y` be proper,
`g : Y' ⟶ Y` any morphism, `X' = Y' ×_Y X` with projections `g' : X' ⟶ X` and `f' : X' ⟶ Y'`,
and `F` an abelian torsion sheaf on `X_étale`. Then the base change map
`g⁻¹ Rf_* F ⟶ Rf'_* (g')⁻¹ F` is an isomorphism (`CohomologyCommutesWithBaseChange f`).

This is `cohomologyCommutesWithBaseChange_of_isProper_of_algClosed`. Its two inputs are
theorems: the stalks of `Rf_*` are the cohomology over the strict henselizations (Tag 03Q9,
`isIso_derivedPushforwardStalkToStrictHenselizationSections_single`), and the case of curves
over algebraically closed fields (Tag 0A59, through `properBaseChangeOverAlgClosed`). -/
theorem cohomologyCommutesWithBaseChange_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] : CohomologyCommutesWithBaseChange.{u, 0} f :=
  cohomologyCommutesWithBaseChange_of_isProper_of_algClosed
    (fun _ Y f _ _ s G ↦ isIso_derivedPushforwardStalkToStrictHenselizationSections_single
      (BigEtaleSite.containing Y) (BigEtaleSite.contains_containing Y) f s G)
    properBaseChangeOverAlgClosed f

/-- **Tag 095U, as the statement `ProperDirectImageVanishingStatement`.** Let `f : X ⟶ Y` be a
proper morphism of schemes all of whose
fibres have dimension at most `n`. Then `R^q f_* F = 0` for every abelian torsion sheaf `F` on
`X_étale` and every `q > 2n`.

This is `properDirectImageVanishingStatement_of_algClosed`. Its three inputs are now theorems:
- Tag 03Q9, `isIso_derivedPushforwardStalkToStrictHenselizationSections_single`.
- Tag 0A59, through `properBaseChangeOverAlgClosed`.
- Vanishing above degree two on proper curves over algebraically closed fields (Tag 0A53),
  `subsingleton_sheafH_of_isProper_of_topologicalKrullDim_le_one`. -/
@[sga "4 XII 5.3" "special case",
  sga "4 XII 5.3bis",
  sga "4 XIV 1.11" "more general",
  sga "5 VII 2.2.3" "more general"]
theorem properDirectImageVanishingStatement : ProperDirectImageVanishingStatement.{u} :=
  properDirectImageVanishingStatement_of_algClosed
    (fun _ Y f _ _ s G ↦ isIso_derivedPushforwardStalkToStrictHenselizationSections_single
      (BigEtaleSite.containing Y) (BigEtaleSite.contains_containing Y) f s G)
    properBaseChangeOverAlgClosed
    (fun k _ _ X π _ hdim G hG q hq ↦
      subsingleton_sheafH_of_isProper_of_topologicalKrullDim_le_one k X π hdim G hG q hq)

/-- **Stacks Project, Tag 095T (Proper Base Change).** Let `f : X ⟶ Y` be a proper morphism of
schemes, `g : Y' ⟶ Y` a morphism of schemes, and `X' = Y' ×_Y X`, given as a cartesian square
`sq` with projections `g' : X' ⟶ X` and `f' : X' ⟶ Y'`. Let `F` be an abelian torsion sheaf on
`X_étale`. Then the base change map `g⁻¹ Rf_* F ⟶ Rf'_* (g')⁻¹ F` of Tag 0A4A
(`etaleAbelianSheafDerivedBaseChange`, in the derived category of abelian sheaves on
`Y'_étale`) is an isomorphism. -/
@[sga "4 XII 5.2" "more general", sga "4 XVII 5.2.2" "special case"]
theorem isIso_etaleAbelianSheafDerivedBaseChange_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, 0} f g g' f' sq.w F) :=
  cohomologyCommutesWithBaseChange_of_isProper f g g' f' sq F hF

/-- **Stacks Project, Tag 095U.** Let `f : X ⟶ Y` be a proper morphism of schemes all of whose
fibres have dimension `≤ n`. Then for every abelian torsion sheaf `F` on `X_étale`,
`R^q f_* F = 0` for every `q > 2n`. Here `R^q f_*` is the `q`-th right derived functor of the
direct image `etaleAbelianDirectImage f` on abelian sheaves. -/
theorem isZero_rightDerived_etaleAbelianDirectImage_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (n : ℕ) (hfib : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ n)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (q : ℕ) (hq : 2 * n < q) :
    IsZero (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived q).obj F) :=
  properDirectImageVanishingStatement f n hfib F hF q (by exact_mod_cast hq)

end Stacks.EtaleCohomology

end
