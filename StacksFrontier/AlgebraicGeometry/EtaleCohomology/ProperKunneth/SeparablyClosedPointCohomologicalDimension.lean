module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricPointStalkCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport

/-!
# The cohomological dimension of a morphism to a separably closed point

Let `Ω` be a separably closed field and `g : Y ⟶ Spec Ω` a quasi-compact and quasi-separated
morphism with `Y` quasi-compact and quasi-separated. Then `cd(g) ≤ cd(Y)`: the higher direct
image `Rⁿg_*F` of a torsion sheaf is a sheaf on `(Spec Ω)_étale`, its stalk at the canonical point
is `Hⁿ(Y, F)`, and a sheaf on the small étale site of the spectrum of a separably closed field
vanishes as soon as that stalk does (the stalk is global sections, and global sections is an
equivalence). This is what lets the absolute bound `cd(Y) < ∞` of [Stacks, Tag 0F10] (2) feed the
proof of [Stacks, Tag 0F14] (2), which uses it through `Rg_*`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.etaleCohomologicalDimension_le_of_isSepClosed`
* `AlgebraicGeometry.Scheme.Hom.etaleCohomologicalDimension_lt_top_of_isSepClosed`

## References

* [Stacks Project, Tag 0F0Z](https://stacks.math.columbia.edu/tag/0F0Z)
* [Stacks Project, Tag 0F10](https://stacks.math.columbia.edu/tag/0F10)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance] additive_globalSections_smallEtale additive_sheafFiber_smallEtale

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of Ω))

/-- **The stalk at the canonical point of `Spec Ω` of `Rⁿg_*F` is the `n`-th derived global
sections of `F` on `Y`**, for `g : Y ⟶ Spec Ω` and `Ω` separably closed. -/
def etaleAbelianSheafFiberRightDerivedDirectImageIsoRightDerivedΓ
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (n : ℕ) :
    (((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) v}).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).obj
      (((etaleAbelianDirectImage.{u, v} g).rightDerived n).obj F) ≅
    ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived n).obj F :=
  let S := ((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) v}).sheafFiber
    (A := AddCommGrpCat.{max (u + 1) v})
  S.mapIso (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso
      (etaleAbelianDirectImage.{u, v} g) (etaleAbelianDerivedDirectImage.{u, v} g)
      (etaleAbelianDerivedDirectImageUnit.{u, v} g)
      Stacks.DerivedFunctor.exists_quasiIso_isKInjective F n).symm ≪≫
    ((S.mapDerivedCategoryHomologyIso (n : ℤ)).app _).symm ≪≫
    (DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
      ((etaleAbelianSheafFiberMapDerivedCategoryDerivedDirectImageIso.{u, v} g).app _) ≪≫
    Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
      (Stacks.DerivedFunctor.totalRightDerived
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}))
      ((Stacks.DerivedFunctor.homotopyMap (Sheaf.Γ Y.smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v})).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
      Stacks.DerivedFunctor.exists_quasiIso_isKInjective F n

/-- An abelian sheaf on the small étale site of the spectrum of a separably closed field vanishes
as soon as its stalk at the canonical point does: the stalk is global sections, which is an
equivalence. -/
theorem isZero_of_isZero_sheafFiber_of_isSepClosed
    (G : Sheaf (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hG : IsZero ((((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) v}).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).obj G)) : IsZero G := by
  have := isEquivalence_globalSections_of_isSepClosed Ω AddCommGrpCat.{max (u + 1) v}
  let Γ := Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}
  exact (Γ.inv.map_isZero (hG.of_iso ((sheafFiberUliftIdIsoGamma.{u, v} Ω).app G).symm)).of_iso
    (Γ.asEquivalence.unitIso.app G)

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] {Y : Scheme.{u}} [CompactSpace Y]
  [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (.of Ω)) [QuasiCompact g] [QuasiSeparated g]

/-- **The cohomological dimension of a morphism to the spectrum of a separably closed field is at
most that of its source**: `cd(g) ≤ cd(Y)`. -/
public theorem etaleCohomologicalDimension_le_of_isSepClosed :
    g.etaleCohomologicalDimension ≤ Scheme.etaleCohomologicalDimension Y := by
  refine etaleCohomologicalDimension_le g _ fun F hF i hi => ?_
  refine Stacks.EtaleCohomology.isZero_of_isZero_sheafFiber_of_isSepClosed.{u, 0} _ ?_
  refine IsZero.of_iso ?_
    (Stacks.EtaleCohomology.etaleAbelianSheafFiberRightDerivedDirectImageIsoRightDerivedΓ.{u, 0}
      g F i)
  exact (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0}
    Y.smallEtaleTopology F i).1
    (Scheme.isEtaleCohomologyBound_etaleCohomologicalDimension Y F hF i hi)

/-- **A morphism to the spectrum of a separably closed field has finite cohomological dimension
as soon as its source does.** -/
public theorem etaleCohomologicalDimension_lt_top_of_isSepClosed
    (h : Scheme.etaleCohomologicalDimension Y < ⊤) : g.etaleCohomologicalDimension < ⊤ :=
  (etaleCohomologicalDimension_le_of_isSepClosed g).trans_lt h

end AlgebraicGeometry.Scheme.Hom

end
