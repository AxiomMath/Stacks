module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerre.FiniteTypeLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.Abelian

/-!
# Finite type locally constant sheaves of modules and the étale fundamental group

Let `X` be a connected scheme, `x` a geometric point of it and `Λ` a **finite** ring. The finite
type locally constant sheaves of `Λ`-modules on the small étale site of `X` form a category
equivalent to the category of finite `Λ`-modules endowed with a commuting continuous action of
`π₁(X, x)`. This is part (3) of Stacks Tag 0DV5.

## Main results

* `AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalence`: the finite type locally
  constant sheaves of `Λ`-modules on `X_étale` are equivalent to the finite `Λ`-modules with a
  commuting continuous action of `π₁(X, x)`.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ConstantSheaf Stacks.GroupCohomology

universe u r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1) (Λ : Type r) [Ring Λ] [Finite Λ]

/-- Presheaves of `Λ`-modules with values in universe `u + 1` on a slice of the small étale site
admit sheafification. -/
public instance hasWeakSheafify_smallEtaleOver_moduleCat (V : SmallEtale B X.1 X.2) :
    HasWeakSheafify ((SmallEtale.topology B X.1 X.2).over V) (ModuleCat.{u + 1} Λ) :=
  letI := hasSheafify_over_moduleCat.{u + 1, u, r, u + 1}
    (SmallEtale.topology B X.1 X.2) Λ V
  inferInstance

omit [ConnectedSpace X.1] in
/-- Over a finite ring, a sheaf of `Λ`-modules is locally constant of finite type iff it is
locally constant with finite values. -/
public theorem isFiniteTypeLocallyConstant_eq_isFiniteLocallyConstant :
    (fun F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) ↦
        IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2) F) =
      (fun F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) ↦
        IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.2) F) := by
  funext F
  refine propext ⟨fun h ↦ ⟨fun U ↦ ?_⟩, fun h U ↦ ?_⟩
  · obtain ⟨I, V, f, hcov, htriv⟩ := h U
    refine ⟨I, V, f, hcov, fun i ↦ ?_⟩
    obtain ⟨E, hE, he⟩ := htriv i
    exact ⟨E, (moduleCat_isFG_iff_finite Λ E).mp hE, he⟩
  · obtain ⟨I, V, f, hcov, htriv⟩ := h.exists_finite_cover U
    refine ⟨I, V, f, hcov, fun i ↦ ?_⟩
    obtain ⟨E, hE, he⟩ := htriv i
    exact ⟨E, (moduleCat_isFG_iff_finite Λ E).mpr hE, he⟩

/-- Over a finite ring, the full subcategory of locally constant sheaves of `Λ`-modules with finite
values is equivalent to that of finite type locally constant sheaves of `Λ`-modules: they have the
same objects. -/
public def finiteTypeLocallyConstantModuleSheafBridge :
    ObjectProperty.FullSubcategory
        (fun F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) ↦
          IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.2) F) ≌
      ObjectProperty.FullSubcategory
        (fun F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2) F) :=
  CategoryTheory.Equivalence.congrFullSubcategory (CategoryTheory.Equivalence.refl)
    (isFiniteTypeLocallyConstant_eq_isFiniteLocallyConstant B X Λ)

/-- For a connected scheme `X` with a geometric point `x` and a finite ring `Λ`, the finite type
locally constant sheaves of `Λ`-modules on `X_étale` are equivalent to the finite `Λ`-modules
endowed with a commuting continuous action of `π₁(X, x)`. -/
@[stacks 0DV5 "(3) finite type locally constant sheaves of Λ-modules, for Λ a finite ring, are \
  the finite π₁(X, x)-modules with commuting Λ-module structure"]
public def finiteTypeLocallyConstantModuleSheafEquivalence :
    ObjectProperty.FullSubcategory
        (fun F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2) F) ≌
      FiniteTypeContinuousModule.{r, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x) :=
  (finiteTypeLocallyConstantModuleSheafBridge B X Λ).symm.trans
    ((finiteLocallyConstantModuleSheafScalarActionEquivalence
          (SmallEtale.topology B X.1 X.2) Λ).trans
      ((scalarActionCongrRight Λ
            (finiteLocallyConstantAbelianSheafEquivalence B X x)).trans
        (finiteTypeContinuousModuleScalarActionEquivalence Λ
          (EtaleFundamentalGroup X.1 x)).symm))

end AlgebraicGeometry

end
