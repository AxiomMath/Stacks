module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.HomologySequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Independence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ConstantFiniteModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportCompactificationIndependence
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSectionsComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition

/-!
# Base change for the higher direct images `R^q f_!` of a torsion sheaf

Let `f' ≫ g = g' ≫ f` be a cartesian square of schemes, `j` a compactification of `f`, and `j'`
any compactification of `f'`, with the base `Y'` of `f'` quasi-compact and quasi-separated. For a
sheaf `Q` of `Λ`-modules on `X_étale` killed by a positive integer,
`R^q f'_! ((g')⁻¹ Q) ≅ g⁻¹ (R^q f_! Q)` for every `q`: the base change isomorphism of `Rf_!` on
`D⁺_tors` ([Stacks, Tag 0F7L], `Stacks.EtaleCohomology.isIso_derivedLowerShriekBaseChange_app`)
computes `Rf'_!` through the base change of `j`, and the independence of the compactification
([Stacks, Tag 0F7I], `Stacks.EtaleCohomology.derivedLowerShriekCompactificationIso`) replaces it by
`j'`; inverse image is exact, so it commutes with placing in degree zero and with cohomology
sheaves.

## Main results

* `Stacks.EtaleCohomology.isTorsionPlus_of_nsmul_id_eq_zero`: an object of `D⁺` killed by a
  positive integer has torsion cohomology sheaves.
* `Stacks.EtaleCohomology.nonempty_lowerShriekHomology_inverseImage_iso`:
  `R^q f'_! ((g')⁻¹ Q) ≅ g⁻¹ (R^q f_! Q)`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` is defined in the standard model
`HasDerivedCategory.standard` of the derived category, so these statements are made in that
model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

/-- An additive functor between preadditive categories preserves annihilation by `m`. -/
private theorem nsmul_id_obj_eq_zero {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] {K : C} {m : ℕ} (h : m • 𝟙 K = 0) :
    m • 𝟙 (F.obj K) = 0 := by
  rw [← F.map_id, ← Functor.map_nsmul, h, Functor.map_zero]

/-- **An object of `D⁺` killed by a positive integer lies in `D⁺_tors`**: `m` kills each of its
cohomology sheaves. -/
theorem isTorsionPlus_of_nsmul_id_eq_zero {Λ : Type} [Ring Λ] {X : Scheme.{u}}
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (m : ℕ) (hm : 0 < m)
    (h : m • 𝟙 K = 0) : isTorsionPlus.{u, 0} Λ X K := fun i =>
  isTorsionEtaleModule_of_nsmul_id_eq_zero_typeZero _ m hm
    (nsmul_id_obj_eq_zero (DerivedCategory.Plus.homologyFunctor _ i) h)

variable (Λ : Type) [Ring Λ] {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g) (j : CompactificationOf (Over.mk f))
  [CompactSpace Y'] [QuasiSeparatedSpace Y'] [IsSeparated f'] [LocallyOfFiniteType f']
  [QuasiCompact f'] (j' : CompactificationOf (Over.mk f'))

include sq in
/-- **Base change for `R^q f_!` of a torsion sheaf**: for a cartesian square `f' ≫ g = g' ≫ f`, a
compactification `j` of `f`, any compactification `j'` of `f'` and a sheaf `Q` of `Λ`-modules
killed by a positive integer, `R^q f'_! ((g')⁻¹ Q) ≅ g⁻¹ (R^q f_! Q)`
([Stacks, Tag 0F7L] and [Stacks, Tag 0F7I]). -/
theorem nonempty_lowerShriekHomology_inverseImage_iso (Q : EtaleModules.{u, 0} Λ X) (m : ℕ)
    (hm : 0 < m) (hQ : m • 𝟙 Q = 0) (q : ℤ) :
    Nonempty ((lowerShriekHomology Λ f' j' q).obj ((etaleModuleInverseImage.{u, 0} Λ g').obj Q) ≅
      (etaleModuleInverseImage.{u, 0} Λ g).obj ((lowerShriekHomology Λ f j q).obj Q)) := by
  let S := DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0
  let K := S.obj Q
  have hK : m • 𝟙 K = 0 := nsmul_id_obj_eq_zero S hQ
  let K' := (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g').obj K
  have hK' : m • 𝟙 K' = 0 := nsmul_id_obj_eq_zero _ hK
  let e₁ : DerivedCategory.Plus.Q.obj ((singlePlus (EtaleModules.{u, 0} Λ X')).obj
      ((etaleModuleInverseImage.{u, 0} Λ g').obj Q)) ≅ K' :=
    (StacksDraft.DerivedSectionsComparison.singlePlusQIso (EtaleModules.{u, 0} Λ X')).app _ ≪≫
      ((etaleModuleInverseImage.{u, 0} Λ g').mapDerivedCategoryPlusObjSingleIso Q).symm
  let e₂ := (derivedLowerShriekCompactificationIso f' j' (j.baseChange sq) Λ).app
    ⟨K', isTorsionPlus_of_nsmul_id_eq_zero K' m hm hK'⟩
  have := isIso_derivedLowerShriekBaseChange_app Λ sq j K
    (isTorsionPlus_of_nsmul_id_eq_zero K m hm hK)
  let e₃ := (asIso ((derivedLowerShriekBaseChange.{u, 0} Λ sq j).app K)).symm
  obtain ⟨e₄⟩ := nonempty_homology_etaleModuleDerivedInverseImagePlus_iso Λ g
    ((derivedLowerShriek.{u, 0} f j Λ).obj K) q
  let e₅ : K ≅ DerivedCategory.Plus.Q.obj ((singlePlus (EtaleModules.{u, 0} Λ X)).obj Q) :=
    ((StacksDraft.DerivedSectionsComparison.singlePlusQIso (EtaleModules.{u, 0} Λ X)).app Q).symm
  exact ⟨(DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((derivedLowerShriek.{u, 0} f' j' Λ).mapIso e₁ ≪≫ e₂ ≪≫ e₃) ≪≫ e₄ ≪≫
    (etaleModuleInverseImage.{u, 0} Λ g).mapIso ((DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((derivedLowerShriek.{u, 0} f j Λ).mapIso e₅))⟩

/-! ### The natural isomorphism -/

section Natural

variable (P : ObjectProperty (EtaleModules.{u, 0} Λ X))
  (hP : ∀ Q, P Q → ∃ m : ℕ, 0 < m ∧ m • 𝟙 Q = 0)

include hP in
/-- A sheaf killed by a positive integer, placed in degree zero, lies in `D⁺_tors`. -/
def singleTorsionPlus : P.FullSubcategory ⥤ (isTorsionPlus.{u, 0} Λ X).FullSubcategory :=
  (isTorsionPlus.{u, 0} Λ X).lift (P.ι ⋙ DerivedCategory.Plus.singleFunctor _ 0) fun Q => by
    obtain ⟨m, hm, h⟩ := hP Q.1 Q.2
    refine isTorsionPlus_of_nsmul_id_eq_zero _ m hm ?_
    change m • 𝟙 ((DerivedCategory.Plus.singleFunctor _ 0).obj Q.1) = 0
    rw [← (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).map_id,
      ← Functor.map_nsmul, h, Functor.map_zero]

include hP in
/-- The inverse image along `g'` of a sheaf killed by a positive integer, placed in degree zero,
lies in `D⁺_tors`. -/
def singleTorsionPlusInverseImage :
    P.FullSubcategory ⥤ (isTorsionPlus.{u, 0} Λ X').FullSubcategory :=
  (isTorsionPlus.{u, 0} Λ X').lift (P.ι ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
      etaleModuleDerivedInverseImagePlus.{u, 0} Λ g') fun Q => by
    obtain ⟨m, hm, h⟩ := hP Q.1 Q.2
    refine isTorsionPlus_of_nsmul_id_eq_zero _ m hm ?_
    change m • 𝟙 ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ g').obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj Q.1)) = 0
    rw [← (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g').map_id,
      ← (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).map_id,
      ← Functor.map_nsmul, ← Functor.map_nsmul, h, Functor.map_zero, Functor.map_zero]

include sq in
/-- **Base change for `R^q f_!`, naturally in the torsion sheaf** ([Stacks, Tag 0F7L] and
[Stacks, Tag 0F7I]): for a cartesian square `f' ≫ g = g' ≫ f`, a compactification `j` of `f`,
any compactification `j'` of `f'` and sheaves `Q` of `Λ`-modules in a class `P` of sheaves each
killed by a positive integer, `R^q f'_! ((g')⁻¹ Q) ≅ g⁻¹ (R^q f_! Q)` naturally in `Q`. -/
def lowerShriekHomologyBaseChangeIso (q : ℤ) :
    P.ι ⋙ etaleModuleInverseImage.{u, 0} Λ g' ⋙ lowerShriekHomology Λ f' j' q ≅
      P.ι ⋙ lowerShriekHomology Λ f j q ⋙ etaleModuleInverseImage.{u, 0} Λ g :=
  let H' := DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, 0} Λ Y') q
  let H := DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, 0} Λ Y) q
  let S' := StacksDraft.DerivedSectionsComparison.singlePlusQIso (EtaleModules.{u, 0} Λ X')
  let S := StacksDraft.DerivedSectionsComparison.singlePlusQIso (EtaleModules.{u, 0} Λ X)
  Functor.isoWhiskerLeft (P.ι ⋙ etaleModuleInverseImage.{u, 0} Λ g')
      (Functor.isoWhiskerRight S' (derivedLowerShriek.{u, 0} f' j' Λ ⋙ H')) ≪≫
    Functor.isoWhiskerLeft P.ι (Functor.isoWhiskerRight
      (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (etaleModuleInverseImage.{u, 0} Λ g') 0).symm
      (derivedLowerShriek.{u, 0} f' j' Λ ⋙ H')) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (singleTorsionPlusInverseImage Λ P hP (g' := g'))
        (derivedLowerShriekCompactificationIso f' j' (j.baseChange sq) Λ)) H' ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (singleTorsionPlus Λ P hP)
      (derivedLowerShriekBaseChangeIso Λ sq j).symm) H' ≪≫
    Functor.isoWhiskerLeft (P.ι ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
      derivedLowerShriek.{u, 0} f j Λ) (Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Stacks.Homology.derivedHomologyIso (etaleModuleInverseImage.{u, 0} Λ g) q)) ≪≫
    Functor.isoWhiskerLeft P.ι (Functor.isoWhiskerRight S.symm
      (derivedLowerShriek.{u, 0} f j Λ ⋙ H ⋙ etaleModuleInverseImage.{u, 0} Λ g))

end Natural

end Stacks.EtaleCohomology
