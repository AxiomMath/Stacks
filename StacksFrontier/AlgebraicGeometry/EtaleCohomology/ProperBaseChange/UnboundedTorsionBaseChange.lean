module
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.IntegralBaseChangeReduction
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveLocalization
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Triangulated
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocalDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMate
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.InjectiveAcyclicityCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.OpenBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModulesFunctor
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AcyclicResolutionBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AcyclicResolutionBaseChangeUnconditional
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeZariskiLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ItemAuxiliary
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ItemAuxiliaryUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.UnderlyingAbelianDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.ExtensionByZeroIsCompact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules

/-!
# Base change for unbounded complexes of sheaves of `ℤ/nℤ`-modules

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of schemes with `f` proper, and let `n ≥ 1`. [Stacks, Tag 0F0C] says that
the base change map `g^{-1}Rf_*E ⟶ Rf'_*(g')^{-1}E` of (0A2A) is an isomorphism for every object
`E` of `D(X_étale, ℤ/nℤ)`, with no boundedness assumption on `E`. Its proof uses two inputs: the
proper base change theorem (Tag 095T), which is the statement that cohomology commutes with base
change for `f`, and the finite cohomological dimension of `f'_*` over a quasi-compact base,
which Tag 095U gives together with the boundedness of fibre dimensions (Morphisms, Tag 0A3V).

This file proves Tag 0F0C from those two inputs, each taken as one named hypothesis, and
everything else proved: the comparison of `D(X_étale, ℤ/nℤ)` with the derived category of
abelian sheaves, the way-out argument for unbounded complexes, and the reduction to an affine
base.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedDirectImageUnit_app_of_isZero_rightDerived`:
  under a bound on the higher direct images of torsion sheaves, the unbounded `Rf_*` is computed
  by any complex of sheaves of `ℤ/nℤ`-modules whose terms have no higher direct images.
* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_zmod_of_isZero_rightDerived` — the
  base change map is invertible at every object of `D(X_étale, ℤ/nℤ)` once the higher direct
  images of `f'` are bounded.
* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_zmod_of_affineOpens` — the same
  with the bound required only over the affine opens of `Y'`.
* `isIso_etaleAbelianDerivedBaseChange_zmod_of_cohomologyCommutesWithBaseChange` — for `f`
  proper, the base change map is invertible at every object of `D(X_étale, ℤ/nℤ)`, assuming
  proper base change for `f` and the vanishing of higher direct images above twice the fibre
  dimension.

## Implementation notes

*`D(X_étale, ℤ/nℤ)`.* A sheaf of `ℤ/nℤ`-modules is a sheaf of modules over the constant sheaf of
rings `Stacks.Cohomology.ZModSheaf.zmodRingSheaf`, as in the rest of the proper base change
development (`Stacks.EtaleCohomology.InjectiveBaseChangeAcyclic`), and `D(X_étale, ℤ/nℤ)` is the
unbounded derived category of that abelian category. The base change map (0A2A) of the source is
a map in `D(Y'_étale)`: it is `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange`, applied to
the image of `E` under the forgetful functor `D(X_étale, ℤ/nℤ) ⥤ D(X_étale)`.

*The way-out argument.* The source applies Derived Categories, Lemma 07K7, to
`f'_* : Mod(X'_étale, ℤ/nℤ) ⥤ Mod(Y'_étale, ℤ/nℤ)`. Here it is applied to the composite
`T = (forget) ⋙ f'_*` of the forgetful functor with the abelian direct image, with right derived
functor `RT = (forget) ⋙ Rf'_*` on `D(X'_étale, ℤ/nℤ)`. That `RT` is a right derived functor of
`T` is the comparison of the two derived categories: the underlying abelian complex of a
K-injective complex of `ℤ/nℤ`-modules computes the abelian `Rf'_*`
(`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedDirectImageUnit_app_toSheaf_of_isKInjective`,
which is the input of Tag 0D6J part (3)). The higher direct images of `T` are those of the
underlying torsion sheaves, so the bound of Tag 095U is the cohomological dimension hypothesis of
07K7.

## References

* [Stacks Project, Tag 0F0C](https://stacks.math.columbia.edu/tag/0F0C)
* [Stacks Project, Tag 07K7](https://stacks.math.columbia.edu/tag/07K7)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
* [Stacks Project, Tag 0A3V](https://stacks.math.columbia.edu/tag/0A3V)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ZModSheaf

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

section WayOut

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)

/-- The forgetful functor from sheaves of `ℤ/nℤ`-modules on `X_étale` to abelian sheaves. -/
abbrev zmodToSheaf (X : Scheme.{u}) (n : ℕ) :
    SheafOfModules.{max (u + 1) v} (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n) ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  SheafOfModules.toSheaf _

/-- The direct image of the underlying abelian sheaf of a sheaf of `ℤ/nℤ`-modules. -/
abbrev zmodUnderlyingDirectImage :
    SheafOfModules.{max (u + 1) v} (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n) ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  zmodToSheaf.{u, v} X n ⋙ etaleAbelianDirectImage.{u, v} f

/-- Its unbounded right derived functor: forget the module structure on the derived category,
then apply the abelian `Rf_*`. -/
abbrev zmodUnderlyingDerivedDirectImage :
    DerivedCategory (SheafOfModules.{max (u + 1) v}
        (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  (zmodToSheaf.{u, v} X n).mapDerivedCategory ⋙ etaleAbelianDerivedDirectImage.{u, v} f

/-- The comparison from the degreewise composite to its derived functor, assembled from the unit
of the abelian `Rf_*`. -/
def zmodUnderlyingDerivedDirectImageUnit :
    (zmodUnderlyingDirectImage.{u, v} f n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ zmodUnderlyingDerivedDirectImage.{u, v} f n :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (zmodUnderlyingDirectImage.{u, v} f n)) (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((zmodToSheaf.{u, v} X n).mapHomotopyCategory (ComplexShape.up ℤ))
      (etaleAbelianDerivedDirectImageUnit.{u, v} f) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (zmodToSheaf.{u, v} X n).mapDerivedCategoryFactorsh.inv
      (etaleAbelianDerivedDirectImage.{u, v} f) ≫
    (Functor.associator _ _ _).hom

/-- The comparison is invertible at a complex of `ℤ/nℤ`-modules exactly when the unit of the
abelian `Rf_*` is invertible at its underlying abelian complex. -/
theorem isIso_zmodUnderlyingDerivedDirectImageUnit_app_iff
    (L : CochainComplex (SheafOfModules.{max (u + 1) v}
      (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n)) ℤ) :
    IsIso ((zmodUnderlyingDerivedDirectImageUnit.{u, v} f n).app
        ((HomotopyCategory.quotient (SheafOfModules.{max (u + 1) v}
          (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n)) (ComplexShape.up ℤ)).obj L)) ↔
      IsIso ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app
        ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
          (ComplexShape.up ℤ)).obj
          (((zmodToSheaf.{u, v} X n).mapHomologicalComplex (ComplexShape.up ℤ)).obj L))) := by
  simp only [zmodUnderlyingDerivedDirectImageUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, isIso_comp_left_iff, isIso_comp_right_iff]
  rfl

/-- The composite derived functor is a right derived functor of the degreewise composite: the
underlying abelian complex of a K-injective complex of `ℤ/nℤ`-modules computes the abelian
`Rf_*`. -/
instance isRightDerivedFunctor_zmodUnderlyingDerivedDirectImage :
    (zmodUnderlyingDerivedDirectImage.{u, v} f n).IsRightDerivedFunctor
      (zmodUnderlyingDerivedDirectImageUnit.{u, v} f n)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ fun I _ ↦
    (isIso_zmodUnderlyingDerivedDirectImageUnit_app_iff.{u, v} f n I).2
      (isIso_etaleAbelianDerivedDirectImageUnit_app_toSheaf_of_isKInjective.{u, v} f _ I)

/-- The higher direct images of the degreewise composite are those of the underlying abelian
sheaves, naturally: `R^q(f_* ∘ forget) ≅ R^q f_* ∘ forget`, both read off the unbounded derived
functors. -/
def zmodUnderlyingDirectImageRightDerivedNatIso (q : ℕ) :
    (zmodUnderlyingDirectImage.{u, v} f n).rightDerived q ≅
      zmodToSheaf.{u, v} X n ⋙ (etaleAbelianDirectImage.{u, v} f).rightDerived q :=
  (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
      (zmodUnderlyingDirectImage.{u, v} f n) (zmodUnderlyingDerivedDirectImage.{u, v} f n)
      (zmodUnderlyingDerivedDirectImageUnit.{u, v} f n)
      Stacks.DerivedFunctor.exists_quasiIso_isKInjective q).symm ≪≫
    Functor.isoWhiskerRight ((zmodToSheaf.{u, v} X n).mapDerivedCategorySingleFunctor 0)
      (etaleAbelianDerivedDirectImage.{u, v} f ⋙ DerivedCategory.homologyFunctor _ (q : ℤ)) ≪≫
    Functor.isoWhiskerLeft (zmodToSheaf.{u, v} X n)
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
        (etaleAbelianDirectImage.{u, v} f) (etaleAbelianDerivedDirectImage.{u, v} f)
        (etaleAbelianDerivedDirectImageUnit.{u, v} f)
        Stacks.DerivedFunctor.exists_quasiIso_isKInjective q)

/-- The higher direct images of the degreewise composite are those of the underlying abelian
sheaves: `R^q(f_* ∘ forget)(M) = R^q f_*(M_ab)`, both read off the unbounded derived functors. -/
def zmodUnderlyingDirectImageRightDerivedIso
    (M : SheafOfModules.{max (u + 1) v} (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n))
    (q : ℕ) :
    ((zmodUnderlyingDirectImage.{u, v} f n).rightDerived q).obj M ≅
      ((etaleAbelianDirectImage.{u, v} f).rightDerived q).obj ((zmodToSheaf.{u, v} X n).obj M) :=
  (zmodUnderlyingDirectImageRightDerivedNatIso.{u, v} f n q).app M

/-- **The way-out argument (Stacks 07K7) for the unbounded `Rf_*` on sheaves of
`ℤ/nℤ`-modules.** Suppose that the higher direct images `R^q f_*` vanish on torsion abelian
sheaves above some degree `d`. Then for every complex `L` of sheaves of `ℤ/nℤ`-modules on
`X_étale`, unbounded in both directions, whose terms have no higher direct images, the unit
`f_* L ⟶ Rf_* L` of the unbounded abelian derived direct image is an isomorphism. -/
theorem isIso_etaleAbelianDerivedDirectImageUnit_app_of_isZero_rightDerived (hn : 0 < n)
    (hcd : ∃ d : ℕ, ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
      Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F → ∀ q : ℕ, d < q →
        IsZero (((etaleAbelianDirectImage.{u, v} f).rightDerived q).obj F))
    (L : CochainComplex (SheafOfModules.{max (u + 1) v}
      (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n)) ℤ)
    (hL : ∀ k q : ℤ, 0 < q →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) q).obj
        ((etaleAbelianDerivedDirectImage.{u, v} f).obj
          ((DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj
            ((zmodToSheaf.{u, v} X n).obj (L.X k)))))) :
    IsIso ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app
      ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
        (ComplexShape.up ℤ)).obj
        (((zmodToSheaf.{u, v} X n).mapHomologicalComplex (ComplexShape.up ℤ)).obj L))) := by
  obtain ⟨d, hd⟩ := hcd
  let T := zmodUnderlyingDirectImage.{u, v} f n
  have := Stacks.Cohomology.CompactExtensionByZero.hasRightDerivedFunctorPlus T
  have hT : ∀ M, IsZero ((T.rightDerived (d + 1)).obj M) := fun M ↦
    (hd _ (torsionSheafProperty_toSheaf_zmod hn M) (d + 1) (by omega)).of_iso
      (zmodUnderlyingDirectImageRightDerivedIso.{u, v} f n M (d + 1))
  have hac : ∀ k : ℤ, T.rightAcyclic (L.X k) := fun k ↦
    (Stacks.DerivedFunctor.rightAcyclic_iff_isZero_homology_obj_singleFunctor T
      (zmodUnderlyingDerivedDirectImage.{u, v} f n)
      (zmodUnderlyingDerivedDirectImageUnit.{u, v} f n)
      Stacks.DerivedFunctor.exists_quasiIso_isKInjective (L.X k)).2 fun q hq ↦
        (hL k q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
          ((etaleAbelianDerivedDirectImage.{u, v} f).mapIso
            (((zmodToSheaf.{u, v} X n).mapDerivedCategorySingleFunctor 0).app (L.X k))))
  have h :=
    (Stacks.Cohomology.CompactExtensionByZero.hasRightDerivedFunctor_and_computed_by_rightAcyclic
      T (d + 1) hT).2 (zmodUnderlyingDerivedDirectImage.{u, v} f n)
    (zmodUnderlyingDerivedDirectImageUnit.{u, v} f n) L hac
  exact (isIso_zmodUnderlyingDerivedDirectImageUnit_app_iff.{u, v} f n L).1 h

end WayOut

section Core

variable {X X' Y Y' : Scheme.{u}}

/-- The inverse image of the underlying abelian sheaf of a sheaf of `ℤ/nℤ`-modules is killed by
`n`, sectionwise. -/
theorem nsmul_inverseImage_toSheaf_eq_zero (g' : X' ⟶ X) (n : ℕ)
    (M : SheafOfModules.{max (u + 1) v} (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n))
    (U : X'.Etaleᵒᵖ)
    (x : ToType (((etaleAbelianInverseImage.{u, v} g').obj
      ((zmodToSheaf.{u, v} X n).obj M)).obj.obj U)) : n • x = 0 := by
  have h : n • 𝟙 ((etaleAbelianInverseImage.{u, v} g').obj ((zmodToSheaf.{u, v} X n).obj M)) =
      0 := by
    rw [← (etaleAbelianInverseImage.{u, v} g').map_id, ← Functor.map_nsmul,
      nsmul_id_toSheaf_eq_zero.{u, v} n M, Functor.map_zero]
  rw [← natCast_zsmul]
  refine (zsmul_id_eq_zero_iff _ n).1 ?_ U x
  rw [natCast_zsmul]
  exact h

/-- The inverse image along `g'` of sheaves of `ℤ/nℤ`-modules, computed on underlying abelian
sheaves. -/
abbrev zmodInverseImage (g' : X' ⟶ X) (n : ℕ) :
    SheafOfModules.{max (u + 1) v} (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n) ⥤
      SheafOfModules.{max (u + 1) v} (zmodRingSheaf.{max (u + 1) v} X'.smallEtaleTopology n) :=
  torsionSheafToModulesFunctor.{max (u + 1) v, max (u + 1) v} X'.smallEtaleTopology n
    (zmodToSheaf.{u, v} X n ⋙ etaleAbelianInverseImage.{u, v} g')
    (nsmul_inverseImage_toSheaf_eq_zero.{u, v} g' n)

/-- **The underived base change map at an injective sheaf of `ℤ/nℤ`-modules is invertible**,
when cohomology commutes with base change for `f`: the underlying abelian sheaf `J` of the
injective sheaf is torsion and has no higher direct images, so neither has `(g')^{-1}J`, and the
derived base change map at `J` is the underived one. -/
theorem isIso_etaleAbelianBaseChange_app_toSheaf_of_injective {f : X ⟶ Y}
    (hf : CohomologyCommutesWithBaseChange.{u, v} f) {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g) {n : ℕ} (hn : 0 < n)
    (J : SheafOfModules.{max (u + 1) v} (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n))
    [Injective J] :
    IsIso ((etaleAbelianBaseChange.{u, v} f g g' f' sq.w).app
      ((zmodToSheaf.{u, v} X n).obj J)) := by
  have hG := isZero_homology_etaleAbelianDerivedDirectImage_single_toSheaf_of_injective.{u, v}
    f n J
  have := hf g g' f' sq ((zmodToSheaf.{u, v} X n).obj J) (torsionSheafProperty_toSheaf_zmod hn J)
  have key := (isIso_etaleAbelianSheafDerivedBaseChange_iff_of_rightAcyclic.{u, v} f g g' f' sq.w
    ((zmodToSheaf.{u, v} X n).obj J) hG fun q hq ↦
      isZero_homology_etaleAbelianDerivedDirectImage_inverseImage_of_isIso f g g' f' sq.w _ q
        (hG q hq)).1 this
  exact key

/-- **Vanishing of a higher direct image is carried to the inverse image of a sheaf of
`ℤ/nℤ`-modules** across a base change map invertible at its underlying abelian sheaf, read on
the sheaf of `ℤ/nℤ`-modules `zmodInverseImage g' n` attached to it. -/
theorem isZero_homology_etaleAbelianDerivedDirectImage_zmodInverseImage_of_isIso
    {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (h : g' ≫ f = f' ≫ g) (n : ℕ)
    (J : SheafOfModules.{max (u + 1) v} (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n))
    [IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' h
      ((zmodToSheaf.{u, v} X n).obj J))] (q : ℤ)
    (hJ : IsZero ((DerivedCategory.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) q).obj
      ((etaleAbelianDerivedDirectImage.{u, v} f).obj
        ((DerivedCategory.singleFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj
          ((zmodToSheaf.{u, v} X n).obj J))))) :
    IsZero ((DerivedCategory.homologyFunctor
        (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) q).obj
      ((etaleAbelianDerivedDirectImage.{u, v} f').obj
        ((DerivedCategory.singleFunctor
          (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj
          ((zmodToSheaf.{u, v} X' n).obj ((zmodInverseImage.{u, v} g' n).obj J))))) := by
  refine (isZero_homology_etaleAbelianDerivedDirectImage_inverseImage_of_isIso f g g' f' h
    _ q hJ).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
      ((etaleAbelianDerivedDirectImage.{u, v} f').mapIso ?_))
  exact (DerivedCategory.singleFunctor _ 0).mapIso
      ((torsionSheafToModulesFunctorCompToSheaf.{max (u + 1) v, max (u + 1) v}
        X'.smallEtaleTopology n (zmodToSheaf.{u, v} X n ⋙ etaleAbelianInverseImage.{u, v} g')
        (nsmul_inverseImage_toSheaf_eq_zero.{u, v} g' n)).app J) ≪≫
    (((etaleAbelianInverseImage.{u, v} g').mapDerivedCategorySingleFunctor 0).app
      ((zmodToSheaf.{u, v} X n).obj J)).symm

/-- **The inverse image of an injective sheaf of `ℤ/nℤ`-modules has no higher direct images**,
when cohomology commutes with base change for `f`, read on the sheaf of `ℤ/nℤ`-modules
`zmodInverseImage g' n` attached to it. -/
theorem isZero_homology_etaleAbelianDerivedDirectImage_zmodInverseImage_of_injective
    {f : X ⟶ Y} (hf : CohomologyCommutesWithBaseChange.{u, v} f) {g : Y' ⟶ Y} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g) {n : ℕ} (hn : 0 < n)
    (J : SheafOfModules.{max (u + 1) v} (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n))
    [Injective J] (q : ℤ) (hq : 0 < q) :
    IsZero ((DerivedCategory.homologyFunctor
        (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) q).obj
      ((etaleAbelianDerivedDirectImage.{u, v} f').obj
        ((DerivedCategory.singleFunctor
          (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0).obj
          ((zmodToSheaf.{u, v} X' n).obj ((zmodInverseImage.{u, v} g' n).obj J))))) := by
  have := hf g g' f' sq ((zmodToSheaf.{u, v} X n).obj J) (torsionSheafProperty_toSheaf_zmod hn J)
  exact isZero_homology_etaleAbelianDerivedDirectImage_zmodInverseImage_of_isIso.{u, v} sq.w n J
    q (isZero_homology_etaleAbelianDerivedDirectImage_single_toSheaf_of_injective.{u, v} f n J q hq)

/-- The underlying abelian complex of `zmodInverseImage g' n` applied to a complex is the inverse
image of the underlying abelian complex. -/
def zmodInverseImageMapHomologicalComplexIso (g' : X' ⟶ X) (n : ℕ)
    (I : CochainComplex (SheafOfModules.{max (u + 1) v}
      (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n)) ℤ) :
    ((zmodToSheaf.{u, v} X' n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((zmodInverseImage.{u, v} g' n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      ((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((zmodToSheaf.{u, v} X n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  (NatIso.mapHomologicalComplex (torsionSheafToModulesFunctorCompToSheaf.{max (u + 1) v,
    max (u + 1) v} X'.smallEtaleTopology n
    (zmodToSheaf.{u, v} X n ⋙ etaleAbelianInverseImage.{u, v} g')
    (nsmul_inverseImage_toSheaf_eq_zero.{u, v} g' n)) (ComplexShape.up ℤ)).app I

/-- **The unbounded `Rf'_*` is computed on the inverse image of a K-injective complex of
injective sheaves of `ℤ/nℤ`-modules**, when cohomology commutes with base change for `f` and the
higher direct images of `f'` are bounded: the way-out argument applied to `zmodInverseImage`. -/
theorem isIso_etaleAbelianDerivedDirectImageUnit_app_inverseImage_toSheaf {f : X ⟶ Y}
    (hf : CohomologyCommutesWithBaseChange.{u, v} f) {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g) {n : ℕ} (hn : 0 < n)
    (hcd : ∃ d : ℕ, ∀ F : Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
      Stacks.Torsion.torsionSheafProperty X'.smallEtaleTopology F → ∀ q : ℕ, d < q →
        IsZero (((etaleAbelianDirectImage.{u, v} f').rightDerived q).obj F))
    (I : CochainComplex (SheafOfModules.{max (u + 1) v}
      (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n)) ℤ) [∀ k, Injective (I.X k)] :
    IsIso ((etaleAbelianDerivedDirectImageUnit.{u, v} f').app
      ((HomotopyCategory.quotient (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
        (ComplexShape.up ℤ)).obj
        (((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((zmodToSheaf.{u, v} X n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))) := by
  have hL := isIso_etaleAbelianDerivedDirectImageUnit_app_of_isZero_rightDerived.{u, v} f' n hn
    hcd (((zmodInverseImage.{u, v} g' n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
    fun k q hq ↦
      isZero_homology_etaleAbelianDerivedDirectImage_zmodInverseImage_of_injective.{u, v} hf sq
        hn (I.X k) q hq
  exact (NatTrans.isIso_app_iff_of_iso _ ((HomotopyCategory.quotient
    (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).mapIso
      (zmodInverseImageMapHomologicalComplexIso.{u, v} g' n I))).1 hL

/-- The degreewise base change comparison is invertible at the underlying abelian complex of a
complex of injective sheaves of `ℤ/nℤ`-modules, when cohomology commutes with base change for
`f`. -/
theorem isIso_etaleAbelianHomotopyBaseChange_app_toSheaf_of_injective {f : X ⟶ Y}
    (hf : CohomologyCommutesWithBaseChange.{u, v} f) {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g) {n : ℕ} (hn : 0 < n)
    (I : CochainComplex (SheafOfModules.{max (u + 1) v}
      (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n)) ℤ) [∀ k, Injective (I.X k)] :
    IsIso ((etaleAbelianHomotopyBaseChange.{u, v} f g g' f' sq.w).app
      ((HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
        (ComplexShape.up ℤ)).obj
        (((zmodToSheaf.{u, v} X n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) := by
  refine isIso_etaleAbelianHomotopyBaseChange_app_unconditional.{u, v} f g g' f' sq.w _ fun k ↦ ?_
  -- The term of the complex is replaced by a variable along an equation of objects. Comparing it
  -- with `(zmodToSheaf X n).obj (I.X k)` directly, under the inverse and direct image functors,
  -- would make the kernel unfold those functors.
  generalize hx : ((HomotopyCategory.quotient
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj
      (((zmodToSheaf.{u, v} X n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).as.X k = x
  have e : (zmodToSheaf.{u, v} X n).obj (I.X k) = x := hx
  subst e
  exact isIso_etaleAbelianBaseChange_app_toSheaf_of_injective.{u, v} hf sq hn (I.X k)

/-- **The base change map at the underlying abelian complex of a K-injective complex of
injective sheaves of `ℤ/nℤ`-modules**, when cohomology commutes with base change for `f` and the
higher direct images of `f'` are bounded. Both derived-functor units in the characterization
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_fac` of the base change map are invertible
there — the first by the comparison of `D(X_étale, ℤ/nℤ)` with `D(X_étale)`, the second by the
way-out argument — and so is the degreewise comparison. -/
theorem isIso_etaleAbelianDerivedBaseChange_app_toSheaf_of_isKInjective {f : X ⟶ Y}
    (hf : CohomologyCommutesWithBaseChange.{u, v} f) {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g) {n : ℕ} (hn : 0 < n)
    (hcd : ∃ d : ℕ, ∀ F : Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
      Stacks.Torsion.torsionSheafProperty X'.smallEtaleTopology F → ∀ q : ℕ, d < q →
        IsZero (((etaleAbelianDirectImage.{u, v} f').rightDerived q).obj F))
    (I : CochainComplex (SheafOfModules.{max (u + 1) v}
      (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n)) ℤ) [I.IsKInjective]
    [∀ k, Injective (I.X k)] :
    IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' sq.w).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj
          (((zmodToSheaf.{u, v} X n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))) := by
  have h₁ : IsIso ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app
      ((HomotopyCategory.quotient
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj
        (((zmodToSheaf.{u, v} X n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :=
    isIso_etaleAbelianDerivedDirectImageUnit_app_toSheaf_of_isKInjective.{u, v} f _ I
  have h₂ := isIso_etaleAbelianHomotopyBaseChange_app_toSheaf_of_injective.{u, v} hf sq hn I
  have h₃ := isIso_etaleAbelianDerivedDirectImageUnit_app_inverseImage_toSheaf.{u, v} hf sq hn
    hcd I
  have hfac := etaleAbelianDerivedBaseChange_fac.{u, v} f g g' f' sq.w
    ((HomotopyCategory.quotient
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj
      (((zmodToSheaf.{u, v} X n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
  rw [← isIso_comp_left_iff
      ((etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.app _ ≫
      (etaleAbelianDerivedInverseImage.{u, v} g).map
        ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app _)),
    Category.assoc, hfac]
  have : IsIso ((etaleAbelianDerivedDirectImageUnit.{u, v} f').app
      (((etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj
          (((zmodToSheaf.{u, v} X n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))) := h₃
  infer_instance

/-- **The base change map at an object of `D(X_étale, ℤ/nℤ)`, under a bound on the higher direct
images of `f'`.** Let cohomology commute with base change for `f` and let the higher direct
images `R^q f'_*` vanish on torsion abelian sheaves above some degree. Then for every object `E`
of the unbounded derived category of sheaves of `ℤ/nℤ`-modules on `X_étale`, `n > 0`, the base
change map `g^{-1}Rf_*E ⟶ Rf'_*(g')^{-1}E` of the underlying object of `D(X_étale)` is an
isomorphism.

This is the argument of the source: represent `E` by a K-injective complex `I` with injective
terms; then `g^{-1}Rf_*E` is computed by `g^{-1}f_*I`; each `(g')^{-1}I^k` has no higher direct
images and `g^{-1}f_*I^k ⟶ f'_*(g')^{-1}I^k` is invertible, both because cohomology commutes with
base change at the torsion sheaf `I^k`; and the way-out argument computes `Rf'_*(g')^{-1}E` by
`f'_*(g')^{-1}I`. -/
theorem isIso_etaleAbelianDerivedBaseChange_zmod_of_isZero_rightDerived {f : X ⟶ Y}
    (hf : CohomologyCommutesWithBaseChange.{u, v} f) {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g) {n : ℕ} (hn : 0 < n)
    (hcd : ∃ d : ℕ, ∀ F : Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
      Stacks.Torsion.torsionSheafProperty X'.smallEtaleTopology F → ∀ q : ℕ, d < q →
        IsZero (((etaleAbelianDirectImage.{u, v} f').rightDerived q).obj F))
    (E : DerivedCategory (SheafOfModules.{max (u + 1) v}
      (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n))) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' sq.w).app
      ((zmodToSheaf.{u, v} X n).mapDerivedCategory.obj E)) := by
  obtain ⟨I, _, _, ⟨e⟩⟩ : ∃ (I : CochainComplex (SheafOfModules.{max (u + 1) v}
      (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n)) ℤ) (_ : I.IsKInjective)
      (_ : ∀ k, Injective (I.X k)),
      Nonempty (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)
        ≅ E) :=
    ⟨_, inferInstance, inferInstance,
      ⟨(DerivedCategory.quotientCompQhIso _).app _ ≪≫
        (asIso (DerivedCategory.Q.map ((Stacks.Injectives.kInjectiveResolutionInclusion _).app
          (DerivedCategory.Q.objPreimage E)))).symm ≪≫ DerivedCategory.Q.objObjPreimageIso E⟩⟩
  have h : ((zmodToSheaf.{u, v} X n).mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) =
      (HomotopyCategory.quotient (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
        (ComplexShape.up ℤ)).obj
        (((zmodToSheaf.{u, v} X n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := rfl
  let e' : (zmodToSheaf.{u, v} X n).mapDerivedCategory.obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).obj
        (((zmodToSheaf.{u, v} X n).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
    (zmodToSheaf.{u, v} X n).mapDerivedCategoryFactorsh.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) ≪≫
      DerivedCategory.Qh.mapIso (eqToIso h)
  refine (NatTrans.isIso_app_iff_of_iso _
    (((zmodToSheaf.{u, v} X n).mapDerivedCategory.mapIso e).symm ≪≫ e')).2 ?_
  exact isIso_etaleAbelianDerivedBaseChange_app_toSheaf_of_isKInjective.{u, v} hf sq hn hcd I

end Core

section AffineBase

variable {X X' Y Y' : Scheme.{u}}

/-- **The base change map at an object of `D(X_étale, ℤ/nℤ)`, checked over the affine opens of
`Y'`.** Let cohomology commute with base change for `f`, and for every affine open `V ⊆ Y'` let
the higher direct images of the restriction `f'⁻¹(V) ⟶ V` vanish on torsion abelian sheaves
above some degree. Then the base change map `g^{-1}Rf_*E ⟶ Rf'_*(g')^{-1}E` is an isomorphism
for every object `E` of `D(X_étale, ℤ/nℤ)`, `n > 0`.

This is the first sentence of the proof of the source ("it is enough to prove this when `Y` and
`Y'` are quasi-compact"). Over an affine open `V ⊆ Y'` the base change map restricts to the base
change map of the cartesian square `f'⁻¹(V) ⟶ X` over `V ⟶ Y`, up to the base change map of the
open immersion `V ⟶ Y'`, which is invertible; and invertibility in `D(Y'_étale)` is local. -/
theorem isIso_etaleAbelianDerivedBaseChange_zmod_of_affineOpens {f : X ⟶ Y}
    (hf : CohomologyCommutesWithBaseChange.{u, v} f) {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g) {n : ℕ} (hn : 0 < n)
    (hcd : ∀ V : Y'.affineOpens, ∃ d : ℕ,
      ∀ F : Sheaf (f' ⁻¹ᵁ V.1).toScheme.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
        Stacks.Torsion.torsionSheafProperty (f' ⁻¹ᵁ V.1).toScheme.smallEtaleTopology F →
          ∀ q : ℕ, d < q →
            IsZero (((etaleAbelianDirectImage.{u, v} (f' ∣_ V.1)).rightDerived q).obj F))
    (E : DerivedCategory (SheafOfModules.{max (u + 1) v}
      (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n))) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' sq.w).app
      ((zmodToSheaf.{u, v} X n).mapDerivedCategory.obj E)) := by
  refine isIso_of_isIso_etaleAbelianDerivedInverseImage (fun V : Y'.affineOpens ↦ V.1.ι)
    (fun y ↦ ?_) _ fun V ↦ ?_
  · obtain ⟨_, ⟨V, hV, rfl⟩, hy, -⟩ := Y'.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ y) isOpen_univ
    exact ⟨⟨V, hV⟩, ⟨y, hy⟩, rfl⟩
  let j := V.1.ι
  let jX := (f' ⁻¹ᵁ V.1).ι
  let fV := f' ∣_ V.1
  have hVsq : IsPullback jX fV f' j := (isPullback_morphismRestrict f' V.1).flip
  have outer : IsPullback (jX ≫ g') fV f (j ≫ g) := hVsq.paste_horiz sq
  let K := (zmodToSheaf.{u, v} X n).mapDerivedCategory.obj E
  have hA := etaleAbelianDerivedBaseChange_comp_app.{u, v} g f f' g' j fV jX sq.w hVsq.w
    (j ≫ g) rfl (jX ≫ g') rfl outer.w K
  have := isIso_etaleAbelianDerivedBaseChange_of_isOpenImmersion.{u, v} f' j jX fV hVsq
  have hLHS : IsIso ((etaleAbelianDerivedBaseChange.{u, v} f (j ≫ g) (jX ≫ g') fV
      outer.w).app K) :=
    isIso_etaleAbelianDerivedBaseChange_zmod_of_isZero_rightDerived.{u, v} hf outer hn (hcd V) E
  rw [hA, isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff,
    isIso_comp_right_iff] at hLHS
  exact hLHS

end AffineBase

section Main

variable {X X' Y Y' : Scheme.{u}}

/-- **[Stacks, Tag 0F0C], from Tags 095T and 095U.** Let `f : X ⟶ Y` be a proper morphism of
schemes, `g : Y' ⟶ Y` a morphism, `X' = Y' ×_Y X` with projections `f' : X' ⟶ Y'` and
`g' : X' ⟶ X`, and `n ≥ 1`. Assume

* `h095T`: cohomology commutes with base change for `f` — the proper base change theorem,
  [Stacks, Tag 095T], for `f`; and
* `h095U`: for every proper morphism `p : S ⟶ T` all of whose fibres have dimension at most `N`,
  `R^q p_* F = 0` for every torsion abelian sheaf `F` on `S_étale` and every `q > 2N` — this is
  the statement of [Stacks, Tag 095U].

Then for every object `E` of `D(X_étale, ℤ/nℤ)` — the unbounded derived category of sheaves of
modules over the constant sheaf of rings `ℤ/nℤ` — the base change map (0A2A)
`g^{-1}Rf_*E ⟶ Rf'_*(g')^{-1}E` is an isomorphism.

The base change map of the source is the map (0A2A) in `D(Y'_étale)`; it is applied to `E`
through the forgetful functor `D(X_étale, ℤ/nℤ) ⥤ D(X_étale)`. The proof is the source's: over
an affine, hence quasi-compact, open `V ⊆ Y'` the fibres of the proper morphism `f'⁻¹(V) ⟶ V`
have bounded dimension (Morphisms, Tag 0A3V,
`AlgebraicGeometry.exists_topologicalKrullDim_fiber_le`), so Tag 095U bounds its higher direct
images, and `isIso_etaleAbelianDerivedBaseChange_zmod_of_affineOpens` applies. -/
theorem isIso_etaleAbelianDerivedBaseChange_zmod_of_cohomologyCommutesWithBaseChange
    {f : X ⟶ Y} [IsProper f] (h095T : CohomologyCommutesWithBaseChange.{u, v} f)
    (h095U : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p] (N : ℕ),
      (∀ t : T, topologicalKrullDim (p.fiber t) ≤ N) →
        ∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
          Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F → ∀ q : ℕ, 2 * N < q →
            IsZero (((etaleAbelianDirectImage.{u, v} p).rightDerived q).obj F))
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g) {n : ℕ} (hn : 0 < n)
    (E : DerivedCategory (SheafOfModules.{max (u + 1) v}
      (zmodRingSheaf.{max (u + 1) v} X.smallEtaleTopology n))) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g g' f' sq.w).app
      ((zmodToSheaf.{u, v} X n).mapDerivedCategory.obj E)) := by
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) sq ‹IsProper f›
  refine isIso_etaleAbelianDerivedBaseChange_zmod_of_affineOpens.{u, v} h095T sq hn
    (fun V ↦ ?_) E
  obtain ⟨N, hN⟩ := exists_topologicalKrullDim_fiber_le (f' ∣_ V.1)
  exact ⟨2 * N, fun F hF q hq ↦ h095U (f' ∣_ V.1) N hN F hF q hq⟩

end Main

end Stacks.EtaleCohomology

end
