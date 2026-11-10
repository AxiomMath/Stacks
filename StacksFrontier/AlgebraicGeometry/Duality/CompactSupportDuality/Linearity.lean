module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactSupportDuality.BaseLinear
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsLinear
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomLinearSource
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualityPairing
public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethDegreeZeroHom

/-!
# `k`-linearity of the identifications used for duality with compact support

Let `X` be a scheme over a field `k`, with the canonical `k`-linear structure
`AlgebraicGeometry.modulesLinear` on `𝒪_X`-modules and on `D(𝒪_X)`.

## Main definitions

* `AlgebraicGeometry.schemeDerivedDualFunctor`: the contravariant functor `R𝓗om_{𝒪_X}(-, M)` on
  `D(𝒪_X)`.
* `AlgebraicGeometry.structureSheafHomAddEquiv`: `Hom_{D(𝒪_X)}(𝒪_X, E) ≃ H^0(X, E)` as abelian
  groups, the right-hand side being the cohomology of the `k`-linear derived global sections
  `AlgebraicGeometry.derivedGlobalSectionsOver`.
* `AlgebraicGeometry.structureSheafHomLinearEquiv`: the same identification, `k`-linearly.

## Main results

* `AlgebraicGeometry.schemeDerivedDualFunctor_map_smul_id`: `R𝓗om(-, M)` carries multiplication
  by a scalar to multiplication by that scalar.
* `AlgebraicGeometry.structureSheafHomAddEquiv_comp`: `Hom(𝒪_X, E) ≃ H^0(X, E)` is natural in `E`.

## Implementation notes

The derived categories are at `CategoryTheory.HasDerivedCategory.standard`, named in each
statement by `letI`.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k))

/-- `R𝓗om_{𝒪_X}(-, M)` as a contravariant functor on `D(𝒪_X)`, in the scheme's spelling of
`𝒪_X`-modules. On objects it is `AlgebraicGeometry.RingedSite.derivedDualInto`. -/
def schemeDerivedDualFunctor {X : Scheme.{u}}
    (M : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules)) :
    letI := HasDerivedCategory.standard X.Modules
    (DerivedCategory X.Modules)ᵒᵖ ⥤ DerivedCategory X.Modules :=
  letI := HasDerivedCategory.standard X.Modules
  letI := HasDerivedCategory.standard (SheafOfModules
    (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O))
  (RingedSite.derivedSheafHomBifunctor (Stacks.SheafOfModules.ringedSite X.sheaf)).flip.obj M

/-- **`R𝓗om(-, M)` carries multiplication by a base scalar to multiplication by that scalar.** -/
theorem schemeDerivedDualFunctor_map_smul_id
    (K M : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules)) (a : k) :
    letI := HasDerivedCategory.standard X.Modules
    letI : Linear k X.Modules := modulesLinear k (Over.mk q)
    (schemeDerivedDualFunctor M).map (a • 𝟙 K).op =
      a • 𝟙 ((schemeDerivedDualFunctor M).obj (op K)) := by
  let _ := HasDerivedCategory.standard X.Modules
  let _ := HasDerivedCategory.standard (SheafOfModules
    (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O))
  let : Linear k X.Modules := modulesLinear k (Over.mk q)
  let : Linear (CatCenter X.Modules) X.Modules := linearCatCenterModules (Over.mk q)
  let b : CatCenter X.Modules := baseCatCenter (Over.mk q) a
  have hD : ∀ {Y Z : DerivedCategory X.Modules} (g : Y ⟶ Z), a • g = b • g := fun {_ _} g =>
    smul_eq_of_toCatCenter_eq (C := X.Modules) a b
      (toCatCenter_eq_globalSectionToEnd (Over.mk q) a) g
  have h := RingedSite.derivedSheafHom_map_globalSectionToEnd_source
    (Stacks.SheafOfModules.ringedSite X.sheaf) (baseSectionFamily (Over.mk q) a) K M
  calc (schemeDerivedDualFunctor M).map (a • 𝟙 K).op
      = (schemeDerivedDualFunctor M).map (b • 𝟙 K).op := by rw [hD (𝟙 K)]
    _ = b • 𝟙 ((schemeDerivedDualFunctor M).obj (op K)) := h
    _ = a • 𝟙 ((schemeDerivedDualFunctor M).obj (op K)) := (hD (𝟙 _)).symm

/-! ### Morphisms out of the structure sheaf -/

open Stacks.AlgebraicGeometry.ProperSupportCoherent in
/-- `Hom_{D(𝒪_X)}(𝒪_X, E) ≃ H^0(X, E)` as abelian groups: Stacks 08JA at the structure sheaf
(`AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv`), read against the
`k`-linear derived global sections. -/
def structureSheafHomAddEquiv
    (E : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules)) :
    letI := HasDerivedCategory.standard X.Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} k)
    (derivedUnitObject X ⟶ E) ≃+
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
        ((derivedGlobalSectionsOver q).obj E) : Type u) :=
  letI := HasDerivedCategory.standard X.Modules
  letI := HasDerivedCategory.standard (ModuleCat.{u} k)
  (structureSheafGlobalSectionsEquivScheme k (Over.mk q) E).symm.trans
    (homologyZeroForgetIso q E).addCommGroupIsoToAddEquiv.symm

open Stacks.AlgebraicGeometry.ProperSupportCoherent in
/-- **Naturality of `Hom(𝒪_X, E) = H^0(X, E)` in `E`**: postcomposition with `φ` is the map
induced by `φ` on cohomology. -/
theorem structureSheafHomAddEquiv_comp
    {E E' : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules)}
    (s : letI := HasDerivedCategory.standard X.Modules; derivedUnitObject X ⟶ E)
    (φ : E ⟶ E') :
    letI := HasDerivedCategory.standard X.Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} k)
    structureSheafHomAddEquiv q E' (s ≫ φ) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
        ((derivedGlobalSectionsOver q).map φ)).hom (structureSheafHomAddEquiv q E s) := by
  let _ := HasDerivedCategory.standard X.Modules
  let _ := HasDerivedCategory.standard (ModuleCat.{u} k)
  let _ := HasDerivedCategory.standard AddCommGrpCat.{u}
  let _ := HasDerivedCategory.standard (SheafOfModules
    (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O))
  apply (homologyZeroForgetIso q E').addCommGroupIsoToAddEquiv.injective
  change (homologyZeroForgetIso q E').hom ((homologyZeroForgetIso q E').inv
      ((structureSheafGlobalSectionsEquivScheme k (Over.mk q) E').symm (s ≫ φ))) =
    (homologyZeroForgetIso q E').hom
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
        ((derivedGlobalSectionsOver q).map φ)).hom (structureSheafHomAddEquiv q E s))
  rw [Iso.inv_hom_id_apply]
  have key := ((CategoryTheory.comp_apply
      ((derivedGlobalSectionsOver q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0 ⋙
        forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).map φ)
      ((homologyZeroForgetNatIso q).hom.app E') (structureSheafHomAddEquiv q E s)).symm.trans
    (ConcreteCategory.congr_hom ((homologyZeroForgetNatIso q).hom.naturality φ)
      (structureSheafHomAddEquiv q E s))).trans
    (CategoryTheory.comp_apply ((homologyZeroForgetNatIso q).hom.app E)
      ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
        (Stacks.SheafOfModules.ringedSite X.sheaf) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map φ)
      (structureSheafHomAddEquiv q E s))
  refine Eq.trans ?_ key.symm
  apply (structureSheafGlobalSectionsEquivScheme k (Over.mk q) E').injective
  refine (AddEquiv.apply_symm_apply _ _).trans ?_
  refine Eq.trans ?_ (RingedSite.derivedStructureSheafGlobalSectionsEquiv_naturality
    (Stacks.SheafOfModules.ringedSite X.sheaf) φ _).symm
  congr 1
  exact ((congrArg (structureSheafGlobalSectionsEquivScheme k (Over.mk q) E)
    (Iso.inv_hom_id_apply (homologyZeroForgetIso q E) _)).trans
      (AddEquiv.apply_symm_apply _ _)).symm

/-- **`Hom_{D(𝒪_X)}(𝒪_X, E) = H^0(X, E)` as `k`-vector spaces**, for the canonical `k`-linear
structure `AlgebraicGeometry.modulesLinear` on the left. -/
def structureSheafHomLinearEquiv
    (E : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules)) :
    letI := HasDerivedCategory.standard X.Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} k)
    letI : Linear k X.Modules := modulesLinear k (Over.mk q)
    (derivedUnitObject X ⟶ E) ≃ₗ[k]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
        ((derivedGlobalSectionsOver q).obj E) : Type u) :=
  letI := HasDerivedCategory.standard X.Modules
  letI := HasDerivedCategory.standard (ModuleCat.{u} k)
  letI : Linear k X.Modules := modulesLinear k (Over.mk q)
  { structureSheafHomAddEquiv q E with
    map_smul' := fun a s => by
      change structureSheafHomAddEquiv q E (a • s) = a • structureSheafHomAddEquiv q E s
      have hs : a • s = s ≫ (a • 𝟙 E) := by rw [Linear.comp_smul, Category.comp_id]
      have hΓ : (derivedGlobalSectionsOver q).map (a • 𝟙 E) =
          a • 𝟙 ((derivedGlobalSectionsOver q).obj E) :=
        _root_.AlgebraicGeometry.derivedGlobalSectionsOver_map_smul_id (X := Over.mk q) a E
      rw [hs, structureSheafHomAddEquiv_comp, hΓ, Functor.Linear.map_smul,
        CategoryTheory.Functor.map_id]
      rfl }

end AlgebraicGeometry

end
