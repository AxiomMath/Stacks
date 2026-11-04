module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricSmoothModelCoefficientMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricSmoothModelInverseImageNatural

/-!
# Naturality of the restriction to `X_k̄` of a map on `X̄_k̄`

Let `X` be a geometrically connected smooth curve over `k` with compactification `j : X ⟶ X̄`,
`k̄` an algebraic closure and `ψ : R →+* Λ`. A map
`θ : res_ψ((j_! F)|_{X̄_k̄}) ⟶ (j_! G)|_{X̄_k̄}` restricts to
`res_ψ(F|_{X_k̄}) ⟶ G|_{X_k̄}` through the smooth model of `X_k̄`
(`Stacks.EtaleCohomology.compactSupportOpenRestriction`). This file proves that the restriction is
natural in `F`: precomposing `θ` with `res_ψ((j_! v)|_{X̄_k̄})` precomposes its restriction with
`res_ψ(v|_{X_k̄})`.

## Main results

* `Stacks.EtaleCohomology.geometricSmoothModelRestrictScalarsInverseImageIso_hom_naturality`.
* `Stacks.EtaleCohomology.geometricSmoothModelCoefficientMap_precomp`.
* `Stacks.EtaleCohomology.compactSupportOpenRestriction_precomp`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] {R Λ : Type} [Ring R] [Ring Λ] (ψ : R →+* Λ)

/-- **`f̄^{-1} res_ψ((j_! F)|_{X̄_k̄}) ≅ res_ψ(q^{-1} j_! F)` is natural in `F`.** -/
theorem geometricSmoothModelRestrictScalarsInverseImageIso_hom_naturality
    {F F' : EtaleModules.{u, 0} Λ X} (v : F ⟶ F') :
    (etaleModuleInverseImage.{u, 0} R (geometricSmoothModel f j kbar).fb).map
        ((etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).map
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map v))) ≫
        (geometricSmoothModelRestrictScalarsInverseImageIso f j kbar ψ F').hom =
      (geometricSmoothModelRestrictScalarsInverseImageIso f j kbar ψ F).hom ≫
        (etaleModuleRestrictScalars ψ (geometricSmoothModel f j kbar).Vb).map
          ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map v)) := by
  have h1 : (etaleModuleInverseImage.{u, 0} R (geometricSmoothModel f j kbar).fb).map
        ((etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).map
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map v))) ≫
        (etaleModuleInverseImageRestrictScalars ψ (geometricSmoothModel f j kbar).fb).hom.app
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F')) =
      (etaleModuleInverseImageRestrictScalars ψ (geometricSmoothModel f j kbar).fb).hom.app
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ≫
        (etaleModuleRestrictScalars ψ (geometricSmoothModel f j kbar).Vb).map
          ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModel f j kbar).fb).map
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).map
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map v))) :=
    (etaleModuleInverseImageRestrictScalars ψ (geometricSmoothModel f j kbar).fb).hom.naturality _
  have h2 : (etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModel f j kbar).fb).map
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).map
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map v)) ≫
        (selfMapRestrictionIso.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))
          (geometricSmoothModel f j kbar).fb (geometricSmoothModelProj f j kbar) rfl).hom.app
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F') =
      (selfMapRestrictionIso.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))
          (geometricSmoothModel f j kbar).fb (geometricSmoothModelProj f j kbar) rfl).hom.app
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F) ≫
        (etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).map
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map v) :=
    (selfMapRestrictionIso.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))
      (geometricSmoothModel f j kbar).fb (geometricSmoothModelProj f j kbar) rfl).hom.naturality _
  have e : ∀ F₀ : EtaleModules.{u, 0} Λ X,
      (geometricSmoothModelRestrictScalarsInverseImageIso f j kbar ψ F₀).hom =
        (etaleModuleInverseImageRestrictScalars ψ (geometricSmoothModel f j kbar).fb).hom.app
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F₀)) ≫
          (etaleModuleRestrictScalars ψ (geometricSmoothModel f j kbar).Vb).map
            ((selfMapRestrictionIso.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))
              (geometricSmoothModel f j kbar).fb (geometricSmoothModelProj f j kbar) rfl).hom.app
                ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F₀)) := fun _ => rfl
  rw [e, e, reassoc_of% h1, Category.assoc, ← Functor.map_comp, h2, Functor.map_comp]

/-- **`Φ_θ` under precomposition**: `Φ` of `res_ψ((j_! v)|_{X̄_k̄}) ≫ θ'` is
`res_ψ(q^{-1}(j_! v)) ≫ Φ_{θ'}`. -/
theorem geometricSmoothModelCoefficientMap_precomp {F F' : EtaleModules.{u, 0} Λ X} (v : F ⟶ F')
    (G : EtaleModules.{u, 0} R X)
    (θ' : (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F')) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)) :
    geometricSmoothModelCoefficientMap f j kbar ψ F G
        ((etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).map
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map v)) ≫ θ') =
      (etaleModuleRestrictScalars ψ (geometricSmoothModel f j kbar).Vb).map
          ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map v)) ≫
        geometricSmoothModelCoefficientMap f j kbar ψ F' G θ' := by
  have h' : (geometricSmoothModelRestrictScalarsInverseImageIso f j kbar ψ F).inv ≫
      (etaleModuleInverseImage.{u, 0} R (geometricSmoothModel f j kbar).fb).map
        ((etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).map
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map v))) =
      (etaleModuleRestrictScalars ψ (geometricSmoothModel f j kbar).Vb).map
          ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map v)) ≫
        (geometricSmoothModelRestrictScalarsInverseImageIso f j kbar ψ F').inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of%
      (geometricSmoothModelRestrictScalarsInverseImageIso_hom_naturality f j kbar ψ v),
      Iso.hom_inv_id, Category.comp_id]
  rw [geometricSmoothModelCoefficientMap, geometricSmoothModelCoefficientMap, Functor.map_comp,
    Category.assoc, reassoc_of% h']

/-- **The restriction to `X_k̄` is natural in the source**: the restriction of
`res_ψ((j_! v)|_{X̄_k̄}) ≫ θ'` is `res_ψ(v|_{X_k̄})` followed by the restriction of `θ'`. -/
theorem compactSupportOpenRestriction_precomp {F F' : EtaleModules.{u, 0} Λ X} (v : F ⟶ F')
    (G : EtaleModules.{u, 0} R X)
    (θ' : (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F')) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)) :
    compactSupportOpenRestriction f j kbar ψ F G
        ((etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).map
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map v)) ≫ θ') =
      (etaleModuleRestrictScalars ψ (pullback f (specAlgebraMap k kbar))).map
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map v) ≫
        compactSupportOpenRestriction f j kbar ψ F' G θ' := by
  have hl : (geometricSmoothModelInverseImageRestrictionIso f j kbar Λ F).inv ≫
      (etaleModuleRestriction.{u, 0} Λ (geometricSmoothModel f j kbar).j).map
        ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).map
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map v)) =
      (etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map v ≫
        (geometricSmoothModelInverseImageRestrictionIso f j kbar Λ F').inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of%
      (geometricSmoothModelInverseImageRestrictionIso_hom_naturality f j kbar Λ v),
      Iso.hom_inv_id, Category.comp_id]
  have hr := restrictionRestrictScalarsIso_hom_naturality ψ (geometricSmoothModel f j kbar).j
    ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).map
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map v))
  rw [compactSupportOpenRestriction, compactSupportOpenRestriction,
    geometricSmoothModelCoefficientMap_precomp, Functor.map_comp, Category.assoc, ← reassoc_of% hr,
    ← Functor.map_comp_assoc, hl, Functor.map_comp, Category.assoc]

end Stacks.EtaleCohomology

end
