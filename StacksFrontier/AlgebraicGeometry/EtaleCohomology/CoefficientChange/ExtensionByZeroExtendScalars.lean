module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.LowerShriekExtendScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.Homology.DerivedCategory.MateDerivedCategory
public import StacksFrontier.CategoryTheory.Adjunction.MateTransport

/-!
# Extension by zero commutes with derived extension of coefficients

Let `φ : Λ₁ → Λ₂` be a homomorphism of commutative rings and `j : U ⟶ X` an étale morphism of
schemes.  The comparison
`Stacks.EtaleCohomology.derivedExtensionByZeroUnboundedExtendScalarsMap`,
`Rj_!(E) ⊗^L_{Λ₁} Λ₂ ⟶ Rj_!(E ⊗^L_{Λ₁} Λ₂)`, built as the mate of the square of extension by
zero and restriction of coefficients, is an isomorphism for every `E` in the unbounded derived
category `D(U_étale, Λ₁)`.  This is the half of the second diagram of [Stacks, Remark 0GL6]
that concerns `Rj_!` in `Rf_! = R(f̄)_* ∘ Rj_!`.

## Main results

* `Stacks.DerivedSquare.rightDerivedExactChangeIso_inv_eq_of_exact`: when the two horizontal
  functors of the square of `Stacks.DerivedSquare.rightDerivedExactChangeIso` are exact too, the
  comparison of derived functors is the derived 2-square of the underived comparison, read
  through the identifications of the right derived functors with the functors induced on
  derived categories.
* `CategoryTheory.TwoSquare.isIso_mapDerivedCategory_natTrans`: the derived 2-square of an
  invertible 2-square of exact functors is invertible.
* `Stacks.EtaleCohomology.isIso_derivedExtensionByZeroUnboundedExtendScalarsMap`: **the
  comparison `Rj_!(E) ⊗^L_{Λ₁} Λ₂ ⟶ Rj_!(E ⊗^L_{Λ₁} Λ₂)` is an isomorphism**, naturally in `E`.

## Implementation notes

No K-flatness enters.  Extension by zero `j_!` and restriction `j^{-1}` are both exact, so the
adjunction `j_! ⊣ j^{-1}` descends to the unbounded derived categories
(`CategoryTheory.Adjunction.mapDerivedCategory`), and so does the square of right adjoints
`j^{-1} ∘ res_φ = res_φ ∘ j^{-1}`, which commutes on the nose
(`Stacks.EtaleCohomology.coefficientPushforwardTwoSquare`).  The square of extension by zero and
restriction of coefficients is by construction the mate of that square
(`Stacks.EtaleCohomology.coefficientPullbackTwoSquare`), and passing to derived categories
carries mates to mates (`CategoryTheory.mateEquiv_mapDerivedCategory`).  The comparison is the
mate of that derived square for the adjunctions `- ⊗^L_{Λ₁} Λ₂ ⊣ res_φ`, hence the iterated
mate of an isomorphism between composites of right adjoints, which is the conjugate of an
isomorphism (`CategoryTheory.iterated_mateEquiv_conjugateEquiv`), hence an isomorphism.

The only non-formal input is the identification of the derived square used to build the
comparison — produced by the uniqueness of right derived functors in
`Stacks.DerivedSquare.rightDerivedExactChangeIso` — with the derived 2-square of the underived
one; that is `Stacks.DerivedSquare.rightDerivedExactChangeIso_inv_eq_of_exact`, checked on the
image of `DerivedCategory.Q` against the units of the right derived functors.

## References

* [Stacks Project, Remark 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Injectives.KInjectiveResolution

universe w w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u r

namespace Stacks.DerivedSquare

section ExactSquare

variable {A₂ : Type u₁} [Category.{v₁} A₂] [Abelian A₂] [HasDerivedCategory.{w₁} A₂]
  [IsGrothendieckAbelian.{w} A₂] {B₂ : Type u₂} [Category.{v₂} B₂] [Abelian B₂]
  [HasDerivedCategory.{w₂} B₂] {A₁ : Type u₃} [Category.{v₃} A₁] [Abelian A₁]
  [HasDerivedCategory.{w₃} A₁] {B₁ : Type u₄} [Category.{v₄} B₁] [Abelian B₁]
  [HasDerivedCategory.{w₄} B₁]
  (F : A₂ ⥤ B₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (F' : A₁ ⥤ B₁) [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  (cA : A₂ ⥤ A₁) [cA.Additive] [PreservesFiniteLimits cA] [PreservesFiniteColimits cA]
  (cB : B₂ ⥤ B₁) [cB.Additive] [PreservesFiniteLimits cB] [PreservesFiniteColimits cB]
  (RF : DerivedCategory A₂ ⥤ DerivedCategory B₂)
  (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ RF)
  (RF' : DerivedCategory A₁ ⥤ DerivedCategory B₁)
  (α' : F'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ RF')
  [RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A₂ (ComplexShape.up ℤ))]
  [RF'.IsRightDerivedFunctor α' (HomologicalComplex.quasiIso A₁ (ComplexShape.up ℤ))]

/-- **For a square of exact functors, the comparison of right derived functors is the derived
2-square of the underived comparison.**  When `F` and `F'` are exact as well as `cA` and `cB`,
the isomorphism `RF ⋙ cB ≅ cA ⋙ RF'` of `Stacks.DerivedSquare.rightDerivedExactChangeIso`,
read through the identifications `RF ≅ F.mapDerivedCategory` and `RF' ≅ F'.mapDerivedCategory`
of the right derived functors of exact functors, is the 2-square
`CategoryTheory.TwoSquare.mapDerivedCategory` of the underived comparison.  Both are morphisms
out of a right derived functor, so they agree as soon as they agree after the unit, on the image
of a complex. -/
theorem rightDerivedExactChangeIso_inv_eq_of_exact (e : F ⋙ cB ≅ cA ⋙ F')
    (hα' : ∀ I : CochainComplex A₂ ℤ, I.IsKInjective →
      IsIso (α'.app ((cA.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :
    (rightDerivedExactChangeIso.{w} F F' cA cB RF α RF' α' e hα').inv =
      Functor.whiskerLeft cA.mapDerivedCategory
          (isoMapDerivedCategoryOfIsRightDerivedFunctor F' RF' α').hom ≫
        (TwoSquare.mk _ _ _ _ e.inv : TwoSquare cA F F' cB).mapDerivedCategory ≫
        Functor.whiskerRight (isoMapDerivedCategoryOfIsRightDerivedFunctor F RF α).inv
          cB.mapDerivedCategory := by
  have := isRightDerivedFunctor_exactChangeUnitDerivedFirst.{w} F cB RF α
  have := isRightDerivedFunctor_exactChangeUnitChangeFirst.{w} F F' cA cB RF' α' e hα'
  refine Functor.rightDerived_ext _ (exactChangeUnitChangeFirst F F' cA cB RF' α' e)
    (HomologicalComplex.quasiIso A₂ (ComplexShape.up ℤ)) _ _ _ ?_
  ext K
  have f₁ : α'.app ((cA.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      (isoMapDerivedCategoryOfIsRightDerivedFunctor F' RF' α').hom.app
        (DerivedCategory.Q.obj ((cA.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) =
      F'.mapDerivedCategoryFactors.inv.app
        ((cA.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
    simp [isoMapDerivedCategoryOfIsRightDerivedFunctor]
  have f₂ : F.mapDerivedCategoryFactors.inv.app K ≫
      (isoMapDerivedCategoryOfIsRightDerivedFunctor F RF α).inv.app (DerivedCategory.Q.obj K) =
      α.app K := by
    simp [isoMapDerivedCategoryOfIsRightDerivedFunctor]
  have f₃ :=
    TwoSquare.mapDerivedCategory_app_Q (TwoSquare.mk _ _ _ _ e.inv : TwoSquare cA F F' cB) K
  have f₄ := (isoMapDerivedCategoryOfIsRightDerivedFunctor F' RF' α').hom.naturality
    (cA.mapDerivedCategoryFactors.inv.app K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    rightDerivedExactChangeIso, Functor.rightDerivedNatIso_inv, Functor.rightDerivedNatTrans_app]
  simp only [Functor.comp_obj] at f₄
  simp only [Iso.refl_inv, NatTrans.id_app, Category.id_comp, exactChangeUnitDerivedFirst,
    exactChangeUnitChangeFirst, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc]
  rw [reassoc_of% f₄, reassoc_of% f₁]
  rw [reassoc_of% f₃, ← Functor.map_comp cB.mapDerivedCategory, f₂,
    ← DerivedCategory.Q.map_comp_assoc, ← DerivedCategory.Q.map_comp_assoc]
  congr 2
  ext i
  simp

end ExactSquare

end Stacks.DerivedSquare

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  {D : Type u₄} [Category.{v₄} D] [Abelian D] [HasDerivedCategory.{w₄} D]

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- The derived 2-square of an invertible 2-square of exact additive functors is invertible:
its transformation is the derived form of an isomorphism, read through two isomorphisms. -/
theorem TwoSquare.isIso_mapDerivedCategory_natTrans {T : A ⥤ B} {L : A ⥤ C} {R : B ⥤ D}
    {Bo : C ⥤ D}
    [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [Bo.Additive] [PreservesFiniteLimits Bo] [PreservesFiniteColimits Bo]
    (α : TwoSquare T L R Bo) [IsIso α] :
    IsIso α.mapDerivedCategory := by
  have : IsIso (NatTrans.mapDerivedCategory α) :=
    ⟨NatTrans.mapDerivedCategory (inv α), by
      rw [← NatTrans.mapDerivedCategory_comp, IsIso.hom_inv_id, NatTrans.mapDerivedCategory_id],
      by rw [← NatTrans.mapDerivedCategory_comp, IsIso.inv_hom_id,
        NatTrans.mapDerivedCategory_id]⟩
  dsimp only [TwoSquare.mapDerivedCategory]
  infer_instance

end CategoryTheory

open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂)
  {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- **Extension by zero commutes with derived extension of coefficients.**  For an étale
morphism `j : U ⟶ X` and a ring map `φ : Λ₁ → Λ₂`, the comparison
`Rj_!(E) ⊗^L_{Λ₁} Λ₂ ⟶ Rj_!(E ⊗^L_{Λ₁} Λ₂)` of
`Stacks.EtaleCohomology.derivedExtensionByZeroUnboundedExtendScalarsMap` is an isomorphism of
functors on the unbounded derived category `D(U_étale, Λ₁)`.

The comparison is the mate, for the adjunctions `- ⊗^L_{Λ₁} Λ₂ ⊣ res_φ`, of the square of
`Rj_!` and restriction of coefficients; that square is the derived 2-square of the underived one
(`Stacks.DerivedSquare.rightDerivedExactChangeIso_inv_eq_of_exact`), whose mate for the
adjunctions `j_! ⊣ j^{-1}` is the identity square of `j^{-1}` and restriction of coefficients.
So the iterated mate of the comparison is the derived form of an identity, an isomorphism, and
an iterated mate is a conjugate, which reflects isomorphisms.

It is an instance, so that each component
`(derivedExtensionByZeroUnboundedExtendScalarsMap φ j).app E`, for `E` in `D(U_étale, Λ₁)`, is
found invertible by instance search. -/
instance isIso_derivedExtensionByZeroUnboundedExtendScalarsMap :
    IsIso (derivedExtensionByZeroUnboundedExtendScalarsMap.{u, r} φ j) := by
  let adj₁ := etaleModuleDerivedExtendRestrictAdj.{u, r} φ U
  let adj₂ := etaleModuleDerivedExtendRestrictAdj.{u, r} φ X
  let ι₁ := etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ₁ j
  let ι₂ := etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ₂ j
  let b₁ := (etaleModuleExtensionByZeroAdj.{u, r} Λ₁ j).mapDerivedCategory
  let b₂ := (etaleModuleExtensionByZeroAdj.{u, r} Λ₂ j).mapDerivedCategory
  let a₁ := b₁.ofNatIsoLeft ι₁.symm
  let a₂ := b₂.ofNatIsoLeft ι₂.symm
  let δ := (coefficientPullbackTwoSquare (Scheme.Etale.smallEtaleCompose j)
    U.smallEtaleTopology X.smallEtaleTopology
    (ModuleCat.restrictScalars.{max (u + 1) r} φ)).mapDerivedCategory
  have hβ : mateEquiv a₂ a₁ (TwoSquare.mk _ _ _ _
      (etaleModuleDerivedExtensionByZeroUnboundedRestrictScalarsIso.{u, r} φ j).inv) =
      mateEquiv b₂ b₁ δ :=
    mateEquiv_ofNatIsoLeft b₂ b₁ ι₂.symm ι₁.symm δ _ fun Y => by
      have h := congrArg (fun t => NatTrans.app t Y)
        (Stacks.DerivedSquare.rightDerivedExactChangeIso_inv_eq_of_exact
          (etaleModuleExtensionByZero.{u, r} Λ₂ j) (etaleModuleExtensionByZero.{u, r} Λ₁ j)
          (etaleModuleRestrictScalarsUniv.{u, r} φ U) (etaleModuleRestrictScalarsUniv.{u, r} φ X)
          (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ₂ j)
          (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ₂ j)
          (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ₁ j)
          (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ₁ j)
          (etaleModuleExtensionByZeroRestrictScalarsIso.{u, r} φ j)
          (fun I _ => Stacks.DerivedSquare.isIso_rightDerivedUnit_app_of_exact
            (etaleModuleExtensionByZero.{u, r} Λ₁ j)
            (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ₁ j)
            (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ₁ j) _))
      exact h
  have hδ : mateEquiv b₂ b₁ δ = (coefficientPushforwardTwoSquare
      (Scheme.Etale.smallEtaleCompose j) U.smallEtaleTopology X.smallEtaleTopology
      (ModuleCat.restrictScalars.{max (u + 1) r} φ)).mapDerivedCategory := by
    refine (mateEquiv_mapDerivedCategory _ _ _).trans ?_
    exact congrArg (fun t => TwoSquare.mapDerivedCategory t)
      (mateEquiv_coefficientPullbackTwoSquare (Scheme.Etale.smallEtaleCompose j)
        U.smallEtaleTopology X.smallEtaleTopology (ModuleCat.restrictScalars.{max (u + 1) r} φ))
  have key := iterated_mateEquiv_conjugateEquiv adj₁ adj₂ a₁ a₂
    ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _
      (etaleModuleDerivedExtensionByZeroUnboundedRestrictScalarsIso.{u, r} φ j).inv))
  rw [Equiv.apply_symm_apply, hβ, hδ] at key
  have hid : IsIso (coefficientPushforwardTwoSquare
      (Scheme.Etale.smallEtaleCompose j) U.smallEtaleTopology X.smallEtaleTopology
      (ModuleCat.restrictScalars.{max (u + 1) r} φ)) :=
    IsIso.id _
  have hiso := TwoSquare.isIso_mapDerivedCategory_natTrans (coefficientPushforwardTwoSquare
      (Scheme.Etale.smallEtaleCompose j) U.smallEtaleTopology X.smallEtaleTopology
      (ModuleCat.restrictScalars.{max (u + 1) r} φ))
  rw [key] at hiso
  have : IsIso (conjugateEquiv (adj₁.comp a₂) (a₁.comp adj₂)
      (derivedExtensionByZeroUnboundedExtendScalarsMap.{u, r} φ j)) := hiso
  exact conjugateEquiv_of_iso (adj₁.comp a₂) (a₁.comp adj₂) _

end Stacks.EtaleCohomology

end
