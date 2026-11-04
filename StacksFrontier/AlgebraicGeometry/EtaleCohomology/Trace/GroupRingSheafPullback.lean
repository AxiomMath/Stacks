module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GroupRingSheafRestrict
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafBasePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.RestrictionOfScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Transition

/-!
# Inverse images of the restricted lisse sheaves of group-ring modules

Let `T` be a finite `ℤ[π₁(X, x̄)]`-module killed by `n` with open stabilizers, `ℱ_T` its lisse
sheaf of `ℤ/n`-modules (Tag 0DV5 (3)) and `res_ρ ℱ_T` its restriction of scalars along a ring map
`ρ : Λ → ℤ/n`. For a morphism `f : Y ⟶ X` of connected schemes, a geometric point `ȳ` of `Y` and a
change of base point `t : F_x̄ ≅ F_{f(ȳ)}`, write `φ = φ_t ∘ f_* : π₁(Y, ȳ) → π₁(X, x̄)`. Then
`f⁻¹ res_ρ ℱ_T ≅ res_ρ ℱ_{T|φ}`
(`Stacks.EtaleCohomology.nonempty_inverseImage_restrictScalars_lisseEtaleSheaf_iso`): inverse image
commutes with restriction of scalars, `ℱ_T` built at `x̄` is `ℱ_{T|φ_t}` built at `f(ȳ)`
(`Stacks.EtaleCohomology.nonempty_lisseSheaf_basePointIso`), Tag 0DV6 for lisse sheaves, and the
restriction of the continuous module of `T` is the continuous module of the restriction
(`Stacks.EtaleCohomology.groupRingContinuousModuleResIso`). Moreover `res_ρ ℱ_P` is constructible
for `ρ` surjective
(`Stacks.EtaleCohomology.isBigSiteConstructibleEtaleModule_restrictScalars_lisseEtaleSheaf`) and
killed by `n`.

## Main results

* `Stacks.EtaleCohomology.isBigSiteConstructibleEtaleModule_restrictScalars_lisseEtaleSheaf`.
* `Stacks.EtaleCohomology.nsmul_id_restrictScalars_lisseEtaleSheaf_eq_zero`.
* `Stacks.EtaleCohomology.nonempty_inverseImage_restrictScalars_lisseEtaleSheaf_iso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidAlgebra Stacks.GroupCohomology AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

section Constructible

attribute [local instance] SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- **`res_ρ ℱ_P` is constructible**, for a finite continuous `π₁(X, x̄)`-module `P` over `ℤ/n`
and a surjection `ρ : Λ → ℤ/n` of Noetherian rings: `ℱ_P` is locally constant of finite type. -/
theorem isBigSiteConstructibleEtaleModule_restrictScalars_lisseEtaleSheaf (B : BigEtaleSite.{u})
    (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1) {Λ : Type} [CommRing Λ]
    [IsNoetherianRing Λ] (n : ℕ) [NeZero n] (ρ : Λ →+* ZMod n) (hρ : Function.Surjective ρ)
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 x)) :
    IsBigSiteConstructibleEtaleModule B X Λ
      ((etaleModuleRestrictScalars ρ X.1).obj ((lisseEtaleSheaf B X x (ZMod n)).obj P)) := by
  refine isConstructibleEtaleModule_restrictScalars B X ρ hρ _ ?_
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X (ZMod n)
  exact isConstructibleModuleSheaf_congr B (ZMod n) X
    ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod n))).unitIso.app
      ((lisseSheaf B X x (ZMod n)).obj P))
    (isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant B X (ZMod n) _
      ((finiteTypeLocallyConstantModuleSheafEquivalence B X x (ZMod n)).inverse.obj P).property)

end Constructible

/-- **`res_ρ ℱ_P` is killed by `n`.** -/
theorem nsmul_id_restrictScalars_lisseEtaleSheaf_eq_zero (B : BigEtaleSite.{u})
    (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1) {Λ : Type} [CommRing Λ]
    (n : ℕ) [NeZero n] (ρ : Λ →+* ZMod n)
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 x)) :
    n • 𝟙 ((etaleModuleRestrictScalars ρ X.1).obj
      ((lisseEtaleSheaf B X x (ZMod n)).obj P)) = 0 := by
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul,
    zmodSheaf_nsmul_id X.1.smallEtaleTopology n, Functor.map_zero]

/-- **`f⁻¹ res_ρ ℱ_T ≅ res_ρ ℱ_{T|φ}`** for `φ = φ_t ∘ f_*`. -/
theorem nonempty_inverseImage_restrictScalars_lisseEtaleSheaf_iso (B : BigEtaleSite.{u})
    {X Y : B.Scheme} [ConnectedSpace X.1] [ConnectedSpace Y.1] (f : Y ⟶ X) (y : GeometricPoint Y.1)
    {x : GeometricPoint X.1} (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor (y.map f.hom))
    {Λ : Type} [CommRing Λ] (n : ℕ) [NeZero n] (ρ : Λ →+* ZMod n) (T : Type (u + 1))
    [AddCommGroup T] [Module (MonoidAlgebra ℤ (EtaleFundamentalGroup X.1 x)) T] [Module (ZMod n) T]
    [Finite T] (hT : GroupRingIsContinuous (EtaleFundamentalGroup X.1 x) T) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ f.hom).obj ((etaleModuleRestrictScalars ρ X.1).obj
        ((lisseEtaleSheaf B X x (ZMod n)).obj (groupRingContinuousModule n T hT))) ≅
      (etaleModuleRestrictScalars ρ Y.1).obj ((lisseEtaleSheaf B Y y (ZMod n)).obj
        (groupRingContinuousModule n
          (GroupRingRestrict ((etaleFundamentalGroupBasePointHom t).comp
            (etaleFundamentalGroupMap f.hom y)).toMonoidHom T)
          (groupRingIsContinuous_groupRingRestrict _ hT)))) := by
  let P := groupRingContinuousModule n T hT
  obtain ⟨α⟩ := nonempty_lisseSheaf_basePointIso B X (ZMod n) t
  obtain ⟨β⟩ := nonempty_etaleModuleInverseImage_lisseEtaleSheaf_iso B f y (ZMod n)
    ((finiteTypeContinuousModuleRes (ZMod n) (etaleFundamentalGroupBasePointHom t)).obj P)
  exact ⟨(etaleModuleInverseImageRestrictScalars ρ f.hom).app _ ≪≫
    (etaleModuleRestrictScalars ρ Y.1).mapIso
      ((etaleModuleInverseImage.{u, 0} (ZMod n) f.hom).mapIso
          ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod n))).functor.mapIso
            (α.app P)) ≪≫ β ≪≫
        (lisseEtaleSheaf B Y y (ZMod n)).mapIso (groupRingContinuousModuleResIso n
          ((etaleFundamentalGroupBasePointHom t).comp (etaleFundamentalGroupMap f.hom y)) hT))⟩

end Stacks.EtaleCohomology

end
