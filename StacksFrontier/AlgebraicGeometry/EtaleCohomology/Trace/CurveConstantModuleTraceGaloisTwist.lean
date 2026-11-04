module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantModuleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceGaloisTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralSelfMapCohomologySheafH
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantTwistComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantSelfMapTwistRestriction

/-!
# The trace of a constant sheaf of modules under a semilinear automorphism of the curve

Let `C` be a smooth proper curve over an algebraically closed field `K`, `Λ` a finite ring with
`#Λ` invertible in `K`, `ζ ∈ K` a primitive `#Λ`-th root of unity and `E` a finite `Λ`-module.
Let `s : C ⟶ C` be an automorphism lying over `Spec τ` for a field automorphism `τ` of `K`.
The constant sheaf `E_C` carries its canonical map `E_C ⟶ s_* E_C` (adjoint to
`s^{-1} E_C ≅ E_C`), so `s` acts on `H²(C, E_C)` by pullback
(`Stacks.EtaleCohomology.integralSelfMapCohomologyEndo`). This file proves that the trace
`τ_ζ : H²(C, E_C) ≅ E` of `Stacks.EtaleCohomology.curveConstantModuleTrace` satisfies
`τ_{τ(ζ)}(s^* y) = τ_ζ(y)`.

The proof reads the action on the cohomology of the underlying abelian sheaf
(`Stacks.EtaleCohomology.etaleModuleCohomologyAddEquivSheafH_integralSelfMapCohomologyEndo`),
identifies the twist there with the canonical comparison `s^{-1} E_C ≅ E_C` of constant abelian
sheaves (`Stacks.EtaleCohomology.inverseImage_underlyingConstantSheafIso_comp_constantIso`), and
concludes with the abelian statement
`Stacks.EtaleCohomology.etaleConstantCohomologyPullback_curveConstantClass_of_twist`.

This is an input of [Stacks, Tag 03VK]: the Galois action on `H²_c(X_k̄, F)` is read through the
trace on the smooth projective model.

## Main results

* `Stacks.EtaleCohomology.inverseImage_underlyingConstantSheafIso_comp_constantIso`.
* `Stacks.EtaleCohomology.curveConstantModuleTrace_integralSelfMapCohomologyEndo_of_twist`.

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.EtaleCohomology

/-- `etaleModules_enoughInjectives` at the coefficient universe `0`. -/
local instance etaleModulesEnoughInjectivesZeroTraceTwist (Λ : Type) [Ring Λ] (Y : Scheme.{u}) :
    EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

section Sections

variable {Λ : Type} [Ring Λ] (Y : Scheme.{u})

/-- **Forgetting the module structure carries constant sections to constant sections**: the
comparison `U(E_Y) ≅ (U E)_Y` sends the image of the constant section of `E` over `V` to the
constant section of the underlying abelian group. -/
theorem forget₂_constantSheafSection_comp_constantSheafForget₂Iso (E : ModuleCat.{u + 1} Λ)
    (V : Y.Etale) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        (constantSheafSection Λ E V) ≫
      ((Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} Λ Y.smallEtaleTopology).hom.app
        E).hom.app (op V) =
    Stacks.ConstantSheaf.constantSheafSection Y.smallEtaleTopology AddCommGrpCat.{u + 1}
      ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj E) V := by
  have := ModuleSheaf.preservesSheafification_forget₂.{u + 1} Λ Y.smallEtaleTopology
  rw [Stacks.ModuleCatLift.constantSheafForget₂Iso_hom_app_hom, NatTrans.comp_app]
  have h1 := congrArg (fun t => t.app (op V))
    (sheafComposeIso_inv_fac Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ((Functor.const Y.Etaleᵒᵖ).obj E))
  have h2 := congrArg (fun t => t.app (op V))
    (toSheafify_naturality Y.smallEtaleTopology
      (Functor.constComp Y.Etaleᵒᵖ E (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).hom)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at h1 h2
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans
    (h2.symm.trans (Category.id_comp _)))

/-- **The comparison `U(E_Y) ≅ E₀,Y` carries constant sections to constant sections**, `E₀` a copy
of the abelian group underlying `E`. -/
theorem forget₂_constantSheafSection_comp_underlyingConstantSheafIso (E : ModuleCat.{u + 1} Λ)
    {E₀ : Type} [AddCommGroup E₀] (e : E ≃+ E₀) (V : Y.Etale) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        (constantSheafSection Λ E V) ≫ (underlyingConstantSheafIso Y E e).hom.hom.app (op V) =
      (AddEquiv.toAddCommGrpIso (X := AddCommGrpCat.of E) (Y := AddCommGrpCat.of (ULift.{u + 1} E₀))
        (e.trans (AddEquiv.ulift.{0, u + 1} (α := E₀)).symm)).hom ≫
        Stacks.ConstantSheaf.constantSheafSection Y.smallEtaleTopology AddCommGrpCat.{u + 1}
          (AddCommGrpCat.of (ULift.{u + 1} E₀)) V := by
  have hA := forget₂_constantSheafSection_comp_constantSheafForget₂Iso Y E V
  have h := congrArg (fun t => t.app (op V))
    (toSheafify_naturality Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).map
      (AddEquiv.toAddCommGrpIso (X := AddCommGrpCat.of E) (Y := AddCommGrpCat.of (ULift.{u + 1} E₀))
        (e.trans (AddEquiv.ulift.{0, u + 1} (α := E₀)).symm)).hom))
  simp only [NatTrans.comp_app, Functor.const_map_app] at h
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hA).trans h.symm)

end Sections

section Transpose

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- **The transpose of a map out of an inverse image, read on underlying abelian sheaves.** For a
map `β : M ⟶ g_* M'` of sheaves of abelian groups (as `ℤ`-modules), the map
`g^{-1}(U M) ≅ U(g^{-1} M) ⟶ U M'` induced by the adjoint `g^{-1}β ≫ ε` transposes, under
`g^{-1} ⊣ g_*` for abelian sheaves, to `U β`. -/
theorem etaleAbelianInverseImageDirectImageAdj_homEquiv_underlyingAbelian
    (M : EtaleModules.{u, 0} ℤ X) (M' : EtaleModules.{u, 0} ℤ Y)
    (β : M ⟶ (etaleModuleDirectImage.{u, 0} ℤ g).obj M') :
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} g).homEquiv
        ((etaleModuleUnderlyingAbelian X ℤ).obj M) ((etaleModuleUnderlyingAbelian Y ℤ).obj M')
        ((etaleModuleUnderlyingAbelianInverseImageIso ℤ g).hom.app M ≫
          (etaleModuleUnderlyingAbelian Y ℤ).map
            ((etaleModuleInverseImage.{u, 0} ℤ g).map β ≫
              (etaleModuleInverseImageAdj.{u, 0} ℤ g).counit.app M')) =
      (etaleModuleUnderlyingAbelian X ℤ).map β := by
  have h := ((etaleModuleInverseImageAdj.{u, 0} ℤ g).homEquiv M M').apply_symm_apply β
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit] at h
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  refine (congrArg (· ≫ _)
    (etaleModuleUnderlyingAbelianInverseImageIso_unit' ℤ g M).symm).trans ?_
  exact (Functor.map_comp (etaleModuleUnderlyingAbelian X ℤ)
    ((etaleModuleInverseImageAdj.{u, 0} ℤ g).unit.app M)
    ((etaleModuleDirectImage.{u, 0} ℤ g).map ((etaleModuleInverseImage.{u, 0} ℤ g).map β ≫
      (etaleModuleInverseImageAdj.{u, 0} ℤ g).counit.app M'))).symm.trans (congrArg _ h)

end Transpose

section Twist

variable {Λ : Type} [Ring Λ] {Y : Scheme.{u}} (s : Y ⟶ Y)

/-- The form of `inverseImage_underlyingConstantSheafIso_comp_constantIso` with the comparison
moved to the source. -/
theorem inverseImage_underlyingConstantSheafIso_inv_comp_twist (E : ModuleCat.{u + 1} Λ)
    {E₀ : Type} [AddCommGroup E₀] (e : E ≃+ E₀) :
    (etaleAbelianInverseImage.{u, 0} s).map (underlyingConstantSheafIso Y E e).inv ≫
        ((etaleModuleUnderlyingAbelianInverseImageIso ℤ s).hom.app
            ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj
              (etaleModuleConstantSheaf Λ E Y)) ≫
          (etaleModuleUnderlyingAbelian Y ℤ).map
            ((etaleModuleInverseImage.{u, 0} ℤ s).map
                ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).map
                  (constantSelfMapTwist Λ E s)) ≫
              (etaleModuleInverseImageAdj.{u, 0} ℤ s).counit.app
                ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj
                  (etaleModuleConstantSheaf Λ E Y)))) ≫
        (underlyingConstantSheafIso Y E e).hom =
      (etaleAbelianInverseImageConstantIso.{u, 0} s).hom.app
        (AddCommGrpCat.of (ULift.{u + 1} E₀)) := by
  apply (((constantSheafAdj _ _ (etaleSiteTerminalIsTerminal Y)).comp
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} s)).homEquiv _ _).injective
  rw [homEquiv_etaleAbelianInverseImageConstantIso, constantSheaf_comp_homEquiv_apply.{u, 0},
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  refine (congrArg (fun t => Stacks.ConstantSheaf.constantSheafSection Y.smallEtaleTopology
      AddCommGrpCat.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} E₀)) (etaleSiteTerminal Y) ≫
        ((underlyingConstantSheafIso Y E e).inv ≫ t ≫
          (etaleAbelianDirectImage.{u, 0} s).map (underlyingConstantSheafIso Y E e).hom).hom.app
          (op (etaleSiteTerminal Y)))
    (etaleAbelianInverseImageDirectImageAdj_homEquiv_underlyingAbelian s
      ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj (etaleModuleConstantSheaf Λ E Y))
      ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj (etaleModuleConstantSheaf Λ E Y))
      ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).map
        (constantSelfMapTwist Λ E s)))).trans ?_
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  show _ ≫ _ ≫ ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
      ((constantSelfMapTwist Λ E s).hom.app (op (etaleSiteTerminal Y))) ≫
    (underlyingConstantSheafIso Y E e).hom.hom.app
      (op ((smallEtaleBaseChange s).obj (etaleSiteTerminal Y)))) = _
  have hT := forget₂_constantSheafSection_comp_underlyingConstantSheafIso Y E e
    (etaleSiteTerminal Y)
  have hT' := forget₂_constantSheafSection_comp_underlyingConstantSheafIso Y E e
    ((smallEtaleBaseChange s).obj (etaleSiteTerminal Y))
  have hα := congrArg (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
    (constantSheafSection_comp_constantSelfMapTwist Λ E s)
  rw [Functor.map_comp] at hα
  have hu : (underlyingConstantSheafIso Y E e).hom.hom.app (op (etaleSiteTerminal Y)) ≫
      (underlyingConstantSheafIso Y E e).inv.hom.app (op (etaleSiteTerminal Y)) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id]
    rfl
  have hcs : Stacks.ConstantSheaf.constantSheafSection Y.smallEtaleTopology AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} E₀)) (etaleSiteTerminal Y) ≫
      (underlyingConstantSheafIso Y E e).inv.hom.app (op (etaleSiteTerminal Y)) =
      (AddEquiv.toAddCommGrpIso (X := AddCommGrpCat.of E) (Y := AddCommGrpCat.of (ULift.{u + 1} E₀))
        (e.trans (AddEquiv.ulift.{0, u + 1} (α := E₀)).symm)).inv ≫
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
          (constantSheafSection Λ E (etaleSiteTerminal Y)) := by
    rw [← Iso.inv_comp_eq] at hT
    exact (congrArg (· ≫ _) hT.symm).trans ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) hu).trans (Category.comp_id _)))))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hcs).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) hα).trans hT'))).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) (Iso.inv_hom_id _)).trans (Category.id_comp _))))))

/-- **The canonical map `E_Y ⟶ s_* E_Y`, read on underlying abelian sheaves, is the comparison
`s^{-1} E₀,Y ≅ E₀,Y` of constant abelian sheaves.** Precisely: the map
`s^{-1}(U E_Y) ⟶ U E_Y` adjoint to `U` of the canonical map (the map entering
`Stacks.EtaleCohomology.etaleModuleCohomologyAddEquivSheafH_integralSelfMapCohomologyEndo`) is
carried by `U E_Y ≅ E₀,Y` to `Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso`. -/
theorem inverseImage_underlyingConstantSheafIso_comp_constantIso (E : ModuleCat.{u + 1} Λ)
    {E₀ : Type} [AddCommGroup E₀] (e : E ≃+ E₀) :
    (etaleAbelianInverseImage.{u, 0} s).map (underlyingConstantSheafIso Y E e).hom ≫
        (etaleAbelianInverseImageConstantIso.{u, 0} s).hom.app
          (AddCommGrpCat.of (ULift.{u + 1} E₀)) =
      ((etaleModuleUnderlyingAbelianInverseImageIso ℤ s).hom.app
            ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj
              (etaleModuleConstantSheaf Λ E Y)) ≫
          (etaleModuleUnderlyingAbelian Y ℤ).map
            ((etaleModuleInverseImage.{u, 0} ℤ s).map
                ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).map
                  (constantSelfMapTwist Λ E s)) ≫
              (etaleModuleInverseImageAdj.{u, 0} ℤ s).counit.app
                ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj
                  (etaleModuleConstantSheaf Λ E Y)))) ≫
        (underlyingConstantSheafIso Y E e).hom := by
  rw [← inverseImage_underlyingConstantSheafIso_inv_comp_twist s E e, ← Category.assoc,
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

end Twist

section Trace

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] [Smooth q] [IsProper q] (Λ : Type) [Ring Λ] [Fintype Λ]
  (hn : IsUnit ((Fintype.card Λ : ℕ) : K)) {ζ : K} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))

/-- **The trace of a constant sheaf under a semilinear automorphism of the curve.** Let
`s : C ⟶ C` be an automorphism lying over `Spec τ`, `τ` a field automorphism of `K`, acting on
`H²(C, E_C)` by pullback through the canonical map `E_C ⟶ s_* E_C`. Then the trace through
`τ(ζ)` of `s^* y` is the trace through `ζ` of `y`: `τ_{τ(ζ)}(s^* y) = τ_ζ(y)`. -/
theorem curveConstantModuleTrace_integralSelfMapCohomologyEndo_of_twist (s : C ⟶ C) [IsIso s]
    (τ : K ≃+* K) (hs : s ≫ q = q ≫ Spec.map (CommRingCat.ofHom τ.toRingHom))
    (E : ModuleCat.{u + 1} Λ) [Finite E]
    (y : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)) :
    curveConstantModuleTrace q Λ hn (hζ.map_of_injective τ.injective) E
        ((integralSelfMapCohomologyEndo Λ s
          ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)
          (constantSelfMapTwist Λ E s) ((2 : ℕ) : ℤ)).hom y) =
      curveConstantModuleTrace q Λ hn hζ E y := by
  have hBR := etaleModuleCohomologyAddEquivSheafH_integralSelfMapCohomologyEndo s
    ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)
    (constantSelfMapTwist Λ E s) 2 y
  have hmap := etaleCohomologyMapTo_comp_mk₀ s
    (underlyingConstantSheafIso C E Shrink.addEquiv.symm).hom _ _
    (underlyingConstantSheafIso C E Shrink.addEquiv.symm).hom
    (inverseImage_underlyingConstantSheafIso_comp_constantIso s E Shrink.addEquiv.symm) 2
    (etaleModuleCohomologyAddEquivSheafH C _ 2 y)
  have hpull : sheafHAddEquivOfIso (underlyingConstantSheafIso C E Shrink.addEquiv.symm) 2
        (etaleModuleCohomologyAddEquivSheafH C _ 2 ((integralSelfMapCohomologyEndo Λ s
          ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)
          (constantSelfMapTwist Λ E s) ((2 : ℕ) : ℤ)).hom y)) =
      etaleConstantCohomologyPullback s (Shrink.{0} E) 2
        (sheafHAddEquivOfIso (underlyingConstantSheafIso C E Shrink.addEquiv.symm) 2
          (etaleModuleCohomologyAddEquivSheafH C _ 2 y)) := by
    rw [sheafHAddEquivOfIso_apply, sheafHAddEquivOfIso_apply, hBR]
    exact hmap.symm
  show curveConstantModuleTraceAddEquiv q Λ hn _ E _ =
    curveConstantModuleTraceAddEquiv q Λ hn hζ E y
  simp only [curveConstantModuleTraceAddEquiv, AddEquiv.trans_apply]
  rw [hpull]
  obtain ⟨φ, hφ⟩ := (bijective_curveConstantClass q hn hζ
    (shrink_card_nsmul_eq_zero Λ E)).2
    (sheafHAddEquivOfIso (underlyingConstantSheafIso C E Shrink.addEquiv.symm) 2
      (etaleModuleCohomologyAddEquivSheafH C _ 2 y))
  rw [← hφ, etaleConstantCohomologyPullback_curveConstantClass_of_twist q hn hζ s τ hs]
  have key : ∀ {ζ' : K} (h : IsPrimitiveRoot ζ' (Fintype.card Λ)),
      (AddEquiv.ofBijective (curveConstantClass q hn h (Shrink.{0} E))
        (bijective_curveConstantClass q hn h (shrink_card_nsmul_eq_zero Λ E))).symm
        (curveConstantClass q hn h (Shrink.{0} E) φ) = φ := fun h =>
    (AddEquiv.ofBijective _ _).symm_apply_apply φ
  rw [key hζ, key (hζ.map_of_injective τ.injective)]

section Boundary

variable {U : Scheme.{u}} (jC : U ⟶ C) [IsOpenImmersion jC]
  (hfin : ((Set.range jC.base)ᶜ).Finite)

omit [IsCurve K q] [Smooth q] [IsProper q] [Fintype Λ] in
/-- The map on `H²` induced by the counit `j_! j^{-1} E_C ⟶ E_C`, written with the index `2` as a
literal or as the cast of `2 : ℕ`. -/
private theorem counitTwoIndex_apply (E : ModuleCat.{u + 1} Λ)
    (z : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj
          ((etaleModuleRestriction.{u, 0} Λ jC).obj (etaleModuleConstantSheaf Λ E C)))) :
    (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus 2).map
            ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app
              ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))).hom z =
    (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
            ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app
              ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))).hom z := rfl

omit [IsCurve K q] [Smooth q] [IsProper q] in
/-- `Stacks.EtaleCohomology.curveExtensionByZeroConstantTrace` is the trace of `E_C` after the
map `H²(C, j_!(E_U)) ⟶ H²(C, E_C)` induced by `j_! E_U ≅ j_! j^{-1} E_C ⟶ E_C`. -/
theorem curveExtensionByZeroConstantTrace_apply [IsCurve K q] [Smooth q] [IsProper q]
    (E : ModuleCat.{u + 1} Λ) [Finite E]
    (y : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj
          ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))) :
    curveExtensionByZeroConstantTrace q Λ hn hζ jC hfin E y =
      curveConstantModuleTrace q Λ hn hζ E
        ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app
            ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))).hom
          ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
            ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
              (((etaleModuleInverseImageConstantIso.{u, 0} Λ jC).app E).symm.hom ≫
                ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ jC).app
                  ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)).hom))).hom
            y)) := by
  simp only [curveExtensionByZeroConstantTrace, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply,
    Iso.trans_hom, Functor.mapIso_hom, asIso_hom, ModuleCat.hom_comp, LinearMap.comp_apply]
  refine congrArg (curveConstantModuleTrace q Λ hn hζ E) ?_
  exact counitTwoIndex_apply Λ jC E _

/-- **The trace of `j_!(E_U)` under a semilinear automorphism of the curve.** Let `s : C ⟶ C` be
an automorphism lying over `Spec τ` which preserves the open `U` (`s_U ≫ j = j ≫ s` cartesian).
It acts on `H²(C, j_!(E_U))` through the extension by zero `j_!(E_U ⟶ s_{U,*} E_U) ≫
(j_! s_{U,*} ⟶ s_* j_!)` of the canonical twist of `E_U`. Then the trace
`H²(C, j_!(E_U)) ≅ E` through `τ(ζ)` of `s^* y` is the trace through `ζ` of `y`. -/
theorem curveExtensionByZeroConstantTrace_integralSelfMapCohomologyEndo_of_twist (sU : U ⟶ U)
    (s : C ⟶ C) [IsIso s] (sq : IsPullback sU jC jC s) (τ : K ≃+* K)
    (hs : s ≫ q = q ≫ Spec.map (CommRingCat.ofHom τ.toRingHom))
    (E : ModuleCat.{u + 1} Λ) [Finite E]
    (y : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj
          ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))) :
    curveExtensionByZeroConstantTrace q Λ hn (hζ.map_of_injective τ.injective) jC hfin E
        ((integralSelfMapCohomologyEndo Λ s
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj (etaleModuleConstantSheaf Λ E U))
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map (constantSelfMapTwist Λ E sU) ≫
            extensionByZeroIntegralDirectImageMap Λ jC jC sU s sq
              (etaleModuleConstantSheaf Λ E U)) ((2 : ℕ) : ℤ)).hom y) =
      curveExtensionByZeroConstantTrace q Λ hn hζ jC hfin E y := by
  have hnat := integralSelfMapCohomologyEndo_naturality Λ s
    (N' := (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)
    ((etaleModuleExtensionByZero.{u, 0} Λ jC).map (constantSelfMapTwist Λ E sU) ≫
      extensionByZeroIntegralDirectImageMap Λ jC jC sU s sq (etaleModuleConstantSheaf Λ E U))
    (constantSelfMapTwist Λ E s)
    ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
        (((etaleModuleInverseImageConstantIso.{u, 0} Λ jC).app E).symm.hom ≫
          ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ jC).app
            ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)).hom) ≫
      (etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app
        ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))
    (extensionByZeroConstantSelfMapTwist_comp_counit Λ E jC sU s sq) ((2 : ℕ) : ℤ)
  rw [Functor.map_comp ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ))
    ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
        (((etaleModuleInverseImageConstantIso.{u, 0} Λ jC).app E).symm.hom ≫
          ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ jC).app
            ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)).hom))
    ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app
        ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))] at hnat
  have hx := congrArg (fun f => f.hom y) hnat
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx
  refine (curveExtensionByZeroConstantTrace_apply q Λ hn (hζ.map_of_injective τ.injective) jC
    hfin E _).trans ((congrArg (curveConstantModuleTrace q Λ hn
      (hζ.map_of_injective τ.injective) E) hx).trans ?_)
  refine Eq.trans ?_ (curveExtensionByZeroConstantTrace_apply q Λ hn hζ jC hfin E y).symm
  convert curveConstantModuleTrace_integralSelfMapCohomologyEndo_of_twist q Λ hn hζ s τ hs E _
    using 3

end Boundary

end Trace

end Stacks.EtaleCohomology

end
