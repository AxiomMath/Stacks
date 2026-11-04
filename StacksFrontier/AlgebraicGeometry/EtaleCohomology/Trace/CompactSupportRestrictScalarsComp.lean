module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportLevelComparison
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent

/-!
# The comparison of `RΓ_c(X_k̄, -)` with restriction of scalars along a composite

Let `ρ₁ : Λ →+* R` and `ρ₂ : R →+* S` be morphisms of commutative rings with composite
`σ = ρ₂ ∘ ρ₁`.  For a bounded below complex `K` of sheaves of `S`-modules, the comparison
`RΓ_c(X_k̄, K)|_Λ ≅ RΓ_c(X_k̄, K|_Λ)` of
`Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyRestrictScalarsIso` along `σ` is the
composite of the comparisons along `ρ₂` and along `ρ₁`.

This is the coherence that makes the identifications `Hⁱ_c(X_k̄, Fₙ)|_{ℤ_ℓ} ≅ Hⁱ(Kₙ)` of
[Tag 03V2](https://stacks.math.columbia.edu/tag/03V2) compatible with the transition maps.

## Main results

* `Stacks.EtaleCohomology.etaleModuleInverseImageRestrictScalars_comp` and
  `Stacks.EtaleCohomology.etaleModuleExtensionByZeroRestrictScalars_comp`: the coherence for
  inverse image and for extension by zero, from the adjunctions.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {Λ R S : Type} [CommRing Λ] [CommRing R] [CommRing S]
  (ρ₁ : Λ →+* R) (ρ₂ : R →+* S) (σ : Λ →+* S) (w : σ = ρ₂.comp ρ₁)

/-! ### Restriction of scalars along a composite -/

/-- Restricting the scalars of a sheaf of modules along `ρ₂` and then along `ρ₁` is restricting
them along the composite. -/
def etaleModuleRestrictScalarsComp (X : Scheme.{u}) :
    etaleModuleRestrictScalars ρ₂ X ⋙ etaleModuleRestrictScalars ρ₁ X ≅
      etaleModuleRestrictScalars σ X where
  hom := sheafCompose_map X.smallEtaleTopology
      (ModuleCat.restrictScalarsComp'.{u + 1} ρ₁ ρ₂ σ w).inv
  inv := sheafCompose_map X.smallEtaleTopology
      (ModuleCat.restrictScalarsComp'.{u + 1} ρ₁ ρ₂ σ w).hom
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

/-- The comparison commutes with direct image. -/
theorem etaleModuleDirectImage_map_restrictScalarsComp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : EtaleModules.{u, 0} S X) :
    (etaleModuleDirectImage.{u, 0} Λ f).map
        ((etaleModuleRestrictScalarsComp ρ₁ ρ₂ σ w X).hom.app M) =
      (etaleModuleRestrictScalarsComp ρ₁ ρ₂ σ w Y).hom.app
        ((etaleModuleDirectImage.{u, 0} S f).obj M) :=
  rfl

/-- The comparison commutes with restriction along an étale morphism. -/
theorem etaleModuleRestriction_map_restrictScalarsComp {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (M : EtaleModules.{u, 0} S X) :
    (etaleModuleRestriction.{u, 0} Λ j).map
        ((etaleModuleRestrictScalarsComp ρ₁ ρ₂ σ w X).hom.app M) =
      (etaleModuleRestrictScalarsComp ρ₁ ρ₂ σ w U).hom.app
        ((etaleModuleRestriction.{u, 0} S j).obj M) :=
  rfl

/-! ### Inverse image -/

/-- The comparison of two adjoint transposes along a composite, on variables. -/
theorem eq_of_unit_squares {C : Type*} [Category* C] {x y z t x' s m : C}
    (U : x ⟶ y) (a : y ⟶ z) (b : z ⟶ t) (cY : x ⟶ x') (U' : x' ⟶ z) (rσu : x' ⟶ t)
    (rru : x ⟶ s) (cY' : s ⟶ t) (r₁uR : x ⟶ m) (r₁fχ : m ⟶ s) (fχ₁ : y ⟶ m)
    (hn : U ≫ a = cY ≫ U') (uσ : U' ≫ b = rσu) (hc : rru ≫ cY' = cY ≫ rσu)
    (u₂ : r₁uR ≫ r₁fχ = rru) (u₁ : U ≫ fχ₁ = r₁uR) :
    U ≫ a ≫ b = U ≫ fχ₁ ≫ r₁fχ ≫ cY' := by
  rw [← Category.assoc, hn, Category.assoc, uσ, ← hc, ← u₂, ← u₁]
  simp only [Category.assoc]

/-- The comparison of inverse image with `res_ρ`, after the unit of `f^{-1} ⊣ f_*`. -/
theorem etaleModuleInverseImageRestrictScalars_unit {Λ Λ' : Type} [CommRing Λ] [CommRing Λ']
    (ρ : Λ →+* Λ') {X Y : Scheme.{u}} (f : X ⟶ Y) (G : EtaleModules.{u, 0} Λ' Y) :
    (etaleModuleInverseImageAdj.{u, 0} Λ f).unit.app ((etaleModuleRestrictScalars ρ Y).obj G) ≫
        (etaleModuleDirectImage.{u, 0} Λ f).map
          ((etaleModuleInverseImageRestrictScalars ρ f).hom.app G) =
      (etaleModuleRestrictScalars ρ Y).map ((etaleModuleInverseImageAdj.{u, 0} Λ' f).unit.app G) :=
  (coefficientSheafPullbackTwoSquare_unit (smallEtaleBaseChange f) Y.smallEtaleTopology
    X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ρ) G).symm

/-- **The comparison of inverse image with restriction of scalars along a composite is the
composite of the comparisons.** -/
theorem etaleModuleInverseImageRestrictScalars_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : EtaleModules.{u, 0} S Y) :
    (etaleModuleInverseImage.{u, 0} Λ f).map
        ((etaleModuleRestrictScalarsComp ρ₁ ρ₂ σ w Y).hom.app G) ≫
        (etaleModuleInverseImageRestrictScalars σ f).hom.app G =
      (etaleModuleInverseImageRestrictScalars ρ₁ f).hom.app
          ((etaleModuleRestrictScalars ρ₂ Y).obj G) ≫
        (etaleModuleRestrictScalars ρ₁ X).map
            ((etaleModuleInverseImageRestrictScalars ρ₂ f).hom.app G) ≫
        (etaleModuleRestrictScalarsComp ρ₁ ρ₂ σ w X).hom.app
            ((etaleModuleInverseImage.{u, 0} S f).obj G) := by
  have u₁ := etaleModuleInverseImageRestrictScalars_unit ρ₁ f
      ((etaleModuleRestrictScalars ρ₂ Y).obj G)
  have u₂ := congrArg (etaleModuleRestrictScalars ρ₁ Y).map
    (etaleModuleInverseImageRestrictScalars_unit ρ₂ f G)
  rw [Functor.map_comp] at u₂
  have uσ := etaleModuleInverseImageRestrictScalars_unit σ f G
  have hn := ((etaleModuleInverseImageAdj.{u, 0} Λ f).unit.naturality
    ((etaleModuleRestrictScalarsComp ρ₁ ρ₂ σ w Y).hom.app G)).symm
  have hc := (etaleModuleRestrictScalarsComp ρ₁ ρ₂ σ w Y).hom.naturality
    ((etaleModuleInverseImageAdj.{u, 0} S f).unit.app G)
  refine ((etaleModuleInverseImageAdj.{u, 0} Λ f).homEquiv _ _).injective ?_
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  exact eq_of_unit_squares _ _ _ _ _ _ _ _ _ _ _ hn uσ hc u₂ u₁

/-! ### Extension by zero -/

/-- The comparison of extension by zero with `res_ρ`, after the unit of `j_! ⊣ j^{-1}`. -/
theorem etaleModuleExtensionByZeroRestrictScalars_unit {Λ Λ' : Type} [CommRing Λ] [CommRing Λ']
    (ρ : Λ →+* Λ') {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] (G : EtaleModules.{u, 0} Λ' U) :
    (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app ((etaleModuleRestrictScalars ρ U).obj G) ≫
        (etaleModuleRestriction.{u, 0} Λ j).map
          ((etaleModuleExtensionByZeroRestrictScalars ρ j).hom.app G) =
      (etaleModuleRestrictScalars ρ U).map
          ((etaleModuleExtensionByZeroAdj.{u, 0} Λ' j).unit.app G) :=
  ((Category.comp_id _).symm.trans (unit_mateEquiv_symm
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (Scheme.Etale.smallEtaleCompose j)
        (ModuleCat.{u + 1} Λ') U.smallEtaleTopology X.smallEtaleTopology)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (Scheme.Etale.smallEtaleCompose j)
        (ModuleCat.{u + 1} Λ) U.smallEtaleTopology X.smallEtaleTopology)
      (coefficientPushforwardTwoSquare (Scheme.Etale.smallEtaleCompose j) U.smallEtaleTopology
        X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ρ)) G)).symm

/-- **The comparison of extension by zero with restriction of scalars along a composite is the
composite of the comparisons.** -/
theorem etaleModuleExtensionByZeroRestrictScalars_comp {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (G : EtaleModules.{u, 0} S U) :
    (etaleModuleExtensionByZero.{u, 0} Λ j).map
        ((etaleModuleRestrictScalarsComp ρ₁ ρ₂ σ w U).hom.app G) ≫
        (etaleModuleExtensionByZeroRestrictScalars σ j).hom.app G =
      (etaleModuleExtensionByZeroRestrictScalars ρ₁ j).hom.app
          ((etaleModuleRestrictScalars ρ₂ U).obj G) ≫
        (etaleModuleRestrictScalars ρ₁ X).map
            ((etaleModuleExtensionByZeroRestrictScalars ρ₂ j).hom.app G) ≫
        (etaleModuleRestrictScalarsComp ρ₁ ρ₂ σ w X).hom.app
          ((etaleModuleExtensionByZero.{u, 0} S j).obj G) := by
  have u₁ := etaleModuleExtensionByZeroRestrictScalars_unit ρ₁ j
      ((etaleModuleRestrictScalars ρ₂ U).obj G)
  have u₂ := congrArg (etaleModuleRestrictScalars ρ₁ U).map
    (etaleModuleExtensionByZeroRestrictScalars_unit ρ₂ j G)
  rw [Functor.map_comp] at u₂
  have uσ := etaleModuleExtensionByZeroRestrictScalars_unit σ j G
  have hn := ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.naturality
    ((etaleModuleRestrictScalarsComp ρ₁ ρ₂ σ w U).hom.app G)).symm
  have hc := (etaleModuleRestrictScalarsComp ρ₁ ρ₂ σ w U).hom.naturality
    ((etaleModuleExtensionByZeroAdj.{u, 0} S j).unit.app G)
  refine ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).homEquiv _ _).injective ?_
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  exact eq_of_unit_squares _ _ _ _ _ _ _ _ _ _ _ hn uσ hc u₂ u₁

/-! ### The termwise comparison on bounded below complexes -/

/-- The coherence of the termwise comparison, on variables. -/
theorem comp_eq_of_three_squares {C : Type*} [Category* C] {a b c d e e' e'' g h : C}
    (x₁ : a ⟶ b) (x₂ : b ⟶ c) (x₃ : c ⟶ d) (e₁ : a ⟶ e) (e₂ : e ⟶ e') (e₃ : e' ⟶ c)
    (i₁ : e' ⟶ g) (i₂ : g ⟶ h) (i₃ : h ⟶ d) (n₁ : e ⟶ e'') (n₂ : e'' ⟶ g) (ν : e'' ⟶ h)
    (hE : x₁ ≫ x₂ = e₁ ≫ e₂ ≫ e₃) (hI : e₃ ≫ x₃ = i₁ ≫ i₂ ≫ i₃) (hN : e₂ ≫ i₁ = n₁ ≫ n₂)
    (h₂ : n₂ ≫ i₂ = ν) :
    x₁ ≫ x₂ ≫ x₃ = (e₁ ≫ n₁) ≫ ν ≫ i₃ := by
  rw [← h₂, ← Category.assoc, hE, Category.assoc, Category.assoc, hI, ← Category.assoc e₂, hN]
  simp only [Category.assoc]

/-- Restriction of scalars along `ρ₂` and then `ρ₁` is restriction along the composite, on bounded
below complexes. -/
def etaleModuleRestrictScalarsCompPlus (X : Scheme.{u})
    (K : CochainComplex.Plus (EtaleModules.{u, 0} S X)) :
    (etaleModuleRestrictScalars ρ₁ X).mapCochainComplexPlus.obj
        ((etaleModuleRestrictScalars ρ₂ X).mapCochainComplexPlus.obj K) ≅
      (etaleModuleRestrictScalars σ X).mapCochainComplexPlus.obj K :=
  ObjectProperty.isoMk _ ((NatIso.mapHomologicalComplex (etaleModuleRestrictScalarsComp ρ₁ ρ₂ σ w X)
    (ComplexShape.up ℤ)).app K.obj)

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

omit [Finite k] in
/-- **The termwise comparison of the restriction to `X̄_k̄` of the extension by zero with
restriction of scalars, along a composite.** -/
theorem compactSupportRestrictionRestrictScalarsIso_comp
    (K : CochainComplex.Plus (EtaleModules.{u, 0} S X)) :
    (compactSupportRestriction f j kbar Λ).map
        (etaleModuleRestrictScalarsCompPlus ρ₁ ρ₂ σ w X K).hom ≫
        (compactSupportRestrictionRestrictScalarsIso σ f j kbar K).inv =
      (compactSupportRestrictionRestrictScalarsIso ρ₁ f j kbar
          ((etaleModuleRestrictScalars ρ₂ X).mapCochainComplexPlus.obj K)).inv ≫
        (etaleModuleRestrictScalars ρ₁
              (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map
          (compactSupportRestrictionRestrictScalarsIso ρ₂ f j kbar K).inv ≫
        (etaleModuleRestrictScalarsCompPlus ρ₁ ρ₂ σ w (fieldBaseChange (Over.mk j.toBase) kbar)
          ((compactSupportRestriction f j kbar S).obj K)).hom := by
  refine ObjectProperty.hom_ext _ (HomologicalComplex.hom_ext _ _ (fun i => ?_))
  let Yb := fieldBaseChange (Over.mk j.toBase) kbar
  let pr := fieldBaseChangeProj (Over.mk j.toBase) kbar
  let G := K.obj.X i
  let M := (etaleModuleExtensionByZero.{u, 0} S j.immersion).obj G
  have hE := congrArg (etaleModuleInverseImage.{u, 0} Λ pr).map
    (etaleModuleExtensionByZeroRestrictScalars_comp ρ₁ ρ₂ σ w j.immersion G)
  simp only [Functor.map_comp] at hE
  have hI := etaleModuleInverseImageRestrictScalars_comp ρ₁ ρ₂ σ w pr M
  have hN := (etaleModuleInverseImageRestrictScalars ρ₁ pr).hom.naturality
    ((etaleModuleExtensionByZeroRestrictScalars ρ₂ j.immersion).hom.app G)
  exact comp_eq_of_three_squares _ _ _ _ _ _ _ _ _ _ _ _ hE hI hN
    ((etaleModuleRestrictScalars ρ₁ Yb).map_comp _ _).symm

/-! ### Naturality of the comparison -/

/-- Two naturality squares, on variables. -/
theorem comp_eq_of_two_naturality {C : Type*} [Category* C] {A B B' D D' E : C}
    (a : A ⟶ B) (x : B ⟶ D) (y : D ⟶ E) (x' : A ⟶ B') (m : B' ⟶ D) (y' : B' ⟶ D') (b : D' ⟶ E)
    (h₁ : a ≫ x = x' ≫ m) (h₂ : m ≫ y = y' ≫ b) :
    a ≫ x ≫ y = x' ≫ y' ≫ b := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

section Naturality

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

omit [Finite k] in
/-- **The termwise comparison of `(j_! -)|_{X̄_k̄}` with `res_ρ` is natural.** -/
theorem compactSupportRestrictionRestrictScalarsIso_hom_naturality
    {K₁ K₂ : CochainComplex.Plus (EtaleModules.{u, 0} Λ' X)} (t : K₁ ⟶ K₂) :
    (etaleModuleRestrictScalars ρ
          (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map
        ((compactSupportRestriction f j kbar Λ').map t) ≫
      (compactSupportRestrictionRestrictScalarsIso ρ f j kbar K₂).hom =
    (compactSupportRestrictionRestrictScalarsIso ρ f j kbar K₁).hom ≫
      (compactSupportRestriction f j kbar Λ).map
          ((etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.map t) := by
  refine ObjectProperty.hom_ext _ (HomologicalComplex.hom_ext _ _ (fun i => ?_))
  have h₁ := (etaleModuleInverseImageRestrictScalars ρ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).inv.naturality
    ((etaleModuleExtensionByZero.{u, 0} Λ' j.immersion).map (t.hom.f i))
  have h₂ := congrArg (etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)).map
    ((etaleModuleExtensionByZeroRestrictScalars ρ j.immersion).inv.naturality (t.hom.f i))
  simp only [Functor.map_comp] at h₂
  exact comp_eq_of_two_naturality _ _ _ _ _ _ _ h₁ h₂

/-- Four naturality squares through three functors, on variables. -/
theorem comp_eq_of_four_naturality {C₁ C₂ C₃ D : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* D] (G₁ : C₁ ⥤ D) (G₂ : C₂ ⥤ C₁) (G₃ : C₃ ⥤ C₂)
    {A B : D} {A₁ B₁ : C₁} {A₂ B₂ : C₂} {A₃ B₃ A₃' B₃' : C₃}
    (m : A ⟶ B) (tΓ₁ : A ⟶ G₁.obj A₁) (tΓ₂ : B ⟶ G₁.obj B₁) (n : A₁ ⟶ B₁)
    (tg₁ : A₁ ⟶ G₂.obj A₂) (tg₂ : B₁ ⟶ G₂.obj B₂) (p : A₂ ⟶ B₂)
    (ψ₁ : A₂ ⟶ G₃.obj A₃) (ψ₂ : B₂ ⟶ G₃.obj B₃) (q : A₃ ⟶ B₃)
    (x₁ : A₃ ⟶ A₃') (x₂ : B₃ ⟶ B₃') (y : A₃' ⟶ B₃')
    (h₁ : m ≫ tΓ₂ = tΓ₁ ≫ G₁.map n) (h₂ : n ≫ tg₂ = tg₁ ≫ G₂.map p)
    (h₃ : p ≫ ψ₂ = ψ₁ ≫ G₃.map q) (h₄ : q ≫ x₂ = x₁ ≫ y) :
    m ≫ tΓ₂ ≫ G₁.map (tg₂ ≫ G₂.map (ψ₂ ≫ G₃.map x₂)) =
      (tΓ₁ ≫ G₁.map (tg₁ ≫ G₂.map (ψ₁ ≫ G₃.map x₁))) ≫ G₁.map (G₂.map (G₃.map y)) := by
  rw [← Category.assoc, h₁, Category.assoc, ← G₁.map_comp, ← Category.assoc n, h₂, Category.assoc,
    ← G₂.map_comp, ← Category.assoc p, h₃, Category.assoc, ← G₃.map_comp, h₄]
  simp only [Functor.map_comp, Category.assoc]

/-- **The comparison `RΓ_c(X_k̄, K)|_Λ ≅ RΓ_c(X_k̄, res_ρ K)` is natural in `K`.** -/
theorem compactSupportFrobeniusCohomologyRestrictScalarsIso_hom_naturality
    {K₁ K₂ : CochainComplex.Plus (EtaleModules.{u, 0} Λ' X)} (t : K₁ ⟶ K₂) :
    (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.map
        ((compactSupportFrobeniusFunctor.{u, 0} Λ' f j kbar).map t) ≫
      (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ f j kbar K₂).hom =
    (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ f j kbar K₁).hom ≫
      (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
        ((etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.map t) := by
  have := Fintype.ofFinite k
  rw [compactSupportFrobeniusCohomologyRestrictScalarsIso_hom_eq,
    compactSupportFrobeniusCohomologyRestrictScalarsIso_hom_eq]
  have h₁ := (etaleModuleDerivedGlobalSectionsRestrictScalars ρ (Spec (.of kbar))).hom.naturality
    ((etaleModuleDerivedDirectImage.{u, 0} Λ' (pullback.snd (Over.mk j.toBase).hom
      (specAlgebraMap k kbar))).map
          (DerivedCategory.Plus.Q.map ((compactSupportRestriction f j kbar Λ').map t)))
  have h₂ := (etaleModuleDerivedDirectImageRestrictScalars ρ (pullback.snd (Over.mk j.toBase).hom
      (specAlgebraMap k kbar))).hom.naturality
    (DerivedCategory.Plus.Q.map ((compactSupportRestriction f j kbar Λ').map t))
  have h₃ := (Functor.mapDerivedCategoryPlusQIso (etaleModuleRestrictScalars ρ
    (fieldBaseChange (Over.mk j.toBase) kbar))).hom.naturality
        ((compactSupportRestriction f j kbar Λ').map t)
  have h₄ := compactSupportRestrictionRestrictScalarsIso_hom_naturality (ρ := ρ) (f := f) (j := j)
    (kbar := kbar) t
  simp only [Functor.comp_map] at h₁ h₂ h₃
  exact comp_eq_of_four_naturality (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar)))
    (etaleModuleDerivedDirectImage.{u, 0} Λ
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
    DerivedCategory.Plus.Q _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄

end Naturality

/-! ### The comparison read on resolutions -/

section Model

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- **The map of `RΓ_c(X_k̄, -)` induced by `t : K ⟶ res_ρ K'`, read on resolutions, as an
equation.** Given `a : K|_{X̄_k̄} ⟶ I` and `b : K'|_{X̄_k̄} ⟶ C` inducing isomorphisms on
`RΓ(Spec k̄, Rg_* -)`, with `I` and `C` acyclic for `Γ(Spec k̄, g_* -)`, and `μ : I ⟶ res_ρ C`
lying over `t`, the composite of `RΓ_c(t)` with the comparison
`RΓ_c(X_k̄, res_ρ K') ≅ RΓ_c(X_k̄, K')|_Λ` is `Γ(Spec k̄, g_* μ)` between the models. -/
theorem compactSupportFrobeniusFunctor_map_comp_restrictScalarsIso_inv_eq
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (K' : CochainComplex.Plus (EtaleModules.{u, 0} Λ' X))
    (tc : K ⟶ (etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.obj K')
    (I : CochainComplex.Plus (EtaleModules.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar)))
    (a : (compactSupportRestriction f j kbar Λ).obj K ⟶ I)
    (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ' (fieldBaseChange (Over.mk j.toBase) kbar)))
    (b : (compactSupportRestriction f j kbar Λ').obj K' ⟶ C)
    (μ : I ⟶ (etaleModuleRestrictScalars ρ
            (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj C)
    (hμ : (compactSupportRestriction f j kbar Λ).map tc ≫
      (compactSupportRestrictionRestrictScalarsIso ρ f j kbar K').inv ≫
      (etaleModuleRestrictScalars ρ
            (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map b =
      a ≫ μ)
    [IsIso ((directImageSectionsDerivedUnit Λ
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).app I)]
    [IsIso ((directImageSectionsDerivedUnit Λ'
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).app C)]
    [IsIso (DerivedCategory.Plus.Q.map b)] :
    (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map tc ≫
        (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ f j kbar K').inv =
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
          ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd (Over.mk j.toBase).hom
            (specAlgebraMap k kbar))).map (DerivedCategory.Plus.Q.map a)) ≫
        inv ((directImageSectionsDerivedUnit Λ
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).app I) ≫
        DerivedCategory.Plus.Q.map
            ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapCochainComplexPlus.map
          ((etaleModuleDirectImage.{u, 0} Λ (pullback.snd (Over.mk j.toBase).hom
            (specAlgebraMap k kbar))).mapCochainComplexPlus.map μ) ≫
          (directImageSectionsRestrictScalarsComplexIso ρ
            (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) C).inv) ≫
        (Functor.mapDerivedCategoryPlusQIso (ModuleCat.restrictScalars.{u + 1} ρ)).inv.app
          ((etaleModuleGlobalSections.{u, 0} Λ' (Spec (.of kbar))).mapCochainComplexPlus.obj
            ((etaleModuleDirectImage.{u, 0} Λ' (pullback.snd (Over.mk j.toBase).hom
              (specAlgebraMap k kbar))).mapCochainComplexPlus.obj C)) ≫
        (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.map
          ((directImageSectionsDerivedUnit Λ'
            (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).app C) ≫
        inv ((ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.map
          ((etaleModuleDerivedGlobalSections.{u, 0} Λ' (Spec (.of kbar))).map
            ((etaleModuleDerivedDirectImage.{u, 0} Λ' (pullback.snd (Over.mk j.toBase).hom
              (specAlgebraMap k kbar))).map (DerivedCategory.Plus.Q.map b)))) := by
  have := Fintype.ofFinite k
  have E1 := compactSupportFrobeniusFunctor_map_comp_restrictScalarsIso_inv ρ f j kbar K K' tc
    I a C b μ hμ
  have E2 := directImageSectionsDerivedUnit_comp_map_restrictScalars ρ
    (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) I C μ
  exact eq_of_two_squares _ _ _ _ _ _ _ _ _ ((Category.assoc _ _ _).trans E1) E2

/-- The localization of `res_ρ` on bounded below complexes, read in the unbounded derived
category. -/
theorem ι_map_mapDerivedCategoryPlusQIso_inv_app {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (M : CochainComplex.Plus A) :
    DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusQIso F).inv.app M) =
      F.mapDerivedCategoryFactors.inv.app M.obj := by
  have e : DerivedCategory.Plus.ι.mapIso ((Functor.mapDerivedCategoryPlusQIso F).app M) =
      F.mapDerivedCategoryFactors.app M.obj :=
    Iso.ext (Functor.ι_map_mapDerivedCategoryPlusQIso_hom_app F M)
  exact congrArg Iso.inv e

end Model

/-! ### The comparison along a composite -/

/-- The composite of the six pieces of a morphism, mapped by a functor. -/
theorem map_comp₆ {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) (g : X₅ ⟶ X₆) :
    F.map (a ≫ b ≫ c ≫ d ≫ e ≫ g) =
      F.map a ≫ F.map b ≫ F.map c ≫ F.map d ≫ F.map e ≫ F.map g := by
  simp only [Functor.map_comp]

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The naturality of the comparison `res_ρ₁ ∘ res_ρ₂ ≅ res_σ` on bounded below complexes. -/
theorem etaleModuleRestrictScalarsCompPlus_hom_naturality {Y : Scheme.{u}}
    {M N : CochainComplex.Plus (EtaleModules.{u, 0} S Y)} (g : M ⟶ N) :
    (etaleModuleRestrictScalarsCompPlus ρ₁ ρ₂ σ w Y M).hom ≫
        (etaleModuleRestrictScalars σ Y).mapCochainComplexPlus.map g =
      (etaleModuleRestrictScalars ρ₁ Y).mapCochainComplexPlus.map
          ((etaleModuleRestrictScalars ρ₂ Y).mapCochainComplexPlus.map g) ≫
        (etaleModuleRestrictScalarsCompPlus ρ₁ ρ₂ σ w Y N).hom :=
  ObjectProperty.hom_ext _ (HomologicalComplex.hom_ext _ _ (fun i =>
    ((etaleModuleRestrictScalarsComp ρ₁ ρ₂ σ w Y).hom.naturality (g.hom.f i)).symm))

/-- The comparison of global sections with `res_ρ`, unfolded. -/
theorem etaleModuleGlobalSectionsRestrictScalars_inv_app {Λ Λ' : Type} [CommRing Λ] [CommRing Λ']
    (ρ : Λ →+* Λ') (T : Scheme.{u}) (N : EtaleModules.{u, 0} Λ' T) :
    (etaleModuleGlobalSectionsRestrictScalars ρ T).inv.app N =
      (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} Λ)
          terminalIsTerminal).hom.app ((etaleModuleRestrictScalars ρ T).obj N) ≫
        (ModuleCat.restrictScalars.{u + 1} ρ).map ((Sheaf.ΓNatIsoSheafSections
          T.smallEtaleTopology (ModuleCat.{u + 1} Λ') terminalIsTerminal).inv.app N) := by
  simp only [etaleModuleGlobalSectionsRestrictScalars]
  rfl

/-- The coherence of the comparison of global sections, on variables. -/
theorem comp_eq_of_round_trip {C : Type*} [Category* C] {A B B' E F G H : C} (a : A ⟶ B)
    (b : B ⟶ B') (m : B' ⟶ E) (c' : B' ⟶ B) (d : B ⟶ E) (e : E ⟶ F) (x : A ⟶ G) (y : G ⟶ H)
    (z : H ⟶ F) (s s' : B ⟶ H) (hm : m = c' ≫ d) (hx : x ≫ y = a ≫ s) (hb : b ≫ c' = 𝟙 _)
    (hd : d ≫ e = s' ≫ z) (hz : s' = s) :
    (a ≫ b) ≫ m ≫ e = x ≫ y ≫ z := by
  rw [← Category.assoc x, hx, hm, ← hz, Category.assoc, Category.assoc, ← Category.assoc b, hb,
    Category.id_comp, hd, Category.assoc]

/-- **The comparison of global sections with restriction of scalars along a composite is the
composite of the comparisons.** -/
theorem etaleModuleGlobalSectionsRestrictScalars_comp (T : Scheme.{u})
    (N : EtaleModules.{u, 0} S T) :
    (etaleModuleGlobalSectionsRestrictScalars ρ₁ T).inv.app
        ((etaleModuleRestrictScalars ρ₂ T).obj N) ≫
        (ModuleCat.restrictScalars.{u + 1} ρ₁).map
          ((etaleModuleGlobalSectionsRestrictScalars ρ₂ T).inv.app N) ≫
        (ModuleCat.restrictScalarsComp'.{u + 1} ρ₁ ρ₂ σ w).inv.app
          ((etaleModuleGlobalSections.{u, 0} S T).obj N) =
      (etaleModuleGlobalSections.{u, 0} Λ T).map
          ((etaleModuleRestrictScalarsComp ρ₁ ρ₂ σ w T).hom.app N) ≫
        (etaleModuleGlobalSectionsRestrictScalars σ T).inv.app N := by
  let ΓΛ := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} Λ) terminalIsTerminal
  let ΓR := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} R) terminalIsTerminal
  let ΓS := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} S) terminalIsTerminal
  have hΓ := ΓΛ.hom.naturality ((etaleModuleRestrictScalarsComp ρ₁ ρ₂ σ w T).hom.app N)
  have hc := (ModuleCat.restrictScalarsComp'.{u + 1} ρ₁ ρ₂ σ w).inv.naturality (ΓS.inv.app N)
  have hR : (ModuleCat.restrictScalars.{u + 1} ρ₁).map
      (ΓR.inv.app ((etaleModuleRestrictScalars ρ₂ T).obj N)) ≫
      (ModuleCat.restrictScalars.{u + 1} ρ₁).map
          (ΓR.hom.app ((etaleModuleRestrictScalars ρ₂ T).obj N)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rw [etaleModuleGlobalSectionsRestrictScalars_inv_app,
        etaleModuleGlobalSectionsRestrictScalars_inv_app,
    etaleModuleGlobalSectionsRestrictScalars_inv_app]
  exact comp_eq_of_round_trip _ _ _ _ _ _ _ _ _ _ _
      ((ModuleCat.restrictScalars.{u + 1} ρ₁).map_comp _ _)
    hΓ hR hc rfl

/-- Stripping two identities, on variables. -/
theorem comp_id_strip {C D : Type*} [Category* C] [Category* D] (Fn : D ⥤ C) {X Y' : C}
    {Z W : D} (i₁ : X ⟶ X) (i₂ : Z ⟶ Z) (a : X ⟶ Fn.obj Z) (b : Z ⟶ W) (c : Fn.obj W ⟶ Y')
    (d : X ⟶ Y') (h₁ : i₁ = 𝟙 X) (h₂ : i₂ = 𝟙 Z) (h : a ≫ Fn.map b ≫ c = d) :
    (i₁ ≫ a) ≫ Fn.map (i₂ ≫ b) ≫ c = d := by
  subst h₁ h₂
  simpa using h

/-- **The comparison of `Γ(Spec k̄, g_* -)` with restriction of scalars along a composite**, on
bounded below complexes. -/
theorem directImageSectionsRestrictScalarsComplexIso_comp {Y T : Scheme.{u}} (g : Y ⟶ T)
    (C : CochainComplex.Plus (EtaleModules.{u, 0} S Y)) :
    ((etaleModuleGlobalSections.{u, 0} Λ T).mapCochainComplexPlus.map
        ((etaleModuleDirectImage.{u, 0} Λ g).mapCochainComplexPlus.map (𝟙 _)) ≫
        (directImageSectionsRestrictScalarsComplexIso ρ₁ g
          ((etaleModuleRestrictScalars ρ₂ Y).mapCochainComplexPlus.obj C)).inv).hom ≫
      ((ModuleCat.restrictScalars.{u + 1} ρ₁).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((etaleModuleGlobalSections.{u, 0} R T).mapCochainComplexPlus.map
          ((etaleModuleDirectImage.{u, 0} R g).mapCochainComplexPlus.map (𝟙 _)) ≫
          (directImageSectionsRestrictScalarsComplexIso ρ₂ g C).inv).hom ≫
      (StacksDraft.DerivedInverseLimit.restrictScalarsComplexComp.{0, u + 1} ρ₁ ρ₂ σ w).hom.app
        ((etaleModuleGlobalSections.{u, 0} S T).mapCochainComplexPlus.obj
          ((etaleModuleDirectImage.{u, 0} S g).mapCochainComplexPlus.obj C)).obj =
    ((etaleModuleGlobalSections.{u, 0} Λ T).mapCochainComplexPlus.map
        ((etaleModuleDirectImage.{u, 0} Λ g).mapCochainComplexPlus.map
          (etaleModuleRestrictScalarsCompPlus ρ₁ ρ₂ σ w Y C).hom) ≫
      (directImageSectionsRestrictScalarsComplexIso σ g C).inv).hom := by
  refine HomologicalComplex.hom_ext _ _ (fun q => ?_)
  have h := etaleModuleGlobalSectionsRestrictScalars_comp ρ₁ ρ₂ σ w T
    ((etaleModuleDirectImage.{u, 0} S g).obj (C.obj.X q))
  have h' : ((etaleModuleGlobalSections.{u, 0} Λ T).map ((etaleModuleDirectImage.{u, 0} Λ g).map
        (𝟙 ((etaleModuleRestrictScalars ρ₁ Y).obj
                ((etaleModuleRestrictScalars ρ₂ Y).obj (C.obj.X q))))) ≫
      (etaleModuleGlobalSectionsRestrictScalars ρ₁ T).inv.app
        ((etaleModuleRestrictScalars ρ₂ T).obj
              ((etaleModuleDirectImage.{u, 0} S g).obj (C.obj.X q)))) ≫
      ((ModuleCat.restrictScalars.{u + 1} ρ₁).map
        ((etaleModuleGlobalSections.{u, 0} R T).map ((etaleModuleDirectImage.{u, 0} R g).map
          (𝟙 ((etaleModuleRestrictScalars ρ₂ Y).obj (C.obj.X q)))) ≫
          (etaleModuleGlobalSectionsRestrictScalars ρ₂ T).inv.app
            ((etaleModuleDirectImage.{u, 0} S g).obj (C.obj.X q))) ≫
        (ModuleCat.restrictScalarsComp'.{u + 1} ρ₁ ρ₂ σ w).inv.app
          ((etaleModuleGlobalSections.{u, 0} S T).obj
                ((etaleModuleDirectImage.{u, 0} S g).obj (C.obj.X q)))) =
      (etaleModuleGlobalSections.{u, 0} Λ T).map ((etaleModuleDirectImage.{u, 0} Λ g).map
          ((etaleModuleRestrictScalarsComp ρ₁ ρ₂ σ w Y).hom.app (C.obj.X q))) ≫
        (etaleModuleGlobalSectionsRestrictScalars σ T).inv.app
          ((etaleModuleDirectImage.{u, 0} S g).obj (C.obj.X q)) := by
    rw [etaleModuleDirectImage_map_restrictScalarsComp]
    exact comp_id_strip (ModuleCat.restrictScalars.{u + 1} ρ₁) _ _ _ _ _ _
      (by rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id])
      (CategoryTheory.Functor.map_id _ _) h
  exact h'

/-- The cancellation in the comparison along a composite, on variables. -/
theorem comp_restrict_cancel {C D : Type*} [Category* C] [Category* D] (Fn : D ⥤ C)
    {P₀ P₁ P₂ P₃ : C} {Q₀ Q₂ Q₃ Q₄ Q₆ Q' : D}
    (x1 : P₀ ⟶ Fn.obj Q₀) (x2 : Q₀ ⟶ Q₆)
    (a1 : P₀ ⟶ P₁) (b1 : P₁ ⟶ P₂) (c1 : P₂ ⟶ P₃) (d1 : P₃ ⟶ Fn.obj Q₂) (u : Q₂ ⟶ Q')
    (y : Q₀ ⟶ Q') [IsIso u] [IsIso y] (c2 : Q₂ ⟶ Q₃) (d2 : Q₃ ⟶ Q₄) (z : Q₄ ⟶ Q₆)
    (h1 : x1 = a1 ≫ b1 ≫ c1 ≫ d1 ≫ Fn.map u ≫ inv (Fn.map y))
    (h2 : x2 = y ≫ inv u ≫ c2 ≫ d2 ≫ z) :
    x1 ≫ Fn.map x2 = a1 ≫ b1 ≫ c1 ≫ d1 ≫ Fn.map (c2 ≫ d2) ≫ Fn.map z := by
  subst h1 h2
  simp only [Functor.map_comp, Functor.map_inv, Category.assoc, IsIso.inv_hom_id_assoc,
    IsIso.hom_inv_id_assoc]

/-- `ι(F⁺(x)) = F(ι(x))` for an exact functor `F`. -/
theorem ι_map_mapDerivedCategoryPlus_map {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : DerivedCategory.Plus A} (x : K ⟶ L) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlus.map x) =
      F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map x) :=
  rfl

/-- The last step of the comparison along a composite, on variables. -/
theorem comp_restrict_final {C D : Type*} [Category* C] [Category* D] (ιF : C ⥤ D)
    {P₀ P₁ P₂ P₃ P₄ P₅ P₆ S₃ S₄ T' : C}
    (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (c1 : P₂ ⟶ P₃) (d1 : P₃ ⟶ P₄) (m : P₄ ⟶ P₅) (z : P₅ ⟶ P₆)
    (cσ : P₂ ⟶ S₃) (dσ : S₃ ⟶ S₄) (zσ : S₄ ⟶ T') (Dd : ιF.obj P₆ ⟶ ιF.obj T')
    (Dd' : ιF.obj P₅ ⟶ ιF.obj S₄)
    (hmid : ιF.map (c1 ≫ d1 ≫ m) ≫ Dd' = ιF.map (cσ ≫ dσ))
    (hend : ιF.map z ≫ Dd = Dd' ≫ ιF.map zσ) :
    ιF.map (a ≫ b ≫ c1 ≫ d1 ≫ m ≫ z) ≫ Dd = ιF.map (a ≫ b ≫ cσ ≫ dσ ≫ zσ) := by
  have h₁ : ιF.map (a ≫ b ≫ c1 ≫ d1 ≫ m ≫ z) ≫ Dd =
      ιF.map a ≫ ιF.map b ≫ (ιF.map (c1 ≫ d1 ≫ m) ≫ Dd') ≫ ιF.map zσ := by
    simp only [Functor.map_comp, Category.assoc] at hend ⊢
    rw [hend]
  rw [h₁, hmid]
  simp only [Functor.map_comp, Category.assoc]

/-- The middle step of the comparison along a composite, on variables. -/
theorem comp_restrict_middle {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D]
    [Category* D'] (Qf : C ⥤ D) (Qf' : C' ⥤ D') (Fn : D' ⥤ D)
    {M₀ M₁ M₄ X₀' : C} {M₂ M₃ : C'} {X₁ : D} {X₂ : D'}
    (x : M₀ ⟶ M₁) (A : Qf.obj M₁ ⟶ Fn.obj (Qf'.obj M₂)) (y : M₂ ⟶ M₃) (B : Qf'.obj M₃ ⟶ X₂)
    (Dd : Fn.obj X₂ ⟶ X₁) (ry : M₁ ⟶ M₄) (A' : Qf.obj M₄ ⟶ Fn.obj (Qf'.obj M₃)) (c : M₄ ⟶ X₀')
    (E : Qf.obj X₀' ⟶ X₁) (z : M₀ ⟶ X₀')
    (n1 : A ≫ Fn.map (Qf'.map y) = Qf.map ry ≫ A') (n2 : A' ≫ Fn.map B ≫ Dd = Qf.map c ≫ E)
    (n3 : x ≫ ry ≫ c = z) :
    Qf.map x ≫ A ≫ Fn.map (Qf'.map y) ≫ Fn.map B ≫ Dd = Qf.map z ≫ E := by
  rw [← Category.assoc A, n1, Category.assoc, n2, ← n3]
  simp only [Functor.map_comp, Category.assoc]

/-- `ι(Q(g)) = Q(g)` for a morphism of bounded below complexes. -/
theorem ι_map_Q_map {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {M M' : CochainComplex.Plus A} (g : M ⟶ M') :
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map g) = DerivedCategory.Q.map g.hom :=
  rfl

section Modules

variable {Λ R S : Type} [CommRing Λ] [CommRing R] [CommRing S]
  (ρ₁ : Λ →+* R) (ρ₂ : R →+* S) (σ : Λ →+* S) (w : σ = ρ₂.comp ρ₁)

/-- **The localization `Q ⋙ res⁺ ≅ res ⋙ Q` along a composite**, on morphisms of bounded below
complexes of modules: two chain maps into restrictions whose composite is a third one give the
same morphism of derived categories, up to the comparison of restrictions along a composite. -/
theorem restrictScalars_comp_Q_map
    {J₀ : CochainComplex.Plus (ModuleCat.{u + 1} Λ)}
        {J₁ : CochainComplex.Plus (ModuleCat.{u + 1} R)}
    {J₂ : CochainComplex.Plus (ModuleCat.{u + 1} S)}
    (g₁ : J₀ ⟶ (ModuleCat.restrictScalars.{u + 1} ρ₁).mapCochainComplexPlus.obj J₁)
    (g₂ : J₁ ⟶ (ModuleCat.restrictScalars.{u + 1} ρ₂).mapCochainComplexPlus.obj J₂)
    (gσ : J₀ ⟶ (ModuleCat.restrictScalars.{u + 1} σ).mapCochainComplexPlus.obj J₂)
    (h : g₁.hom ≫
        ((ModuleCat.restrictScalars.{u + 1} ρ₁).mapHomologicalComplex (ComplexShape.up ℤ)).map
          g₂.hom ≫
        (StacksDraft.DerivedInverseLimit.restrictScalarsComplexComp.{0, u + 1} ρ₁ ρ₂ σ w).hom.app
          J₂.obj = gσ.hom) :
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map g₁ ≫
        (Functor.mapDerivedCategoryPlusQIso (ModuleCat.restrictScalars.{u + 1} ρ₁)).inv.app J₁ ≫
        (ModuleCat.restrictScalars.{u + 1} ρ₁).mapDerivedCategoryPlus.map
          (DerivedCategory.Plus.Q.map g₂ ≫
            (Functor.mapDerivedCategoryPlusQIso
                  (ModuleCat.restrictScalars.{u + 1} ρ₂)).inv.app J₂)) ≫
      (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{0, u + 1} ρ₁ ρ₂ σ w).hom.app
        (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj J₂)) =
    DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map gσ ≫
      (Functor.mapDerivedCategoryPlusQIso (ModuleCat.restrictScalars.{u + 1} σ)).inv.app J₂) := by
  have n1 : (ModuleCat.restrictScalars.{u + 1} ρ₁).mapDerivedCategoryFactors.inv.app J₁.obj ≫
      (ModuleCat.restrictScalars.{u + 1} ρ₁).mapDerivedCategory.map (DerivedCategory.Q.map g₂.hom) =
      DerivedCategory.Q.map (((ModuleCat.restrictScalars.{u + 1} ρ₁).mapHomologicalComplex
        (ComplexShape.up ℤ)).map g₂.hom) ≫
      (ModuleCat.restrictScalars.{u + 1} ρ₁).mapDerivedCategoryFactors.inv.app
        (((ModuleCat.restrictScalars.{u + 1} ρ₂).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj J₂.obj) :=
    ((ModuleCat.restrictScalars.{u + 1} ρ₁).mapDerivedCategoryFactors.inv.naturality g₂.hom).symm
  have n2 := StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp_factors.{0, u + 1} ρ₁ ρ₂ σ w
      J₂.obj
  simp only [Functor.map_comp, ι_map_mapDerivedCategoryPlusQIso_inv_app]
  rw [ι_map_mapDerivedCategoryPlus_map, ι_map_mapDerivedCategoryPlus_map,
    ι_map_mapDerivedCategoryPlusQIso_inv_app, ι_map_Q_map, ι_map_Q_map, ι_map_Q_map]
  have := comp_restrict_middle DerivedCategory.Q DerivedCategory.Q
    (ModuleCat.restrictScalars.{u + 1} ρ₁).mapDerivedCategory g₁.hom _ g₂.hom _ _ _ _ _ _ gσ.hom
    n1 n2 h
  exact (Category.assoc _ _ _).trans ((whisker_eq _ ((Category.assoc _ _ _).trans
    (whisker_eq _ (Category.assoc _ _ _)))).trans this)

/-- The comparison of restrictions along a composite, after a morphism `u ≫ y⁻¹`. -/
theorem restrictScalars_comp_map_comp_inv {A B B' : DerivedCategory.Plus (ModuleCat.{u + 1} S)}
    (x : A ⟶ B') (y : B ⟶ B') [IsIso y] :
    DerivedCategory.Plus.ι.map ((ModuleCat.restrictScalars.{u + 1} ρ₁).mapDerivedCategoryPlus.map
        ((ModuleCat.restrictScalars.{u + 1} ρ₂).mapDerivedCategoryPlus.map x ≫
          inv ((ModuleCat.restrictScalars.{u + 1} ρ₂).mapDerivedCategoryPlus.map y))) ≫
      (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{0, u + 1} ρ₁ ρ₂ σ w).hom.app
        (DerivedCategory.Plus.ι.obj B) =
    (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{0, u + 1} ρ₁ ρ₂ σ w).hom.app
        (DerivedCategory.Plus.ι.obj A) ≫
      DerivedCategory.Plus.ι.map
          ((ModuleCat.restrictScalars.{u + 1} σ).mapDerivedCategoryPlus.map x ≫
        inv ((ModuleCat.restrictScalars.{u + 1} σ).mapDerivedCategoryPlus.map y)) := by
  rw [← Functor.map_inv, ← Functor.map_comp, ← Functor.map_inv, ← Functor.map_comp]
  exact
    (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{0, u + 1} ρ₁ ρ₂ σ w).hom.naturality
      (DerivedCategory.Plus.ι.map (x ≫ inv y))

end Modules

/-- The middle step of the comparison along a composite: the models `Γ(Spec k̄, g_* -)` of the
three comparisons are compatible. -/
theorem restrictScalars_comp_directImageSections_Q {Y T : Scheme.{u}} (g : Y ⟶ T)
    (C : CochainComplex.Plus (EtaleModules.{u, 0} S Y)) :
    DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.Q.map
        ((etaleModuleGlobalSections.{u, 0} Λ T).mapCochainComplexPlus.map
          ((etaleModuleDirectImage.{u, 0} Λ g).mapCochainComplexPlus.map (𝟙 _)) ≫
          (directImageSectionsRestrictScalarsComplexIso ρ₁ g
            ((etaleModuleRestrictScalars ρ₂ Y).mapCochainComplexPlus.obj C)).inv) :
          ((etaleModuleDirectImage.{u, 0} Λ g).mapCochainComplexPlus ⋙
            (etaleModuleGlobalSections.{u, 0} Λ T).mapCochainComplexPlus ⋙
                DerivedCategory.Plus.Q).obj
            ((etaleModuleRestrictScalars ρ₁ Y).mapCochainComplexPlus.obj
              ((etaleModuleRestrictScalars ρ₂ Y).mapCochainComplexPlus.obj C)) ⟶ _) ≫
        (Functor.mapDerivedCategoryPlusQIso (ModuleCat.restrictScalars.{u + 1} ρ₁)).inv.app _ ≫
        (ModuleCat.restrictScalars.{u + 1} ρ₁).mapDerivedCategoryPlus.map
          (DerivedCategory.Plus.Q.map
                ((etaleModuleGlobalSections.{u, 0} R T).mapCochainComplexPlus.map
            ((etaleModuleDirectImage.{u, 0} R g).mapCochainComplexPlus.map (𝟙 _)) ≫
            (directImageSectionsRestrictScalarsComplexIso ρ₂ g C).inv) ≫
            (Functor.mapDerivedCategoryPlusQIso
                  (ModuleCat.restrictScalars.{u + 1} ρ₂)).inv.app _)) ≫
      (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{0, u + 1} ρ₁ ρ₂ σ w).hom.app
        (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj
          ((etaleModuleGlobalSections.{u, 0} S T).mapCochainComplexPlus.obj
            ((etaleModuleDirectImage.{u, 0} S g).mapCochainComplexPlus.obj C)))) =
    DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.Q.map
        ((etaleModuleGlobalSections.{u, 0} Λ T).mapCochainComplexPlus.map
          ((etaleModuleDirectImage.{u, 0} Λ g).mapCochainComplexPlus.map
            (etaleModuleRestrictScalarsCompPlus ρ₁ ρ₂ σ w Y C).hom) ≫
          (directImageSectionsRestrictScalarsComplexIso σ g C).inv) :
          ((etaleModuleDirectImage.{u, 0} Λ g).mapCochainComplexPlus ⋙
            (etaleModuleGlobalSections.{u, 0} Λ T).mapCochainComplexPlus ⋙
                DerivedCategory.Plus.Q).obj
            ((etaleModuleRestrictScalars ρ₁ Y).mapCochainComplexPlus.obj
              ((etaleModuleRestrictScalars ρ₂ Y).mapCochainComplexPlus.obj C)) ⟶ _) ≫
      (Functor.mapDerivedCategoryPlusQIso (ModuleCat.restrictScalars.{u + 1} σ)).inv.app _) :=
  restrictScalars_comp_Q_map ρ₁ ρ₂ σ w _ _ _
      (directImageSectionsRestrictScalarsComplexIso_comp ρ₁ ρ₂ σ w g C)

omit [Finite k] in
/-- The middle step of the comparison along a composite, at the restriction to `X̄_k̄`. -/
theorem restrictScalars_comp_directImageSections_Q_fieldBaseChange
    (C : CochainComplex.Plus (EtaleModules.{u, 0} S (fieldBaseChange (Over.mk j.toBase) kbar))) :
    DerivedCategory.Plus.ι.map
        (DerivedCategory.Plus.Q.map
            ((etaleModuleGlobalSections.{u, 0} Λ
                    (Spec (CommRingCat.of kbar))).mapCochainComplexPlus.map
                ((etaleModuleDirectImage.{u, 0} Λ
                        (pullback.snd (Over.mk j.toBase).hom
                              (specAlgebraMap k kbar))).mapCochainComplexPlus.map
                  (𝟙 ((etaleModuleRestrictScalars ρ₁
                            (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
                    ((etaleModuleRestrictScalars ρ₂
                            (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
                          C)))) ≫
              (directImageSectionsRestrictScalarsComplexIso ρ₁
                  (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
                  ((etaleModuleRestrictScalars ρ₂
                          (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
                        C)).inv) ≫
          (Functor.mapDerivedCategoryPlusQIso (ModuleCat.restrictScalars.{u + 1} ρ₁)).inv.app
              ((etaleModuleGlobalSections.{u, 0} R
                      (Spec (CommRingCat.of kbar))).mapCochainComplexPlus.obj
                ((etaleModuleDirectImage.{u, 0} R
                        (pullback.snd (Over.mk j.toBase).hom
                              (specAlgebraMap k kbar))).mapCochainComplexPlus.obj
                  ((etaleModuleRestrictScalars ρ₂
                          (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
                        C))) ≫
            (ModuleCat.restrictScalars.{u + 1} ρ₁).mapDerivedCategoryPlus.map
              (DerivedCategory.Plus.Q.map
                  ((etaleModuleGlobalSections.{u, 0} R
                          (Spec (CommRingCat.of kbar))).mapCochainComplexPlus.map
                      ((etaleModuleDirectImage.{u, 0} R
                              (pullback.snd (Over.mk j.toBase).hom
                                    (specAlgebraMap k kbar))).mapCochainComplexPlus.map
                        (𝟙 ((etaleModuleRestrictScalars ρ₂
                          (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
                            C))) ≫
                    (directImageSectionsRestrictScalarsComplexIso ρ₂
                        (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) C).inv) ≫
                (Functor.mapDerivedCategoryPlusQIso (ModuleCat.restrictScalars.{u + 1} ρ₂)).inv.app
                  ((etaleModuleGlobalSections.{u, 0} S
                          (Spec (CommRingCat.of kbar))).mapCochainComplexPlus.obj
                    ((etaleModuleDirectImage.{u, 0} S
                            (pullback.snd (Over.mk j.toBase).hom
                                  (specAlgebraMap k kbar))).mapCochainComplexPlus.obj
                      C)))) ≫
      (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{0, u + 1} ρ₁ ρ₂ σ w).hom.app
        (DerivedCategory.Plus.ι.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleGlobalSections.{u, 0} S
                    (Spec (CommRingCat.of kbar))).mapCochainComplexPlus.obj
              ((etaleModuleDirectImage.{u, 0} S
                      (pullback.snd (Over.mk j.toBase).hom
                        (specAlgebraMap k kbar))).mapCochainComplexPlus.obj C)))) =
    DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Q.map
          ((etaleModuleGlobalSections.{u, 0} Λ
                  (Spec (CommRingCat.of kbar))).mapCochainComplexPlus.map
              ((etaleModuleDirectImage.{u, 0} Λ
                      (pullback.snd (Over.mk j.toBase).hom
                            (specAlgebraMap k kbar))).mapCochainComplexPlus.map
                (etaleModuleRestrictScalarsCompPlus ρ₁ ρ₂ σ w
                      (fieldBaseChange (Over.mk j.toBase) kbar) C).hom) ≫
            (directImageSectionsRestrictScalarsComplexIso σ
                  (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
                C).inv) ≫
        (Functor.mapDerivedCategoryPlusQIso (ModuleCat.restrictScalars.{u + 1} σ)).inv.app
          ((etaleModuleGlobalSections.{u, 0} S
                  (Spec (CommRingCat.of kbar))).mapCochainComplexPlus.obj
            ((etaleModuleDirectImage.{u, 0} S
                    (pullback.snd (Over.mk j.toBase).hom
                          (specAlgebraMap k kbar))).mapCochainComplexPlus.obj
              C))) :=
  restrictScalars_comp_directImageSections_Q ρ₁ ρ₂ σ w _ C

/-- **The comparison along a composite, read on an injective resolution.** -/
theorem compactSupportFrobeniusCohomologyRestrictScalarsIso_comp_of_resolution
    (K' : CochainComplex.Plus (EtaleModules.{u, 0} S X))
    (C : CochainComplex.Plus (EtaleModules.{u, 0} S (fieldBaseChange (Over.mk j.toBase) kbar)))
    (hC : ∀ q, Injective (C.obj.X q)) (b : (compactSupportRestriction f j kbar S).obj K' ⟶ C)
    [hQb : IsIso (DerivedCategory.Plus.Q.map b)] :
    DerivedCategory.Plus.ι.map (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ₁ f j kbar
        ((etaleModuleRestrictScalars ρ₂ X).mapCochainComplexPlus.obj K')).inv ≫
      (ModuleCat.restrictScalars.{u + 1} ρ₁).mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map
              (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ₂ f j kbar K').inv) ≫
      (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{0, u + 1} ρ₁ ρ₂ σ w).hom.app
        (DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, 0} S f j kbar K')) =
    DerivedCategory.Plus.ι.map ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
        (etaleModuleRestrictScalarsCompPlus ρ₁ ρ₂ σ w X K').hom ≫
      (compactSupportFrobeniusCohomologyRestrictScalarsIso σ f j kbar K').inv) := by
  have := Fintype.ofFinite k
  -- invertibility
  have hQb₂ : IsIso (DerivedCategory.Plus.Q.map
        ((compactSupportRestrictionRestrictScalarsIso ρ₂ f j kbar K').inv ≫
          (etaleModuleRestrictScalars ρ₂
            (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map b)) := by
    have h := (Functor.mapDerivedCategoryPlusQIso
      (etaleModuleRestrictScalars ρ₂ (fieldBaseChange (Over.mk j.toBase) kbar))).hom.naturality b
    simp only [Functor.comp_map] at h
    have := IsIso.of_isIso_fac_left h.symm
    rw [Functor.map_comp]
    infer_instance
  have hU : IsIso ((directImageSectionsDerivedUnit S
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).app C) :=
    isIso_directImageSectionsDerivedUnit_app _
        (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) C hC
  have hU₂ : IsIso ((directImageSectionsDerivedUnit R
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).app
        ((etaleModuleRestrictScalars ρ₂
            (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj C)) :=
    isIso_directImageSectionsDerivedUnit_app_restrictScalars ρ₂
        (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) C hC
  have hU₁ : IsIso ((directImageSectionsDerivedUnit Λ
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).app
        ((etaleModuleRestrictScalars ρ₁
            (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
          ((etaleModuleRestrictScalars ρ₂
              (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj C))) := by
    have := isIso_directImageSectionsDerivedUnit_app_restrictScalars σ
        (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) C hC
    exact IsIso.of_isIso_fac_right
      ((directImageSectionsDerivedUnit Λ
            (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).naturality
          (etaleModuleRestrictScalarsCompPlus ρ₁ ρ₂ σ w
            (fieldBaseChange (Over.mk j.toBase) kbar) C).hom).symm
  -- the three readings on resolutions
  have e₂ := compactSupportFrobeniusFunctor_map_comp_restrictScalarsIso_inv_eq (ρ := ρ₂) (f := f)
    (j := j) (kbar := kbar)
    ((etaleModuleRestrictScalars ρ₂ X).mapCochainComplexPlus.obj K') K' (𝟙 _)
        ((etaleModuleRestrictScalars ρ₂
            (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj C)
        ((compactSupportRestrictionRestrictScalarsIso ρ₂ f j kbar K').inv ≫
          (etaleModuleRestrictScalars ρ₂
            (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map b) C b (𝟙 _)
        (by rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id])
  rw [CategoryTheory.Functor.map_id] at e₂
  replace e₂ := (Category.id_comp
    (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ₂ f j kbar K').inv).symm.trans e₂
  have e₁ := compactSupportFrobeniusFunctor_map_comp_restrictScalarsIso_inv_eq (ρ := ρ₁) (f := f)
    (j := j) (kbar := kbar)
    ((etaleModuleRestrictScalars ρ₁ X).mapCochainComplexPlus.obj
          ((etaleModuleRestrictScalars ρ₂ X).mapCochainComplexPlus.obj K'))
        ((etaleModuleRestrictScalars ρ₂ X).mapCochainComplexPlus.obj K') (𝟙 _)
        ((etaleModuleRestrictScalars ρ₁
            (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
          ((etaleModuleRestrictScalars ρ₂
              (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj C))
        ((compactSupportRestrictionRestrictScalarsIso ρ₁ f j kbar
            ((etaleModuleRestrictScalars ρ₂ X).mapCochainComplexPlus.obj K')).inv ≫
          (etaleModuleRestrictScalars ρ₁
            (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map
          ((compactSupportRestrictionRestrictScalarsIso ρ₂ f j kbar K').inv ≫
            (etaleModuleRestrictScalars ρ₂
              (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map b))
        ((etaleModuleRestrictScalars ρ₂
            (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj C)
        ((compactSupportRestrictionRestrictScalarsIso ρ₂ f j kbar K').inv ≫
          (etaleModuleRestrictScalars ρ₂
            (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map b) (𝟙 _)
    (by rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id])
  rw [CategoryTheory.Functor.map_id] at e₁
  replace e₁ := (Category.id_comp
    (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ₁ f j kbar
          ((etaleModuleRestrictScalars ρ₂ X).mapCochainComplexPlus.obj K')).inv).symm.trans e₁
  have hμσ : (compactSupportRestriction f j kbar Λ).map
      (etaleModuleRestrictScalarsCompPlus ρ₁ ρ₂ σ w X K').hom ≫
      (compactSupportRestrictionRestrictScalarsIso σ f j kbar K').inv ≫
      (etaleModuleRestrictScalars σ
            (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map b =
      ((compactSupportRestrictionRestrictScalarsIso ρ₁ f j kbar
              ((etaleModuleRestrictScalars ρ₂ X).mapCochainComplexPlus.obj K')).inv ≫
            (etaleModuleRestrictScalars ρ₁
              (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map
            ((compactSupportRestrictionRestrictScalarsIso ρ₂ f j kbar K').inv ≫
              (etaleModuleRestrictScalars ρ₂
                (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map b)) ≫
          (etaleModuleRestrictScalarsCompPlus ρ₁ ρ₂ σ w
            (fieldBaseChange (Over.mk j.toBase) kbar) C).hom := by
    rw [← Category.assoc, compactSupportRestrictionRestrictScalarsIso_comp, Category.assoc,
      Category.assoc, etaleModuleRestrictScalarsCompPlus_hom_naturality]
    simp only [Functor.map_comp, Category.assoc]
  have eσ := compactSupportFrobeniusFunctor_map_comp_restrictScalarsIso_inv_eq (ρ := σ) (f := f)
    (j := j) (kbar := kbar)
    ((etaleModuleRestrictScalars ρ₁ X).mapCochainComplexPlus.obj
          ((etaleModuleRestrictScalars ρ₂ X).mapCochainComplexPlus.obj K')) K'
    (etaleModuleRestrictScalarsCompPlus ρ₁ ρ₂ σ w X K').hom
        ((etaleModuleRestrictScalars ρ₁
            (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
          ((etaleModuleRestrictScalars ρ₂
              (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj C))
        ((compactSupportRestrictionRestrictScalarsIso ρ₁ f j kbar
            ((etaleModuleRestrictScalars ρ₂ X).mapCochainComplexPlus.obj K')).inv ≫
          (etaleModuleRestrictScalars ρ₁
            (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map
          ((compactSupportRestrictionRestrictScalarsIso ρ₂ f j kbar K').inv ≫
            (etaleModuleRestrictScalars ρ₂
              (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map b)) C b
    (etaleModuleRestrictScalarsCompPlus ρ₁ ρ₂ σ w
          (fieldBaseChange (Over.mk j.toBase) kbar) C).hom hμσ
  have key := comp_restrict_cancel (ModuleCat.restrictScalars.{u + 1} ρ₁).mapDerivedCategoryPlus
    _ _ _ _ _ _ _ _ _ _ _ e₁ e₂
  rw [← ι_map_mapDerivedCategoryPlus_map]
  refine (Category.assoc _ _ _).symm.trans
      ((eq_whisker (DerivedCategory.Plus.ι.map_comp _ _).symm _).trans ?_)
  refine (eq_whisker (congrArg (fun z => DerivedCategory.Plus.ι.map z) key) _).trans
    (Eq.trans ?_ (congrArg (fun z => DerivedCategory.Plus.ι.map z) eσ).symm)
  refine comp_restrict_final (DerivedCategory.Plus.ι (C := ModuleCat.{u + 1} Λ))
    (T' := (ModuleCat.restrictScalars.{u + 1} σ).mapDerivedCategoryPlus.obj
      (compactSupportFrobeniusCohomology.{u, 0} S f j kbar K'))
    (Dd' :=
      (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{0, u + 1} ρ₁ ρ₂ σ w).hom.app
        (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj
          ((etaleModuleGlobalSections.{u, 0} S (Spec (.of kbar))).mapCochainComplexPlus.obj
            ((etaleModuleDirectImage.{u, 0} S
                (pullback.snd (Over.mk j.toBase).hom
                  (specAlgebraMap k kbar))).mapCochainComplexPlus.obj C)))))
    _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · exact restrictScalars_comp_directImageSections_Q_fieldBaseChange ρ₁ ρ₂ σ w (f := f) (j := j)
      (kbar := kbar) C
  · exact restrictScalars_comp_map_comp_inv ρ₁ ρ₂ σ w _ _


/-- **The comparison of `RΓ_c(X_k̄, -)` with restriction of scalars along a composite is the
composite of the comparisons**, in the unbounded derived category. -/
theorem compactSupportFrobeniusCohomologyRestrictScalarsIso_comp
    (K' : CochainComplex.Plus (EtaleModules.{u, 0} S X)) :
    DerivedCategory.Plus.ι.map (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ₁ f j kbar
        ((etaleModuleRestrictScalars ρ₂ X).mapCochainComplexPlus.obj K')).inv ≫
      (ModuleCat.restrictScalars.{u + 1} ρ₁).mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map
              (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ₂ f j kbar K').inv) ≫
      (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{0, u + 1} ρ₁ ρ₂ σ w).hom.app
        (DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, 0} S f j kbar K')) =
    DerivedCategory.Plus.ι.map ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
        (etaleModuleRestrictScalarsCompPlus ρ₁ ρ₂ σ w X K').hom ≫
      (compactSupportFrobeniusCohomologyRestrictScalarsIso σ f j kbar K').inv) := by
  have := Fintype.ofFinite k
  let N := (compactSupportRestriction f j kbar S).obj K'
  obtain ⟨a₀, ha₀⟩ := (CochainComplex.plus_iff _ N.obj).1 N.property
  obtain ⟨Rs, -, -⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a₀ N.obj
  let C : CochainComplex.Plus (EtaleModules.{u, 0} S (fieldBaseChange (Over.mk j.toBase) kbar)) :=
    ⟨Rs.cocomplex, Rs.boundedBelow⟩
  let b : N ⟶ C := ObjectProperty.homMk Rs.ι
  have hQb : IsIso (DerivedCategory.Plus.Q.map b) := by
    have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map b)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso
        (C := EtaleModules.{u, 0} S (fieldBaseChange (Over.mk j.toBase) kbar)) Rs.ι).2 inferInstance
    exact isIso_of_fully_faithful DerivedCategory.Plus.ι _
  exact compactSupportFrobeniusCohomologyRestrictScalarsIso_comp_of_resolution ρ₁ ρ₂ σ w f j kbar
    K' C Rs.injective b

end Stacks.EtaleCohomology

end
