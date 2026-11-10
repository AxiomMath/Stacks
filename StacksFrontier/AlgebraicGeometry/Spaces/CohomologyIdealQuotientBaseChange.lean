module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyAffineFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CohomologyAdicUniformBoundsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyFiniteAlgebra

/-!
# Cohomology of `ℱ / J ℱ` as cohomology on the closed subspace `V(J)`

Let `V` be an affine object of the site with functions `A = Γ(V, 𝒪)`, let `p : X ⟶ V` be a
morphism of algebraic spaces, `ℱ` a quasi-coherent `𝒪_X`-module and `J ⊆ A` an ideal.  Let
`X_J = Spec (A / J) ×_V X` be the closed subspace of `X` cut out by `J`, with `ℱ_J` the pullback
of `ℱ`.  Then

`H ⁱ (X, ℱ / J ℱ) ≅ H ⁱ (X_J, ℱ_J)`

as `A`-modules, where `ℱ / J ℱ` is identified with `ℱ ⊗_A (A / J)`: both are cokernels of the
multiplication map `⨁_{a ∈ J} ℱ ⟶ ℱ`.

## Main definitions

* `ModuleCat.sigmaIdealHom`: the map `⨁_{a ∈ J} A ⟶ A` whose `a`-th component is
  multiplication by `a`; its cokernel is `A / J`
  (`ModuleCat.isColimitCokernelCoforkIdealQuotientMk`).
* `AlgebraicGeometry.Space.sectionsTensorIdealQuotientIso`: `ℱ ⊗_A (A / J) ≅ ℱ / J ℱ` as
  abelian sheaves.
* `AlgebraicGeometry.Space.idealQuotientSpecObject`: `Spec (A / J)` as an object of the site
  over `V`.
* `AlgebraicGeometry.Space.cohomologyIdealQuotientBaseChangeEquiv`:
  `H ⁱ (X, ℱ / J ℱ) ≅ H ⁱ (X_J, ℱ_J)` as `A`-modules.

## References

* [Stacks Project, Tag 08B1](https://stacks.math.columbia.edu/tag/08B1)
* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u v

/-! ### `A / J` as a cokernel -/

namespace ModuleCat

variable {A : Type u} [CommRing A] (J : Ideal A)

/-- The quotient `A / J`, as an object of `ModuleCat A`. -/
abbrev idealQuotient : ModuleCat.{u} A := ModuleCat.of A (A ⧸ J)

/-- The projection `A ⟶ A / J`. -/
def idealQuotientMk : ModuleCat.of A A ⟶ idealQuotient J := ModuleCat.ofHom J.mkQ

/-- Multiplication by `a` on `A / J`. -/
def idealQuotientMul (a : A) : idealQuotient J ⟶ idealQuotient J :=
  ModuleCat.ofHom (LinearMap.lsmul A (A ⧸ J) a)

/-- Multiplication by `a` on `A / J` composed with `A ⟶ A / J` is `A ⟶ A / J` composed with
multiplication by `a` on `A`. -/
theorem idealQuotientMk_comp_idealQuotientMul (a : A) :
    idealQuotientMk J ≫ idealQuotientMul J a =
      ModuleCat.ofHom (LinearMap.toSpanSingleton A A a) ≫ idealQuotientMk J := by
  ext
  simp [idealQuotientMk, idealQuotientMul, mul_comm, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq]

/-- The map `⨁_{a ∈ J} A ⟶ A` whose `a`-th component is multiplication by `a`. -/
def sigmaIdealHom : (∐ fun _ : J => ModuleCat.of A A) ⟶ ModuleCat.of A A :=
  Sigma.desc fun a => ModuleCat.ofHom (LinearMap.toSpanSingleton A A a)

/-- The `a`-th component of `⨁_{a ∈ J} A ⟶ A` is multiplication by `a`. -/
@[reassoc]
theorem ι_sigmaIdealHom (a : J) :
    Sigma.ι (fun _ : J => ModuleCat.of A A) a ≫ sigmaIdealHom J =
      ModuleCat.ofHom (LinearMap.toSpanSingleton A A a) :=
  Sigma.ι_comp_desc _ _

/-- For `a ∈ J`, multiplication by `a` on `A` followed by `A ⟶ A / J` is zero. -/
theorem toSpanSingleton_comp_idealQuotientMk {a : A} (ha : a ∈ J) :
    ModuleCat.ofHom (LinearMap.toSpanSingleton A A a) ≫ idealQuotientMk J = 0 := by
  ext
  simpa [idealQuotientMk] using (Ideal.Quotient.eq_zero_iff_mem).2 ha

/-- The composite `⨁_{a ∈ J} A ⟶ A ⟶ A / J` is zero. -/
@[reassoc (attr := simp)]
theorem sigmaIdealHom_idealQuotientMk : sigmaIdealHom J ≫ idealQuotientMk J = 0 :=
  Sigma.hom_ext _ _ fun a => by
    rw [ι_sigmaIdealHom_assoc, toSpanSingleton_comp_idealQuotientMk J a.2, comp_zero]

/-- **`A / J` is the cokernel of `⨁_{a ∈ J} A ⟶ A`.** -/
def isColimitCokernelCoforkIdealQuotientMk :
    IsColimit (CokernelCofork.ofπ (idealQuotientMk J) (sigmaIdealHom_idealQuotientMk J)) :=
  ModuleCat.isColimitCokernelCofork _ _
    (LinearMap.exact_iff.2 (le_antisymm (fun x hx => by
      have hx' : x ∈ J := by simpa [idealQuotientMk] using hx
      refine ⟨(Sigma.ι (fun _ : J => ModuleCat.of A A) ⟨x, hx'⟩).hom 1, ?_⟩
      simpa using ConcreteCategory.congr_hom (ι_sigmaIdealHom J ⟨x, hx'⟩) 1)
      (by
        rintro _ ⟨z, rfl⟩
        exact ConcreteCategory.congr_hom (sigmaIdealHom_idealQuotientMk J) z)))
    J.mkQ_surjective

end ModuleCat

namespace CategoryTheory.Iso

variable {C : Type*} [Category C] {P Q P' R : C}

/-- Conjugation by `e₁⁻¹ ≫ e₂ ≫ e₃` carries an endomorphism `m` to `n`, given commuting squares
for each of the three isomorphisms. -/
theorem symm_trans_trans_hom_comm (e₁ : P ≅ Q) (e₂ : P ≅ P') (e₃ : P' ≅ R) (w : P ⟶ P)
    (m : Q ⟶ Q) (w' : P' ⟶ P') (n : R ⟶ R) (h₁ : w ≫ e₁.hom = e₁.hom ≫ m)
    (h₂ : w ≫ e₂.hom = e₂.hom ≫ w') (h₃ : w' ≫ e₃.hom = e₃.hom ≫ n) :
    m ≫ (e₁.symm ≪≫ e₂ ≪≫ e₃).hom = (e₁.symm ≪≫ e₂ ≪≫ e₃).hom ≫ n := by
  have h₁' : m ≫ e₁.inv = e₁.inv ≫ w := by
    rw [Iso.comp_inv_eq, Category.assoc, h₁, Iso.inv_hom_id_assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, h₁']
  simp only [Category.assoc, reassoc_of% h₂, h₃]

end CategoryTheory.Iso

namespace ModuleCat

variable {R Γ₁ Γ₂ : Type*} [CommRing R] [Ring Γ₁] [Ring Γ₂] (φ₁ : R →+* Γ₁) (φ₂ : R →+* Γ₂)
  {M₁ : ModuleCat.{v} Γ₁} {M₂ : ModuleCat.{v} Γ₂}

/-- An isomorphism of the underlying abelian groups of a `Γ₁`-module and a `Γ₂`-module that is
compatible with the actions of `R` through `φ₁` and `φ₂`, as an `R`-linear equivalence. -/
def restrictScalarsLinearEquivOfForget₂Iso
    (Θ : (forget₂ (ModuleCat.{v} Γ₁) AddCommGrpCat.{v}).obj M₁ ≅
      (forget₂ (ModuleCat.{v} Γ₂) AddCommGrpCat.{v}).obj M₂)
    (h : ∀ (r : R) (x : M₁), Θ.hom (φ₁ r • x) = φ₂ r • (show M₂ from Θ.hom x)) :
    (restrictScalars φ₁).obj M₁ ≃ₗ[R] (restrictScalars φ₂).obj M₂ :=
  AddEquiv.toLinearEquiv Θ.addCommGroupIsoToAddEquiv h

/-- An isomorphism `Θ` of underlying abelian groups commuting with endomorphisms `μ₁ r`, `μ₂ r`
that act as `φ₁ r`, `φ₂ r` is compatible with the actions of `R` through `φ₁` and `φ₂`. -/
theorem forget₂Iso_hom_smul_of_naturality
    (Θ : (forget₂ (ModuleCat.{v} Γ₁) AddCommGrpCat.{v}).obj M₁ ≅
      (forget₂ (ModuleCat.{v} Γ₂) AddCommGrpCat.{v}).obj M₂)
    (μ₁ : R → (M₁ ⟶ M₁)) (μ₂ : R → (M₂ ⟶ M₂)) (hμ₁ : ∀ r x, (μ₁ r).hom x = φ₁ r • x)
    (hμ₂ : ∀ r x, (μ₂ r).hom x = φ₂ r • x)
    (hΘ : ∀ r, (forget₂ (ModuleCat.{v} Γ₁) AddCommGrpCat.{v}).map (μ₁ r) ≫ Θ.hom =
      Θ.hom ≫ (forget₂ (ModuleCat.{v} Γ₂) AddCommGrpCat.{v}).map (μ₂ r)) (r : R) (x : M₁) :
    Θ.hom (φ₁ r • x) = φ₂ r • (show M₂ from Θ.hom x) := by
  rw [← hμ₁, ← hμ₂]
  exact ConcreteCategory.congr_hom (hΘ r) x

end ModuleCat

namespace AlgebraicGeometry.Space

attribute [local instance] hasInjectiveResolutions_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### `ℱ ⊗_A (A / J) ≅ ℱ / J ℱ` -/

section SheafIso

variable {V : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS} (p : X ⟶ schemeSpace V)
  (F : Modules.{u, u} B S hS X.1 X.2) (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))

/-- The functor `M ↦ ℱ ⊗_A M` preserves coequalizers. -/
instance sectionsTensorSheaf_preservesColimitsOfShape_walkingParallelPair :
    PreservesColimitsOfShape WalkingParallelPair
      (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F) :=
  have := sectionsTensorSheaf_preservesColimitsOfShape B S hS X
    (baseFunctionsToGlobalSections B S hS p) F (ULiftHom.{u} (ULift.{u} WalkingParallelPair))
  preservesColimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv.{u, u} WalkingParallelPair).symm _

/-- The underlying abelian sheaf functor on `𝒪_X`-modules preserves coequalizers. -/
instance moduleToAbelianSheaf_preservesColimitsOfShape_walkingParallelPair :
    PreservesColimitsOfShape WalkingParallelPair (moduleToAbelianSheaf B S hS X) :=
  have := moduleToAbelianSheaf_preservesColimitsOfShape B S hS X
    (ULiftHom.{u} (ULift.{u} WalkingParallelPair))
  preservesColimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv.{u, u} WalkingParallelPair).symm _

/-- The composite `⨁_{a ∈ J} ℱ ⟶ ℱ ⟶ ℱ / J ℱ` is zero. -/
@[reassoc (attr := simp)]
theorem idealMultipleHom_idealQuotientπ :
    idealMultipleHom (baseFunctionsToGlobalSections B S hS p) F J ≫
      idealQuotientπ (baseFunctionsToGlobalSections B S hS p) F J = 0 := by
  rw [← Abelian.image.fac (idealMultipleHom (baseFunctionsToGlobalSections B S hS p) F J),
    Category.assoc]
  exact (congrArg (_ ≫ ·) (idealMultipleι_idealQuotientπ _ F J)).trans comp_zero

/-- `ℱ / J ℱ` is the cokernel of `⨁_{a ∈ J} ℱ ⟶ ℱ`. -/
def isColimitIdealQuotientπ :
    IsColimit (CokernelCofork.ofπ (idealQuotientπ (baseFunctionsToGlobalSections B S hS p) F J)
      (idealMultipleHom_idealQuotientπ B S hS p F J)) :=
  isCokernelEpiComp
    (cokernelIsCokernel (idealMultipleι (baseFunctionsToGlobalSections B S hS p) F J))
    (Abelian.factorThruImage _) (Abelian.image.fac _).symm

/-- The composite `ℱ ⊗_A ⨁_{a ∈ J} A ⟶ ℱ ⊗_A A ≅ ℱ ⟶ ℱ / J ℱ` is zero. -/
theorem sectionsTensorSheaf_map_sigmaIdealHom_comp :
    (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F).map
        (ModuleCat.sigmaIdealHom J) ≫
      (sectionsTensorSheafUnitIso B S hS X (baseFunctionsToGlobalSections B S hS p) F).hom ≫
        (moduleToAbelianSheaf B S hS X).map
          (idealQuotientπ (baseFunctionsToGlobalSections B S hS p) F J) = 0 := by
  have := sectionsTensorSheaf_preservesColimitsOfShape B S hS X
    (baseFunctionsToGlobalSections B S hS p) F (Discrete J)
  refine (isColimitOfPreserves (sectionsTensorSheaf B S hS X
    (baseFunctionsToGlobalSections B S hS p) F) (colimit.isColimit
      (Discrete.functor fun _ : J => ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))).hom_ext fun ⟨a⟩ => ?_
  rw [comp_zero, Functor.mapCocone_ι_app, colimit.cocone_ι, ← Functor.map_comp_assoc,
    ModuleCat.ι_sigmaIdealHom J a,
    reassoc_of% (sectionsTensorSheaf_map_toSpanSingleton_comp_unitIso_hom B S hS p F a.1),
    ← Functor.map_comp, ← comp_globalSmul, globalSmul_idealQuotient_eq_zero _ F J a.2, comp_zero,
    Functor.map_zero, comp_zero]

/-- The composite `⨁_{a ∈ J} ℱ ⟶ ℱ ≅ ℱ ⊗_A A ⟶ ℱ ⊗_A (A / J)` is zero. -/
theorem moduleToAbelianSheaf_map_idealMultipleHom_comp :
    (moduleToAbelianSheaf B S hS X).map
        (idealMultipleHom (baseFunctionsToGlobalSections B S hS p) F J) ≫
      (sectionsTensorSheafUnitIso B S hS X (baseFunctionsToGlobalSections B S hS p) F).inv ≫
        (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F).map
          (ModuleCat.idealQuotientMk J) = 0 := by
  have := moduleToAbelianSheaf_preservesColimitsOfShape B S hS X (Discrete J)
  refine (isColimitOfPreserves (moduleToAbelianSheaf B S hS X) (colimit.isColimit
      (Discrete.functor fun _ : J => F))).hom_ext fun ⟨a⟩ => ?_
  have h : colimit.ι (Discrete.functor fun _ : J => F) ⟨a⟩ ≫
      idealMultipleHom (baseFunctionsToGlobalSections B S hS p) F J =
        globalSmul _ (baseFunctionsToGlobalSections B S hS p a) F :=
    ι_idealMultipleHom _ F J a
  rw [comp_zero, Functor.mapCocone_ι_app, colimit.cocone_ι, ← Functor.map_comp_assoc, h,
    ← cancel_epi
      (sectionsTensorSheafUnitIso B S hS X (baseFunctionsToGlobalSections B S hS p) F).hom,
    ← reassoc_of% (sectionsTensorSheaf_map_toSpanSingleton_comp_unitIso_hom B S hS p F a.1),
    Iso.hom_inv_id_assoc,
    ← Functor.map_comp, ModuleCat.toSpanSingleton_comp_idealQuotientMk J a.2, Functor.map_zero,
    comp_zero]

/-- `ℱ ⊗_A (A / J)` is the cokernel of `ℱ ⊗_A ⨁_{a ∈ J} A ⟶ ℱ ⊗_A A`. -/
def isColimitSectionsTensorSheafMkQ :
    IsColimit (CokernelCofork.ofπ ((sectionsTensorSheaf B S hS X
      (baseFunctionsToGlobalSections B S hS p) F).map (ModuleCat.idealQuotientMk J))
      (show (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F).map
          (ModuleCat.sigmaIdealHom J) ≫ (sectionsTensorSheaf B S hS X
            (baseFunctionsToGlobalSections B S hS p) F).map (ModuleCat.idealQuotientMk J) = 0 by
        rw [← Functor.map_comp, ModuleCat.sigmaIdealHom_idealQuotientMk, Functor.map_zero])) :=
  CokernelCofork.mapIsColimit _ (ModuleCat.isColimitCokernelCoforkIdealQuotientMk J) _

/-- The underlying abelian sheaf of `ℱ / J ℱ` is the cokernel of that of
`⨁_{a ∈ J} ℱ ⟶ ℱ`. -/
def isColimitModuleToAbelianSheafIdealQuotientπ :
    IsColimit (CokernelCofork.ofπ ((moduleToAbelianSheaf B S hS X).map
      (idealQuotientπ (baseFunctionsToGlobalSections B S hS p) F J))
      (show (moduleToAbelianSheaf B S hS X).map
          (idealMultipleHom (baseFunctionsToGlobalSections B S hS p) F J) ≫
            (moduleToAbelianSheaf B S hS X).map
              (idealQuotientπ (baseFunctionsToGlobalSections B S hS p) F J) = 0 by
        rw [← Functor.map_comp, idealMultipleHom_idealQuotientπ, Functor.map_zero])) :=
  CokernelCofork.mapIsColimit _ (isColimitIdealQuotientπ B S hS p F J) _

/-- The comparison `ℱ ⊗_A (A / J) ⟶ ℱ / J ℱ`, induced by `ℱ ⊗_A A ≅ ℱ ⟶ ℱ / J ℱ`. -/
def sectionsTensorIdealQuotientHom :
    (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F).obj
        (ModuleCat.idealQuotient J) ⟶
      (moduleToAbelianSheaf B S hS X).obj
        (idealQuotient (baseFunctionsToGlobalSections B S hS p) F J) :=
  (CokernelCofork.IsColimit.desc' (isColimitSectionsTensorSheafMkQ B S hS p F J) _
    (sectionsTensorSheaf_map_sigmaIdealHom_comp B S hS p F J)).1

/-- The comparison `ℱ ⊗_A (A / J) ⟶ ℱ / J ℱ` restricts along `ℱ ⊗_A A ⟶ ℱ ⊗_A (A / J)` to
`ℱ ⊗_A A ≅ ℱ ⟶ ℱ / J ℱ`. -/
@[reassoc]
theorem sectionsTensorSheaf_map_mkQ_comp_sectionsTensorIdealQuotientHom :
    (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F).map
        (ModuleCat.idealQuotientMk J) ≫ sectionsTensorIdealQuotientHom B S hS p F J =
      (sectionsTensorSheafUnitIso B S hS X (baseFunctionsToGlobalSections B S hS p) F).hom ≫
        (moduleToAbelianSheaf B S hS X).map
          (idealQuotientπ (baseFunctionsToGlobalSections B S hS p) F J) :=
  (CokernelCofork.IsColimit.desc' (isColimitSectionsTensorSheafMkQ B S hS p F J) _
    (sectionsTensorSheaf_map_sigmaIdealHom_comp B S hS p F J)).2

/-- The inverse comparison `ℱ / J ℱ ⟶ ℱ ⊗_A (A / J)`, induced by `ℱ ≅ ℱ ⊗_A A ⟶ ℱ ⊗_A (A / J)`. -/
def sectionsTensorIdealQuotientInv :
    (moduleToAbelianSheaf B S hS X).obj
        (idealQuotient (baseFunctionsToGlobalSections B S hS p) F J) ⟶
      (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F).obj
        (ModuleCat.idealQuotient J) :=
  (CokernelCofork.IsColimit.desc' (isColimitModuleToAbelianSheafIdealQuotientπ B S hS p F J) _
    (moduleToAbelianSheaf_map_idealMultipleHom_comp B S hS p F J)).1

/-- The comparison `ℱ / J ℱ ⟶ ℱ ⊗_A (A / J)` restricts along `ℱ ⟶ ℱ / J ℱ` to
`ℱ ≅ ℱ ⊗_A A ⟶ ℱ ⊗_A (A / J)`. -/
@[reassoc]
theorem moduleToAbelianSheaf_map_idealQuotientπ_comp_sectionsTensorIdealQuotientInv :
    (moduleToAbelianSheaf B S hS X).map
        (idealQuotientπ (baseFunctionsToGlobalSections B S hS p) F J) ≫
      sectionsTensorIdealQuotientInv B S hS p F J =
      (sectionsTensorSheafUnitIso B S hS X (baseFunctionsToGlobalSections B S hS p) F).inv ≫
        (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F).map
          (ModuleCat.idealQuotientMk J) :=
  (CokernelCofork.IsColimit.desc' (isColimitModuleToAbelianSheafIdealQuotientπ B S hS p F J) _
    (moduleToAbelianSheaf_map_idealMultipleHom_comp B S hS p F J)).2

/-- **`ℱ ⊗_A (A / J) ≅ ℱ / J ℱ`**, as abelian sheaves: both are the cokernel of the
multiplication map `⨁_{a ∈ J} ℱ ⟶ ℱ`.  It is characterized by
`AlgebraicGeometry.Space.sectionsTensorSheaf_map_mkQ_comp_sectionsTensorIdealQuotientHom`. -/
def sectionsTensorIdealQuotientIso :
    (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F).obj
        (ModuleCat.idealQuotient J) ≅
      (moduleToAbelianSheaf B S hS X).obj
        (idealQuotient (baseFunctionsToGlobalSections B S hS p) F J) where
  hom := sectionsTensorIdealQuotientHom B S hS p F J
  inv := sectionsTensorIdealQuotientInv B S hS p F J
  hom_inv_id := by
    have h : (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F).map
        (ModuleCat.idealQuotientMk J) ≫ sectionsTensorIdealQuotientHom B S hS p F J ≫
          sectionsTensorIdealQuotientInv B S hS p F J =
        (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F).map
          (ModuleCat.idealQuotientMk J) ≫ 𝟙 _ := by
      rw [sectionsTensorSheaf_map_mkQ_comp_sectionsTensorIdealQuotientHom_assoc,
        moduleToAbelianSheaf_map_idealQuotientπ_comp_sectionsTensorIdealQuotientInv,
        Iso.hom_inv_id_assoc, Category.comp_id]
    exact Cofork.IsColimit.hom_ext (isColimitSectionsTensorSheafMkQ B S hS p F J) h
  inv_hom_id := by
    have h : (moduleToAbelianSheaf B S hS X).map
        (idealQuotientπ (baseFunctionsToGlobalSections B S hS p) F J) ≫
          sectionsTensorIdealQuotientInv B S hS p F J ≫
            sectionsTensorIdealQuotientHom B S hS p F J =
        (moduleToAbelianSheaf B S hS X).map
          (idealQuotientπ (baseFunctionsToGlobalSections B S hS p) F J) ≫ 𝟙 _ := by
      rw [moduleToAbelianSheaf_map_idealQuotientπ_comp_sectionsTensorIdealQuotientInv_assoc,
        sectionsTensorSheaf_map_mkQ_comp_sectionsTensorIdealQuotientHom,
        Iso.inv_hom_id_assoc, Category.comp_id]
    exact Cofork.IsColimit.hom_ext (isColimitModuleToAbelianSheafIdealQuotientπ B S hS p F J) h

/-- `ℱ ⊗_A (A / J) ≅ ℱ / J ℱ` carries multiplication by `a ∈ A` on `A / J` to multiplication by
the function `p^♯ a` on `ℱ / J ℱ`. -/
theorem sectionsTensorIdealQuotientIso_hom_naturality
    (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F).map
        (ModuleCat.idealQuotientMul J a) ≫ sectionsTensorIdealQuotientHom B S hS p F J =
      sectionsTensorIdealQuotientHom B S hS p F J ≫ (moduleToAbelianSheaf B S hS X).map
        (globalSmul _ (baseFunctionsToGlobalSections B S hS p a)
          (idealQuotient (baseFunctionsToGlobalSections B S hS p) F J)) := by
  have h : (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F).map
        (ModuleCat.idealQuotientMk J) ≫
      (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F).map
        (ModuleCat.idealQuotientMul J a) ≫ sectionsTensorIdealQuotientHom B S hS p F J =
      (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F).map
        (ModuleCat.idealQuotientMk J) ≫ sectionsTensorIdealQuotientHom B S hS p F J ≫
        (moduleToAbelianSheaf B S hS X).map
          (globalSmul _ (baseFunctionsToGlobalSections B S hS p a)
            (idealQuotient (baseFunctionsToGlobalSections B S hS p) F J)) :=
    calc _ = (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F).map
            (ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ a)) ≫
          (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F).map
            (ModuleCat.idealQuotientMk J) ≫ sectionsTensorIdealQuotientHom B S hS p F J := by
          rw [← Functor.map_comp_assoc
              (sectionsTensorSheaf B S hS X (baseFunctionsToGlobalSections B S hS p) F)
              (ModuleCat.idealQuotientMk J),
            ModuleCat.idealQuotientMk_comp_idealQuotientMul, Functor.map_comp_assoc]
      _ = (sectionsTensorSheafUnitIso B S hS X (baseFunctionsToGlobalSections B S hS p) F).hom ≫
            (moduleToAbelianSheaf B S hS X).map
              (globalSmul _ (baseFunctionsToGlobalSections B S hS p a) F) ≫
            (moduleToAbelianSheaf B S hS X).map
              (idealQuotientπ (baseFunctionsToGlobalSections B S hS p) F J) := by
          rw [sectionsTensorSheaf_map_mkQ_comp_sectionsTensorIdealQuotientHom B S hS p F J]
          exact (reassoc_of%
            (sectionsTensorSheaf_map_toSpanSingleton_comp_unitIso_hom B S hS p F a)) _
      _ = (sectionsTensorSheafUnitIso B S hS X (baseFunctionsToGlobalSections B S hS p) F).hom ≫
            (moduleToAbelianSheaf B S hS X).map
              (idealQuotientπ (baseFunctionsToGlobalSections B S hS p) F J) ≫
            (moduleToAbelianSheaf B S hS X).map
              (globalSmul _ (baseFunctionsToGlobalSections B S hS p a)
                (idealQuotient (baseFunctionsToGlobalSections B S hS p) F J)) :=
          congrArg ((sectionsTensorSheafUnitIso B S hS X
              (baseFunctionsToGlobalSections B S hS p) F).hom ≫ ·) (by
            rw [← Functor.map_comp (moduleToAbelianSheaf B S hS X),
              ← Functor.map_comp (moduleToAbelianSheaf B S hS X), comp_globalSmul])
      _ = _ := (sectionsTensorSheaf_map_mkQ_comp_sectionsTensorIdealQuotientHom_assoc B S hS p F J
          _).symm
  exact Cofork.IsColimit.hom_ext (isColimitSectionsTensorSheafMkQ B S hS p F J) h

end SheafIso

/-! ### `H ⁱ (X, ℱ / J ℱ) ≅ H ⁱ (X_J, ℱ_J)` -/

section Cohomology

variable {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))

/-- `A / J` is of finite type over `A`. -/
instance algebraFiniteType_quotient :
    Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ J) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ _ J) Ideal.Quotient.mk_surjective

/-- `Spec (A / J)` as an object of the site over the affine object `V` with `A = Γ(V, 𝒪)`. -/
abbrev idealQuotientSpecObject : BigFppfOver B S hS :=
  specAlgebraObjectOver B S hS Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (RingEquiv.refl _)
    (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ J)

/-- The closed immersion `Spec (A / J) ⟶ V`. -/
abbrev idealQuotientSpecMap : idealQuotientSpecObject B S hS J ⟶ V :=
  specAlgebraMapOver B S hS Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (RingEquiv.refl _)
    (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ J)

/-- `Spec (A / J)` is affine. -/
instance isAffine_idealQuotientSpecObject :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (idealQuotientSpecObject B S hS J)) :=
  inferInstanceAs (IsAffine (Spec _))

/-- On global functions, `Spec (A / J) ⟶ V` is the projection `A ⟶ A / J` followed by
`A / J ≅ Γ(Spec (A / J), 𝒪)`. -/
theorem idealQuotientSpecMap_appTop (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    ((BigFppfOver.toScheme B S hS).map (idealQuotientSpecMap B S hS J)).appTop a =
      (Scheme.ΓSpecIso (.of (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ J))).inv
        (Ideal.Quotient.mk J a) :=
  specAlgebraToAffine_appTop B S hS _ (RingEquiv.refl _) _ a

/-- The functions on `Spec (A / J)` are `A / J`, as `A`-modules. -/
def idealQuotientSpecFunctionsIso :
    ModuleCat.idealQuotient J ≅ baseChangeTensorModule B S hS (idealQuotientSpecMap B S hS J) :=
  letI := ((BigFppfOver.toScheme B S hS).map (idealQuotientSpecMap B S hS J)).appTop.hom.toAlgebra
  LinearEquiv.toModuleIso (X₁ := Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ J)
    (X₂ := Γ((BigFppfOver.toScheme B S hS).obj (idealQuotientSpecObject B S hS J), ⊤))
    { toFun := fun x =>
        (Scheme.ΓSpecIso (.of (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ J))).inv x
      invFun := fun y =>
        (Scheme.ΓSpecIso (.of (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ J))).hom y
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a x => by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        have h : (a • Ideal.Quotient.mk J x : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ J) =
            Ideal.Quotient.mk J a * Ideal.Quotient.mk J x :=
          Algebra.smul_def a _
        rw [h, map_mul, ← idealQuotientSpecMap_appTop B S hS J a]
        rfl
      left_inv := fun x => Iso.inv_hom_id_apply
        (Scheme.ΓSpecIso (.of (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ J))) x
      right_inv := fun y => Iso.hom_inv_id_apply
        (Scheme.ΓSpecIso (.of (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ J))) y }

/-- The isomorphism `A / J ≅ Γ(Spec (A / J), 𝒪)` carries multiplication by `a ∈ A` to
multiplication by the image of `a` in `Γ(Spec (A / J), 𝒪)`. -/
theorem idealQuotientMul_comp_idealQuotientSpecFunctionsIso_hom
    (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    ModuleCat.idealQuotientMul J a ≫ (idealQuotientSpecFunctionsIso B S hS J).hom =
      (idealQuotientSpecFunctionsIso B S hS J).hom ≫ baseChangeTensorModuleMul B S hS
        (idealQuotientSpecMap B S hS J)
        (((BigFppfOver.toScheme B S hS).map (idealQuotientSpecMap B S hS J)).appTop a) :=
  ModuleCat.hom_ext (LinearMap.ext fun x =>
    map_smul (idealQuotientSpecFunctionsIso B S hS J).toLinearEquiv a x)

variable {X : AlgebraicSpaces B S hS} (p : X ⟶ schemeSpace V) (F : Modules.{u, u} B S hS X.1 X.2)

/-- The closed subspace `X_J = Spec (A / J) ×_V X` of `X`. -/
abbrev idealQuotientBaseChange : AlgebraicSpaces B S hS :=
  pullback (schemeSpaceMap (idealQuotientSpecMap B S hS J)) p

/-- The pullback `ℱ_J` of `ℱ` to `X_J = Spec (A / J) ×_V X`. -/
abbrev idealQuotientBaseChangeModule :
    Modules.{u, u} B S hS (idealQuotientBaseChange B S hS J p).1
      (idealQuotientBaseChange B S hS J p).2 :=
  (modulePullback B S hS (pullback.snd (schemeSpaceMap (idealQuotientSpecMap B S hS J)) p)).obj F

/-- The action of `A` on the functions of `X_J`, through `A ⟶ A / J`. -/
abbrev idealQuotientBaseChangeRingHom :
    Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+*
      GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (idealQuotientBaseChange B S hS J p).1 (idealQuotientBaseChange B S hS J p).2).O) :=
  (baseFunctionsToGlobalSections B S hS
    (pullback.fst (schemeSpaceMap (idealQuotientSpecMap B S hS J)) p)).comp
    ((BigFppfOver.toScheme B S hS).map (idealQuotientSpecMap B S hS J)).appTop.hom

/-- `H ⁱ (X, ℱ / J ℱ) ≅ H ⁱ (X_J, ℱ_J)` as abelian groups: `ℱ / J ℱ ≅ ℱ ⊗_A (A / J)`
(`AlgebraicGeometry.Space.sectionsTensorIdealQuotientIso`), `A / J = Γ(Spec (A / J), 𝒪)`, and
`AlgebraicGeometry.Space.cohomologySectionsTensorBaseChangeIso`. -/
abbrev cohomologyIdealQuotientBaseChangeIso (hF : F.IsQuasicoherentOnSite) (i : ℕ) :
    (forget₂ _ AddCommGrpCat.{u + 1}).obj ((spaceCohomology B S hS X i).obj
        (idealQuotient (baseFunctionsToGlobalSections B S hS p) F J)) ≅
      (forget₂ _ AddCommGrpCat.{u + 1}).obj ((spaceCohomology B S hS
        (idealQuotientBaseChange B S hS J p) i).obj (idealQuotientBaseChangeModule B S hS J p F)) :=
  (cohomologyIsoOfAbelianSheafIso B S hS (sectionsTensorIdealQuotientIso B S hS p F J) i).symm ≪≫
    (cohomologySectionsTensor B S hS X (baseFunctionsToGlobalSections B S hS p) F i).mapIso
      (idealQuotientSpecFunctionsIso B S hS J) ≪≫
    cohomologySectionsTensorBaseChangeIso B S hS (idealQuotientSpecMap B S hS J) p F hF i

/-- The isomorphism `H ⁱ (X, ℱ / J ℱ) ≅ H ⁱ (X_J, ℱ_J)` carries multiplication by `a ∈ A` on
the source to multiplication by `a` on the target. -/
theorem cohomologyIdealQuotientBaseChangeIso_hom_naturality (hF : F.IsQuasicoherentOnSite)
    (i : ℕ)
    (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    (forget₂ _ AddCommGrpCat.{u + 1}).map ((spaceCohomology B S hS X i).map
        (globalSmul _ (baseFunctionsToGlobalSections B S hS p a)
          (idealQuotient (baseFunctionsToGlobalSections B S hS p) F J))) ≫
        (cohomologyIdealQuotientBaseChangeIso B S hS J p F hF i).hom =
      (cohomologyIdealQuotientBaseChangeIso B S hS J p F hF i).hom ≫
        (forget₂ _ AddCommGrpCat.{u + 1}).map ((spaceCohomology B S hS
          (idealQuotientBaseChange B S hS J p) i).map (globalSmul _
            (idealQuotientBaseChangeRingHom B S hS J p a)
            (idealQuotientBaseChangeModule B S hS J p F))) :=
  Iso.symm_trans_trans_hom_comm _ _ _ _ _ _ _
    (cohomologyIsoOfAbelianSheafIso_hom_naturality B S hS _ i _ _
      (sectionsTensorIdealQuotientIso_hom_naturality B S hS p F J a))
    (((cohomologySectionsTensor B S hS X (baseFunctionsToGlobalSections B S hS p) F i).map_comp
        _ _).symm.trans ((congrArg (cohomologySectionsTensor B S hS X
          (baseFunctionsToGlobalSections B S hS p) F i).map
        (idealQuotientMul_comp_idealQuotientSpecFunctionsIso_hom B S hS J a)).trans
        ((cohomologySectionsTensor B S hS X (baseFunctionsToGlobalSections B S hS p) F i).map_comp
          _ _)))
    (cohomologySectionsTensorBaseChangeIso_hom_naturality B S hS (idealQuotientSpecMap B S hS J) p
      F hF i (((BigFppfOver.toScheme B S hS).map (idealQuotientSpecMap B S hS J)).appTop a))

/-- **`H ⁱ (X, ℱ / J ℱ) ≅ H ⁱ (X_J, ℱ_J)` as `A`-modules**, for a quasi-coherent `ℱ` on an
algebraic space `X` over the affine object `V`, `A = Γ(V, 𝒪)`, `J ⊆ A` an ideal and
`X_J = Spec (A / J) ×_V X`. -/
def cohomologyIdealQuotientBaseChangeEquiv (hF : F.IsQuasicoherentOnSite) (i : ℕ) :
    cohomologyRes (baseFunctionsToGlobalSections B S hS p) i
        (idealQuotient (baseFunctionsToGlobalSections B S hS p) F J) ≃ₗ[Γ((BigFppfOver.toScheme
          B S hS).obj V, ⊤)]
      cohomologyRes (idealQuotientBaseChangeRingHom B S hS J p) i
        (idealQuotientBaseChangeModule B S hS J p F) :=
  ModuleCat.restrictScalarsLinearEquivOfForget₂Iso _ _
    (cohomologyIdealQuotientBaseChangeIso B S hS J p F hF i)
    (ModuleCat.forget₂Iso_hom_smul_of_naturality _ _ _
      (fun a => (spaceCohomology B S hS X i).map (globalSmul _
        (baseFunctionsToGlobalSections B S hS p a)
        (idealQuotient (baseFunctionsToGlobalSections B S hS p) F J)))
      (fun a => (spaceCohomology B S hS (idealQuotientBaseChange B S hS J p) i).map (globalSmul _
        (idealQuotientBaseChangeRingHom B S hS J p a)
        (idealQuotientBaseChangeModule B S hS J p F)))
      (fun _ x => spaceCohomology_map_globalSmul_apply B S hS i _ _ x)
      (fun _ x => spaceCohomology_map_globalSmul_apply B S hS i _ _ x)
      (cohomologyIdealQuotientBaseChangeIso_hom_naturality B S hS J p F hF i))

end Cohomology

end AlgebraicGeometry.Space

end
