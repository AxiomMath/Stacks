module

public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

/-!
# The adjunction of a derived extension of scalars, and composition

Let `f : R →+* A` be a homomorphism of commutative rings and let `D` be a total derived
extension of scalars along `f`, in arbitrary models of the two derived categories. This file
records the adjunction `D ⊣ f_*` of Stacks 0GMT for the bundle `D`, the fact that a
bounded-above complex of flat modules computes `D`, and the composition of derived extensions of
scalars along `R → R₁ → R₂`: the composite of the two derived functors is the derived functor
of the composite, by uniqueness of left adjoints, and adjoint transposes compose accordingly.

## Main definitions

* `CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.adjunction`: the
  adjunction between `D.functor` and derived restriction of scalars.
* `CochainComplex.DerivedExtensionScalars.derivedRestrictScalarsCompIso`: derived restriction
  of scalars along `φ₂` and then `φ₁` is derived restriction along `φ₂ ∘ φ₁`, in any models.
* `CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.compIso`: the
  composite of two derived extensions of scalars is the derived extension along the composite.

## Main results

* `CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.comparison_isIso_of_flat`:
  a bounded-above complex of flat modules computes derived extension of scalars.
* `CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.compIso_homEquiv_symm`:
  the transpose of a composite `g ≫ φ₁_* h` along `φ₂ ∘ φ₁` is the image of the transpose of `g`
  followed by the transpose of `h`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w wR wA w₀ w₁ w₂

namespace CochainComplex.DerivedExtensionScalars

namespace TotalDerivedExtensionScalars

variable {R : Type u} {A : Type w} [CommRing R] [CommRing A] {f : R →+* A}
  [HasDerivedCategory.{wR} (ModuleCat.{max v u w} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{max v u w} A)]

/-- **Stacks 0GMT** for a bundle: derived extension of scalars `D.functor` is left adjoint to
derived restriction of scalars. -/
def adjunction (D : TotalDerivedExtensionScalars.{u, v, w, wR, wA} f) :
    D.functor ⊣ (ModuleCat.restrictScalars.{max v u w, u, w} f).mapDerivedCategory :=
  @derivedExtensionScalarsAdjunction.{u, w, v} R A _ _ f _ _ D.functor D.comparison
    D.isLeftDerived

/-- A bounded-above complex of flat modules computes derived extension of scalars: it is K-flat
(Stacks 064K). -/
theorem comparison_isIso_of_flat (D : TotalDerivedExtensionScalars.{u, v, w, wR, wA} f)
    (P : CochainComplex (ModuleCat.{max v u w} R) ℤ) (n : ℤ) [P.IsStrictlyLE n]
    [∀ i, Module.Flat R (P.X i)] : IsIso (D.comparison.app P) :=
  D.comparison_isIso_of_kFlat P (CochainComplex.KFlat.kFlat_of_flat.{u, max v w} P n)

end TotalDerivedExtensionScalars

section Comp

variable {R R₁ R₂ : Type u} [CommRing R] [CommRing R₁] [CommRing R₂]
  [HasDerivedCategory.{w₀} (ModuleCat.{max v u} R)]
  [HasDerivedCategory.{w₁} (ModuleCat.{max v u} R₁)]
  [HasDerivedCategory.{w₂} (ModuleCat.{max v u} R₂)]

/-- Derived restriction of scalars along `φ₂` followed by derived restriction along `φ₁` is
derived restriction along `φ₂ ∘ φ₁`, in any models of the three derived categories. -/
def derivedRestrictScalarsCompIso (φ₁ : R →+* R₁) (φ₂ : R₁ →+* R₂) :
    (ModuleCat.restrictScalars.{max v u} φ₂).mapDerivedCategory ⋙
      (ModuleCat.restrictScalars.{max v u} φ₁).mapDerivedCategory ≅
        (ModuleCat.restrictScalars.{max v u} (φ₂.comp φ₁)).mapDerivedCategory := by
  let F := ModuleCat.restrictScalars.{max v u} φ₂
  let G := ModuleCat.restrictScalars.{max v u} φ₁
  let H := ModuleCat.restrictScalars.{max v u} (φ₂.comp φ₁)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max v u} R₂) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ F.mapDerivedCategory ⋙ G.mapDerivedCategory)
    (DerivedCategory.Q ⋙ H.mapDerivedCategory)
    (F.mapDerivedCategory ⋙ G.mapDerivedCategory) H.mapDerivedCategory
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso
        (ModuleCat.restrictScalarsComp φ₁ φ₂).symm (ComplexShape.up ℤ)) _ ≪≫
      H.mapDerivedCategoryFactors.symm)

namespace TotalDerivedExtensionScalars

variable {φ₁ : R →+* R₁} {φ₂ : R₁ →+* R₂}

/-- **Composition of derived extensions of scalars.** For `φ₁ : R →+* R₁`, `φ₂ : R₁ →+* R₂` and
derived extensions of scalars `D₁`, `D₂`, `D₂₁` along `φ₁`, `φ₂` and `φ₂ ∘ φ₁`, the composite
`D₁ ⋙ D₂` is `D₂₁`: both are left adjoint to derived restriction of scalars along `φ₂ ∘ φ₁`. -/
def compIso (D₁ : TotalDerivedExtensionScalars.{u, v, u, w₀, w₁} φ₁)
    (D₂ : TotalDerivedExtensionScalars.{u, v, u, w₁, w₂} φ₂)
    (D₂₁ : TotalDerivedExtensionScalars.{u, v, u, w₀, w₂} (φ₂.comp φ₁)) :
    D₁.functor ⋙ D₂.functor ≅ D₂₁.functor :=
  Adjunction.leftAdjointUniq
    ((D₁.adjunction.comp D₂.adjunction).ofNatIsoRight (derivedRestrictScalarsCompIso φ₁ φ₂))
    D₂₁.adjunction

/-- **Transposes compose.** For `g : K ⟶ φ₁_* M` and `h : M ⟶ φ₂_* N`, the transpose along
`φ₂ ∘ φ₁` of `g ≫ φ₁_* h`, read through `derivedRestrictScalarsCompIso`, is `compIso` followed
by the image under `D₂` of the transpose of `g` and then by the transpose of `h`. -/
theorem compIso_homEquiv_symm (D₁ : TotalDerivedExtensionScalars.{u, v, u, w₀, w₁} φ₁)
    (D₂ : TotalDerivedExtensionScalars.{u, v, u, w₁, w₂} φ₂)
    (D₂₁ : TotalDerivedExtensionScalars.{u, v, u, w₀, w₂} (φ₂.comp φ₁))
    {K : DerivedCategory (ModuleCat.{max v u} R)} {M : DerivedCategory (ModuleCat.{max v u} R₁)}
    {N : DerivedCategory (ModuleCat.{max v u} R₂)}
    (g : K ⟶ (ModuleCat.restrictScalars.{max v u} φ₁).mapDerivedCategory.obj M)
    (h : M ⟶ (ModuleCat.restrictScalars.{max v u} φ₂).mapDerivedCategory.obj N) :
    (D₂₁.adjunction.homEquiv K N).symm
        (g ≫ (ModuleCat.restrictScalars.{max v u} φ₁).mapDerivedCategory.map h ≫
          (derivedRestrictScalarsCompIso φ₁ φ₂).hom.app N) =
      (compIso D₁ D₂ D₂₁).inv.app K ≫
        D₂.functor.map ((D₁.adjunction.homEquiv K M).symm g) ≫
          (D₂.adjunction.homEquiv M N).symm h := by
  let A := (D₁.adjunction.comp D₂.adjunction).ofNatIsoRight (derivedRestrictScalarsCompIso φ₁ φ₂)
  have key : ∀ x : K ⟶ (ModuleCat.restrictScalars.{max v u} (φ₂.comp φ₁)).mapDerivedCategory.obj N,
      (compIso D₁ D₂ D₂₁).hom.app K ≫ (D₂₁.adjunction.homEquiv K N).symm x =
        (A.homEquiv K N).symm x := by
    intro x
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    change (Adjunction.leftAdjointUniq A D₂₁.adjunction).hom.app K ≫ _ ≫ _ = _
    rw [← Category.assoc, ← (Adjunction.leftAdjointUniq A D₂₁.adjunction).hom.naturality x,
      Category.assoc, Adjunction.leftAdjointUniq_hom_app_counit]
  rw [← cancel_epi ((compIso D₁ D₂ D₂₁).hom.app K), key, Iso.hom_inv_id_app_assoc,
    Adjunction.homEquiv_ofNatIsoRight_symm_apply]
  simp only [Category.assoc, Iso.hom_inv_id_app, Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
  have hid : (ModuleCat.restrictScalars.{max v u} φ₁).mapDerivedCategory.map h ≫
      𝟙 (((ModuleCat.restrictScalars.{max v u} φ₂).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{max v u} φ₁).mapDerivedCategory).obj N) =
      (ModuleCat.restrictScalars.{max v u} φ₁).mapDerivedCategory.map h :=
    Category.comp_id _
  rw [hid, Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_left_symm]

end TotalDerivedExtensionScalars

end Comp

end CochainComplex.DerivedExtensionScalars
