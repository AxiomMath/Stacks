module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import StacksFrontier.Algebra.Category.ModuleCat.NoncommExtendScalars
public import Mathlib.CategoryTheory.Sites.Adjunction

/-!
# Restriction of scalars of sheaves of modules on the small étale site

Let `ρ : Λ →+* Λ'` be a morphism of rings, not necessarily commutative. A sheaf of `Λ'`-modules on
the small étale site of a scheme `X` is a sheaf of `Λ`-modules through `ρ`; this is the functor
`res_ρ : Mod(X_étale, Λ') ⥤ Mod(X_étale, Λ)` along which [Tag 03V2] compares the cohomology of a
`ℤ/ℓⁿ⁺¹ℤ`-module with the cohomology of the same sheaf viewed as a `ℤ_ℓ`-module.

This file records the functor and its interaction with the underived functors that compactly
supported cohomology is built from:

* `res_ρ` has a left adjoint (sheafified extension of scalars) and a right adjoint (coextension
  of scalars, which needs no sheafification), so it is exact;
* it commutes on the nose with direct image `f_*` and with global sections, both of which only
  restrict or evaluate sections;
* it commutes up to a canonical isomorphism with inverse image `f^{-1}` and with extension by
  zero `j_!`.  These comparisons are the mates of the strict comparisons of the right adjoints,
  `Stacks.EtaleCohomology.coefficientPullbackTwoSquare`, so they are compatible with the units
  of the adjunctions by construction.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleRestrictScalars`: the functor `res_ρ`.
* `Stacks.EtaleCohomology.etaleModuleCoextendScalarsAdj`: `res_ρ ⊣ coextension of scalars`.
* `Stacks.EtaleCohomology.etaleModuleNoncommExtendScalarsAdj`: `extension of scalars ⊣ res_ρ`;
  `Stacks.EtaleCohomology.etaleModuleExtendScalarsAdj` is the same for commutative rings, through
  Mathlib's `ModuleCat.extendScalars`.
* `Stacks.EtaleCohomology.etaleModuleInverseImageRestrictScalars`:
  `f^{-1} ∘ res_ρ ≅ res_ρ ∘ f^{-1}`.
* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroRestrictScalars`:
  `j_! ∘ res_ρ ≅ res_ρ ∘ j_!`.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {Λ Λ' : Type} [Ring Λ] [Ring Λ'] (ρ : Λ →+* Λ')

/-! ### The functor and its adjoints -/

/-- **Restriction of scalars along `ρ : Λ →+* Λ'`** for sheaves of modules on the small étale
site of `X`: a sheaf of `Λ'`-modules read as a sheaf of `Λ`-modules. -/
abbrev etaleModuleRestrictScalars (X : Scheme.{u}) :
    EtaleModules.{u, 0} Λ' X ⥤ EtaleModules.{u, 0} Λ X :=
  sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ρ)

/-- Coextension of scalars along `ρ` for sheaves of modules on the small étale site:
`M ↦ Hom_Λ(Λ', M)` sectionwise.  It preserves the sheaf condition, being a right adjoint. -/
abbrev etaleModuleCoextendScalars (X : Scheme.{u}) :
    EtaleModules.{u, 0} Λ X ⥤ EtaleModules.{u, 0} Λ' X :=
  sheafCompose X.smallEtaleTopology
    (ModuleCat.coextendScalars ρ : ModuleCat.{u + 1} Λ ⥤ ModuleCat.{u + 1} Λ')

/-- **`res_ρ ⊣ coextension of scalars`** on sheaves of modules on the small étale site: the
sectionwise adjunction, restricted to sheaves. -/
def etaleModuleCoextendScalarsAdj (X : Scheme.{u}) :
    etaleModuleRestrictScalars ρ X ⊣ etaleModuleCoextendScalars ρ X :=
  Adjunction.restrictFullyFaithful
    ((ModuleCat.restrictCoextendScalarsAdj.{u + 1} ρ).whiskerRight X.Etaleᵒᵖ)
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _)
    (Iso.refl _) (Iso.refl _)

/-- Sheafified extension of scalars along `ρ` for not necessarily commutative rings, the left
adjoint of `res_ρ`, built from `Stacks.NoncommChangeOfRings.extendScalars`. -/
abbrev etaleModuleNoncommExtendScalars (X : Scheme.{u}) :
    EtaleModules.{u, 0} Λ X ⥤ EtaleModules.{u, 0} Λ' X :=
  Sheaf.composeAndSheafify X.smallEtaleTopology
    (Stacks.NoncommChangeOfRings.extendScalars.{u + 1} ρ :
      ModuleCat.{u + 1} Λ ⥤ ModuleCat.{u + 1} Λ')

/-- **`extension of scalars ⊣ res_ρ`** on sheaves of modules on the small étale site, for not
necessarily commutative rings. -/
def etaleModuleNoncommExtendScalarsAdj (X : Scheme.{u}) :
    etaleModuleNoncommExtendScalars ρ X ⊣ etaleModuleRestrictScalars ρ X :=
  Sheaf.adjunction _ (Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{u + 1} ρ)

/-- `res_ρ` is a left adjoint, with right adjoint coextension of scalars. -/
instance etaleModuleRestrictScalars_isLeftAdjoint (X : Scheme.{u}) :
    (etaleModuleRestrictScalars ρ X).IsLeftAdjoint :=
  (etaleModuleCoextendScalarsAdj ρ X).isLeftAdjoint

/-- `res_ρ` is a right adjoint, with left adjoint sheafified extension of scalars. -/
instance etaleModuleRestrictScalars_isRightAdjoint (X : Scheme.{u}) :
    (etaleModuleRestrictScalars ρ X).IsRightAdjoint :=
  (etaleModuleNoncommExtendScalarsAdj ρ X).isRightAdjoint

/-- `res_ρ` is additive. -/
instance etaleModuleRestrictScalars_additive (X : Scheme.{u}) :
    (etaleModuleRestrictScalars ρ X).Additive where
  map_add := rfl

/-- `res_ρ` is left exact, being a right adjoint. -/
instance etaleModuleRestrictScalars_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (etaleModuleRestrictScalars ρ X) :=
  inferInstance

/-- `res_ρ` is right exact, being a left adjoint. -/
instance etaleModuleRestrictScalars_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (etaleModuleRestrictScalars ρ X) :=
  inferInstance


section Commutative

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- Sheafified extension of scalars along a morphism `ρ` of commutative rings, the left adjoint of
`res_ρ`. -/
abbrev etaleModuleExtendScalars (X : Scheme.{u}) :
    EtaleModules.{u, 0} Λ X ⥤ EtaleModules.{u, 0} Λ' X :=
  Sheaf.composeAndSheafify X.smallEtaleTopology
    (ModuleCat.extendScalars ρ : ModuleCat.{u + 1} Λ ⥤ ModuleCat.{u + 1} Λ')

/-- **`extension of scalars ⊣ res_ρ`** on sheaves of modules on the small étale site. -/
def etaleModuleExtendScalarsAdj (X : Scheme.{u}) :
    etaleModuleExtendScalars ρ X ⊣ etaleModuleRestrictScalars ρ X :=
  Sheaf.adjunction _ (ModuleCat.extendRestrictScalarsAdj.{u + 1} ρ)

end Commutative

/-! ### The comparison for the abstract inverse image -/

section AbstractPullback

variable {C D : Type*} [Category* C] [Category* D] (uf : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [uf.IsContinuous J K]
  {A B : Type*} [Category* A] [Category* B] (Gf : A ⥤ B)
  [HasWeakSheafify K A] [HasWeakSheafify K B]
  [∀ P : Cᵒᵖ ⥤ A, uf.op.HasLeftKanExtension P] [∀ P : Cᵒᵖ ⥤ B, uf.op.HasLeftKanExtension P]
  [Gf.PreservesLeftKanExtensions uf.op]
  [J.HasSheafCompose Gf] [K.HasSheafCompose Gf] [K.PreservesSheafification Gf]

/-- **The comparison of the two composites of the abstract inverse image
`CategoryTheory.Functor.sheafPullback` with a change of coefficients**: the mate of the strict
commutation of direct image with the change of coefficients,
`Stacks.EtaleCohomology.coefficientPushforwardTwoSquare`. -/
def coefficientSheafPullbackTwoSquare :
    TwoSquare (sheafCompose J Gf) (uf.sheafPullback A J K) (uf.sheafPullback B J K)
      (sheafCompose K Gf) :=
  (mateEquiv (uf.sheafAdjunctionContinuous A J K) (uf.sheafAdjunctionContinuous B J K)).symm
    (coefficientPushforwardTwoSquare uf J K Gf)

/-- The unit of `f^{-1} ⊣ f_*` followed by `f_*` of the identification of the two inverse images
is the unit of the Kan-extension construction. -/
private theorem unit_comp_map_sheafPullbackIso_hom {A' : Type*} [Category* A']
    [HasWeakSheafify K A'] [∀ P : Cᵒᵖ ⥤ A', uf.op.HasLeftKanExtension P] (c : Sheaf J A') :
    (uf.sheafAdjunctionContinuous A' J K).unit.app c ≫
      (uf.sheafPushforwardContinuous A' J K).map
        ((Functor.sheafPullbackConstruction.sheafPullbackIso uf A' J K).hom.app c) =
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf A' J K).unit.app c :=
  Adjunction.unit_leftAdjointUniq_hom_app (uf.sheafAdjunctionContinuous A' J K)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf A' J K) c

omit [Gf.PreservesLeftKanExtensions uf.op] [K.PreservesSheafification Gf] in
/-- The comparison is compatible with the units: `Gf` applied to the unit of `f^{-1} ⊣ f_*` is
the unit at the image followed by direct image of the comparison. -/
theorem coefficientSheafPullbackTwoSquare_unit (c : Sheaf J A) :
    (sheafCompose J Gf).map ((uf.sheafAdjunctionContinuous A J K).unit.app c) =
      (uf.sheafAdjunctionContinuous B J K).unit.app ((sheafCompose J Gf).obj c) ≫
        (uf.sheafPushforwardContinuous B J K).map
          ((coefficientSheafPullbackTwoSquare uf J K Gf).app c) := by
  have h := unit_mateEquiv_symm (uf.sheafAdjunctionContinuous A J K)
    (uf.sheafAdjunctionContinuous B J K) (coefficientPushforwardTwoSquare uf J K Gf) c
  exact (Category.comp_id _).symm.trans h

omit [K.PreservesSheafification Gf] in
/-- The comparison for the abstract inverse image is the comparison for the Kan-extension
construction, conjugated by the identifications of the two inverse images. -/
theorem coefficientSheafPullbackTwoSquare_app (c : Sheaf J A) :
    (coefficientSheafPullbackTwoSquare uf J K Gf).app c =
      (Functor.sheafPullbackConstruction.sheafPullbackIso uf B J K).hom.app
          ((sheafCompose J Gf).obj c) ≫
        coefficientPullbackComparison uf J K Gf c ≫
        (sheafCompose K Gf).map
          ((Functor.sheafPullbackConstruction.sheafPullbackIso uf A J K).inv.app c) := by
  refine ((uf.sheafAdjunctionContinuous B J K).homEquiv _ _).injective ?_
  simp only [Adjunction.homEquiv_unit]
  rw [← coefficientSheafPullbackTwoSquare_unit]
  have e1 := unit_comp_map_sheafPullbackIso_hom uf J K ((sheafCompose J Gf).obj c)
  have e2 := unit_comp_map_sheafPullbackIso_hom uf J K c
  have e3 : (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf A J K).unit.app c ≫
      (uf.sheafPushforwardContinuous A J K).map
        ((Functor.sheafPullbackConstruction.sheafPullbackIso uf A J K).inv.app c) =
      (uf.sheafAdjunctionContinuous A J K).unit.app c := by
    rw [← e2, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  rw [← e3, Functor.map_comp, Functor.map_comp, Functor.map_comp, reassoc_of% e1,
    reassoc_of% (coefficientPullbackComparison_unit uf J K Gf c)]
  congr 1
  exact (Category.id_comp _).symm

/-- **The comparison for the abstract inverse image is invertible.** -/
instance isIso_coefficientSheafPullbackTwoSquare :
    IsIso (coefficientSheafPullbackTwoSquare uf J K Gf) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro c
  rw [coefficientSheafPullbackTwoSquare_app, ← coefficientPullbackTwoSquare_app]
  infer_instance

end AbstractPullback

/-! ### Commutation with the underived functors -/

/-- `res_ρ` preserves colimits of every size, being a left adjoint sectionwise; in particular it
preserves the left Kan extensions defining inverse image and extension by zero. -/
instance restrictScalars_preservesLeftKanExtensions {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) [∀ P : C ⥤ ModuleCat.{u + 1} Λ', L.HasPointwiseLeftKanExtension P] :
    (ModuleCat.restrictScalars.{u + 1} ρ).PreservesLeftKanExtensions L := by
  intro P
  have : PreservesColimitsOfSize.{max u_1 u_2, max u_3 u_4}
      (ModuleCat.restrictScalars.{u + 1} ρ) :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1} ρ).leftAdjoint_preservesColimits
  infer_instance

/-- **Direct image commutes with `res_ρ` on the nose**: `res_ρ ∘ f_* = f_* ∘ res_ρ`. -/
def etaleModuleDirectImageRestrictScalars {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleModuleDirectImage.{u, 0} Λ' f ⋙ etaleModuleRestrictScalars ρ Y ≅
      etaleModuleRestrictScalars ρ X ⋙ etaleModuleDirectImage.{u, 0} Λ f :=
  Iso.refl _

/-- **Global sections commute with `res_ρ` on the nose.** -/
def etaleModuleGlobalSectionsRestrictScalars (X : Scheme.{u}) :
    etaleModuleGlobalSections.{u, 0} Λ' X ⋙ ModuleCat.restrictScalars.{u + 1} ρ ≅
      etaleModuleRestrictScalars ρ X ⋙ etaleModuleGlobalSections.{u, 0} Λ X :=
  Functor.isoWhiskerRight (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ') terminalIsTerminal) _ ≪≫
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl) :
      (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ')).obj (op (⊤_ X.Etale)) ⋙
          ModuleCat.restrictScalars.{u + 1} ρ ≅
        etaleModuleRestrictScalars ρ X ⋙
          (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op (⊤_ X.Etale))) ≪≫
    Functor.isoWhiskerLeft (etaleModuleRestrictScalars ρ X)
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
        (ModuleCat.{u + 1} Λ) terminalIsTerminal).symm

/-- **Inverse image commutes with `res_ρ`**: the comparison `f^{-1} ∘ res_ρ ⟶ res_ρ ∘ f^{-1}`
is the mate of the strict commutation of direct image with `res_ρ`, and it is invertible. -/
def etaleModuleInverseImageRestrictScalars {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleModuleRestrictScalars ρ Y ⋙ etaleModuleInverseImage.{u, 0} Λ f ≅
      etaleModuleInverseImage.{u, 0} Λ' f ⋙ etaleModuleRestrictScalars ρ X :=
  asIso (coefficientSheafPullbackTwoSquare (smallEtaleBaseChange f) Y.smallEtaleTopology
    X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ρ))

/-- **Extension by zero commutes with `res_ρ`**, by the same mate construction for
`j_! ⊣ j^{-1}`. -/
def etaleModuleExtensionByZeroRestrictScalars {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    etaleModuleRestrictScalars ρ U ⋙ etaleModuleExtensionByZero.{u, 0} Λ j ≅
      etaleModuleExtensionByZero.{u, 0} Λ' j ⋙ etaleModuleRestrictScalars ρ X :=
  asIso (coefficientPullbackTwoSquare (Scheme.Etale.smallEtaleCompose j) U.smallEtaleTopology
    X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ρ))

end Stacks.EtaleCohomology

end
