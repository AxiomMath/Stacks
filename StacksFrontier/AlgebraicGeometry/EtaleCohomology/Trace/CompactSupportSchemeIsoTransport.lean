module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSheafExcisionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicExcisionWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageStalkTowerNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldExtensionCohomologyLinear
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison

/-!
# Compactly supported cohomology along an isomorphism of schemes

Let `α : Y ⟶ X` be an isomorphism of schemes. Extension by zero along `α` is an equivalence of
categories of sheaves of `Λ`-modules, with inverse the extension by zero along `α⁻¹`
(`(α⁻¹ ≫ α)_! = (𝟙 X)_! = 𝟭`); hence `α_! α⁻¹ ≅ 𝟭`
(`Stacks.EtaleCohomology.etaleModuleInverseImageExtensionByZeroIsoOfIsIso`).

If `j` compactifies `X` over a finite field `k`, the composite `j ∘ α` compactifies `Y`
(`AlgebraicGeometry.CompactificationOf.restrictOpen`) and
`RΓ_c(Y_k̄, α⁻¹ G) ≅ RΓ_c(X_k̄, α_! α⁻¹ G) ≅ RΓ_c(X_k̄, G)`, compatibly with the canonical
geometric Frobenius. Applied to the levels of an ℓ-adic sheaf `F` with coefficients in `O` this
gives an `E`-linear isomorphism `Hⁱ_c(Y_k̄, α⁻¹F ⊗ ℚ_ℓ) ≃ Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` carrying `π_Y^*` to
`π_X^*` (`Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.rationalIsoOfIsIsoLinearEquiv`). This
moves the cohomology of a fibre of Laumon's family along its identification with a base change
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleInverseImageExtensionByZeroIsoOfIsIso`: `α_! α⁻¹ ≅ 𝟭`.
* `Stacks.EtaleCohomology.compactSupportSheafCohomologyInverseImageIsoOfIsIso`.
* `Stacks.EtaleCohomology.LAdicSheaf.geometricCompactlySupportedCohomologySystemIsoOfIsIso`.
* `Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.rationalIsoOfIsIsoLinearEquiv`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.rationalIsoOfIsIsoLinearEquiv_frobenius`.

The standard model `HasDerivedCategory.standard` is used because compactly supported cohomology is
defined there.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-! ### Extension by zero along an isomorphism -/

section ExtensionByZero

variable (Λ : Type r) [Ring Λ]

/-- Extension by zero along equal étale morphisms; stated on variables. -/
public def etaleModuleExtensionByZeroCongrIso {U X : Scheme.{u}} {a b : U ⟶ X} [Etale a]
    [Etale b] (h : a = b) :
    etaleModuleExtensionByZero.{u, r} Λ a ≅ etaleModuleExtensionByZero.{u, r} Λ b := by
  subst h
  exact Iso.refl _

variable {Y X : Scheme.{u}} (α : Y ⟶ X) [IsIso α]

/-- `(α⁻¹)_! ⋙ α_! ≅ 𝟭` for an isomorphism `α`. -/
public def etaleModuleExtensionByZeroInvCompIso :
    etaleModuleExtensionByZero.{u, r} Λ (inv α) ⋙ etaleModuleExtensionByZero.{u, r} Λ α ≅ 𝟭 _ :=
  (etaleModuleExtensionByZeroCompIso.{u, r} Λ (inv α) α).symm ≪≫
    etaleModuleExtensionByZeroCongrIso Λ (IsIso.inv_hom_id α) ≪≫ etaleModuleExtensionByZeroIdIso Λ X

/-- `α_! ⋙ (α⁻¹)_! ≅ 𝟭` for an isomorphism `α`. -/
public def etaleModuleExtensionByZeroCompInvIso :
    etaleModuleExtensionByZero.{u, r} Λ α ⋙ etaleModuleExtensionByZero.{u, r} Λ (inv α) ≅ 𝟭 _ :=
  (etaleModuleExtensionByZeroCompIso.{u, r} Λ α (inv α)).symm ≪≫
    etaleModuleExtensionByZeroCongrIso Λ (IsIso.hom_inv_id α) ≪≫ etaleModuleExtensionByZeroIdIso Λ Y

/-- **Extension by zero along an isomorphism is an equivalence**, with inverse the extension by
zero along the inverse. -/
public def etaleModuleExtensionByZeroEquivOfIsIso :
    EtaleModules.{u, r} Λ Y ≌ EtaleModules.{u, r} Λ X :=
  CategoryTheory.Equivalence.mk (etaleModuleExtensionByZero.{u, r} Λ α)
    (etaleModuleExtensionByZero.{u, r} Λ (inv α))
    (etaleModuleExtensionByZeroCompInvIso Λ α).symm (etaleModuleExtensionByZeroInvCompIso Λ α)

/-- **`α_! α⁻¹ ≅ 𝟭`** for an isomorphism `α`, with `α⁻¹` the restriction. -/
public def etaleModuleRestrictionExtensionByZeroIsoOfIsIso :
    etaleModuleRestriction.{u, r} Λ α ⋙ etaleModuleExtensionByZero.{u, r} Λ α ≅ 𝟭 _ :=
  Functor.isoWhiskerRight
    ((etaleModuleExtensionByZeroEquivOfIsIso Λ α).toAdjunction.rightAdjointUniq
      (etaleModuleExtensionByZeroAdj.{u, r} Λ α)).symm _ ≪≫
    etaleModuleExtensionByZeroInvCompIso Λ α

/-- **`α_! α⁻¹ ≅ 𝟭`** for an isomorphism `α`, with `α⁻¹` the inverse image. -/
public def etaleModuleInverseImageExtensionByZeroIsoOfIsIso :
    etaleModuleInverseImage.{u, r} Λ α ⋙ etaleModuleExtensionByZero.{u, r} Λ α ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (etaleModuleInverseImageRestrictionIso.{u, r} Λ α) _ ≪≫
    etaleModuleRestrictionExtensionByZeroIsoOfIsIso Λ α

end ExtensionByZero

/-! ### `Hⁱ_c` of sheaves along an isomorphism -/

section Sheaf

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] (i : ℤ) {Y : Scheme.{u}} (α : Y ⟶ X) [IsIso α]

/-- **`Hⁱ_c(Y_k̄, α⁻¹ G) ≅ Hⁱ_c(X_k̄, G)`** for an isomorphism `α : Y ⟶ X`, `Y` compactified by
`j ∘ α`, naturally in the sheaf `G` on `X`. -/
public def compactSupportSheafCohomologyInverseImageIsoOfIsIso :
    etaleModuleInverseImage.{u, 0} Λ α ⋙
        compactSupportSheafCohomology Λ (α ≫ f) (j.restrictOpen α) kbar i ≅
      compactSupportSheafCohomology Λ f j kbar i :=
  Functor.isoWhiskerLeft _ (compactSupportSheafCohomologyRestrictOpenIso Λ f j kbar i α) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (etaleModuleInverseImageExtensionByZeroIsoOfIsIso Λ α) _ ≪≫
    Functor.leftUnitor _

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The identification `Hⁱ_c(Y_k̄, α⁻¹ -) ≅ Hⁱ_c(X_k̄, -)` carries `π_Y^*` to `π_X^*`. -/
public theorem compactSupportSheafCohomologyInverseImageIsoOfIsIso_hom_frobenius
    (G : EtaleModules.{u, 0} Λ X) :
    (compactSupportSheafFrobenius Λ (α ≫ f) (j.restrictOpen α) kbar p q hcard i).app
        ((etaleModuleInverseImage.{u, 0} Λ α).obj G) ≫
      (compactSupportSheafCohomologyInverseImageIsoOfIsIso Λ f j kbar i α).hom.app G =
    (compactSupportSheafCohomologyInverseImageIsoOfIsIso Λ f j kbar i α).hom.app G ≫
      (compactSupportSheafFrobenius Λ f j kbar p q hcard i).app G := by
  have h := congrArg (fun t => NatTrans.app t ((etaleModuleInverseImage.{u, 0} Λ α).obj G))
    (compactSupportSheafCohomologyRestrictOpenIso_hom_frobenius Λ f j kbar i α p q hcard)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  have hn := (compactSupportSheafFrobenius Λ f j kbar p q hcard i).naturality
    ((etaleModuleInverseImageExtensionByZeroIsoOfIsIso Λ α).hom.app G)
  simp only [compactSupportSheafCohomologyInverseImageIsoOfIsIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp, Functor.comp_obj,
    Functor.id_obj]
  rw [reassoc_of% h, Category.assoc]
  exact congrArg (_ ≫ ·) hn.symm

end Sheaf

/-! ### Pasting squares along composites of isomorphisms -/

section Paste

variable {𝒞 : Type*} [Category* 𝒞]

/-- Pasting two squares along composites of isomorphisms; stated on variables. -/
public theorem comp_trans_hom_eq_trans_hom_comp {A₁ A₂ A₃ B₁ B₂ B₃ : 𝒞} (e₁ : A₁ ≅ A₂)
    (e₂ : A₂ ≅ A₃) (e₁' : B₁ ≅ B₂) (e₂' : B₂ ≅ B₃) (a₁ : A₁ ⟶ B₁) (a₂ : A₂ ⟶ B₂) (a₃ : A₃ ⟶ B₃)
    (h₁ : a₁ ≫ e₁'.hom = e₁.hom ≫ a₂) (h₂ : a₂ ≫ e₂'.hom = e₂.hom ≫ a₃) :
    a₁ ≫ (e₁' ≪≫ e₂').hom = (e₁ ≪≫ e₂).hom ≫ a₃ := by
  rw [Iso.trans_hom, Iso.trans_hom, reassoc_of% h₁, h₂, Category.assoc]

/-- A square of isomorphisms read backwards; stated on variables. -/
public theorem comp_symm_hom_eq_symm_hom_comp {A₁ A₂ B₁ B₂ : 𝒞} (e : A₁ ≅ A₂) (e' : B₁ ≅ B₂)
    (a₁ : A₁ ⟶ B₁) (a₂ : A₂ ⟶ B₂) (h : a₁ ≫ e'.hom = e.hom ≫ a₂) :
    a₂ ≫ e'.symm.hom = e.symm.hom ≫ a₁ := by
  rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end Paste

/-! ### The towers of an ℓ-adic sheaf along an isomorphism -/

section LAdic

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {X X' : B.Scheme} [IsNoetherian X.1] [IsNoetherian X'.1] (g : X' ⟶ X)
  [IsIso (B.inclusion.map g)]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f)) (kbar : Type u)
  [Field kbar] [Algebra k kbar] (i : ℤ)

/-- **`(n ↦ Hⁱ_c(X'_k̄, (g⁻¹F)ₙ)) ≅ (n ↦ Hⁱ_c(X_k̄, Fₙ))`** for an isomorphism `g : X' ⟶ X`, `X'`
compactified by `j ∘ g`. -/
public def LAdicSheaf.geometricCompactlySupportedCohomologySystemIsoOfIsIso
    (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    LAdicSheaf.geometricCompactlySupportedCohomologySystem B X' ℓ (B.inclusion.map g ≫ f)
        (j.restrictOpen (B.inclusion.map g)) kbar (LAdicSheaf.inverseImage g F) i ≅
      LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i :=
  (LAdicSheaf.padicTowerCohomologyIso B X' ℓ (B.inclusion.map g ≫ f)
      (j.restrictOpen (B.inclusion.map g)) kbar (LAdicSheaf.inverseImage g F) i).symm ≪≫
    (Functor.isoWhiskerRight (LAdicSheaf.padicTowerInverseImageIso B ℓ g F).symm _ ≪≫
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
        (compactSupportSheafCohomologyInverseImageIsoOfIsIso ℤ_[ℓ] f j kbar i
          (B.inclusion.map g))) ≪≫
      LAdicSheaf.padicTowerCohomologyIso B X ℓ f j kbar F i)

omit [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] [AlgebraicGeometry.IsNoetherian X'.1] [Fintype k]
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- The middle step is natural in the tower. -/
private theorem associator_isoWhiskerLeft_naturality {T T' : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X.1}
    (τ : T ⟶ T') :
    Functor.whiskerRight (Functor.whiskerRight τ
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map g)))
        (compactSupportSheafCohomology ℤ_[ℓ] (B.inclusion.map g ≫ f)
          (j.restrictOpen (B.inclusion.map g)) kbar i) ≫
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft T'
        (compactSupportSheafCohomologyInverseImageIsoOfIsIso ℤ_[ℓ] f j kbar i
          (B.inclusion.map g))).hom =
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft T
        (compactSupportSheafCohomologyInverseImageIsoOfIsIso ℤ_[ℓ] f j kbar i
          (B.inclusion.map g))).hom ≫
      Functor.whiskerRight τ (compactSupportSheafCohomology ℤ_[ℓ] f j kbar i) := by
  ext n : 2
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Iso.trans_hom,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.id_comp]
  exact (compactSupportSheafCohomologyInverseImageIsoOfIsIso ℤ_[ℓ] f j kbar i
    (B.inclusion.map g)).hom.naturality (τ.app n)

/-- **The identification is natural in the ℓ-adic sheaf.** -/
public theorem LAdicSheaf.geometricCompactlySupportedCohomologySystemIsoOfIsIso_hom_naturality
    {F G : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ G) :
    LAdicSheaf.geometricCompactlySupportedCohomologySystemMap (B.inclusion.map g ≫ f)
        (j.restrictOpen (B.inclusion.map g)) kbar (LAdicSheaf.inverseImageMap g φ) i ≫
      (LAdicSheaf.geometricCompactlySupportedCohomologySystemIsoOfIsIso B ℓ g f j kbar i G).hom =
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemIsoOfIsIso B ℓ g f j kbar i F).hom ≫
      LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar φ i := by
  have h₁ := comp_symm_hom_eq_symm_hom_comp _ _ _ _
    (LAdicSheaf.padicTowerCohomologyIso_hom_naturality B ℓ (B.inclusion.map g ≫ f)
      (j.restrictOpen (B.inclusion.map g)) kbar (LAdicSheaf.inverseImageMap g φ) i)
  have h₂ : Functor.whiskerRight (LAdicSheaf.padicTowerMap (LAdicSheaf.inverseImageMap g φ))
        (compactSupportSheafCohomology ℤ_[ℓ] (B.inclusion.map g ≫ f)
          (j.restrictOpen (B.inclusion.map g)) kbar i) ≫
      (Functor.isoWhiskerRight (LAdicSheaf.padicTowerInverseImageIso B ℓ g G).symm _).hom =
    (Functor.isoWhiskerRight (LAdicSheaf.padicTowerInverseImageIso B ℓ g F).symm _).hom ≫
      Functor.whiskerRight (Functor.whiskerRight (LAdicSheaf.padicTowerMap φ)
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map g)))
        (compactSupportSheafCohomology ℤ_[ℓ] (B.inclusion.map g ≫ f)
          (j.restrictOpen (B.inclusion.map g)) kbar i) := by
    have h := comp_symm_hom_eq_symm_hom_comp _ _ _ _
      (LAdicSheaf.padicTowerInverseImageIso_hom_naturality B ℓ g φ)
    have h' := congrArg (fun t => Functor.whiskerRight t
      (compactSupportSheafCohomology ℤ_[ℓ] (B.inclusion.map g ≫ f)
        (j.restrictOpen (B.inclusion.map g)) kbar i)) h
    simp only [Functor.whiskerRight_comp] at h'
    exact h'
  exact comp_trans_hom_eq_trans_hom_comp _ _ _ _ _ _ _ h₁
    (comp_trans_hom_eq_trans_hom_comp _ _ _ _ _ _ _ h₂
      (comp_trans_hom_eq_trans_hom_comp _ _ _ _ _ _ _
        (associator_isoWhiskerLeft_naturality B ℓ g f j kbar i (LAdicSheaf.padicTowerMap φ))
        (LAdicSheaf.padicTowerCohomologyIso_hom_naturality B ℓ f j kbar φ i)))

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The identification carries `π_{X'}^*` to `π_X^*`** on the inverse systems. -/
public theorem LAdicSheaf.geometricCompactlySupportedCohomologySystemIsoOfIsIso_hom_frobenius
    (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X' ℓ (B.inclusion.map g ≫ f)
        (j.restrictOpen (B.inclusion.map g)) kbar (LAdicSheaf.inverseImage g F) i
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] (B.inclusion.map g ≫ f)
          (j.restrictOpen (B.inclusion.map g)) kbar p q hcard) ≫
      (LAdicSheaf.geometricCompactlySupportedCohomologySystemIsoOfIsIso B ℓ g f j kbar i F).hom =
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemIsoOfIsIso B ℓ g f j kbar i F).hom ≫
      LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar F i
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard) := by
  have h₁ := comp_symm_hom_eq_symm_hom_comp _ _ _ _
    (LAdicSheaf.padicTowerCohomologyIso_hom_frobenius B X' ℓ (B.inclusion.map g ≫ f)
      (j.restrictOpen (B.inclusion.map g)) kbar p q hcard (LAdicSheaf.inverseImage g F) i)
  have h₂ : Functor.whiskerLeft (LAdicSheaf.padicTower B X' ℓ (LAdicSheaf.inverseImage g F))
        (compactSupportSheafFrobenius ℤ_[ℓ] (B.inclusion.map g ≫ f)
          (j.restrictOpen (B.inclusion.map g)) kbar p q hcard i) ≫
      (Functor.isoWhiskerRight (LAdicSheaf.padicTowerInverseImageIso B ℓ g F).symm _).hom =
    (Functor.isoWhiskerRight (LAdicSheaf.padicTowerInverseImageIso B ℓ g F).symm _).hom ≫
      Functor.whiskerLeft (LAdicSheaf.padicTower B X ℓ F ⋙
          etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map g))
        (compactSupportSheafFrobenius ℤ_[ℓ] (B.inclusion.map g ≫ f)
          (j.restrictOpen (B.inclusion.map g)) kbar p q hcard i) := by
    ext n : 2
    exact ((compactSupportSheafFrobenius ℤ_[ℓ] (B.inclusion.map g ≫ f)
      (j.restrictOpen (B.inclusion.map g)) kbar p q hcard i).naturality
        ((LAdicSheaf.padicTowerInverseImageIso B ℓ g F).inv.app n)).symm
  have h₃ : Functor.whiskerLeft (LAdicSheaf.padicTower B X ℓ F ⋙
          etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map g))
        (compactSupportSheafFrobenius ℤ_[ℓ] (B.inclusion.map g ≫ f)
          (j.restrictOpen (B.inclusion.map g)) kbar p q hcard i) ≫
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
        (compactSupportSheafCohomologyInverseImageIsoOfIsIso ℤ_[ℓ] f j kbar i
          (B.inclusion.map g))).hom =
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
        (compactSupportSheafCohomologyInverseImageIsoOfIsIso ℤ_[ℓ] f j kbar i
          (B.inclusion.map g))).hom ≫
      Functor.whiskerLeft (LAdicSheaf.padicTower B X ℓ F)
        (compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i) := by
    ext n : 2
    simp only [NatTrans.comp_app, Iso.trans_hom, Functor.associator_hom_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp]
    exact compactSupportSheafCohomologyInverseImageIsoOfIsIso_hom_frobenius ℤ_[ℓ] f j kbar i
      (B.inclusion.map g) p q hcard _
  exact comp_trans_hom_eq_trans_hom_comp _ _ _ _ _ _ _ h₁
    (comp_trans_hom_eq_trans_hom_comp _ _ _ _ _ _ _ h₂
      (comp_trans_hom_eq_trans_hom_comp _ _ _ _ _ _ _ h₃
        (LAdicSheaf.padicTowerCohomologyIso_hom_frobenius B X ℓ f j kbar p q hcard F i)))

/-- **`Hⁱ_c(X'_k̄, g⁻¹F ⊗ ℚ_ℓ) ≅ Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`** for an isomorphism `g : X' ⟶ X`. -/
public def LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsoOfIsIso
    (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X' ℓ (B.inclusion.map g ≫ f)
        (j.restrictOpen (B.inclusion.map g)) kbar (LAdicSheaf.inverseImage g F) i ≅
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i :=
  (rationalLim.{u + 1} (ℓ := ℓ)).mapIso
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemIsoOfIsIso B ℓ g f j kbar i F)

/-- The rational identification is natural in the ℓ-adic sheaf. -/
public theorem LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsoOfIsIso_hom_naturality
    {F G : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ G) :
    (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
        (LAdicSheaf.geometricCompactlySupportedCohomologyMap (B.inclusion.map g ≫ f)
          (j.restrictOpen (B.inclusion.map g)) kbar (LAdicSheaf.inverseImageMap g φ) i) ≫
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsoOfIsIso B ℓ g f j kbar i G).hom =
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsoOfIsIso B ℓ g f j kbar i F).hom ≫
      (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
        (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ i) :=
  map_comp_map_eq_of_comp_eq (rationalLim.{u + 1} (ℓ := ℓ)) _ _ _ _
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemIsoOfIsIso_hom_naturality B ℓ g f j kbar
      i φ)

/-- The rational identification carries `π_{X'}^*` to `π_X^*`. -/
public theorem LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsoOfIsIso_hom_frobenius
    (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X' ℓ (B.inclusion.map g ≫ f)
        (j.restrictOpen (B.inclusion.map g)) kbar p q hcard (LAdicSheaf.inverseImage g F) i ≫
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsoOfIsIso B ℓ g f j kbar i F).hom =
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsoOfIsIso B ℓ g f j kbar i F).hom ≫
      LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i :=
  map_comp_map_eq_of_comp_eq (rationalLim.{u + 1} (ℓ := ℓ)) _ _ _ _
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemIsoOfIsIso_hom_frobenius B ℓ g f j kbar
      i p q hcard F)

variable {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (F : LAdicSheaf.CoefficientSheaf B X ℓ O)
  (E : Type) [CommRing E] [Algebra ℚ_[ℓ] E] [Algebra O E]
  [IsLocalization (Submonoid.powers (ℓ : O)) E]

set_option backward.isDefEq.respectTransparency false in
/-- **`Hⁱ_c(X'_k̄, g⁻¹F ⊗ ℚ_ℓ) ≃ Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`, `E`-linearly**, for an isomorphism
`g : X' ⟶ X`, `X'` compactified by `j ∘ g`. -/
public def LAdicSheaf.CoefficientSheaf.rationalIsoOfIsIsoLinearEquiv :
    letI := (LAdicSheaf.CoefficientSheaf.inverseImage g F).rationalCohomologyModule
      (B.inclusion.map g ≫ f) (j.restrictOpen (B.inclusion.map g)) kbar i E
    letI := F.rationalCohomologyModule f j kbar i E
    LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X' ℓ (B.inclusion.map g ≫ f)
        (j.restrictOpen (B.inclusion.map g)) kbar
        (LAdicSheaf.CoefficientSheaf.inverseImage g F).toLAdicSheaf i ≃ₗ[E]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i :=
  LAdicSheaf.CoefficientSheaf.rationalLinearEquivOfCommute _ F _ f _ j kbar kbar i i E
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsoOfIsIso B ℓ g f j kbar i
      F.toLAdicSheaf).toLinearEquiv
    (fun o v => by
      have h := LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsoOfIsIso_hom_naturality B ℓ
        g f j kbar i (F.act o).asHom
      exact congrArg (fun t => t.hom v) h)

omit [Algebra ℚ_[ℓ] E] in
set_option backward.isDefEq.respectTransparency false in
/-- The `E`-linear identification carries `π_{X'}^*` to `π_X^*`. -/
public theorem LAdicSheaf.CoefficientSheaf.rationalIsoOfIsIsoLinearEquiv_frobenius
    (v : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X' ℓ (B.inclusion.map g ≫ f)
        (j.restrictOpen (B.inclusion.map g)) kbar
        (LAdicSheaf.CoefficientSheaf.inverseImage g F).toLAdicSheaf i) :
    F.rationalIsoOfIsIsoLinearEquiv B ℓ g f j kbar i E
        ((LAdicSheaf.CoefficientSheaf.inverseImage g F).rationalGeometricCompactlySupportedFrobenius
          (B.inclusion.map g ≫ f) (j.restrictOpen (B.inclusion.map g)) kbar i E p q hcard v) =
      F.rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard
        (F.rationalIsoOfIsIsoLinearEquiv B ℓ g f j kbar i E v) := by
  have h := LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsoOfIsIso_hom_frobenius B ℓ g f
    j kbar i p q hcard F.toLAdicSheaf
  exact congrArg (fun t => t.hom v) h

end LAdic

end Stacks.EtaleCohomology

end
