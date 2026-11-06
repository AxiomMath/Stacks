module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AlgebraicClosureIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSchemeIsoTransport

/-!
# `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` does not depend on the algebraic closure, `E`-linearly

Let `X` be a separated scheme of finite type over a finite field `k`, compactified by `j`, and
`σ : k̄₁ ≃ₐ[k] k̄₂` an isomorphism of `k`-algebras between two fields. The natural isomorphism
`Hⁱ_c(X_{k̄₂}, -) ≅ Hⁱ_c(X_{k̄₁}, -)` on sheaves of `ℤ_ℓ`-modules
(`Stacks.EtaleCohomology.compactSupportSheafCohomologyAlgEquivIso`), which carries the canonical
Frobenius over `k̄₂` to the one over `k̄₁`, passes to the inverse systems of the levels of an
ℓ-adic sheaf `F` and to the limit: `Hⁱ_c(X_{k̄₂}, F ⊗ ℚ_ℓ) ≅ Hⁱ_c(X_{k̄₁}, F ⊗ ℚ_ℓ)`, naturally in
`F`, Frobenius-equivariantly. For `F` with coefficients in a `ℤ_ℓ`-algebra `O`, naturality makes it
commute with the action of `O`, so it is `E`-linear for `E = O[1/ℓ]`. This is the independence of
the algebraic closure needed to identify the fibres of Laumon's Fourier family
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.geometricCompactlySupportedCohomologySystemAlgEquivIso`.
* `Stacks.EtaleCohomology.LAdicSheaf.rationalGeometricCompactlySupportedCohomologyAlgEquivIso`.
* `Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.rationalAlgEquivLinearEquiv`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.rationalAlgEquivLinearEquiv_frobenius`.

The standard model `HasDerivedCategory.standard` is used because compactly supported cohomology is
defined there.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

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
  {X : B.Scheme} [IsNoetherian X.1]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f)) {kbar₁ kbar₂ : Type u}
  [Field kbar₁] [Algebra k kbar₁] [Field kbar₂] [Algebra k kbar₂] (σ : kbar₁ ≃ₐ[k] kbar₂) (i : ℤ)

/-- **`(n ↦ Hⁱ_c(X_{k̄₂}, Fₙ)) ≅ (n ↦ Hⁱ_c(X_{k̄₁}, Fₙ))`** for `σ : k̄₁ ≃ₐ[k] k̄₂`. -/
public def LAdicSheaf.geometricCompactlySupportedCohomologySystemAlgEquivIso
    (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar₂ F i ≅
      LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar₁ F i :=
  (LAdicSheaf.padicTowerCohomologyIso B X ℓ f j kbar₂ F i).symm ≪≫
    Functor.isoWhiskerLeft (LAdicSheaf.padicTower B X ℓ F)
      (compactSupportSheafCohomologyAlgEquivIso ℤ_[ℓ] f j σ i) ≪≫
    LAdicSheaf.padicTowerCohomologyIso B X ℓ f j kbar₁ F i

/-- A transport square for `e₁.symm ≪≫ e₂ ≪≫ e₃` from squares for `e₁`, `e₂`, `e₃`. -/
private theorem comp_symm_trans_trans_hom_eq {C : Type*} [Category C]
    {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : C} {e₁ : A₁ ≅ A₂} {e₂ : A₁ ≅ A₃} {e₃ : A₃ ≅ A₄}
    {e₁' : B₁ ≅ B₂} {e₂' : B₁ ≅ B₃} {e₃' : B₃ ≅ B₄}
    {a₁ : A₁ ⟶ B₁} {a₂ : A₂ ⟶ B₂} {a₃ : A₃ ⟶ B₃} {a₄ : A₄ ⟶ B₄}
    (h₁ : a₁ ≫ e₁'.hom = e₁.hom ≫ a₂) (h₂ : a₁ ≫ e₂'.hom = e₂.hom ≫ a₃)
    (h₃ : a₃ ≫ e₃'.hom = e₃.hom ≫ a₄) :
    a₂ ≫ (e₁'.symm ≪≫ e₂' ≪≫ e₃').hom = (e₁.symm ≪≫ e₂ ≪≫ e₃).hom ≫ a₄ :=
  comp_trans_hom_eq_trans_hom_comp _ _ _ _ _ _ _ (comp_symm_hom_eq_symm_hom_comp _ _ _ _ h₁)
    (comp_trans_hom_eq_trans_hom_comp _ _ _ _ _ _ _ h₂ h₃)

/-- **The identification is natural in the ℓ-adic sheaf.** -/
public theorem LAdicSheaf.geometricCompactlySupportedCohomologySystemAlgEquivIso_hom_naturality
    {F G : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ G) :
    LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar₂ φ i ≫
        (LAdicSheaf.geometricCompactlySupportedCohomologySystemAlgEquivIso B ℓ f j σ i G).hom =
      (LAdicSheaf.geometricCompactlySupportedCohomologySystemAlgEquivIso B ℓ f j σ i F).hom ≫
        LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar₁ φ i := by
  have h₂ : Functor.whiskerRight (LAdicSheaf.padicTowerMap φ)
        (compactSupportSheafCohomology ℤ_[ℓ] f j kbar₂ i) ≫
      (Functor.isoWhiskerLeft (LAdicSheaf.padicTower B X ℓ G)
        (compactSupportSheafCohomologyAlgEquivIso ℤ_[ℓ] f j σ i)).hom =
      (Functor.isoWhiskerLeft (LAdicSheaf.padicTower B X ℓ F)
        (compactSupportSheafCohomologyAlgEquivIso ℤ_[ℓ] f j σ i)).hom ≫
        Functor.whiskerRight (LAdicSheaf.padicTowerMap φ)
          (compactSupportSheafCohomology ℤ_[ℓ] f j kbar₁ i) := by
    ext n : 2
    exact (compactSupportSheafCohomologyAlgEquivIso ℤ_[ℓ] f j σ i).hom.naturality
      ((LAdicSheaf.padicTowerMap φ).app n)
  exact comp_symm_trans_trans_hom_eq
    (LAdicSheaf.padicTowerCohomologyIso_hom_naturality B ℓ f j kbar₂ φ i) h₂
    (LAdicSheaf.padicTowerCohomologyIso_hom_naturality B ℓ f j kbar₁ φ i)

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The identification carries `π_X^*` over `k̄₂` to `π_X^*` over `k̄₁`** on the inverse
systems. -/
public theorem LAdicSheaf.geometricCompactlySupportedCohomologySystemAlgEquivIso_hom_frobenius
    (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar₂ F i
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar₂ p q hcard) ≫
      (LAdicSheaf.geometricCompactlySupportedCohomologySystemAlgEquivIso B ℓ f j σ i F).hom =
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemAlgEquivIso B ℓ f j σ i F).hom ≫
      LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar₁ F i
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar₁ p q hcard) := by
  have h₂ : Functor.whiskerLeft (LAdicSheaf.padicTower B X ℓ F)
        (compactSupportSheafFrobenius ℤ_[ℓ] f j kbar₂ p q hcard i) ≫
      (Functor.isoWhiskerLeft (LAdicSheaf.padicTower B X ℓ F)
        (compactSupportSheafCohomologyAlgEquivIso ℤ_[ℓ] f j σ i)).hom =
      (Functor.isoWhiskerLeft (LAdicSheaf.padicTower B X ℓ F)
        (compactSupportSheafCohomologyAlgEquivIso ℤ_[ℓ] f j σ i)).hom ≫
        Functor.whiskerLeft (LAdicSheaf.padicTower B X ℓ F)
          (compactSupportSheafFrobenius ℤ_[ℓ] f j kbar₁ p q hcard i) := by
    ext n : 2
    exact congrArg (fun t => NatTrans.app t ((LAdicSheaf.padicTower B X ℓ F).obj n))
      (compactSupportSheafCohomologyAlgEquivIso_hom_frobenius ℤ_[ℓ] f j σ p q hcard i)
  exact comp_symm_trans_trans_hom_eq
    (LAdicSheaf.padicTowerCohomologyIso_hom_frobenius B X ℓ f j kbar₂ p q hcard F i) h₂
    (LAdicSheaf.padicTowerCohomologyIso_hom_frobenius B X ℓ f j kbar₁ p q hcard F i)

/-- **`Hⁱ_c(X_{k̄₂}, F ⊗ ℚ_ℓ) ≅ Hⁱ_c(X_{k̄₁}, F ⊗ ℚ_ℓ)`** for `σ : k̄₁ ≃ₐ[k] k̄₂`. -/
public def LAdicSheaf.rationalGeometricCompactlySupportedCohomologyAlgEquivIso
    (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar₂ F i ≅
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar₁ F i :=
  (rationalLim.{u + 1} (ℓ := ℓ)).mapIso
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemAlgEquivIso B ℓ f j σ i F)

/-- The rational identification is natural in the ℓ-adic sheaf. -/
public theorem LAdicSheaf.rationalGeometricCompactlySupportedCohomologyAlgEquivIso_hom_naturality
    {F G : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ G) :
    (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
        (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar₂ φ i) ≫
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyAlgEquivIso B ℓ f j σ i G).hom =
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyAlgEquivIso B ℓ f j σ i F).hom ≫
      (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
        (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar₁ φ i) :=
  map_comp_map_eq_of_comp_eq (rationalLim.{u + 1} (ℓ := ℓ)) _ _ _ _
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemAlgEquivIso_hom_naturality B ℓ f j σ i φ)

/-- The rational identification carries `π_X^*` over `k̄₂` to `π_X^*` over `k̄₁`. -/
public theorem LAdicSheaf.rationalGeometricCompactlySupportedCohomologyAlgEquivIso_hom_frobenius
    (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar₂ p q hcard F i ≫
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyAlgEquivIso B ℓ f j σ i F).hom =
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyAlgEquivIso B ℓ f j σ i F).hom ≫
      LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar₁ p q hcard F i :=
  map_comp_map_eq_of_comp_eq (rationalLim.{u + 1} (ℓ := ℓ)) _ _ _ _
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemAlgEquivIso_hom_frobenius B ℓ f j σ i p q
      hcard F)

variable {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (F : LAdicSheaf.CoefficientSheaf B X ℓ O)
  (E : Type) [CommRing E] [Algebra ℚ_[ℓ] E] [Algebra O E]
  [IsLocalization (Submonoid.powers (ℓ : O)) E]

set_option backward.isDefEq.respectTransparency false in
/-- **`Hⁱ_c(X_{k̄₂}, F ⊗ ℚ_ℓ) ≃ Hⁱ_c(X_{k̄₁}, F ⊗ ℚ_ℓ)`, `E`-linearly**, for
`σ : k̄₁ ≃ₐ[k] k̄₂`. -/
public def LAdicSheaf.CoefficientSheaf.rationalAlgEquivLinearEquiv :
    letI := F.rationalCohomologyModule f j kbar₂ i E
    letI := F.rationalCohomologyModule f j kbar₁ i E
    LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar₂ F.toLAdicSheaf i ≃ₗ[E]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar₁ F.toLAdicSheaf i :=
  LAdicSheaf.CoefficientSheaf.rationalLinearEquivOfCommute F F f f j j kbar₂ kbar₁ i i E
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyAlgEquivIso B ℓ f j σ i
      F.toLAdicSheaf).toLinearEquiv
    (fun o v => by
      have h := LAdicSheaf.rationalGeometricCompactlySupportedCohomologyAlgEquivIso_hom_naturality B
        ℓ f j σ i (F.act o).asHom
      exact congrArg (fun t => t.hom v) h)

omit [Algebra ℚ_[ℓ] E] in
/-- The `E`-linear identification carries `π_X^*` over `k̄₂` to `π_X^*` over `k̄₁`. -/
public theorem LAdicSheaf.CoefficientSheaf.rationalAlgEquivLinearEquiv_frobenius
    (v : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar₂
      F.toLAdicSheaf i) :
    F.rationalAlgEquivLinearEquiv B ℓ f j σ i E
        (F.rationalGeometricCompactlySupportedFrobenius f j kbar₂ i E p q hcard v) =
      F.rationalGeometricCompactlySupportedFrobenius f j kbar₁ i E p q hcard
        (F.rationalAlgEquivLinearEquiv B ℓ f j σ i E v) :=
  congrArg (fun t => t.hom v)
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyAlgEquivIso_hom_frobenius B ℓ f j σ i p
      q hcard F.toLAdicSheaf)

end LAdic

end Stacks.EtaleCohomology

end
