module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSheafExcisionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage

/-!
# Excision for the weights of `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`

Let `X` be a separated scheme of finite type over a finite field `k`, compactified by
`j : X ⟶ X̄`, let `F` be an ℓ-adic sheaf on `X`, and let `X = U ⊔ Z` with `j_U : U ⟶ X` an open
immersion and `i : Z ⟶ X` the complementary closed immersion, compactified by the induced
compactifications.  If the complex roots, read along `ι`, of the characteristic polynomials of
the geometric Frobenius on `Hⁱ_c(U_k̄, F|_U ⊗ ℚ_ℓ)` and on `Hⁱ_c(Z_k̄, F|_Z ⊗ ℚ_ℓ)` have absolute
values `q' ^ (w / 2)` with `w ≤ b`, so do those on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`.

The finiteness of the groups `Hⁱ_c(X_k̄, j_{U!} F|_U,ₙ)` at the finite levels, which makes the
limit exact, is a hypothesis here.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.padicTowerInverseImageIso`: the tower of levels of `g⁻¹F` is
  the inverse image of the tower of levels of `F`.

## Main results

* In the namespace `Stacks.EtaleCohomology.LAdicSheaf`,
  `isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_of_openClosed`:
  if the Frobenius weights on `Hⁱ_c(U_k̄, F|_U ⊗ ℚ_ℓ)` and `Hⁱ_c(Z_k̄, F|_Z ⊗ ℚ_ℓ)` are at most
  `b`, so are those on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

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

/-- **The tower of levels of `g⁻¹F` is the inverse image of the tower of levels of `F`**, for a
morphism `g : X' ⟶ X` of the big étale site. -/
public def LAdicSheaf.padicTowerInverseImageIso {X X' : B.Scheme} [IsNoetherian X.1]
    [IsNoetherian X'.1] (g : X' ⟶ X)
    (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    LAdicSheaf.padicTower B X ℓ F ⋙ etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map g) ≅
      LAdicSheaf.padicTower B X' ℓ (LAdicSheaf.inverseImage g F) :=
  let α : LAdicSheaf.padicTower B X ℓ F ⋙
      etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map g) ⟶
      LAdicSheaf.padicTower B X' ℓ (LAdicSheaf.inverseImage g F) :=
    NatTrans.ofOpSequence (fun n => (padicLevelInverseImageIso B g ℓ n (F.level n)).hom)
      (fun n => by
        rw [Functor.comp_map, LAdicSheaf.padicTower_map_succ, LAdicSheaf.padicTower_map_succ]
        exact padicLevelInverseImageIso_transition B g ℓ F n)
  haveI : IsIso α :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun n => by
      induction n using Opposite.rec with
      | op n =>
        exact (inferInstance : IsIso (padicLevelInverseImageIso B g ℓ n (F.level n)).hom))
  asIso α

variable {X : B.Scheme} [IsNoetherian X.1]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [QuasiCompact f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- Whiskering an isomorphism of towers on the right commutes with a natural endomorphism of the
functor applied to the towers. -/
lemma whiskerLeft_comp_isoWhiskerRight_hom {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟]
    {T₁ T₂ : ℕᵒᵖ ⥤ 𝒞} (e : T₁ ≅ T₂) {H : 𝒞 ⥤ 𝒟} (φ : H ⟶ H) :
    Functor.whiskerLeft T₁ φ ≫ (Functor.isoWhiskerRight e H).hom =
      (Functor.isoWhiskerRight e H).hom ≫ Functor.whiskerLeft T₂ φ := by
  ext n
  exact (φ.naturality (e.hom.app n)).symm

/-- Pasting two intertwining squares along a composite of isomorphisms. -/
lemma comp_trans_hom {𝒞 : Type*} [Category* 𝒞] {A₁ A₂ A₃ : 𝒞} (e₁ : A₁ ≅ A₂)
    (e₂ : A₂ ≅ A₃) (a₁ : A₁ ⟶ A₁) (a₂ : A₂ ⟶ A₂) (a₃ : A₃ ⟶ A₃) (h₁ : a₁ ≫ e₁.hom = e₁.hom ≫ a₂)
    (h₂ : a₂ ≫ e₂.hom = e₂.hom ≫ a₃) : a₁ ≫ (e₁ ≪≫ e₂).hom = (e₁ ≪≫ e₂).hom ≫ a₃ := by
  rw [Iso.trans_hom, reassoc_of% h₁, h₂, Category.assoc]

namespace LAdicSheaf

/-- **Excision for the weights of `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`.**  For an open immersion `j_U : U ⟶ X`
with complementary closed immersion `i : Z ⟶ X`, compactified by the compactifications induced
by `j`: if the complex roots, read along `ι`, of the characteristic polynomials of the geometric
Frobenius on `Hⁱ_c(U_k̄, F|_U ⊗ ℚ_ℓ)` and on `Hⁱ_c(Z_k̄, F|_Z ⊗ ℚ_ℓ)` have absolute values
`q' ^ (w / 2)` with `w ≤ b`, so do those on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`.  The groups
`Hⁱ_c(X_k̄, j_{U!} F|_U,ₙ)` at the finite levels are assumed finite. -/
public theorem
    isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_of_openClosed
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ) {U Z : B.Scheme} [IsNoetherian U.1]
    [IsNoetherian Z.1] (jU : U ⟶ X) (iZ : Z ⟶ X) [IsOpenImmersion (B.inclusion.map jU)]
    [IsClosedImmersion (B.inclusion.map iZ)] [QuasiCompact (B.inclusion.map jU ≫ f)]
    (hij : Set.range (B.inclusion.map jU).base = (Set.range (B.inclusion.map iZ).base)ᶜ)
    (hfin : ∀ n, Finite ((compactSupportSheafCohomology ℤ_[ℓ] f j kbar i).obj
      ((etaleModuleOpenPart ℤ_[ℓ] (B.inclusion.map jU)).obj
        ((LAdicSheaf.padicTower B X ℓ F).obj n))))
    [hX : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)]
    [hU : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ (B.inclusion.map jU ≫ f)
        (j.restrictOpen (B.inclusion.map jU)) kbar (LAdicSheaf.inverseImage jU F) i)]
    [hZ : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Z ℓ (B.inclusion.map iZ ≫ f)
        (j.restrictClosed (B.inclusion.map iZ)) kbar (LAdicSheaf.inverseImage iZ F) i)]
    {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {b : ℤ}
    (hFU : IsCharpolyNormMixedOfWeightLE q' ι b
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ (B.inclusion.map jU ≫ f)
        (j.restrictOpen (B.inclusion.map jU)) kbar p q hcard (LAdicSheaf.inverseImage jU F) i).hom)
    (hFZ : IsCharpolyNormMixedOfWeightLE q' ι b
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B Z ℓ (B.inclusion.map iZ ≫ f)
        (j.restrictClosed (B.inclusion.map iZ)) kbar p q hcard
        (LAdicSheaf.inverseImage iZ F) i).hom) :
    IsCharpolyNormMixedOfWeightLE q' ι b
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
        F i).hom := by
  set jU' := B.inclusion.map jU
  set iZ' := B.inclusion.map iZ
  set T := LAdicSheaf.padicTower B X ℓ F
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i)) := hX
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.geometricCompactlySupportedCohomologySystem B U ℓ (jU' ≫ f) (j.restrictOpen jU')
        kbar (LAdicSheaf.inverseImage jU F) i)) := hU
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.geometricCompactlySupportedCohomologySystem B Z ℓ (iZ' ≫ f)
        (j.restrictClosed iZ') kbar (LAdicSheaf.inverseImage iZ F) i)) := hZ
  have hXT : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (T ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) :=
    finiteDimensional_rationalLim_of_iso.{u + 1}
      (LAdicSheaf.padicTowerCohomologyIso B X ℓ f j kbar F i).symm
  have hUT : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.padicTower B U ℓ (LAdicSheaf.inverseImage jU F) ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (jU' ≫ f) (j.restrictOpen jU') kbar i)) :=
    finiteDimensional_rationalLim_of_iso.{u + 1}
      (LAdicSheaf.padicTowerCohomologyIso B U ℓ (jU' ≫ f) (j.restrictOpen jU') kbar
        (LAdicSheaf.inverseImage jU F) i).symm
  have hZT : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.padicTower B Z ℓ (LAdicSheaf.inverseImage iZ F) ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (iZ' ≫ f) (j.restrictClosed iZ') kbar i)) :=
    finiteDimensional_rationalLim_of_iso.{u + 1}
      (LAdicSheaf.padicTowerCohomologyIso B Z ℓ (iZ' ≫ f) (j.restrictClosed iZ') kbar
        (LAdicSheaf.inverseImage iZ F) i).symm
  let eU : T ⋙ etaleModuleRestriction.{u, 0} ℤ_[ℓ] jU' ≅
      LAdicSheaf.padicTower B U ℓ (LAdicSheaf.inverseImage jU F) :=
    Functor.isoWhiskerLeft T (etaleModuleInverseImageRestrictionIso.{u, 0} ℤ_[ℓ] jU').symm ≪≫
      LAdicSheaf.padicTowerInverseImageIso B ℓ jU F
  let eZ : T ⋙ etaleModuleInverseImage.{u, 0} ℤ_[ℓ] iZ' ≅
      LAdicSheaf.padicTower B Z ℓ (LAdicSheaf.inverseImage iZ F) :=
    LAdicSheaf.padicTowerInverseImageIso B ℓ iZ F
  let EU := towerOpenPartCohomologyIso f j kbar jU' T i ≪≫ Functor.isoWhiskerRight eU
    (compactSupportSheafCohomology ℤ_[ℓ] (jU' ≫ f) (j.restrictOpen jU') kbar i)
  let EZ := towerClosedPartCohomologyIso f j kbar iZ' T i ≪≫ Functor.isoWhiskerRight eZ
    (compactSupportSheafCohomology ℤ_[ℓ] (iZ' ≫ f) (j.restrictClosed iZ') kbar i)
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      ((T ⋙ etaleModuleOpenPart ℤ_[ℓ] jU') ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) :=
    finiteDimensional_rationalLim_of_iso.{u + 1} EU.symm (hA := hUT)
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      ((T ⋙ etaleModuleClosedPart ℤ_[ℓ] iZ') ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) :=
    finiteDimensional_rationalLim_of_iso.{u + 1} EZ.symm (hA := hZT)
  rw [LAdicSheaf.isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_iff]
    at hFU hFZ ⊢
  refine isCharpolyNormMixedOfWeightLE_rationalLim_of_openClosed f j kbar p q hcard iZ' jU' hij T
    i hfin ?_ ?_
  · refine (isCharpolyNormMixedOfWeightLE_rationalLimMap_iff_of_iso.{u + 1} EU _ _ ?_
      (hA' := hUT)).2 hFU
    exact comp_trans_hom _ _ _ _ _
      (towerOpenPartCohomologyIso_hom_frobenius f j kbar p q hcard jU' T i)
      (whiskerLeft_comp_isoWhiskerRight_hom eU _)
  · refine (isCharpolyNormMixedOfWeightLE_rationalLimMap_iff_of_iso.{u + 1} EZ _ _ ?_
      (hA' := hZT)).2 hFZ
    exact comp_trans_hom _ _ _ _ _
      (towerClosedPartCohomologyIso_hom_frobenius f j kbar p q hcard iZ' T i)
      (whiskerLeft_comp_isoWhiskerRight_hom eZ _)

end LAdicSheaf

end Stacks.EtaleCohomology

end
