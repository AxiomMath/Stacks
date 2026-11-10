module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicExcisionWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusPoincarePairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportDimensionZeroHomology
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Excision for the Frobenius characteristic roots of `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`

Let `X` be a separated scheme of finite type over a finite field `k`, compactified by
`j : X ⟶ X̄`, let `F` be an ℓ-adic sheaf on `X`, and let `X = U ⊔ Z` with `j_U : U ⟶ X` an open
immersion and `i : Z ⟶ X` the complementary closed immersion, compactified by the induced
compactifications.  Every root of the characteristic polynomial of the geometric Frobenius on
`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is a root of the one on `Hⁱ_c(U_k̄, F_U ⊗ ℚ_ℓ)` or of the one on
`Hⁱ_c(Z_k̄, F_Z ⊗ ℚ_ℓ)`, for any ℓ-adic sheaves `F_U`, `F_Z` whose towers of levels are the
restrictions of the tower of levels of `F`.

This is the form of excision used in the proof of purity in
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) for `X` whose geometric fibre is
disconnected: it propagates an arbitrary property of the characteristic roots (purity of a
weight), not only an upper bound on the weights. The sheaves on `U` and `Z` are given through
their towers of levels so that they may be inverse images along composite morphisms.

## Main results

* `charpoly_rationalLimMap_eq_of_iso`.
* `isRoot_charpoly_rationalLimMap_or_of_exact`.
* `LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_rationalLimMap`.
* `LAdicSheaf.isRoot_charpoly_rationalGeometricCompactlySupportedFrobenius_or_of_openClosed`.
* `LAdicSheaf.isCharpolyPureOfWeight_rationalGeometricCompactlySupportedFrobenius_of_openClosed`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-- A closed immersion followed by a morphism locally of finite type is locally of finite type
(stated for instance search, which times out finding it on the composites below). -/
local instance (priority := high) locallyOfFiniteType_comp_LAdicExcisionCharpolyRoots
    {X Y S : Scheme} (i : X ⟶ Y) (g : Y ⟶ S) [IsClosedImmersion i] [LocallyOfFiniteType g] :
    LocallyOfFiniteType (i ≫ g) :=
  MorphismProperty.comp_mem @LocallyOfFiniteType i g
    ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType i).mp
      ((IsClosedImmersion.iff_isFinite_and_mono i).mp ‹_›).1).2 ‹_›

/-! ### Characteristic roots on rational limits of towers -/

section RationalLim

variable {ℓ : ℕ} [Fact ℓ.Prime] [HasLimitsOfShape ℕᵒᵖ (ModuleCat.{v} ℤ_[ℓ])]

/-- **The characteristic polynomial on the rational limit of a tower only depends on the tower
with its endomorphism up to isomorphism.** -/
theorem charpoly_rationalLimMap_eq_of_iso {A A' : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]} (e : A ≅ A')
    (φ : A ⟶ A) (φ' : A' ⟶ A') (h : φ ≫ e.hom = e.hom ≫ φ')
    [hA : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj A)]
    [hA' : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj A')] :
    ((rationalLim (ℓ := ℓ)).map φ').hom.charpoly =
      ((rationalLim (ℓ := ℓ)).map φ).hom.charpoly := by
  let L := ((rationalLim (ℓ := ℓ)).mapIso e).toLinearEquiv
  have hcomm : ∀ v, L (((rationalLim (ℓ := ℓ)).map φ).hom v) =
      ((rationalLim (ℓ := ℓ)).map φ').hom (L v) := fun v => by
    have h' := congrArg (fun t => ((rationalLim (ℓ := ℓ)).map t).hom v) h
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h'
    exact h'
  have hconj : ((rationalLim (ℓ := ℓ)).map φ').hom = L.conj ((rationalLim (ℓ := ℓ)).map φ).hom := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨w, rfl⟩ := L.surjective v
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact (hcomm w).symm
  rw [hconj, LinearEquiv.charpoly_conj]

/-- **Characteristic roots along an exact sequence of towers.**  Let `α : A ⟶ B`, `β : B ⟶ C` be
maps of towers of `ℤ_ℓ`-modules, exact at every level, with every `A n` finite, intertwining
endomorphisms `φA`, `φB`, `φC`.  Every root along `ι` of the characteristic polynomial of the
endomorphism induced by `φB` on the rational limit of `B` is a root of the one of `A` or of the
one of `C`. -/
theorem isRoot_charpoly_rationalLimMap_or_of_exact {A B C : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]}
    (α : A ⟶ B) (β : B ⟶ C)
    (hex : ∀ n, Function.Exact (α.app n) (β.app n)) (hfin : ∀ n, Finite (A.obj n))
    (φA : A ⟶ A) (φB : B ⟶ B) (φC : C ⟶ C) (hα : φA ≫ α = α ≫ φB) (hβ : φB ≫ β = β ≫ φC)
    [hA : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj A)]
    [hB : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj B)]
    [hC : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj C)] (ι : ℚ_[ℓ] →+* ℂ) {z : ℂ}
    (hz : ((((rationalLim (ℓ := ℓ)).map φB).hom).charpoly.map ι).IsRoot z) :
    ((((rationalLim (ℓ := ℓ)).map φA).hom).charpoly.map ι).IsRoot z ∨
      ((((rationalLim (ℓ := ℓ)).map φC).hom).charpoly.map ι).IsRoot z := by
  refine isRoot_charpoly_map_or_of_exact ι (j := ((rationalLim (ℓ := ℓ)).map α).hom)
    (p := ((rationalLim (ℓ := ℓ)).map β).hom) (fun a => ?_) (fun b => ?_)
    (exact_rationalLimMap_of_finite α β hex hfin) hz
  · simpa only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] using
      congrArg (fun t => (ModuleCat.Hom.hom ((rationalLim (ℓ := ℓ)).map t)) a) hα
  · simpa only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] using
      congrArg (fun t => (ModuleCat.Hom.hom ((rationalLim (ℓ := ℓ)).map t)) b) hβ

end RationalLim

/-! ### Excision for ℓ-adic sheaves -/

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
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **The Frobenius characteristic polynomial on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is the one on the rational
limit of the tower of levels.** -/
theorem LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_rationalLimMap
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ)
    [hX : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)]
    [FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.padicTower B X ℓ F ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i))] :
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
        i).hom.charpoly =
      ((rationalLim.{u + 1} (ℓ := ℓ)).map
        (Functor.whiskerLeft (LAdicSheaf.padicTower B X ℓ F)
          (compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i))).hom.charpoly := by
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i)) := hX
  exact charpoly_rationalLimMap_eq_of_iso (LAdicSheaf.padicTowerCohomologyIso B X ℓ f j kbar F i)
    _ _ (LAdicSheaf.padicTowerCohomologyIso_hom_frobenius B X ℓ f j kbar p q hcard F i)

/-- Whiskering an isomorphism of towers on the right commutes with a natural endomorphism of the
functor applied to the towers. -/
alias whiskerLeft_comp_isoWhiskerRight_hom_of_tower := whiskerLeft_comp_isoWhiskerRight_hom

omit [LocallyOfFiniteType f] [IsSeparated f] in
/-- **Excision for the Frobenius characteristic roots of `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`.**  For an open
immersion `j_U : U ⟶ X` with complementary closed immersion `i : Z ⟶ X`, compactified by the
compactifications induced by `j`, and ℓ-adic sheaves `F_U` on `U`, `F_Z` on `Z` whose towers of
levels are identified with the inverse images of the tower of levels of `F`: every root along `ι`
of the characteristic polynomial of the geometric Frobenius on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is a root of
the one on `Hⁱ_c(U_k̄, F_U ⊗ ℚ_ℓ)` or of the one on `Hⁱ_c(Z_k̄, F_Z ⊗ ℚ_ℓ)`.  The groups
`Hⁱ_c(U_k̄, F_U,ₙ)` at the finite levels are assumed finite. -/
theorem LAdicSheaf.isRoot_charpoly_rationalGeometricCompactlySupportedFrobenius_or_of_openClosed
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ) {U Z : B.Scheme} [IsNoetherian U.1]
    [IsNoetherian Z.1] (jU : U ⟶ X) (iZ : Z ⟶ X) [IsOpenImmersion (B.inclusion.map jU)]
    [IsClosedImmersion (B.inclusion.map iZ)] [QuasiCompact (B.inclusion.map jU ≫ f)]
    (hij : Set.range (B.inclusion.map jU).base = (Set.range (B.inclusion.map iZ).base)ᶜ)
    (FU : LAdicSheaf.{u, u + 1} B U ℓ) (FZ : LAdicSheaf.{u, u + 1} B Z ℓ)
    (eU : LAdicSheaf.padicTower B X ℓ F ⋙ etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
      (B.inclusion.map jU) ≅ LAdicSheaf.padicTower B U ℓ FU)
    (eZ : LAdicSheaf.padicTower B X ℓ F ⋙ etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
      (B.inclusion.map iZ) ≅ LAdicSheaf.padicTower B Z ℓ FZ)
    (hfin : ∀ n, Finite ((compactSupportSheafCohomology ℤ_[ℓ] (B.inclusion.map jU ≫ f)
      (j.restrictOpen (B.inclusion.map jU)) kbar i).obj ((LAdicSheaf.padicTower B U ℓ FU).obj n)))
    [hX : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)]
    [hU : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ (B.inclusion.map jU ≫ f)
        (j.restrictOpen (B.inclusion.map jU)) kbar FU i)]
    [hZ : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Z ℓ (B.inclusion.map iZ ≫ f)
        (j.restrictClosed (B.inclusion.map iZ)) kbar FZ i)]
    (ι : ℚ_[ℓ] →+* ℂ) {z : ℂ}
    (hz : ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
      i).hom.charpoly.map ι).IsRoot z) :
    ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ (B.inclusion.map jU ≫ f)
        (j.restrictOpen (B.inclusion.map jU)) kbar p q hcard FU i).hom.charpoly.map ι).IsRoot z ∨
      ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B Z ℓ (B.inclusion.map iZ ≫ f)
        (j.restrictClosed (B.inclusion.map iZ)) kbar p q hcard FZ i).hom.charpoly.map ι).IsRoot
          z := by
  set jU' := B.inclusion.map jU
  set iZ' := B.inclusion.map iZ
  set T := LAdicSheaf.padicTower B X ℓ F
  -- the rational limits of the towers of `X`, `U` and `Z`
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i)) := hX
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.geometricCompactlySupportedCohomologySystem B U ℓ (jU' ≫ f) (j.restrictOpen jU')
        kbar FU i)) := hU
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.geometricCompactlySupportedCohomologySystem B Z ℓ (iZ' ≫ f)
        (j.restrictClosed iZ') kbar FZ i)) := hZ
  have hXT : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (T ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) :=
    finiteDimensional_rationalLim_of_iso.{u + 1}
      (LAdicSheaf.padicTowerCohomologyIso B X ℓ f j kbar F i).symm
  have hUT : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.padicTower B U ℓ FU ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (jU' ≫ f) (j.restrictOpen jU') kbar i)) :=
    finiteDimensional_rationalLim_of_iso.{u + 1}
      (LAdicSheaf.padicTowerCohomologyIso B U ℓ (jU' ≫ f) (j.restrictOpen jU') kbar FU i).symm
  have hZT : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.padicTower B Z ℓ FZ ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (iZ' ≫ f) (j.restrictClosed iZ') kbar i)) :=
    finiteDimensional_rationalLim_of_iso.{u + 1}
      (LAdicSheaf.padicTowerCohomologyIso B Z ℓ (iZ' ≫ f) (j.restrictClosed iZ') kbar FZ i).symm
  -- the open and closed parts of the tower of `X`, read on `U` and `Z`
  let eU' : T ⋙ etaleModuleRestriction.{u, 0} ℤ_[ℓ] jU' ≅ LAdicSheaf.padicTower B U ℓ FU :=
    Functor.isoWhiskerLeft T (etaleModuleInverseImageRestrictionIso.{u, 0} ℤ_[ℓ] jU').symm ≪≫ eU
  let EU := towerOpenPartCohomologyIso f j kbar jU' T i ≪≫ Functor.isoWhiskerRight eU'
    (compactSupportSheafCohomology ℤ_[ℓ] (jU' ≫ f) (j.restrictOpen jU') kbar i)
  let EZ := towerClosedPartCohomologyIso f j kbar iZ' T i ≪≫ Functor.isoWhiskerRight eZ
    (compactSupportSheafCohomology ℤ_[ℓ] (iZ' ≫ f) (j.restrictClosed iZ') kbar i)
  have hfin' : ∀ n, Finite ((compactSupportSheafCohomology ℤ_[ℓ] f j kbar i).obj
      ((etaleModuleOpenPart ℤ_[ℓ] jU').obj (T.obj n))) := fun n =>
    @Finite.of_equiv _ _ (hfin n) (EU.app n).toLinearEquiv.toEquiv.symm
  have hA : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      ((T ⋙ etaleModuleOpenPart ℤ_[ℓ] jU') ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) :=
    finiteDimensional_rationalLim_of_iso.{u + 1} EU.symm (hA := hUT)
  have hC : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      ((T ⋙ etaleModuleClosedPart ℤ_[ℓ] iZ') ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) :=
    finiteDimensional_rationalLim_of_iso.{u + 1} EZ.symm (hA := hZT)
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (T ⋙ 𝟭 _ ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) := hXT
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (T ⋙ etaleModuleOpenPart ℤ_[ℓ] jU' ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) := hA
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (T ⋙ etaleModuleClosedPart ℤ_[ℓ] iZ' ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) := hC
  rw [LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_rationalLimMap B ℓ f j
    kbar p q hcard F i] at hz
  have hU' : (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ (jU' ≫ f)
      (j.restrictOpen jU') kbar p q hcard FU i).hom.charpoly =
      ((rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerLeft (T ⋙ etaleModuleOpenPart ℤ_[ℓ] jU')
        (compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i))).hom.charpoly :=
    (LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_rationalLimMap B ℓ
      (jU' ≫ f) (j.restrictOpen jU') kbar p q hcard FU i).trans
      (charpoly_rationalLimMap_eq_of_iso.{u + 1} EU _ _ (comp_trans_hom_eq_of_comm _ _ _ _ _
        (towerOpenPartCohomologyIso_hom_frobenius f j kbar p q hcard jU' T i)
        (whiskerLeft_comp_isoWhiskerRight_hom_of_tower eU' _)) (hA := hA) (hA' := hUT))
  have hZ' : (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B Z ℓ (iZ' ≫ f)
      (j.restrictClosed iZ') kbar p q hcard FZ i).hom.charpoly =
      ((rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerLeft (T ⋙ etaleModuleClosedPart ℤ_[ℓ] iZ')
        (compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i))).hom.charpoly :=
    (LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_rationalLimMap B ℓ
      (iZ' ≫ f) (j.restrictClosed iZ') kbar p q hcard FZ i).trans
      (charpoly_rationalLimMap_eq_of_iso.{u + 1} EZ _ _ (comp_trans_hom_eq_of_comm _ _ _ _ _
        (towerClosedPartCohomologyIso_hom_frobenius f j kbar p q hcard iZ' T i)
        (whiskerLeft_comp_isoWhiskerRight_hom_of_tower eZ _)) (hA := hC) (hA' := hZT))
  rw [hU', hZ']
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (T ⋙ (etaleModuleRestriction.{u, 0} ℤ_[ℓ] jU' ⋙ etaleModuleExtensionByZero.{u, 0} ℤ_[ℓ] jU') ⋙
        compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) := hA
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (T ⋙ (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] iZ' ⋙ etaleModuleDirectImage.{u, 0} ℤ_[ℓ] iZ') ⋙
        compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)) := hC
  refine isRoot_charpoly_rationalLimMap_or_of_exact.{u + 1}
    (Functor.whiskerLeft T
      (Functor.whiskerRight (etaleModuleExtensionByZeroAdj.{u, 0} ℤ_[ℓ] jU').counit
        (compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)))
    (Functor.whiskerLeft T (Functor.whiskerRight (etaleModuleInverseImageAdj.{u, 0} ℤ_[ℓ] iZ').unit
      (compactSupportSheafCohomology ℤ_[ℓ] f j kbar i)))
    (fun n => exact_compactSupportSheafCohomology_openClosed ℤ_[ℓ] f j kbar iZ' jU' hij (T.obj n) i)
    hfin' _ _ _ ?_ ?_ (hA := hA) (hB := hXT) (hC := hC) ι hz
  all_goals
    refine NatTrans.ext (funext fun n => ?_)
    first
    | exact ((compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i).naturality
        ((etaleModuleExtensionByZeroAdj.{u, 0} ℤ_[ℓ] jU').counit.app (T.obj n))).symm
    | exact ((compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i).naturality
        ((etaleModuleInverseImageAdj.{u, 0} ℤ_[ℓ] iZ').unit.app (T.obj n))).symm

omit [LocallyOfFiniteType f] [IsSeparated f] in
/-- **Purity of weight `w` passes through excision**: if the Frobenius on `Hⁱ_c(U_k̄, F_U ⊗ ℚ_ℓ)`
and on `Hⁱ_c(Z_k̄, F_Z ⊗ ℚ_ℓ)` is pure of weight `w`, so is the one on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`. -/
theorem LAdicSheaf.isCharpolyPureOfWeight_rationalGeometricCompactlySupportedFrobenius_of_openClosed
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ) {U Z : B.Scheme} [IsNoetherian U.1]
    [IsNoetherian Z.1] (jU : U ⟶ X) (iZ : Z ⟶ X) [IsOpenImmersion (B.inclusion.map jU)]
    [IsClosedImmersion (B.inclusion.map iZ)] [QuasiCompact (B.inclusion.map jU ≫ f)]
    (hij : Set.range (B.inclusion.map jU).base = (Set.range (B.inclusion.map iZ).base)ᶜ)
    (FU : LAdicSheaf.{u, u + 1} B U ℓ) (FZ : LAdicSheaf.{u, u + 1} B Z ℓ)
    (eU : LAdicSheaf.padicTower B X ℓ F ⋙ etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
      (B.inclusion.map jU) ≅ LAdicSheaf.padicTower B U ℓ FU)
    (eZ : LAdicSheaf.padicTower B X ℓ F ⋙ etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
      (B.inclusion.map iZ) ≅ LAdicSheaf.padicTower B Z ℓ FZ)
    (hfin : ∀ n, Finite ((compactSupportSheafCohomology ℤ_[ℓ] (B.inclusion.map jU ≫ f)
      (j.restrictOpen (B.inclusion.map jU)) kbar i).obj ((LAdicSheaf.padicTower B U ℓ FU).obj n)))
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)]
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ (B.inclusion.map jU ≫ f)
        (j.restrictOpen (B.inclusion.map jU)) kbar FU i)]
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Z ℓ (B.inclusion.map iZ ≫ f)
        (j.restrictClosed (B.inclusion.map iZ)) kbar FZ i)]
    {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {w : ℤ}
    (hFU : IsCharpolyPureOfWeight q' ι w
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ (B.inclusion.map jU ≫ f)
        (j.restrictOpen (B.inclusion.map jU)) kbar p q hcard FU i).hom)
    (hFZ : IsCharpolyPureOfWeight q' ι w
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B Z ℓ (B.inclusion.map iZ ≫ f)
        (j.restrictClosed (B.inclusion.map iZ)) kbar p q hcard FZ i).hom) :
    IsCharpolyPureOfWeight q' ι w
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
        i).hom := fun z hz =>
  (LAdicSheaf.isRoot_charpoly_rationalGeometricCompactlySupportedFrobenius_or_of_openClosed B ℓ f j
    kbar p q hcard F i jU iZ hij FU FZ eU eZ hfin ι hz).elim (hFU z) (hFZ z)

end LAdic

end Stacks.EtaleCohomology

end
