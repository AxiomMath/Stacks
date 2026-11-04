module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportCompactificationIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupportFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationCommutantCohomology

/-!
# Changing the compactification is natural in the ℓ-adic sheaf

Let `g : j ⟶ l` be a morphism of compactifications of a scheme `X` separated of finite type over
a finite field. The isomorphism `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` through `j` `≅` through `l` of
`Stacks.EtaleCohomology.LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso` is natural
in the ℓ-adic sheaf `F`: it commutes with the maps induced by morphisms of ℓ-adic sheaves. In
particular it commutes with the action of the coefficients of an ℓ-adic sheaf with coefficients,
which is what makes it `E`-linear. This is used to move the inclusion `H⁰_loc ⊆ H¹_c` of Weil II
1.8 ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), built with a compactification of a
curve `W ⊇ V`, to the given compactification of `V`.

## Main results

All names are in the namespace `Stacks.EtaleCohomology.LAdicSheaf`.

* `geometricCompactlySupportedCohomologySystemHomIso_hom_naturality`: the isomorphism of inverse
  systems `n ↦ Hⁱ_c(X_k̄, Fₙ)` through `j` and through `l` is natural in `F`.
* `rationalGeometricCompactlySupportedCohomologyHomIso_hom_naturality`: the isomorphism
  `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` through `j` `≅` through `l` is natural in `F`.
* `CoefficientSheaf.rationalGeometricCompactlySupportedCohomologyHomIso_hom_rationalRingHom`: this
  isomorphism is `E`-linear for an ℓ-adic sheaf with coefficients in `O` and `E = O[1/ℓ]`.

## Implementation notes

The standard model `HasDerivedCategory.standard` of the derived category is used, since compactly
supported cohomology is defined there.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

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
  {X : B.Scheme} [IsNoetherian X.1] {k : Type u} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  {j l : CompactificationOf (Over.mk f)} (g : j ⟶ l) (kbar : Type u) [Field kbar]
  [Algebra k kbar]

/-- A commutative square carried by a functor. -/
public theorem map_comp_map_eq_of_comp_eq {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {w x y z : C} (a : w ⟶ x) (b : x ⟶ z) (c : w ⟶ y) (d : y ⟶ z) (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, ← F.map_comp, h]

/-- **The isomorphism of the inverse systems `n ↦ Hⁱ_c(X_k̄, Fₙ)` through `j` and through `l` is
natural in the ℓ-adic sheaf.** -/
public theorem LAdicSheaf.geometricCompactlySupportedCohomologySystemHomIso_hom_naturality
    {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G) (i : ℤ) :
    LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar φ i ≫
        (LAdicSheaf.geometricCompactlySupportedCohomologySystemHomIso B ℓ f g kbar G i).hom =
      (LAdicSheaf.geometricCompactlySupportedCohomologySystemHomIso B ℓ f g kbar F i).hom ≫
        LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f l kbar φ i := by
  refine NatTrans.ext (funext fun n => ?_)
  have h := map_comp_map_eq_of_comp_eq
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i) _ _ _ _
    (compactSupportFrobeniusCohomologyHomIso_hom_naturality ℤ_[ℓ] f g kbar
      ((sheafSingleComplex ℤ_[ℓ]).map
        ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
          (LAdicSheaf.padicLevelMap φ n.unop)))
      (LAdicSheaf.exists_nsmul_id_sheafSingleComplex_padicTower B ℓ F n)
      (LAdicSheaf.exists_nsmul_id_sheafSingleComplex_padicTower B ℓ G n))
  have e₁ : ∀ {C : Type _} [Category C] {a b c : C} (x : a ⟶ b) (y : b ⟶ c),
      x ≫ (𝟙 b ≫ y ≫ 𝟙 c) = x ≫ y := fun x y => by simp
  have e₂ : ∀ {C : Type _} [Category C] {a b c : C} (x : b ⟶ c) (y : a ⟶ b),
      y ≫ x = (𝟙 a ≫ y ≫ 𝟙 b) ≫ x := fun x y => by simp
  exact (e₁ _ _).trans (h.trans (e₂ _ _))

/-- **The isomorphism `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` through `j` `≅` through `l` is natural in the ℓ-adic
sheaf.** -/
public theorem LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso_hom_naturality
    {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G) (i : ℤ) :
    (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
        (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ i) ≫
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso B ℓ f g kbar G i).hom =
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso B ℓ f g kbar F i).hom ≫
        (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
          (LAdicSheaf.geometricCompactlySupportedCohomologyMap f l kbar φ i) :=
  map_comp_map_eq_of_comp_eq (rationalLim.{u + 1} (ℓ := ℓ)) _ _ _ _
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemHomIso_hom_naturality B ℓ f g kbar φ i)

/-- Conjugating an endomorphism by an isomorphism of modules. -/
public theorem iso_conj_apply {R : Type*} [Ring R] {M N : ModuleCat.{u + 1} R} (e : M ≅ N)
    (a : M ⟶ M) (b : N ⟶ N) (h : a ≫ e.hom = e.hom ≫ b) (w : N) :
    e.hom (a (e.inv w)) = b w := by
  simpa using congrArg (fun t => t.hom (e.inv w)) h

/-- **The isomorphism `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` through `j` `≅` through `l` is `E`-linear** for an
ℓ-adic sheaf with coefficients in `O` and `E = O[1/ℓ]`. -/
public theorem LAdicSheaf.CoefficientSheaf.rationalGeometricCompactlySupportedCohomologyHomIso_hom_rationalRingHom
    {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (F : LAdicSheaf.CoefficientSheaf B X ℓ O) (i : ℤ)
    (E : Type) [CommRing E] [Algebra ℚ_[ℓ] E] [Algebra O E]
    [IsLocalization (Submonoid.powers (ℓ : O)) E] (e : E)
    (v : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i) :
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso B ℓ f g kbar
        F.toLAdicSheaf i).hom (F.rationalRingHom f j kbar i E e v) =
      F.rationalRingHom f l kbar i E e
        ((LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso B ℓ f g kbar
          F.toLAdicSheaf i).hom v) := by
  let c := (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso B ℓ f g kbar
    F.toLAdicSheaf i).toLinearEquiv
  have hO : (c.conjRingEquiv.toRingHom.comp (F.rationalRingHom f j kbar i E)).comp
        (algebraMap O E) = (F.rationalRingHom f l kbar i E).comp (algebraMap O E) := by
    refine RingHom.ext fun o => ?_
    simp only [RingHom.comp_apply, LAdicSheaf.CoefficientSheaf.rationalRingHom_algebraMap_apply]
    exact LinearMap.ext fun w => iso_conj_apply _ _ _
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso_hom_naturality B ℓ f g kbar
        (F.act o) i) w
  refine Eq.trans ?_ (LinearMap.congr_fun
    (RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (ℓ : O)) hO) e)
    ((LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso B ℓ f g kbar
      F.toLAdicSheaf i).hom v))
  show _ = c (F.rationalRingHom f j kbar i E e (c.symm (c v)))
  rw [LinearEquiv.symm_apply_apply]
  rfl

end Stacks.EtaleCohomology
