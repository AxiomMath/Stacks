module

public import StacksFrontier.Homology.Perfect.FlatComplexFibreVanishing
public import StacksFrontier.Homology.Perfect.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.Homology.ModuleCatHomologyMapElementwise
public import StacksFrontier.Homology.ExtendScalars.Localization
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A chain map which is a fibre quasi-isomorphism in low degrees is one nearby

Let `R` be a ring, `p` a prime of `R` and `φ : C ⟶ D` a chain map of bounded complexes of flat
`R`-modules which are perfect in `D(R)`. If `φ ⊗ κ(p)` induces isomorphisms on cohomology in all
degrees `≤ n` and an injection in degree `n + 1`, then there is `f ∉ p` such that `φ ⊗_R B`
induces isomorphisms on cohomology in all degrees `≤ n`, for every `R`-algebra `B` in which `f`
is invertible.

By the long exact sequence of the mapping cone of `φ`, its cohomology in degrees `≤ n` vanishes
exactly when `φ` is an isomorphism on cohomology in degrees `≤ n` and injective in degree `n + 1`.

## Main results

* `StacksDraft.Perfect.isZero_homology_mappingCone_of_epi_of_mono`: the cone has no cohomology in
  degree `n₀` when `Hⁿ⁰(φ)` is onto and `Hⁿ⁰⁺¹(φ)` is injective.
* `StacksDraft.Perfect.exists_away_isIso_homologyMap_of_fibre`: the spreading out.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace StacksDraft.Perfect

section HomologySequence

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

/-- The cohomology of the image of a complex in the derived category is its cohomology. -/
def homologyQIso (M : CochainComplex C ℤ) (n : ℤ) :
    (DerivedCategory.homologyFunctor C n).obj (DerivedCategory.Q.obj M) ≅ M.homology n :=
  (DerivedCategory.homologyFunctorFactors C n).app M

/-- The map induced on cohomology by the image of `φ` in the derived category is
`HomologicalComplex.homologyMap φ n`, up to the isomorphisms `homologyQIso`. -/
theorem homologyFunctor_map_Q_eq (n : ℤ) :
    (DerivedCategory.homologyFunctor C n).map (DerivedCategory.Q.map φ) =
      (homologyQIso K n).hom ≫ HomologicalComplex.homologyMap φ n ≫ (homologyQIso L n).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  exact DerivedCategory.homologyFunctorFactors_hom_naturality φ n

omit [Abelian C] [HasDerivedCategory C] in
private theorem epi_conj_iff {A B A' B' : C} (e : A ≅ A') (e' : B ≅ B') (h : A' ⟶ B') :
    Epi (e.hom ≫ h ≫ e'.inv) ↔ Epi h := by simp

omit [Abelian C] [HasDerivedCategory C] in
private theorem mono_conj_iff {A B A' B' : C} (e : A ≅ A') (e' : B ≅ B') (h : A' ⟶ B') :
    Mono (e.hom ≫ h ≫ e'.inv) ↔ Mono h := by simp

/-- The image of `φ` in the derived category is an epimorphism on `Hⁿ` if and only if `φ` is. -/
theorem epi_homologyFunctor_map_Q_iff (n : ℤ) :
    Epi ((DerivedCategory.homologyFunctor C n).map (DerivedCategory.Q.map φ)) ↔
      Epi (HomologicalComplex.homologyMap φ n) := by
  rw [homologyFunctor_map_Q_eq]
  exact epi_conj_iff _ _ _

/-- The image of `φ` in the derived category is a monomorphism on `Hⁿ` if and only if `φ` is. -/
theorem mono_homologyFunctor_map_Q_iff (n : ℤ) :
    Mono ((DerivedCategory.homologyFunctor C n).map (DerivedCategory.Q.map φ)) ↔
      Mono (HomologicalComplex.homologyMap φ n) := by
  rw [homologyFunctor_map_Q_eq]
  exact mono_conj_iff _ _ _

/-- The cohomology of the derived image of the mapping cone is that of the mapping cone. -/
def homologyMappingConeIso (n : ℤ) :
    (DerivedCategory.homologyFunctor C n).obj
        (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle φ)).obj₃ ≅
      (CochainComplex.mappingCone φ).homology n :=
  (DerivedCategory.homologyFunctorFactors C n).app (CochainComplex.mappingCone φ)

/-- **The mapping cone has no cohomology in degree `n₀` when `Hⁿ⁰(φ)` is onto and `Hⁿ⁰⁺¹(φ)` is
injective.** This is the exactness of `Hⁿ⁰(L) ⟶ Hⁿ⁰(cone φ) ⟶ Hⁿ⁰⁺¹(K)` in the long exact
sequence of the distinguished triangle of the cone. -/
@[sga "6 I 1.4.2" "(ii) ⇒ (i)"]
theorem isZero_homology_mappingCone_of_epi_of_mono (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (he : Epi (HomologicalComplex.homologyMap φ n₀))
    (hm : Mono (HomologicalComplex.homologyMap φ n₁)) :
    IsZero ((CochainComplex.mappingCone φ).homology n₀) := by
  have hT := DerivedCategory.mappingCone_triangle_distinguished φ
  exact ((DerivedCategory.HomologySequence.exact₃ _ hT n₀ n₁ h).isZero_X₂
    ((DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff _ hT n₀).1
      ((epi_homologyFunctor_map_Q_iff φ n₀).2 he))
    ((DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT n₀ n₁ h).1
      ((mono_homologyFunctor_map_Q_iff φ n₁).2 hm))).of_iso
    (homologyMappingConeIso φ n₀).symm

/-- If the mapping cone has no cohomology in degree `n₀`, then `Hⁿ⁰(φ)` is onto. -/
theorem epi_homologyMap_of_isZero_homology_mappingCone (n₀ : ℤ)
    (hz : IsZero ((CochainComplex.mappingCone φ).homology n₀)) :
    Epi (HomologicalComplex.homologyMap φ n₀) := by
  have hT := DerivedCategory.mappingCone_triangle_distinguished φ
  exact (epi_homologyFunctor_map_Q_iff φ n₀).1
    ((DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff _ hT n₀).2
      ((hz.of_iso (homologyMappingConeIso φ n₀)).eq_of_tgt _ _))

/-- If the mapping cone has no cohomology in degree `n₀`, then `Hⁿ⁰⁺¹(φ)` is injective. -/
theorem mono_homologyMap_of_isZero_homology_mappingCone (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (hz : IsZero ((CochainComplex.mappingCone φ).homology n₀)) :
    Mono (HomologicalComplex.homologyMap φ n₁) := by
  have hT := DerivedCategory.mappingCone_triangle_distinguished φ
  exact (mono_homologyFunctor_map_Q_iff φ n₁).1
    ((DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT n₀ n₁ h).2
      ((hz.of_iso (homologyMappingConeIso φ n₀)).eq_of_src _ _))

end HomologySequence

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] {C D : CochainComplex (ModuleCat.{u} R) ℤ} (φ : C ⟶ D)

/-- Termwise extension of scalars of a chain map. -/
abbrev extendScalarsCxMap {B : Type u} [CommRing B] (ψ : R →+* B) :
    extendScalarsCx ψ C ⟶ extendScalarsCx ψ D :=
  ((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)).map φ

/-- Termwise extension of scalars commutes with the mapping cone. -/
def extendScalarsCxMappingConeIso {B : Type u} [CommRing B] (ψ : R →+* B) :
    extendScalarsCx ψ (CochainComplex.mappingCone φ) ≅
      CochainComplex.mappingCone (extendScalarsCxMap φ ψ) :=
  CochainComplex.mappingCone.mapHomologicalComplexIso φ (ModuleCat.extendScalars.{u, u, u} ψ)

/-- The mapping cone of a map of complexes concentrated in degrees `≥ c` is concentrated in
degrees `≥ c - 1`. -/
theorem isStrictlyGE_mappingCone (c : ℤ) [C.IsStrictlyGE c] [D.IsStrictlyGE c] :
    (CochainComplex.mappingCone φ).IsStrictlyGE (c - 1) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨C.isZero_of_isStrictlyGE c _ (by omega), D.isZero_of_isStrictlyGE c _ (by omega)⟩

/-- The mapping cone of a map of complexes concentrated in degrees `≤ d` is concentrated in
degrees `≤ d`. -/
theorem isStrictlyLE_mappingCone (d : ℤ) [C.IsStrictlyLE d] [D.IsStrictlyLE d] :
    (CochainComplex.mappingCone φ).IsStrictlyLE d := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨C.isZero_of_isStrictlyLE d _ (by omega), D.isZero_of_isStrictlyLE d _ (by omega)⟩

private lemma flat_prod {A B : Type u} [AddCommMonoid A] [Module R A] [AddCommMonoid B]
    [Module R B] [Module.Flat R A] [Module.Flat R B] : Module.Flat R (A × B) := by
  rw [Module.Flat.iff_rTensor_injectiveₛ]
  intro P _ _ S x y hxy
  have key : ∀ (M : Type u) [AddCommMonoid M] [Module R M] [Module.Flat R M]
      (π : A × B →ₗ[R] M), (π.lTensor S) x = (π.lTensor S) y := by
    intro M _ _ _ π
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := M) S.subtype
      Subtype.val_injective
    have compat (z : TensorProduct R S (A × B)) :
        (S.subtype.rTensor M) (π.lTensor S z) = π.lTensor P (S.subtype.rTensor (A × B) z) := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp
      | add x y hx hy => simp_all
    rw [compat x, compat y, hxy]
  have hp (z : TensorProduct R S (A × B)) : TensorProduct.prodRight R R S A B z =
      ((LinearMap.fst R A B).lTensor S z, (LinearMap.snd R A B).lTensor S z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp [Prod.mk_zero_zero]
    | tmul x y => simp
    | add x y hx hy => simp_all
  apply (TensorProduct.prodRight R R S A B).injective
  rw [hp, hp]
  exact Prod.ext (key A _) (key B _)

/-- The mapping cone of a map of complexes of flat `R`-modules has flat terms. -/
theorem flat_mappingCone_X [∀ i, Module.Flat R (C.X i)] [∀ i, Module.Flat R (D.X i)] (i : ℤ) :
    Module.Flat R ((CochainComplex.mappingCone φ).X i) :=
  have : Module.Flat R (C.X (i + 1) × D.X i) := flat_prod
  Module.Flat.of_linearEquiv ((HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl ≪≫
    ModuleCat.biprodIsoProd _ _).toLinearEquiv)

/-- The mapping cone of a map between complexes that are perfect in `D(R)` is perfect. -/
theorem isPerfect_mappingCone (hC : IsPerfect (DerivedCategory.Q.obj C))
    (hD : IsPerfect (DerivedCategory.Q.obj D)) :
    IsPerfect (DerivedCategory.Q.obj (CochainComplex.mappingCone φ)) :=
  (isPerfect_of_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished φ)).1 hC hD

/-- **A chain map which is a fibre quasi-isomorphism in low degrees is one nearby.** Let
`φ : C ⟶ D` be a chain map of bounded complexes of flat `R`-modules which are perfect in `D(R)`,
and `p` a prime. If `φ ⊗ κ(p)` is an isomorphism on cohomology in degrees `≤ n` and injective on
cohomology in degree `n + 1`, then there is `f ∉ p` such that `φ ⊗_R B` is an isomorphism on
cohomology in degrees `≤ n` for every ring map `R → B` inverting `f`. -/
theorem exists_away_isIso_homologyMap_of_fibre (c d : ℤ) [C.IsStrictlyGE c] [C.IsStrictlyLE d]
    [D.IsStrictlyGE c] [D.IsStrictlyLE d] [∀ i, Module.Flat R (C.X i)]
    [∀ i, Module.Flat R (D.X i)] (hC : IsPerfect (DerivedCategory.Q.obj C))
    (hD : IsPerfect (DerivedCategory.Q.obj D)) (p : Ideal R) [p.IsPrime] (n : ℤ)
    (hiso : ∀ i ≤ n, IsIso (HomologicalComplex.homologyMap
      (extendScalarsCxMap φ (algebraMap R p.ResidueField)) i))
    (hmono : Mono (HomologicalComplex.homologyMap
      (extendScalarsCxMap φ (algebraMap R p.ResidueField)) (n + 1))) :
    ∃ f : R, f ∉ p ∧ ∀ {B : Type u} [CommRing B] (ψ : R →+* B), IsUnit (ψ f) →
      ∀ i ≤ n, IsIso (HomologicalComplex.homologyMap (extendScalarsCxMap φ ψ) i) := by
  have := isStrictlyGE_mappingCone φ c
  have := isStrictlyLE_mappingCone φ d
  have := flat_mappingCone_X φ
  obtain ⟨f, hf, hB⟩ := exists_away_isZero_homology_extendScalars_of_fibre
    (CochainComplex.mappingCone φ) (c - 1) d (isPerfect_mappingCone φ hC hD) p n
    (fun i hi => by
      refine IsZero.of_iso ?_ (HomologicalComplex.homologyFunctor _ _ i |>.mapIso
        (extendScalarsCxMappingConeIso φ (algebraMap R p.ResidueField)))
      refine isZero_homology_mappingCone_of_epi_of_mono _ i (i + 1) rfl
        (have := hiso i hi; inferInstance) ?_
      by_cases hi' : i + 1 ≤ n
      · have := hiso (i + 1) hi'
        infer_instance
      · obtain rfl : i = n := by omega
        exact hmono)
  refine ⟨f, hf, fun {B} _ ψ hψ i hi => ?_⟩
  have hz : ∀ j ≤ n, IsZero ((CochainComplex.mappingCone (extendScalarsCxMap φ ψ)).homology j) :=
    fun j hj => (hB ψ hψ j hj).of_iso (HomologicalComplex.homologyFunctor _ _ j |>.mapIso
      (extendScalarsCxMappingConeIso φ ψ)).symm
  have he := epi_homologyMap_of_isZero_homology_mappingCone _ i (hz i hi)
  have hm := mono_homologyMap_of_isZero_homology_mappingCone _ (i - 1) i (by omega)
    (hz (i - 1) (by omega))
  exact isIso_of_mono_of_epi _

section Elementwise

open scoped ChangeOfRings

variable {C D : CochainComplex (ModuleCat.{u} R) ℤ} (φ : C ⟶ D)

/-- The differential into degree `0` of a base change of a complex in degrees `≥ 0` vanishes. -/
private theorem d_neg_one_apply {B : Type u} [CommRing B] (ψ : R →+* B)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) [M.IsStrictlyGE 0]
    (y : (extendScalarsCx ψ M).X (-1)) : (extendScalarsCx ψ M).d (-1) 0 y = 0 := by
  rw [((extendScalarsCx ψ M).isZero_of_isStrictlyGE 0 (-1) (by omega)).eq_of_src
    ((extendScalarsCx ψ M).d (-1) 0) 0]
  rfl

/-- Extension of scalars sends `1 ⊗ x` to `0` when a map kills `x`. -/
private theorem extendScalars_map_one_tmul_eq_zero {B : Type u} [CommRing B] (ψ : R →+* B)
    {M N : ModuleCat.{u} R} (g : M ⟶ N) (x : M) (h : g.hom x = 0) :
    ((ModuleCat.extendScalars ψ).map g).hom ((1 : B) ⊗ₜ[R, ψ] x) = 0 := by
  rw [ModuleCat.ExtendScalars.map_tmul, h, TensorProduct.tmul_zero]
  rfl

private theorem next_zero : (ComplexShape.up ℤ).next 0 = 1 := by simp
private theorem prev_one : (ComplexShape.up ℤ).prev 1 = 0 := by simp
private theorem next_one : (ComplexShape.up ℤ).next 1 = 2 := by simp

/-- On complexes concentrated in nonnegative degrees, the elementwise conditions on degree-zero
cocycles give an isomorphism on `H⁰`. -/
private theorem isIso_homologyMap_zero_of_elementwise {B : Type u} [CommRing B] (ψ : R →+* B)
    [C.IsStrictlyGE 0] [D.IsStrictlyGE 0]
    (h0 : ∀ x : (extendScalarsCx ψ C).X 0, (extendScalarsCx ψ C).d 0 1 x = 0 →
      (extendScalarsCxMap φ ψ).f 0 x = 0 → x = 0)
    (h0' : ∀ y : (extendScalarsCx ψ D).X 0, (extendScalarsCx ψ D).d 0 1 y = 0 →
      ∃ x : (extendScalarsCx ψ C).X 0, (extendScalarsCx ψ C).d 0 1 x = 0 ∧
        (extendScalarsCxMap φ ψ).f 0 x = y) :
    IsIso (HomologicalComplex.homologyMap (extendScalarsCxMap φ ψ) 0) := by
  have hm : Mono (HomologicalComplex.homologyMap (extendScalarsCxMap φ ψ) 0) := by
    rw [HomologicalComplex.mono_homologyMap_iff_elementwise _ (-1) 0 1 (by simp) next_zero]
    intro x hx y hy
    exact ⟨0, by rw [map_zero]; exact (h0 x hx (hy.trans (d_neg_one_apply ψ D y))).symm⟩
  have he : Epi (HomologicalComplex.homologyMap (extendScalarsCxMap φ ψ) 0) := by
    rw [HomologicalComplex.epi_homologyMap_iff_elementwise _ (-1) 0 1 (by simp) next_zero]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := h0' y hy
    exact ⟨x, hx, 0, by rw [map_zero, add_zero]⟩
  exact isIso_of_mono_of_epi _

private theorem isIso_homologyMap_of_neg {B : Type u} [CommRing B] (ψ : R →+* B)
    [C.IsStrictlyGE 0] [D.IsStrictlyGE 0] (i : ℤ) (hi : i < 0) :
    IsIso (HomologicalComplex.homologyMap (extendScalarsCxMap φ ψ) i) := by
  have h1 : IsZero ((extendScalarsCx ψ C).homology i) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _
      ((extendScalarsCx ψ C).isZero_of_isStrictlyGE 0 i hi)
  have h2 : IsZero ((extendScalarsCx ψ D).homology i) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _
      ((extendScalarsCx ψ D).isZero_of_isStrictlyGE 0 i hi)
  exact ⟨⟨0, h1.eq_of_src _ _, h2.eq_of_src _ _⟩⟩

private theorem localizedModuleMap_mk' {M N : ModuleCat.{u} R} (S : Submonoid R) (g : M ⟶ N)
    (x : M) (s : S) :
    (ModuleCat.localizedModuleMap.{u} S g).hom
        (IsLocalizedModule.mk' (M.localizedModuleMkLinearMap S) x s) =
      IsLocalizedModule.mk' (N.localizedModuleMkLinearMap S) (g.hom x) s := by
  change (IsLocalizedModule.mapExtendScalars S (M.localizedModuleMkLinearMap S)
    (N.localizedModuleMkLinearMap S) (Localization S) g.hom) _ = _
  rw [IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_mk']

/-- **Fibre isomorphism on `H⁰` and fibre injectivity on `H¹`, on elements, spread out.** Let
`φ : C ⟶ D` be a chain map of complexes of flat `R`-modules concentrated in degrees `[0, d]`,
perfect in `D(R)`, and `p` a prime. Assume that on degree-zero cocycles `φ ⊗ κ(p)` is injective
and surjective, and that a degree-one cocycle of `C ⊗ κ(p)` whose image is a coboundary is a
coboundary. Then there is `f ∉ p` such that on degree-zero cocycles `φ` is injective and surjective
up to powers of `f`. -/
theorem exists_away_of_fibre_elementwise (d : ℤ) [C.IsStrictlyGE 0] [C.IsStrictlyLE d]
    [D.IsStrictlyGE 0] [D.IsStrictlyLE d] [∀ i, Module.Flat R (C.X i)]
    [∀ i, Module.Flat R (D.X i)] (hC : IsPerfect (DerivedCategory.Q.obj C))
    (hD : IsPerfect (DerivedCategory.Q.obj D)) (p : Ideal R) [p.IsPrime]
    (h0 : ∀ x : (extendScalarsCx (algebraMap R p.ResidueField) C).X 0,
      (extendScalarsCx (algebraMap R p.ResidueField) C).d 0 1 x = 0 →
      (extendScalarsCxMap φ (algebraMap R p.ResidueField)).f 0 x = 0 → x = 0)
    (h0' : ∀ y : (extendScalarsCx (algebraMap R p.ResidueField) D).X 0,
      (extendScalarsCx (algebraMap R p.ResidueField) D).d 0 1 y = 0 →
      ∃ x : (extendScalarsCx (algebraMap R p.ResidueField) C).X 0,
        (extendScalarsCx (algebraMap R p.ResidueField) C).d 0 1 x = 0 ∧
          (extendScalarsCxMap φ (algebraMap R p.ResidueField)).f 0 x = y)
    (h1 : ∀ x : (extendScalarsCx (algebraMap R p.ResidueField) C).X 1,
      (extendScalarsCx (algebraMap R p.ResidueField) C).d 1 2 x = 0 →
      ∀ y : (extendScalarsCx (algebraMap R p.ResidueField) D).X 0,
        (extendScalarsCxMap φ (algebraMap R p.ResidueField)).f 1 x =
          (extendScalarsCx (algebraMap R p.ResidueField) D).d 0 1 y →
        ∃ w : (extendScalarsCx (algebraMap R p.ResidueField) C).X 0,
          (extendScalarsCx (algebraMap R p.ResidueField) C).d 0 1 w = x) :
    ∃ f : R, f ∉ p ∧
      (∀ x : C.X 0, C.d 0 1 x = 0 → φ.f 0 x = 0 → ∃ n : ℕ, f ^ n • x = 0) ∧
      (∀ y : D.X 0, D.d 0 1 y = 0 →
        ∃ x : C.X 0, C.d 0 1 x = 0 ∧ ∃ n : ℕ, φ.f 0 x = f ^ n • y) := by
  obtain ⟨f, hf, hB⟩ := exists_away_isIso_homologyMap_of_fibre φ 0 d hC hD p 0
    (fun i hi => by
      rcases lt_or_eq_of_le hi with hi | rfl
      · exact isIso_homologyMap_of_neg φ _ i hi
      · exact isIso_homologyMap_zero_of_elementwise φ _ h0 h0')
    (by
      rw [HomologicalComplex.mono_homologyMap_iff_elementwise _ 0 (0 + 1) 2 (by simp)
        (by simp)]
      exact h1)
  refine ⟨f, hf, ?_⟩
  let S := Localization.Away f
  let ψ : R →+* S := algebraMap R S
  have hiso := hB ψ (IsLocalization.Away.algebraMap_isUnit f) 0 le_rfl
  have hm := (HomologicalComplex.mono_homologyMap_iff_elementwise
    (extendScalarsCxMap φ ψ) (-1) 0 1 (by simp) next_zero).1 inferInstance
  have he := (HomologicalComplex.epi_homologyMap_iff_elementwise
    (extendScalarsCxMap φ ψ) (-1) 0 1 (by simp) next_zero).1 inferInstance
  let E := extendScalars_iso_localizedModuleFunctor.{u, u} (Submonoid.powers f)
  have hE : ∀ (M : ModuleCat.{u} R) (m : M),
      (E.hom.app M).hom ((1 : S) ⊗ₜ[R, ψ] m) = M.localizedModuleMkLinearMap _ m := fun M m => by
    rw [extendScalars_iso_localizedModuleFunctor_hom_app_tmul, one_smul]
  have hEnat : ∀ {M N : ModuleCat.{u} R} (g : M ⟶ N) (z : (ModuleCat.extendScalars ψ).obj M),
      (E.hom.app N).hom (((ModuleCat.extendScalars ψ).map g).hom z) =
        (ModuleCat.localizedModuleMap.{u} (Submonoid.powers f) g).hom ((E.hom.app M).hom z) :=
    fun g z => congr($(E.hom.naturality g).hom z)
  constructor
  · intro x hx hφx
    obtain ⟨w, hw⟩ := hm _ (extendScalars_map_one_tmul_eq_zero ψ (C.d 0 1) x hx) 0 (by
      rw [map_zero]
      exact extendScalars_map_one_tmul_eq_zero ψ (φ.f 0) x hφx)
    have h1x : (1 : S) ⊗ₜ[R, ψ] x = 0 := hw.symm.trans (d_neg_one_apply ψ C w)
    have : (C.X 0).localizedModuleMkLinearMap (Submonoid.powers f) x = 0 :=
      (hE (C.X 0) x).symm.trans ((congrArg (E.hom.app (C.X 0)).hom h1x).trans (map_zero _))
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers f)
      ((C.X 0).localizedModuleMkLinearMap _)).1 this
    exact ⟨n, hn⟩
  · intro y hy
    obtain ⟨ξ, hξ, y₁, hy₁⟩ := he _ (extendScalars_map_one_tmul_eq_zero ψ (D.d 0 1) y hy)
    rw [d_neg_one_apply ψ D y₁, add_zero] at hy₁
    obtain ⟨⟨x, ⟨_, m, rfl⟩⟩, hxm⟩ := IsLocalizedModule.mk'_surjective (Submonoid.powers f)
      ((C.X 0).localizedModuleMkLinearMap _) ((E.hom.app (C.X 0)).hom ξ)
    simp only [Function.uncurry_apply_pair] at hxm
    have hdx := congrArg (E.hom.app (C.X 1)).hom hξ
    change (E.hom.app (C.X 1)).hom (((ModuleCat.extendScalars ψ).map (C.d 0 1)).hom ξ) = _ at hdx
    rw [hEnat, ← hxm, map_zero, localizedModuleMap_mk'] at hdx
    obtain ⟨⟨_, n₁, rfl⟩, hn₁⟩ := (IsLocalizedModule.mk'_eq_zero'
      (f := (C.X 1).localizedModuleMkLinearMap (Submonoid.powers f)) _).1 hdx
    have hφx := congrArg (E.hom.app (D.X 0)).hom hy₁
    change _ = (E.hom.app (D.X 0)).hom (((ModuleCat.extendScalars ψ).map (φ.f 0)).hom ξ) at hφx
    rw [hEnat, ← hxm, hE, localizedModuleMap_mk',
      ← IsLocalizedModule.mk'_one (Submonoid.powers f)] at hφx
    obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ := (IsLocalizedModule.mk'_eq_mk'_iff
      (f := (D.X 0).localizedModuleMkLinearMap (Submonoid.powers f)) _ _ _ _).1 hφx
    have hn₁' : f ^ n₁ • C.d 0 1 x = 0 := hn₁
    have hn₂' : f ^ n₂ • φ.f 0 x = f ^ n₂ • f ^ m • y := by
      simpa only [Submonoid.smul_def, OneMemClass.coe_one, one_smul] using hn₂
    refine ⟨f ^ (n₁ + n₂) • x, ?_, m + n₁ + n₂, ?_⟩
    · rw [map_smul, pow_add, mul_comm, mul_smul]
      change f ^ n₂ • f ^ n₁ • C.d 0 1 x = 0
      rw [hn₁', smul_zero]
    · rw [map_smul, show f ^ (m + n₁ + n₂) = f ^ n₁ * (f ^ n₂ * f ^ m) by ring, mul_smul,
        mul_smul, ← hn₂', pow_add, mul_smul]

section TwoTargets

open scoped ChangeOfRings

/-- The biproduct of two complexes concentrated in degrees `≥ n` is concentrated in degrees
`≥ n`. -/
theorem isStrictlyGE_biprod (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) [K.IsStrictlyGE n]
    [L.IsStrictlyGE n] : (K ⊞ L).IsStrictlyGE n := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact IsZero.of_iso ((biprod_isZero_iff _ _).2 ⟨K.isZero_of_isStrictlyGE n i hi,
    L.isZero_of_isStrictlyGE n i hi⟩) (HomologicalComplex.biprodXIso K L i)

/-- The biproduct of two complexes concentrated in degrees `≤ n` is concentrated in degrees
`≤ n`. -/
theorem isStrictlyLE_biprod (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) [K.IsStrictlyLE n]
    [L.IsStrictlyLE n] : (K ⊞ L).IsStrictlyLE n := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact IsZero.of_iso ((biprod_isZero_iff _ _).2 ⟨K.isZero_of_isStrictlyLE n i hi,
    L.isZero_of_isStrictlyLE n i hi⟩) (HomologicalComplex.biprodXIso K L i)

/-- The biproduct of two complexes of flat `R`-modules has flat terms. -/
theorem flat_biprod_X (K L : CochainComplex (ModuleCat.{u} R) ℤ) [∀ i, Module.Flat R (K.X i)]
    [∀ i, Module.Flat R (L.X i)] (i : ℤ) : Module.Flat R ((K ⊞ L).X i) :=
  have : Module.Flat R (K.X i × L.X i) := flat_prod
  Module.Flat.of_linearEquiv ((HomologicalComplex.biprodXIso K L i ≪≫
    ModuleCat.biprodIsoProd (K.X i) (L.X i)).toLinearEquiv)

/-- The biproduct of two complexes that are perfect in `D(R)` is perfect. -/
theorem isPerfect_biprod (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsPerfect (DerivedCategory.Q.obj K)) (hL : IsPerfect (DerivedCategory.Q.obj L)) :
    IsPerfect (DerivedCategory.Q.obj (K ⊞ L)) := by
  have h := (isPerfect_of_distinguished _
    (binaryBiproductTriangle_distinguished (DerivedCategory.Q.obj K)
      (DerivedCategory.Q.obj L))).2.1 hK hL
  have : PreservesBinaryBiproducts (DerivedCategory.Q (C := ModuleCat.{u} R)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  exact isPerfect_of_iso (DerivedCategory.Q.mapBiprod K L) h


/-- **Fibre isomorphism on `H⁰` and fibre injectivity on `H¹`, for `(ρ₁, ρ₂ + u)`, spread out.** -/
theorem exists_away_of_fibre_two {C D₁ D₂ E : CochainComplex (ModuleCat.{u} R) ℤ} (d : ℤ)
    [C.IsStrictlyGE 0] [C.IsStrictlyLE d]
    [D₁.IsStrictlyGE 0] [D₁.IsStrictlyLE d] [D₂.IsStrictlyGE 0] [D₂.IsStrictlyLE d]
    [E.IsStrictlyGE 0] [E.IsStrictlyLE 0] [∀ i, Module.Flat R (C.X i)]
    [∀ i, Module.Flat R (D₁.X i)] [∀ i, Module.Flat R (D₂.X i)] [∀ i, Module.Flat R (E.X i)]
    (hC : IsPerfect (DerivedCategory.Q.obj C)) (hD₁ : IsPerfect (DerivedCategory.Q.obj D₁))
    (hD₂ : IsPerfect (DerivedCategory.Q.obj D₂)) (hE : IsPerfect (DerivedCategory.Q.obj E))
    (hd : 0 ≤ d) (ρ₁ : C ⟶ D₁) (ρ₂ : C ⟶ D₂) (u : E ⟶ D₂) (p : Ideal R) [p.IsPrime]
    (h0 : ∀ (x : (extendScalarsCx (algebraMap R p.ResidueField) C).X 0)
      (z : (extendScalarsCx (algebraMap R p.ResidueField) E).X 0),
      (extendScalarsCx (algebraMap R p.ResidueField) C).d 0 1 x = 0 →
      (extendScalarsCxMap ρ₁ (algebraMap R p.ResidueField)).f 0 x = 0 →
      (extendScalarsCxMap ρ₂ (algebraMap R p.ResidueField)).f 0 x +
        (extendScalarsCxMap u (algebraMap R p.ResidueField)).f 0 z = 0 → x = 0 ∧ z = 0)
    (h0' : ∀ (y₁ : (extendScalarsCx (algebraMap R p.ResidueField) D₁).X 0)
      (y₂ : (extendScalarsCx (algebraMap R p.ResidueField) D₂).X 0),
      (extendScalarsCx (algebraMap R p.ResidueField) D₁).d 0 1 y₁ = 0 →
      (extendScalarsCx (algebraMap R p.ResidueField) D₂).d 0 1 y₂ = 0 →
      ∃ (x : (extendScalarsCx (algebraMap R p.ResidueField) C).X 0)
        (z : (extendScalarsCx (algebraMap R p.ResidueField) E).X 0),
        (extendScalarsCx (algebraMap R p.ResidueField) C).d 0 1 x = 0 ∧
        (extendScalarsCxMap ρ₁ (algebraMap R p.ResidueField)).f 0 x = y₁ ∧
        (extendScalarsCxMap ρ₂ (algebraMap R p.ResidueField)).f 0 x +
          (extendScalarsCxMap u (algebraMap R p.ResidueField)).f 0 z = y₂)
    (h1 : ∀ x : (extendScalarsCx (algebraMap R p.ResidueField) C).X 1,
      (extendScalarsCx (algebraMap R p.ResidueField) C).d 1 2 x = 0 →
      ∀ (y₁ : (extendScalarsCx (algebraMap R p.ResidueField) D₁).X 0)
        (y₂ : (extendScalarsCx (algebraMap R p.ResidueField) D₂).X 0),
        (extendScalarsCxMap ρ₁ (algebraMap R p.ResidueField)).f 1 x =
          (extendScalarsCx (algebraMap R p.ResidueField) D₁).d 0 1 y₁ →
        (extendScalarsCxMap ρ₂ (algebraMap R p.ResidueField)).f 1 x =
          (extendScalarsCx (algebraMap R p.ResidueField) D₂).d 0 1 y₂ →
        ∃ w : (extendScalarsCx (algebraMap R p.ResidueField) C).X 0,
          (extendScalarsCx (algebraMap R p.ResidueField) C).d 0 1 w = x) :
    ∃ a : R, a ∉ p ∧ ∀ y₁ : D₁.X 0, D₁.d 0 1 y₁ = 0 →
      ∃ (x : C.X 0) (w : E.X 0) (n : ℕ), C.d 0 1 x = 0 ∧ ρ₁.f 0 x = a ^ n • y₁ ∧
        ρ₂.f 0 x + u.f 0 w = 0 := by
  set ψ := algebraMap R p.ResidueField
  set G := ModuleCat.extendScalars.{u, u, u} ψ
  have : (C ⊞ E).IsStrictlyGE 0 := isStrictlyGE_biprod C E 0
  have : E.IsStrictlyLE d := CochainComplex.isStrictlyLE_of_le E 0 d hd
  have : (C ⊞ E).IsStrictlyLE d := isStrictlyLE_biprod C E d
  have : (D₁ ⊞ D₂).IsStrictlyGE 0 := isStrictlyGE_biprod D₁ D₂ 0
  have : (D₁ ⊞ D₂).IsStrictlyLE d := isStrictlyLE_biprod D₁ D₂ d
  have : ∀ i, Module.Flat R ((C ⊞ E).X i) := flat_biprod_X C E
  have : ∀ i, Module.Flat R ((D₁ ⊞ D₂).X i) := flat_biprod_X D₁ D₂
  set φ : C ⊞ E ⟶ D₁ ⊞ D₂ := biprod.lift (biprod.fst ≫ ρ₁) (biprod.fst ≫ ρ₂ + biprod.snd ≫ u)
  have hfst : ∀ i, φ.f i ≫ (biprod.fst : D₁ ⊞ D₂ ⟶ D₁).f i =
      (biprod.fst : C ⊞ E ⟶ C).f i ≫ ρ₁.f i := fun i => by
    rw [← HomologicalComplex.comp_f, biprod.lift_fst, HomologicalComplex.comp_f]
  have hsnd : ∀ i, φ.f i ≫ (biprod.snd : D₁ ⊞ D₂ ⟶ D₂).f i =
      (biprod.fst : C ⊞ E ⟶ C).f i ≫ ρ₂.f i + (biprod.snd : C ⊞ E ⟶ E).f i ≫ u.f i := fun i => by
    rw [← HomologicalComplex.comp_f, biprod.lift_snd, HomologicalComplex.add_f_apply,
      HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  -- decomposition of elements, before and after base change
  have hdec : ∀ {K L : CochainComplex (ModuleCat.{u} R) ℤ} (i : ℤ)
      (x : (extendScalarsCx ψ (K ⊞ L)).X i),
      x = (G.map ((biprod.inl : K ⟶ K ⊞ L).f i)) ((G.map ((biprod.fst : K ⊞ L ⟶ K).f i)) x) +
        (G.map ((biprod.inr : L ⟶ K ⊞ L).f i)) ((G.map ((biprod.snd : K ⊞ L ⟶ L).f i)) x) := by
    intro K L i x
    have h := congrArg (fun g => (G.map (g.f i)) x) (biprod.total (X := K) (Y := L))
    simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
      HomologicalComplex.id_f, G.map_add, G.map_comp, G.map_id] at h
    exact h.symm
  have hmapd : ∀ {K L : CochainComplex (ModuleCat.{u} R) ℤ} (g : K ⟶ L) (i j : ℤ)
      (x : (extendScalarsCx ψ K).X i),
      (G.map (g.f j)) ((extendScalarsCx ψ K).d i j x) =
        (extendScalarsCx ψ L).d i j ((G.map (g.f i)) x) := by
    intro K L g i j x
    change (G.map (K.d i j) ≫ G.map (g.f j)) x = (G.map (g.f i) ≫ G.map (L.d i j)) x
    rw [← G.map_comp, ← G.map_comp, g.comm]
  have hfstκ : ∀ i (x : (extendScalarsCx ψ (C ⊞ E)).X i),
      (G.map ((biprod.fst : D₁ ⊞ D₂ ⟶ D₁).f i)) ((extendScalarsCxMap φ ψ).f i x) =
        (extendScalarsCxMap ρ₁ ψ).f i ((G.map ((biprod.fst : C ⊞ E ⟶ C).f i)) x) := fun i x => by
    change (G.map (φ.f i) ≫ G.map _) x = (G.map _ ≫ G.map (ρ₁.f i)) x
    rw [← G.map_comp, ← G.map_comp, hfst]
  have hsndκ : ∀ i (x : (extendScalarsCx ψ (C ⊞ E)).X i),
      (G.map ((biprod.snd : D₁ ⊞ D₂ ⟶ D₂).f i)) ((extendScalarsCxMap φ ψ).f i x) =
        (extendScalarsCxMap ρ₂ ψ).f i ((G.map ((biprod.fst : C ⊞ E ⟶ C).f i)) x) +
          (extendScalarsCxMap u ψ).f i ((G.map ((biprod.snd : C ⊞ E ⟶ E).f i)) x) :=
    fun i x => by
      change (G.map (φ.f i) ≫ G.map _) x = (G.map _ ≫ G.map (ρ₂.f i)) x +
        (G.map _ ≫ G.map (u.f i)) x
      rw [← G.map_comp, ← G.map_comp, ← G.map_comp, hsnd, G.map_add]
      rfl
  have hφinl : ∀ i (x : (extendScalarsCx ψ C).X i),
      (extendScalarsCxMap φ ψ).f i ((G.map ((biprod.inl : C ⟶ C ⊞ E).f i)) x) =
        (G.map ((biprod.inl : D₁ ⟶ D₁ ⊞ D₂).f i)) ((extendScalarsCxMap ρ₁ ψ).f i x) +
        (G.map ((biprod.inr : D₂ ⟶ D₁ ⊞ D₂).f i)) ((extendScalarsCxMap ρ₂ ψ).f i x) :=
    fun i x => by
      have h : (biprod.inl : C ⟶ C ⊞ E) ≫ φ = ρ₁ ≫ biprod.inl + ρ₂ ≫ biprod.inr := by
        refine biprod.hom_ext _ _ ?_ ?_ <;> simp [φ]
      change (G.map _ ≫ G.map (φ.f i)) x = (G.map (ρ₁.f i) ≫ G.map _) x +
        (G.map (ρ₂.f i) ≫ G.map _) x
      rw [← G.map_comp, ← G.map_comp, ← G.map_comp, ← HomologicalComplex.comp_f, h,
        HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
        G.map_add]
      rfl
  have hφinr : ∀ i (z : (extendScalarsCx ψ E).X i),
      (extendScalarsCxMap φ ψ).f i ((G.map ((biprod.inr : E ⟶ C ⊞ E).f i)) z) =
        (G.map ((biprod.inr : D₂ ⟶ D₁ ⊞ D₂).f i)) ((extendScalarsCxMap u ψ).f i z) :=
    fun i z => by
      have h : (biprod.inr : E ⟶ C ⊞ E) ≫ φ = u ≫ biprod.inr := by
        refine biprod.hom_ext _ _ ?_ ?_ <;> simp [φ]
      change (G.map _ ≫ G.map (φ.f i)) z = (G.map (u.f i) ≫ G.map _) z
      rw [← G.map_comp, ← G.map_comp, ← HomologicalComplex.comp_f, h, HomologicalComplex.comp_f]
  have hE1 : ∀ z : (extendScalarsCx ψ E).X 1, z = 0 := fun z =>
    @Subsingleton.elim _ ((ModuleCat.isZero_iff_subsingleton).1
      (G.map_isZero (E.isZero_of_isStrictlyLE 0 1 (by norm_num)))) z 0
  obtain ⟨a, ha, -, hsurj⟩ := exists_away_of_fibre_elementwise φ d
    (isPerfect_biprod C E hC hE) (isPerfect_biprod D₁ D₂ hD₁ hD₂) p
    (fun x hx hφx => by
      have hx1 := hmapd (biprod.fst : C ⊞ E ⟶ C) 0 1 x
      rw [hx, map_zero] at hx1
      have hφ1 := hfstκ 0 x
      have hφ2 := hsndκ 0 x
      rw [hφx, map_zero] at hφ1 hφ2
      obtain ⟨h1, h2⟩ := h0 _ _ hx1.symm hφ1.symm hφ2.symm
      rw [hdec 0 x, h1, h2, map_zero, map_zero, add_zero])
    (fun y hy => by
      have hy1 := hmapd (biprod.fst : D₁ ⊞ D₂ ⟶ D₁) 0 1 y
      have hy2 := hmapd (biprod.snd : D₁ ⊞ D₂ ⟶ D₂) 0 1 y
      rw [hy, map_zero] at hy1 hy2
      obtain ⟨x, z, hx, hx1, hx2⟩ := h0' _ _ hy1.symm hy2.symm
      refine ⟨(G.map ((biprod.inl : C ⟶ C ⊞ E).f 0)) x +
        (G.map ((biprod.inr : E ⟶ C ⊞ E).f 0)) z, ?_, ?_⟩
      · rw [map_add, ← hmapd, ← hmapd, hx, hE1 ((extendScalarsCx ψ E).d 0 1 z), map_zero,
          map_zero, add_zero]
      · rw [map_add, hφinl, hφinr, hx1, add_assoc, ← map_add, hx2]
        exact (hdec 0 y).symm)
    (fun x hx y hy => by
      have hz := hE1 ((G.map ((biprod.snd : C ⊞ E ⟶ E).f 1)) x)
      have hx1 := hmapd (biprod.fst : C ⊞ E ⟶ C) 1 2 x
      rw [hx, map_zero] at hx1
      have hφ1 := hfstκ 1 x
      have hφ2 := hsndκ 1 x
      rw [hy, hmapd] at hφ1 hφ2
      rw [hz, map_zero, add_zero] at hφ2
      obtain ⟨w, hw⟩ := h1 _ hx1.symm _ _ hφ1.symm hφ2.symm
      refine ⟨(G.map ((biprod.inl : C ⟶ C ⊞ E).f 0)) w, ?_⟩
      rw [← hmapd, hw]
      conv_rhs => rw [hdec 1 x, hz, map_zero, add_zero])
  refine ⟨a, ha, fun y₁ hy₁ => ?_⟩
  obtain ⟨x', hx', n, hφx'⟩ := hsurj ((biprod.inl : D₁ ⟶ D₁ ⊞ D₂).f 0 y₁) (by
    change ((biprod.inl : D₁ ⟶ D₁ ⊞ D₂).f 0 ≫ (D₁ ⊞ D₂).d 0 1) y₁ = 0
    rw [(biprod.inl : D₁ ⟶ D₁ ⊞ D₂).comm, ConcreteCategory.comp_apply, hy₁, map_zero])
  refine ⟨(biprod.fst : C ⊞ E ⟶ C).f 0 x', (biprod.snd : C ⊞ E ⟶ E).f 0 x', n, ?_, ?_, ?_⟩
  · change ((biprod.fst : C ⊞ E ⟶ C).f 0 ≫ C.d 0 1) x' = 0
    rw [(biprod.fst : C ⊞ E ⟶ C).comm 0 1, ConcreteCategory.comp_apply, hx', map_zero]
  · have e1 : (biprod.fst : D₁ ⊞ D₂ ⟶ D₁).f 0 ((biprod.inl : D₁ ⟶ D₁ ⊞ D₂).f 0 y₁) = y₁ := by
      change ((biprod.inl : D₁ ⟶ D₁ ⊞ D₂) ≫ biprod.fst).f 0 y₁ = y₁
      rw [biprod.inl_fst]
      rfl
    have h := congrArg ((biprod.fst : D₁ ⊞ D₂ ⟶ D₁).f 0) hφx'
    rw [map_smul, e1] at h
    rw [← h, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, hfst]
  · have e2 : (biprod.snd : D₁ ⊞ D₂ ⟶ D₂).f 0 ((biprod.inl : D₁ ⟶ D₁ ⊞ D₂).f 0 y₁) = 0 := by
      change ((biprod.inl : D₁ ⟶ D₁ ⊞ D₂) ≫ biprod.snd).f 0 y₁ = 0
      rw [biprod.inl_snd]
      rfl
    have h := congrArg ((biprod.snd : D₁ ⊞ D₂ ⟶ D₂).f 0) hφx'
    rw [map_smul, e2, smul_zero] at h
    rw [← h, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply, hsnd]
    rfl

/-- **`exists_away_of_fibre_two` with the degree-zero fibre conditions read on generators.**
If the degree-zero fibre cocycles of `C`, `D₁` and `D₂` are the multiples of `x₀`, `y₁` and
`y₂ ≠ 0`, those of `E` the multiples of `z₁` with `u z₁ = y₂`, and `ρ₁ x₀ ≠ 0`, then the
degree-zero hypotheses of `exists_away_of_fibre_two` hold. -/
theorem exists_away_of_fibre_two_of_generators {C D₁ D₂ E : CochainComplex (ModuleCat.{u} R) ℤ}
    (d : ℤ) [C.IsStrictlyGE 0] [C.IsStrictlyLE d]
    [D₁.IsStrictlyGE 0] [D₁.IsStrictlyLE d] [D₂.IsStrictlyGE 0] [D₂.IsStrictlyLE d]
    [E.IsStrictlyGE 0] [E.IsStrictlyLE 0] [∀ i, Module.Flat R (C.X i)]
    [∀ i, Module.Flat R (D₁.X i)] [∀ i, Module.Flat R (D₂.X i)] [∀ i, Module.Flat R (E.X i)]
    (hC : IsPerfect (DerivedCategory.Q.obj C)) (hD₁ : IsPerfect (DerivedCategory.Q.obj D₁))
    (hD₂ : IsPerfect (DerivedCategory.Q.obj D₂)) (hE : IsPerfect (DerivedCategory.Q.obj E))
    (hd : 0 ≤ d) (ρ₁ : C ⟶ D₁) (ρ₂ : C ⟶ D₂) (u : E ⟶ D₂) (p : Ideal R) [p.IsPrime]
    (x₀ : (extendScalarsCx (algebraMap R p.ResidueField) C).X 0)
    (hx₀ : (extendScalarsCx (algebraMap R p.ResidueField) C).d 0 1 x₀ = 0)
    (hα : ∀ x : (extendScalarsCx (algebraMap R p.ResidueField) C).X 0,
      (extendScalarsCx (algebraMap R p.ResidueField) C).d 0 1 x = 0 →
        ∃ c : p.ResidueField, x = c • x₀)
    (y₁ : (extendScalarsCx (algebraMap R p.ResidueField) D₁).X 0)
    (hβ₁ : ∀ y : (extendScalarsCx (algebraMap R p.ResidueField) D₁).X 0,
      (extendScalarsCx (algebraMap R p.ResidueField) D₁).d 0 1 y = 0 →
        ∃ c : p.ResidueField, y = c • y₁)
    (y₂ : (extendScalarsCx (algebraMap R p.ResidueField) D₂).X 0) (hy₂ : y₂ ≠ 0)
    (hβ₂ : ∀ y : (extendScalarsCx (algebraMap R p.ResidueField) D₂).X 0,
      (extendScalarsCx (algebraMap R p.ResidueField) D₂).d 0 1 y = 0 →
        ∃ c : p.ResidueField, y = c • y₂)
    (z₁ : (extendScalarsCx (algebraMap R p.ResidueField) E).X 0)
    (hz : ∀ z : (extendScalarsCx (algebraMap R p.ResidueField) E).X 0,
      ∃ c : p.ResidueField, z = c • z₁)
    (hu : (extendScalarsCxMap u (algebraMap R p.ResidueField)).f 0 z₁ = y₂)
    (hγ : (extendScalarsCxMap ρ₁ (algebraMap R p.ResidueField)).f 0 x₀ ≠ 0)
    (h1 : ∀ x : (extendScalarsCx (algebraMap R p.ResidueField) C).X 1,
      (extendScalarsCx (algebraMap R p.ResidueField) C).d 1 2 x = 0 →
      ∀ (y₁ : (extendScalarsCx (algebraMap R p.ResidueField) D₁).X 0)
        (y₂ : (extendScalarsCx (algebraMap R p.ResidueField) D₂).X 0),
        (extendScalarsCxMap ρ₁ (algebraMap R p.ResidueField)).f 1 x =
          (extendScalarsCx (algebraMap R p.ResidueField) D₁).d 0 1 y₁ →
        (extendScalarsCxMap ρ₂ (algebraMap R p.ResidueField)).f 1 x =
          (extendScalarsCx (algebraMap R p.ResidueField) D₂).d 0 1 y₂ →
        ∃ w : (extendScalarsCx (algebraMap R p.ResidueField) C).X 0,
          (extendScalarsCx (algebraMap R p.ResidueField) C).d 0 1 w = x) :
    ∃ a : R, a ∉ p ∧ ∀ y₁ : D₁.X 0, D₁.d 0 1 y₁ = 0 →
      ∃ (x : C.X 0) (w : E.X 0) (n : ℕ), C.d 0 1 x = 0 ∧ ρ₁.f 0 x = a ^ n • y₁ ∧
        ρ₂.f 0 x + u.f 0 w = 0 := by
  have hcomm : ∀ {K L : CochainComplex (ModuleCat.{u} R) ℤ} (g : K ⟶ L)
      (x : (extendScalarsCx (algebraMap R p.ResidueField) K).X 0),
      (extendScalarsCx (algebraMap R p.ResidueField) L).d 0 1
          ((extendScalarsCxMap g (algebraMap R p.ResidueField)).f 0 x) =
        (extendScalarsCxMap g (algebraMap R p.ResidueField)).f 1
          ((extendScalarsCx (algebraMap R p.ResidueField) K).d 0 1 x) := fun g x => by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      (extendScalarsCxMap g (algebraMap R p.ResidueField)).comm]
  obtain ⟨l₁, hl₁⟩ := hβ₁ ((extendScalarsCxMap ρ₁ (algebraMap R p.ResidueField)).f 0 x₀)
    (by rw [hcomm, hx₀, map_zero])
  obtain ⟨l₂, hl₂⟩ := hβ₂ ((extendScalarsCxMap ρ₂ (algebraMap R p.ResidueField)).f 0 x₀)
    (by rw [hcomm, hx₀, map_zero])
  have hl₁0 : l₁ ≠ 0 := by
    rintro rfl
    exact hγ (by rw [hl₁, zero_smul])
  exact exists_away_of_fibre_two d hC hD₁ hD₂ hE hd ρ₁ ρ₂ u p
    (fun x z hx h₁ h₂ => by
      obtain ⟨c, rfl⟩ := hα x hx
      obtain ⟨c', rfl⟩ := hz z
      rw [map_smul, hl₁, smul_smul] at h₁
      obtain rfl : c = 0 := (mul_eq_zero.1 ((smul_eq_zero.1 h₁).resolve_right
        fun h => hγ (by rw [hl₁, h, smul_zero]))).resolve_right hl₁0
      rw [zero_smul, map_zero, zero_add, map_smul, hu] at h₂
      obtain rfl : c' = 0 := (smul_eq_zero.1 h₂).resolve_right hy₂
      exact ⟨zero_smul _ _, zero_smul _ _⟩)
    (fun y₁' y₂' hy₁' hy₂' => by
      obtain ⟨c₁, rfl⟩ := hβ₁ y₁' hy₁'
      obtain ⟨c₂, rfl⟩ := hβ₂ y₂' hy₂'
      refine ⟨(c₁ * l₁⁻¹) • x₀, (c₂ - c₁ * l₁⁻¹ * l₂) • z₁, ?_, ?_, ?_⟩
      · rw [map_smul, hx₀, smul_zero]
      · rw [map_smul, hl₁, smul_smul, mul_assoc, inv_mul_cancel₀ hl₁0, mul_one]
      · rw [map_smul, map_smul, hl₂, hu, smul_smul, ← add_smul]
        congr 1
        ring)
    h1

end TwoTargets

end Elementwise

end StacksDraft.Perfect

end
