module

public import StacksFrontier.AlgebraicGeometry.Spaces.CechStructureSheafBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperModuleCohomologyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.Homology.DerivedIndexing.Extend
public import StacksFrontier.Homology.KFlat.UnitCocycleLocalTriviality

/-!
# The Čech complex of the structure sheaf of a proper flat algebraic space

Let `X` be a proper algebraic space over `Spec A` with a surjective étale chart `U` with affine
scheme, and `C` the Čech complex of its structure sheaf for `U`
(`AlgebraicGeometry.Space.cechStructureComplex`). We prove:

* its cohomology is `H^*(X, 𝒪_X)`, hence finite over a Noetherian `A` (Stacks 08AS) and zero in
  high degrees (Stacks 073G);
* it is K-flat when `X` is moreover flat over `Spec A`;
* its first differential is the difference of the two pullbacks along the kernel pair
  `U ×_X U ⇉ U`, the first term of the Čech nerve being that kernel pair.

## Main results

* `AlgebraicGeometry.Space.nonempty_uliftHomology_cechStructureComplex_iso`:
  `H^n(C) = H^n(X, 𝒪_X)`.
* `AlgebraicGeometry.Space.moduleFinite_homology_cechStructureComplex` and
  `AlgebraicGeometry.Space.exists_isZero_homology_cechStructureComplex`.
* `AlgebraicGeometry.Space.kFlat_cechStructureComplex`.
* `AlgebraicGeometry.Space.isPullback_cechNerve_one` and
  `AlgebraicGeometry.Space.cechUnitComplex_d_zero_one`.
* `AlgebraicGeometry.Space.exists_away_equalizerTensorExact`: for `X` also flat and `A`
  Noetherian, exactness of `0 → κ(𝔭) → κ(𝔭) ⊗ Γ(U) → κ(𝔭) ⊗ Γ(U ×_X U)` at a prime `𝔭` spreads
  to every `A`-algebra in which some `h ∉ 𝔭` is invertible.
* `Subalgebra.bijective_algebraMap_of_linearEquiv`: a subalgebra free of rank one is the base.

## References

* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 073G](https://stacks.math.columbia.edu/tag/073G)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial ComplexShape
open Stacks.Cohomology.SiteModules

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace Stacks.CechTop

variable {C : Type*} [Category* C] (U : C) [∀ n : ℕ, HasProduct (fun _ : Fin (n + 1) => U)]

/-- The two faces `U × U ⟶ U` of the Čech nerve exhibit its first term as a binary product. -/
noncomputable def cechNerveOneIsLimit :
    IsLimit (BinaryFan.mk ((cechNerve U).map (SimplexCategory.δ (1 : Fin 2)).op)
      ((cechNerve U).map (SimplexCategory.δ (0 : Fin 2)).op)) := by
  have e₁ : (SimplexCategory.δ (1 : Fin 2)).toOrderHom (0 : Fin 1) = 0 := rfl
  have e₀ : (SimplexCategory.δ (0 : Fin 2)).toOrderHom (0 : Fin 1) = 1 := rfl
  have h₁ : (cechNerve U).map (SimplexCategory.δ (1 : Fin 2)).op ≫ cechπ U 0 0 = cechπ U 1 0 :=
    (cechNerve_map_cechπ U _ 0).trans (congrArg (cechπ U 1) e₁)
  have h₀ : (cechNerve U).map (SimplexCategory.δ (0 : Fin 2)).op ≫ cechπ U 0 0 = cechπ U 1 1 :=
    (cechNerve_map_cechπ U _ 0).trans (congrArg (cechπ U 1) e₀)
  refine BinaryFan.isLimitMk (fun s => prepend U (s.fst ≫ cechπ U 0 0) 0 s.snd) ?_ ?_ ?_
  · intro s
    refine cechNerve_hom_ext U fun i => ?_
    obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    exact (Category.assoc _ _ _).trans ((congrArg (prepend U (s.fst ≫ cechπ U 0 0) 0 s.snd ≫ ·)
      h₁).trans (prepend_π_zero U _ 0 s.snd))
  · intro s
    refine cechNerve_hom_ext U fun i => ?_
    obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    exact (Category.assoc _ _ _).trans ((congrArg (prepend U (s.fst ≫ cechπ U 0 0) 0 s.snd ≫ ·)
      h₀).trans (prepend_π_succ U _ 0 s.snd 0))
  · intro s m hm₁ hm₂
    refine cechNerve_hom_ext U fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · refine Eq.trans ?_ (prepend_π_zero U _ 0 s.snd).symm
      refine Eq.trans ?_ (congrArg (· ≫ cechπ U 0 0) hm₁)
      exact ((congrArg (m ≫ ·) h₁).symm).trans (Category.assoc _ _ _).symm
    · obtain rfl : j = 0 := Fin.fin_one_eq_zero j
      refine Eq.trans ?_ (prepend_π_succ U _ 0 s.snd 0).symm
      refine Eq.trans ?_ (congrArg (· ≫ cechπ U 0 0) hm₂)
      exact ((congrArg (m ≫ ·) h₀).symm).trans (Category.assoc _ _ _).symm

end Stacks.CechTop

/-- **A subalgebra free of rank one is the base ring.** If a subalgebra `S` of an `R`-algebra is
isomorphic to `R` as an `R`-module, the structure map `R ⟶ S` is bijective. -/
theorem Subalgebra.bijective_algebraMap_of_linearEquiv {R T : Type*} [CommRing R] [CommRing T]
    [Algebra R T] (S : Subalgebra R T) (e : S ≃ₗ[R] R) :
    Function.Bijective (algebraMap R S) := by
  set s₀ : S := e.symm 1
  have hs : ∀ s : S, s = e s • s₀ := fun s => by
    apply e.injective
    rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  set c := e 1
  set d := e (s₀ * s₀)
  have hcd : c * d = 1 := by
    have h₁ : s₀ = (c * d) • s₀ := by
      calc s₀ = 1 * s₀ := (one_mul _).symm
        _ = (c • s₀) * s₀ := by rw [← hs 1]
        _ = c • (s₀ * s₀) := smul_mul_assoc _ _ _
        _ = c • (d • s₀) := by rw [← hs (s₀ * s₀)]
        _ = (c * d) • s₀ := smul_smul _ _ _
    have h₂ := congrArg e h₁
    rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one] at h₂
    exact h₂.symm
  have hc : IsUnit c := IsUnit.of_mul_eq_one d hcd
  refine ⟨fun a b hab => ?_, fun s => ⟨e s * d, ?_⟩⟩
  · have h : e (algebraMap R S a) = e (algebraMap R S b) := congrArg e hab
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul] at h
    exact hc.mul_left_injective h
  · calc algebraMap R S (e s * d) = (e s * d) • (1 : S) := Algebra.algebraMap_eq_smul_one _
      _ = (e s * d) • (c • s₀) := by rw [← hs 1]
      _ = e s • s₀ := by rw [smul_smul, mul_assoc, mul_comm d c, hcd, mul_one]
      _ = s := (hs s).symm

namespace ModuleCat

open scoped TensorProduct ChangeOfRings

/-- Extension of scalars along an algebra map is the tensor product, `S`-linearly. -/
noncomputable def extendScalarsAlgebraMapObjEquiv {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj M ≃ₗ[S] S ⊗[R] M :=
  let e : (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) ≃ₗ[R] S :=
    { AddEquiv.refl S with map_smul' := fun r s => (Algebra.smul_def r (show S from s)).symm }
  let eR := TensorProduct.congr e (LinearEquiv.refl R M)
  { __ := eR.toAddEquiv
    map_smul' := by
      intro s x
      let f₁ : (ModuleCat.extendScalars (algebraMap R S)).obj M →+ S ⊗[R] M :=
        eR.toAddMonoidHom.comp (AddMonoidHom.mk' (s • ·) (smul_add s))
      let f₂ : (ModuleCat.extendScalars (algebraMap R S)).obj M →+ S ⊗[R] M :=
        (AddMonoidHom.mk' (s • ·) (smul_add s)).comp eR.toAddMonoidHom
      change f₁ x = f₂ x
      induction x using TensorProduct.inductionOn with
      | add x y hx hy =>
        exact ((map_add f₁ x y).trans (congrArg₂ (· + ·) hx hy)).trans (map_add f₂ x y).symm
      | tmul a m => rfl }

/-- The identification is natural. -/
theorem extendScalarsAlgebraMapObjEquiv_naturality {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] {M N : ModuleCat.{u} R} (g : M ⟶ N)
    (x : (ModuleCat.extendScalars (algebraMap R S)).obj M) :
    extendScalarsAlgebraMapObjEquiv N ((ModuleCat.extendScalars (algebraMap R S)).map g x) =
      LinearMap.lTensor S g.hom (extendScalarsAlgebraMapObjEquiv M x) := by
  let f₁ : (ModuleCat.extendScalars (algebraMap R S)).obj M →+ S ⊗[R] N :=
    (extendScalarsAlgebraMapObjEquiv N).toAddMonoidHom.comp
      ((ModuleCat.extendScalars (algebraMap R S)).map g).hom.toAddMonoidHom
  let f₂ : (ModuleCat.extendScalars (algebraMap R S)).obj M →+ S ⊗[R] N :=
    (LinearMap.lTensor S g.hom).toAddMonoidHom.comp
      (extendScalarsAlgebraMapObjEquiv M).toAddMonoidHom
  change f₁ x = f₂ x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact ((map_add f₁ x y).trans (congrArg₂ (· + ·) hx hy)).trans (map_add f₂ x y).symm
  | tmul a m => rfl

end ModuleCat

namespace AlgHom

open scoped TensorProduct

variable {A C D : Type u} [CommRing A] [CommRing C] [CommRing D] [Algebra A C] [Algebra A D]
  (p₁ p₂ : C →ₐ[A] D) (A' : Type u) [CommRing A'] [Algebra A A']

/-- The equalizer of the two maps `A' ⊗_A C ⇉ A' ⊗_A D` of `A'`-algebras induced by two maps of
`A`-algebras `p₁ p₂ : C → D`. -/
abbrev lTensorEqualizer : Subalgebra A' (A' ⊗[A] C) :=
  AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id A' A') p₁)
    (Algebra.TensorProduct.map (AlgHom.id A' A') p₂)

variable {p₁ p₂ A'}

/-- `A' ⊗ p` as a linear map is `A' ⊗ p` as a map of algebras. -/
theorem lTensor_toLinearMap_apply_eq_map (p : C →ₐ[A] D) (x : A' ⊗[A] C) :
    p.toLinearMap.lTensor A' x = Algebra.TensorProduct.map (AlgHom.id A' A') p x := by
  induction x using TensorProduct.inductionOn with
  | tmul a c => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- An element of `A' ⊗_A C` lies in the equalizer exactly when `A' ⊗ p₁` and `A' ⊗ p₂` agree
on it. -/
theorem mem_lTensorEqualizer_iff (x : A' ⊗[A] C) :
    x ∈ lTensorEqualizer p₁ p₂ A' ↔ p₁.toLinearMap.lTensor A' x = p₂.toLinearMap.lTensor A' x := by
  rw [AlgHom.mem_equalizer, lTensor_toLinearMap_apply_eq_map, lTensor_toLinearMap_apply_eq_map]

/-- The structure map `A' → lTensorEqualizer p₁ p₂ A'` sends `a` to `a ⊗ 1`. -/
theorem coe_algebraMap_lTensorEqualizer (a : A') :
    ((algebraMap A' (lTensorEqualizer p₁ p₂ A') a : lTensorEqualizer p₁ p₂ A') : A' ⊗[A] C) =
      tmulOne A C A' a :=
  rfl

/-- **The equalizer sequence is exact after base change to `A'` exactly when the equalizer of
`A' ⊗_A C ⇉ A' ⊗_A D` is `A'`.** -/
theorem equalizerTensorExact_iff_bijective_algebraMap_lTensorEqualizer :
    EqualizerTensorExact p₁ p₂ A' ↔
      Function.Bijective (algebraMap A' (lTensorEqualizer p₁ p₂ A')) := by
  rw [equalizerTensorExact_iff_tmulOne]
  have hmem (x : A' ⊗[A] C) :
      (p₁.toLinearMap - p₂.toLinearMap).lTensor A' x = 0 ↔ x ∈ lTensorEqualizer p₁ p₂ A' := by
    rw [mem_lTensorEqualizer_iff, LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero]
  constructor
  · rintro ⟨hinj, hex⟩
    refine ⟨fun a b hab => hinj ?_, fun s => ?_⟩
    · rw [← coe_algebraMap_lTensorEqualizer (p₁ := p₁) (p₂ := p₂) a,
        ← coe_algebraMap_lTensorEqualizer (p₁ := p₁) (p₂ := p₂) b, hab]
    · obtain ⟨a, ha⟩ := hex s ((hmem s).2 s.2)
      exact ⟨a, Subtype.ext ((coe_algebraMap_lTensorEqualizer a).trans ha)⟩
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun a b hab => hinj (Subtype.ext ?_), fun x hx => ?_⟩
    · rwa [coe_algebraMap_lTensorEqualizer, coe_algebraMap_lTensorEqualizer]
    · obtain ⟨a, ha⟩ := hsurj ⟨x, (hmem x).1 hx⟩
      exact ⟨a, (coe_algebraMap_lTensorEqualizer a).symm.trans (congrArg Subtype.val ha)⟩

/-- **The kernel of a map of modules presenting `p₂ - p₁`, after extension of scalars to `A'`, is
the equalizer of `A' ⊗_A C ⇉ A' ⊗_A D`.** -/
theorem nonempty_ker_extendScalars_linearEquiv_lTensorEqualizer {M₀ M₁ : ModuleCat.{u} A}
    (d : M₀ ⟶ M₁) (e₀ : M₀ ≃ₗ[A] C) (e₁ : M₁ ≃ₗ[A] D)
    (hd : ∀ x, e₁ (d.hom x) = (p₂.toLinearMap - p₁.toLinearMap) (e₀ x)) :
    Nonempty (LinearMap.ker ((ModuleCat.extendScalars (algebraMap A A')).map d).hom ≃ₗ[A']
      lTensorEqualizer p₁ p₂ A') := by
  let E₀ := (ModuleCat.extendScalarsAlgebraMapObjEquiv (S := A') M₀).trans
    (e₀.baseChange A A' M₀ C)
  let E₁ := (ModuleCat.extendScalarsAlgebraMapObjEquiv (S := A') M₁).trans
    (e₁.baseChange A A' M₁ D)
  have hE (x : (ModuleCat.extendScalars (algebraMap A A')).obj M₀) :
      E₁ (((ModuleCat.extendScalars (algebraMap A A')).map d).hom x) =
        (p₂.toLinearMap - p₁.toLinearMap).lTensor A' (E₀ x) := by
    change e₁.baseChange A A' M₁ D (ModuleCat.extendScalarsAlgebraMapObjEquiv M₁
      ((ModuleCat.extendScalars (algebraMap A A')).map d x)) =
      (p₂.toLinearMap - p₁.toLinearMap).lTensor A'
        (e₀.baseChange A A' M₀ C (ModuleCat.extendScalarsAlgebraMapObjEquiv M₀ x))
    rw [ModuleCat.extendScalarsAlgebraMapObjEquiv_naturality]
    generalize ModuleCat.extendScalarsAlgebraMapObjEquiv M₀ x = z
    induction z using TensorProduct.inductionOn with
    | tmul a m =>
      rw [LinearMap.lTensor_tmul, LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul,
        LinearMap.lTensor_tmul, hd]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨(E₀.ofSubmodules _ (Subalgebra.toSubmodule (lTensorEqualizer p₁ p₂ A')) ?_).trans
    (Subalgebra.toSubmoduleEquiv _)⟩
  ext y
  rw [Submodule.mem_map_equiv, LinearMap.mem_ker, Subalgebra.mem_toSubmodule,
    mem_lTensorEqualizer_iff, ← E₁.map_eq_zero_iff, hE, LinearEquiv.apply_symm_apply,
    LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero, eq_comm]

end AlgHom

namespace AlgebraicGeometry.Space

attribute [local instance] CategoryTheory.Limits.hasProduct_fin_succ_of_hasBinaryProducts

section Cohomology

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
  (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- The category of sheaves of modules on the small étale site of `X` has enough injectives. -/
local instance : EnoughInjectives (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
  enoughInjectives_modules B (Spec (.of A)) hA X hX

attribute [local instance] hasSheafify_smallEtaleRingedSite_spec

/-- On the small étale site of `X`, the morphisms of presheaves of abelian groups inverted by
sheafification are the locally bijective ones. -/
local instance :
    (smallEtaleRingedSite B (Spec (.of A)) hA X hX).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstanceAs ((SmallEtale.topology B (Spec (.of A)) hA X).WEqualsLocallyBijective
    AddCommGrpCat.{u})

/-- **The cohomology of the Čech complex of the structure sheaf is `H^n(X, 𝒪_X)`**, as
`A`-modules, after the universe lift. -/
theorem nonempty_uliftHomology_cechStructureComplex_iso
    (hsep : HasAffineIntersections B (Spec (.of A)) hA X)
    (U : SmallEtale B (Spec (.of A)) hA X) (hUs : IsSurjective B (Spec (.of A)) hA U.obj.hom)
    (hUa : IsAffineChart B (Spec (.of A)) hA X U) (n : ℕ) :
    Nonempty ((ModuleCat.uliftFunctor.{u + 1} A).obj
        ((cechStructureComplex A B hA X hX U).homology n) ≅
      ((globalSectionsOverSpec A B hA X hX).rightDerived n).obj (SheafOfModules.unit _)) := by
  have := hasInjectiveResolutions_modules B (Spec (.of A)) hA X hX
  let R := InjectiveResolution.of (SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O))
  obtain ⟨T, φ, ψ, hφ, hψ⟩ := exists_quasiIso_cechComplexOverBase A B hA X hX hsep U hUs hUa
    _ (isQuasicoherentOnSite_of_isCartesianOnAffineCharts _ isCartesianOnAffineCharts_unit) R
  let K := Stacks.CechTop.cechComplexOverBase
    (show (smallEtaleRingedSite B (Spec (.of A)) hA X hX).C from U)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
    (baseRingHom A B hA X hX) (SheafOfModules.unit _)
  let F := ModuleCat.uliftFunctor.{u + 1} A
  let G := globalSectionsOverSpec A B hA X hX
  have hψn := (quasiIsoAt_iff_isIso_homologyMap ψ (n : ℤ)).1 inferInstance
  have hφn := (quasiIsoAt_iff_isIso_homologyMap φ (n : ℤ)).1 inferInstance
  exact ⟨F.mapIso (K.extendHomologyIso embeddingUpNat (j := n) rfl) ≪≫
    ((K.sc n).mapHomologyIso F).symm ≪≫
    (((F.mapHomologicalComplex _).obj K).extendHomologyIso embeddingUpNat (j := n) rfl).symm ≪≫
    @asIso _ _ _ _ (HomologicalComplex.homologyMap ψ (n : ℤ)) hψn ≪≫
    (@asIso _ _ _ _ (HomologicalComplex.homologyMap φ (n : ℤ)) hφn).symm ≪≫
    HomologicalComplex.homologyMapIso (G.mapExtendIso R.cocomplex embeddingUpNat) n ≪≫
    (((G.mapHomologicalComplex _).obj R.cocomplex).extendHomologyIso embeddingUpNat
      (j := n) rfl) ≪≫ (R.isoRightDerivedObj G n).symm⟩

/-- `Γ(X, -)` over the base followed by its right derived functors is the restriction of scalars of
the right derived functors of `Γ(X, -)`. -/
theorem nonempty_rightDerived_globalSectionsOverSpec_iso
    (M : Modules.{u, u} B (Spec (.of A)) hA X hX) (n : ℕ) :
    Nonempty (((globalSectionsOverSpec A B hA X hX).rightDerived n).obj M ≅
      (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)).obj
        (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).rightDerived n).obj M)) := by
  have : PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)) :=
    ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have : PreservesFiniteColimits (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)) :=
    ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have : (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  exact ⟨(Functor.rightDerivedCompIso (globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O))
    (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)) n).app M⟩

/-- For `X` proper over `Spec A`, the lifted cohomology of the Čech complex of the structure sheaf
is the restriction of scalars of `H^n(X, 𝒪_X)`. -/
private theorem nonempty_uliftHomology_cechStructureComplex_iso_restrictScalars
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA)))) (hprop : IsProper B (Spec (.of A)) hA f)
    (U : SmallEtale B (Spec (.of A)) hA X) (hUs : IsSurjective B (Spec (.of A)) hA U.obj.hom)
    (hUa : IsAffineChart B (Spec (.of A)) hA X U) (n : ℕ) :
    Nonempty ((ModuleCat.uliftFunctor.{u + 1} A).obj
        ((cechStructureComplex A B hA X hX U).homology n) ≅
      (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)).obj
        (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).rightDerived n).obj
            (SheafOfModules.unit _))) := by
  obtain ⟨e⟩ := nonempty_uliftHomology_cechStructureComplex_iso A B hA X hX
    (hasAffineIntersections_of_isSeparated A B hA X hX f hprop.1) U hUs hUa n
  obtain ⟨e'⟩ := nonempty_rightDerived_globalSectionsOverSpec_iso A B hA X hX
    (SheafOfModules.unit _) n
  exact ⟨e ≪≫ e'⟩

/-- The Čech complex of the structure sheaf has zero cohomology in negative degrees. -/
theorem isZero_homology_cechStructureComplex_of_neg (U : SmallEtale B (Spec (.of A)) hA X)
    (i : ℤ) (hi : i < 0) : IsZero ((cechStructureComplex A B hA X hX U).homology i) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    ((cechStructureComplex A B hA X hX U).isZero_of_isStrictlyGE 0 i hi)

/-- **The cohomology modules of the Čech complex of the structure sheaf are finite** over a
Noetherian base, for `X` proper over `Spec A` (Stacks 08AS). -/
theorem moduleFinite_homology_cechStructureComplex [IsNoetherianRing A]
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA)))) (hprop : IsProper B (Spec (.of A)) hA f)
    (U : SmallEtale B (Spec (.of A)) hA X) (hUs : IsSurjective B (Spec (.of A)) hA U.obj.hom)
    (hUa : IsAffineChart B (Spec (.of A)) hA X U) (i : ℤ) :
    Module.Finite A ((cechStructureComplex A B hA X hX U).homology i) := by
  rcases lt_or_ge i 0 with hi | hi
  · have := ModuleCat.subsingleton_of_isZero
      (isZero_homology_cechStructureComplex_of_neg A B hA X hX U i hi)
    infer_instance
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = i := ⟨i.toNat, by omega⟩
    have : Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X
        (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
      ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isProper A B hA X hX f hprop⟩
    obtain ⟨e⟩ := nonempty_uliftHomology_cechStructureComplex_iso_restrictScalars A B hA X hX f
      hprop U hUs hUa n
    have hfin := moduleFinite_cohomology_of_isProper X hX f hprop (SheafOfModules.unit _) n
    have : Module.Finite A (ULift.{u + 1} ((cechStructureComplex A B hA X hX U).homology n)) :=
      Module.Finite.equiv e.toLinearEquiv.symm
    exact Module.Finite.equiv (ULift.moduleEquiv (R := A))

/-- **The Čech complex of the structure sheaf has no cohomology in high degrees**, for `X` proper
over `Spec A`. -/
theorem exists_isZero_homology_cechStructureComplex
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA)))) (hprop : IsProper B (Spec (.of A)) hA f)
    (U : SmallEtale B (Spec (.of A)) hA X) (hUs : IsSurjective B (Spec (.of A)) hA U.obj.hom)
    (hUa : IsAffineChart B (Spec (.of A)) hA X U) :
    ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((cechStructureComplex A B hA X hX U).homology i) := by
  obtain ⟨N, hN⟩ := exists_forall_isZero_rightDerived_globalSections_of_qcqs A B hA
    B.contains_terminal X hX (isQuasiCompactSpace_of_isProper_baseObject A B hA X hX f hprop)
    (isAbsolutelyQuasiSeparated_of_isProper_baseObject A B hA X hX f hprop)
  refine ⟨N, fun i hi => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = i := ⟨i.toNat, by omega⟩
  obtain ⟨e⟩ := nonempty_uliftHomology_cechStructureComplex_iso_restrictScalars A B hA X hX f
    hprop U hUs hUa n
  have h₁ : IsZero ((ModuleCat.uliftFunctor.{u + 1} A).obj
      ((cechStructureComplex A B hA X hX U).homology n)) :=
    IsZero.of_iso ((ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)).map_isZero
      (hN _ (isQuasicoherentOnSite_of_isCartesianOnAffineCharts _ isCartesianOnAffineCharts_unit)
        n (by omega))) e
  rw [ModuleCat.isZero_iff_subsingleton] at h₁ ⊢
  exact (Equiv.ulift.{u + 1} (α := ((cechStructureComplex A B hA X hX U).homology n :
    Type u))).subsingleton_congr.1 h₁

/-- **The Čech complex of the structure sheaf of a proper flat algebraic space is K-flat.** -/
theorem kFlat_cechStructureComplex
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA)))) (hprop : IsProper B (Spec (.of A)) hA f)
    (hflat : IsFlat B (Spec (.of A)) hA f)
    (U : SmallEtale B (Spec (.of A)) hA X) (hUs : IsSurjective B (Spec (.of A)) hA U.obj.hom)
    (hUa : IsAffineChart B (Spec (.of A)) hA X U) :
    (cechStructureComplex A B hA X hX U).KFlat := by
  have hsep : HasAffineIntersections B (Spec (.of A)) hA X :=
    hasAffineIntersections_of_isSeparated A B hA X hX f hprop.1
  have := flat_cechStructureComplex_X A B hA X hX f hflat hsep U hUa
  obtain ⟨N, hN⟩ := exists_exact_rTensor_quotient_cechStructureComplex hX f hprop U hUs hUa
  exact CochainComplex.KFlat.kFlat_of_rTensor_quotient_exact _ N hN

end Cohomology

section KernelPair

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- A binary product in the small étale site of a presheaf `F` is the fibre product over `F`. -/
theorem isPullback_of_isLimit_binaryFan {V P : SmallEtale B S hS F} (π₁ π₂ : P ⟶ V)
    (hP : IsLimit (BinaryFan.mk π₁ π₂)) :
    IsPullback (yoneda.map π₁.hom.left) (yoneda.map π₂.hom.left) V.obj.hom V.obj.hom := by
  let e := hP.conePointUniqueUpToIso (SmallEtale.prodIsLimit B S hS F V V)
  have h₁ : e.hom ≫ SmallEtale.prodFst B S hS F V V = π₁ :=
    hP.conePointUniqueUpToIso_hom_comp (SmallEtale.prodIsLimit B S hS F V V) ⟨.left⟩
  have h₂ : e.hom ≫ SmallEtale.prodSnd B S hS F V V = π₂ :=
    hP.conePointUniqueUpToIso_hom_comp (SmallEtale.prodIsLimit B S hS F V V) ⟨.right⟩
  let e' : P.obj.left ≅ (SmallEtale.prodObj B S hS F V V).obj.left :=
    (SmallEtale.toOver B S hS F).mapIso e
  have k₁ : e'.inv ≫ π₁.hom.left = V.property.rep.fst' V.obj.hom :=
    (Iso.inv_comp_eq e').2 (congrArg (fun k : P ⟶ V => k.hom.left) h₁).symm
  have k₂ : e'.inv ≫ π₂.hom.left = V.property.rep.snd V.obj.hom :=
    (Iso.inv_comp_eq e').2 (congrArg (fun k : P ⟶ V => k.hom.left) h₂).symm
  refine IsPullback.of_iso (V.property.rep.isPullback' V.obj.hom) (yoneda.mapIso e').symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · exact (Category.comp_id _).trans ((congrArg yoneda.map k₁).symm.trans (yoneda.map_comp _ _))
  · exact (Category.comp_id _).trans ((congrArg yoneda.map k₂).symm.trans (yoneda.map_comp _ _))

/-- **The first term of the Čech nerve of an étale chart is the kernel pair of the chart.** -/
theorem isPullback_cechNerve_one (U : (smallEtaleRingedSite B S hS F hF).C) :
    IsPullback
      (yoneda.map ((Stacks.CechTop.cechNerve U).map (SimplexCategory.δ (1 : Fin 2)).op).hom.left)
      (yoneda.map ((Stacks.CechTop.cechNerve U).map (SimplexCategory.δ (0 : Fin 2)).op).hom.left)
      ((Stacks.CechTop.cechNerve U).obj (op ⦋0⦌)).obj.hom
      ((Stacks.CechTop.cechNerve U).obj (op ⦋0⦌)).obj.hom :=
  isPullback_of_isLimit_binaryFan B S hS F _ _ (Stacks.CechTop.cechNerveOneIsLimit U)

end KernelPair

section CoreN

open TensorProduct
open scoped ChangeOfRings

variable {A : Type u} [CommRing A] {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))}
  {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
  (U : (smallEtaleRingedSite B (Spec (.of A)) hA X hX).C)

/-- The scheme of the zeroth term `U` of the Čech nerve of a chart. -/
abbrev cechW : BigFppfOver B (Spec (.of A)) hA :=
  ((Stacks.CechTop.cechNerve U).obj (op ⦋0⦌)).obj.left

/-- The scheme of the first term `U ×_X U` of the Čech nerve of a chart. -/
abbrev cechR : BigFppfOver B (Spec (.of A)) hA :=
  ((Stacks.CechTop.cechNerve U).obj (op ⦋1⦌)).obj.left

/-- The first projection `U ×_X U ⟶ U`. -/
abbrev cechR₁ : cechR hX U ⟶ cechW hX U :=
  ((Stacks.CechTop.cechNerve U).map (SimplexCategory.δ (1 : Fin 2)).op).hom.left

/-- The second projection `U ×_X U ⟶ U`. -/
abbrev cechR₂ : cechR hX U ⟶ cechW hX U :=
  ((Stacks.CechTop.cechNerve U).map (SimplexCategory.δ (0 : Fin 2)).op).hom.left

/-- The `ℕ`-graded Čech complex of the structure sheaf. -/
abbrev cechUnitComplex : CochainComplex (ModuleCat.{u} A) ℕ :=
  Stacks.CechTop.cechComplexOverBase U
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
    (baseRingHom A B hA X hX) (SheafOfModules.unit _)

/-- **The first Čech differential is the difference of the two pullbacks.** -/
theorem cechUnitComplex_d_zero_one (c : (cechUnitComplex hX U).X 0) :
    letI := siteObjectAlgebra B A (cechW hX U)
    letI := siteObjectAlgebra B A (cechR hX U)
    ((cechUnitComplex hX U).d 0 1) c =
      ((siteObjectAlgHom B (cechR₂ hX U)).toLinearMap -
        (siteObjectAlgHom B (cechR₁ hX U)).toLinearMap) c := by
  rw [Stacks.CechTop.cechComplex_d_apply_eq_sum_moduleCat, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, one_smul,
    ← sub_eq_add_neg]
  rfl

/-- The degree-zero cohomology of a complex of modules concentrated in degrees `≥ 0` is the kernel
of its first differential. -/
noncomputable def _root_.CochainComplex.kerLinearEquivHomologyZero {R : Type u} [Ring R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.d (-1) 0 = 0) :
    LinearMap.ker (K.d 0 1).hom ≃ₗ[R] K.homology 0 :=
  (LinearEquiv.ofEq _ _ (by
      have h : (ComplexShape.up ℤ).next 0 = 1 := CochainComplex.next ℤ 0
      have hinj : Function.Injective (K.XIsoOfEq h.symm).hom.hom :=
        (K.XIsoOfEq h.symm).toLinearEquiv.injective
      change LinearMap.ker (K.d 0 1).hom = LinearMap.ker (K.d 0 ((ComplexShape.up ℤ).next 0)).hom
      rw [← K.d_comp_XIsoOfEq_hom h.symm 0, ModuleCat.hom_comp, LinearMap.ker_comp,
        LinearMap.ker_eq_bot.2 hinj, Submodule.comap_bot])).trans
    ((K.sc 0).moduleCatCyclesIso.symm ≪≫ K.isoHomologyπ (-1) 0 (by simp) hK).toLinearEquiv

/-- **Global functions are constant near a point once they are on its fibre, over a Noetherian
base.** Let `X` be a proper flat algebraic space over `Spec A`, `A` Noetherian, with a surjective
affine étale chart `U`, and `p₁ p₂ : Γ(U) ⇉ Γ(U ×_X U)` the two pullbacks. If at a prime `𝔭` the
sequence `0 → κ(𝔭) → κ(𝔭) ⊗ Γ(U) → κ(𝔭) ⊗ Γ(U ×_X U)` is exact, there is `h ∉ 𝔭` such that the
same sequence is exact over every `A`-algebra `A'` in which `h` is invertible. -/
theorem exists_away_equalizerTensorExact [IsNoetherianRing A]
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA)))) (hprop : IsProper B (Spec (.of A)) hA f)
    (hflat : IsFlat B (Spec (.of A)) hA f) (hUs : IsSurjective B (Spec (.of A)) hA U.obj.hom)
    (hUa : IsAffineChart B (Spec (.of A)) hA X U) (P : Ideal A) [P.IsPrime]
    (hP : letI := siteObjectAlgebra B A (cechW hX U)
      letI := siteObjectAlgebra B A (cechR hX U)
      AlgHom.EqualizerTensorExact (siteObjectAlgHom B (cechR₁ hX U))
        (siteObjectAlgHom B (cechR₂ hX U)) P.ResidueField) :
    ∃ h : A, h ∉ P ∧ ∀ (A' : Type u) [CommRing A'] [Algebra A A'], IsUnit (algebraMap A A' h) →
      letI := siteObjectAlgebra B A (cechW hX U)
      letI := siteObjectAlgebra B A (cechR hX U)
      AlgHom.EqualizerTensorExact (siteObjectAlgHom B (cechR₁ hX U))
        (siteObjectAlgHom B (cechR₂ hX U)) A' := by
  let := siteObjectAlgebra B A (cechW hX U)
  let := siteObjectAlgebra B A (cechR hX U)
  let p₁ := siteObjectAlgHom B (cechR₁ hX U)
  let p₂ := siteObjectAlgHom B (cechR₂ hX U)
  let K := cechUnitComplex hX U
  let C := cechStructureComplex A B hA X hX U
  have hsep : HasAffineIntersections B (Spec (.of A)) hA X :=
    hasAffineIntersections_of_isSeparated A B hA X hX f hprop.1
  have := flat_cechStructureComplex_X A B hA X hX f hflat hsep U hUa
  let ι₀ := K.extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl
  let ι₁ := K.extendXIso ComplexShape.embeddingUpNat (i := 1) (i' := 1) rfl
  let e₀ : C.X 0 ≃ₗ[A] Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (cechW hX U), ⊤) :=
    ι₀.toLinearEquiv
  let e₁ : C.X 1 ≃ₗ[A] Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (cechR hX U), ⊤) :=
    ι₁.toLinearEquiv
  have hd (x : C.X 0) : e₁ ((C.d 0 1).hom x) = (p₂.toLinearMap - p₁.toLinearMap) (e₀ x) := by
    have h := HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat
      (i := 0) (j := 1) (i' := 0) (j' := 1) rfl rfl
    change ι₁.hom.hom ((C.d 0 1).hom x) = _
    rw [h]
    change ι₁.hom.hom (ι₁.inv.hom ((K.d 0 1).hom (ι₀.hom.hom x))) = _
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.inv_hom_id, ModuleCat.hom_id,
      LinearMap.id_apply]
    exact cechUnitComplex_d_zero_one hX U _
  have hmid := (AlgHom.equalizerTensorExact_iff_bijective_algebraMap_lTensorEqualizer).1 hP
  have hinj := ((AlgHom.equalizerTensorExact_iff_tmulOne).1 hP).1
  let κ := P.ResidueField
  let x₀ : C.X 0 := e₀.symm 1
  have hx₀ : (C.d 0 1).hom x₀ = 0 := by
    apply e₁.injective
    rw [hd, map_zero, LinearEquiv.apply_symm_apply, LinearMap.sub_apply,
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, map_one, map_one, sub_self]
  have hzero : ∀ {A' : Type u} [CommRing A'] (φ : A →+* A'),
      (Stacks.AlgebraicGeometry.ProperFlatGlobalSections.extendScalarsComplex φ C).d (-1) 0 = 0 :=
    fun φ => ((ModuleCat.extendScalars.{u, u, u} φ).map_isZero
      (C.isZero_of_isStrictlyGE 0 (-1) (by omega))).eq_of_src _ _
  obtain ⟨Eκ⟩ := AlgHom.nonempty_ker_extendScalars_linearEquiv_lTensorEqualizer (A' := κ)
    (C.d 0 1) e₀ e₁ hd
  have hrank : Module.finrank κ
      ((Stacks.AlgebraicGeometry.ProperFlatGlobalSections.extendScalarsComplex
        (algebraMap A κ) C).homology 0) = 1 := by
    rw [← (CochainComplex.kerLinearEquivHomologyZero _ (hzero (algebraMap A κ))).finrank_eq]
    exact (Eκ.trans (LinearEquiv.ofBijective (Algebra.linearMap κ _) hmid).symm).finrank_eq.trans
      (Module.finrank_self κ)
  have hne : (1 : κ) ⊗ₜ[A, algebraMap A κ] x₀ ≠ 0 := by
    intro h0
    have h1 : (e₀.baseChange A κ _ _) (ModuleCat.extendScalarsAlgebraMapObjEquiv (S := κ) (C.X 0)
        ((1 : κ) ⊗ₜ[A, algebraMap A κ] x₀)) =
        (e₀.baseChange A κ _ _) (ModuleCat.extendScalarsAlgebraMapObjEquiv (S := κ) (C.X 0) 0) :=
      congrArg (fun z => (e₀.baseChange A κ _ _)
        (ModuleCat.extendScalarsAlgebraMapObjEquiv (S := κ) (C.X 0) z)) h0
    rw [LinearEquiv.map_zero, LinearEquiv.map_zero] at h1
    change (e₀.baseChange A κ _ _) ((1 : κ) ⊗ₜ[A] x₀) = 0 at h1
    rw [LinearEquiv.baseChange_tmul, LinearEquiv.apply_symm_apply] at h1
    exact one_ne_zero (hinj (h1.trans (map_zero (AlgHom.tmulOne A _ κ)).symm))
  obtain ⟨h, hh, hB⟩ := CochainComplex.exists_away_nonempty_ker_extendScalars_linearEquiv C
    (kFlat_cechStructureComplex A B hA X hX f hprop hflat U hUs hUa)
    (moduleFinite_homology_cechStructureComplex A B hA X hX f hprop U hUs hUa)
    (exists_isZero_homology_cechStructureComplex A B hA X hX f hprop U hUs hUa) x₀ hx₀ P hrank hne
  refine ⟨h, hh, fun A' _ _ hu => ?_⟩
  obtain ⟨E⟩ := hB (algebraMap A A') hu
  obtain ⟨F⟩ := AlgHom.nonempty_ker_extendScalars_linearEquiv_lTensorEqualizer (A' := A')
    (C.d 0 1) e₀ e₁ hd
  exact (AlgHom.equalizerTensorExact_iff_bijective_algebraMap_lTensorEqualizer).2
    (Subalgebra.bijective_algebraMap_of_linearEquiv _ (F.symm.trans E))

end CoreN

end AlgebraicGeometry.Space

end
