module

public import StacksFrontier.Algebra.Module.FlatComplexNakayama
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSections
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk

/-!
# Finiteness of the cohomology of a base change of a Čech complex

Let `f : X ⟶ Spec A` be separated and proper, `U` a finite affine open cover of `X` and `F` a
coherent `𝒪_X`-module. For a Noetherian `A`-algebra `S` the base change `S ⊗_A C` of the
alternating Čech complex `C` of `F` is the alternating Čech complex of the pullback of `F` to
`X ×_A S` (`Stacks.Cech.cechBaseChangeData`), so its cohomology is the cohomology of a coherent
module on a proper `S`-scheme and hence finite over `S` ([Stacks, Tag 02O5]).

This file records the two instances of that used by the Nakayama arguments of
`StacksFrontier/Algebra/Module/FlatComplexNakayama.lean`: the middle cohomology of
`S ⊗ C⁰ ⟶ S ⊗ C¹ ⟶ S ⊗ C²` (`Stacks.CechBaseChange.finite_homology_baseChange`) and the kernel
of `S ⊗ C⁰ ⟶ S ⊗ C¹` (`Stacks.CechBaseChange.finite_ker_baseChange`) are finite `S`-modules, for
every algebra structure on `S`.

## References

* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.CechBaseChange

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) {I : Type u}
  (U : I → X.Opens) (F : X.Modules)

/-- The degree-zero differential of the alternating Čech complex. -/
noncomputable abbrev d₀ := ((Stacks.Cech.alternatingCechModuleComplex f U F).d 0 1).hom

/-- The degree-one differential of the alternating Čech complex. -/
noncomputable abbrev d₁ := ((Stacks.Cech.alternatingCechModuleComplex f U F).d 1 2).hom

/-- The differential `Cᵖ ⟶ Cᵖ⁺¹` of the alternating Čech complex is
`Stacks.Cech.alternatingCechModuleDiff`. -/
theorem d_eq (p : ℕ) : (Stacks.Cech.alternatingCechModuleComplex f U F).d p (p + 1) =
    Stacks.Cech.alternatingCechModuleDiff f U F p := by
  simp only [Stacks.Cech.alternatingCechModuleComplex, CochainComplex.of_d]

/-- The composite `d₁ ∘ d₀` of the first two Čech differentials vanishes. -/
theorem d₁_comp_d₀ : d₁ f U F ∘ₗ d₀ f U F = 0 := by
  rw [← ModuleCat.hom_comp, HomologicalComplex.d_comp_d, ModuleCat.hom_zero]

/-- The base change of a proper separated morphism with a finite affine cover and a coherent
module along `Spec S ⟶ Spec A` again has these properties. -/
private theorem pullback_cover_data [IsProper f] [F.IsCoherent] (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (hUaff : ∀ i, IsAffineOpen (U i)) {S : Type u} [CommRing S] [IsNoetherianRing S] (φ : A →+* S) :
    IsSeparated (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) ∧
    IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) ∧
    ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).obj F).IsCoherent ∧
    (⊤ : (pullback f (Spec.map (CommRingCat.ofHom φ))).Opens) =
      ⨆ i, pullback.fst f (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ U i ∧
    ∀ i, IsAffineOpen (pullback.fst f (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ U i) := by
  have hsq := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom φ))
  refine ⟨MorphismProperty.of_isPullback hsq inferInstance,
    MorphismProperty.of_isPullback hsq inferInstance, isCoherent_pullback _ F, ?_, fun i => ?_⟩
  · rw [← Scheme.Hom.preimage_iSup, ← hU, Scheme.Hom.preimage_top]
  · exact Stacks.Cech.isAffineOpen_preimage_of_isPullback φ f _ _ hsq (hUaff i)

section Core

variable [Finite I] [IsSeparated f] [F.IsQuasicoherent] (hUaff : ∀ i, IsAffineOpen (U i))
  {S : Type u} [CommRing S] (φ : A →+* S)

/-- The base change of `X` along `Spec S ⟶ Spec A`. -/
noncomputable abbrev X' : Scheme.{u} := pullback f (Spec.map (CommRingCat.ofHom φ))

/-- The degreewise base-change isomorphism `S ⊗_A Cᵖ ≃ C'ᵖ`. -/
noncomputable def bcEquiv (p : ℕ) :
    letI : Algebra A S := φ.toAlgebra
    S ⊗[A] (Stacks.Cech.alternatingCechModuleComplex f U F).X p ≃ₗ[S]
      (Stacks.Cech.alternatingCechModuleComplex (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))
        (fun i => pullback.fst f (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ U i)
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).obj F)).X
          p :=
  letI : Algebra A S := φ.toAlgebra
  (Stacks.Cech.alternatingCechModuleObjBaseChangeIso (pullback.fst f _) U
    (fun i => pullback.fst f (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ U i) (Equiv.refl _)
    F (fun _ => rfl) φ f (pullback.snd f _)
    (Stacks.Cech.baseRingHom_comp_app φ f _ _ (IsPullback.of_hasPullback _ _))
    (IsPullback.of_hasPullback _ _) hUaff p).toLinearEquiv

/-- The base-change isomorphisms `bcEquiv` commute with the differentials: they form an
isomorphism from `S ⊗_A C` to the alternating Čech complex of the pullback of `F` to
`X ×_A S`. -/
theorem bcEquiv_comm (p : ℕ) :
    letI : Algebra A S := φ.toAlgebra
    (bcEquiv f U F hUaff φ (p + 1)).toLinearMap ∘ₗ
        (((Stacks.Cech.alternatingCechModuleComplex f U F).d p (p + 1)).hom).baseChange S =
      ((Stacks.Cech.alternatingCechModuleComplex (pullback.snd f _)
        (fun i => pullback.fst f (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ U i)
        ((Scheme.Modules.pullback (pullback.fst f _)).obj F)).d p (p + 1)).hom ∘ₗ
        (bcEquiv f U F hUaff φ p).toLinearMap := by
  let : Algebra A S := φ.toAlgebra
  have h' := congrArg ModuleCat.Hom.hom
    (Stacks.Cech.alternatingCechModuleObjBaseChangeIso_comm (pullback.fst f _) U
      (fun i => pullback.fst f (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ U i)
      (Equiv.refl _) F (fun _ => rfl) φ f (pullback.snd f _)
      (Stacks.Cech.baseRingHom_comp_app φ f _ _ (IsPullback.of_hasPullback _ _))
      (IsPullback.of_hasPullback _ _) hUaff p)
  simp only [ModuleCat.hom_comp] at h'
  refine LinearMap.ext fun x => ?_
  rw [d_eq, d_eq]
  exact (LinearMap.congr_fun h' x).symm

end Core

section Finite

variable [Finite I] [LinearOrder I] [IsSeparated f] [IsProper f] [F.IsCoherent]
  (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))

omit [Finite I] in
include hU hUaff in
/-- The homology of the alternating Čech complex of a coherent module on a proper scheme over a
Noetherian ring is finite in every degree. -/
theorem finite_homology_cech [IsNoetherianRing A] (m : ℕ) :
    Module.Finite A ((Stacks.Cech.alternatingCechModuleComplex f U F).homology m) := by
  have :=
    AlgebraicGeometry.ProperFlatGlobalSections.moduleFinite_homology_baseAlternatingCechComplex
      f U hU F (fun _ s => Stacks.Cech.inter_isAffineOpen f U hUaff s)
      AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase m
  have e := ((Stacks.Cech.alternatingCechModuleComplex f U F).extendHomologyIso
      ComplexShape.embeddingUpNat (j := m) (j' := (m : ℤ)) rfl).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ (m : ℤ)).mapIso
      (Stacks.AlgebraicGeometry.ProperFlatGlobalSections.baseAlternatingCechComplexIsoExtend
        f U hU F).symm
  have : Module.Finite A ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A)
      (ComplexShape.up ℤ) (m : ℤ)).obj
      (Stacks.AlgebraicGeometry.ProperFlatGlobalSections.baseAlternatingCechComplex f U hU F)) :=
    this
  exact Module.Finite.equiv e.toLinearEquiv.symm

end Finite

/-! ### Linear algebra: transport of middle cohomology along isomorphisms -/

section Transport

variable {R : Type u} [CommRing R] {M₀ M₁ M₂ N₀ N₁ N₂ : Type u} [AddCommGroup M₀]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N₀] [AddCommGroup N₁] [AddCommGroup N₂]
  [Module R M₀] [Module R M₁] [Module R M₂] [Module R N₀] [Module R N₁] [Module R N₂]

/-- The middle cohomology of `M₀ ⟶ M₁ ⟶ M₂`, as cycles modulo boundaries. -/
abbrev midHomology (d₀ : M₀ →ₗ[R] M₁) (d₁ : M₁ →ₗ[R] M₂) : Type u :=
  LinearMap.ker d₁ ⧸ (LinearMap.range d₀).comap (LinearMap.ker d₁).subtype

/-- Equivalences intertwining two linear maps carry the kernel of one onto the kernel of the
other. -/
private theorem map_ker_eq_ker_of_linearEquiv_comp_eq (d₁ : M₁ →ₗ[R] M₂) (d₁' : N₁ →ₗ[R] N₂)
    (e₁ : M₁ ≃ₗ[R] N₁) (e₂ : M₂ ≃ₗ[R] N₂) (h₁ : e₂.toLinearMap ∘ₗ d₁ = d₁' ∘ₗ e₁.toLinearMap) :
    (LinearMap.ker d₁).map e₁.toLinearMap = LinearMap.ker d₁' := by
  ext y
  rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker,
    ← LinearEquiv.map_eq_zero_iff e₂]
  change (e₂.toLinearMap ∘ₗ d₁) (e₁.symm y) = 0 ↔ _
  rw [h₁, LinearMap.comp_apply]
  simp

/-- Conjugate complexes have isomorphic middle cohomology. -/
noncomputable def midHomologyEquiv (d₀ : M₀ →ₗ[R] M₁) (d₁ : M₁ →ₗ[R] M₂) (d₀' : N₀ →ₗ[R] N₁)
    (d₁' : N₁ →ₗ[R] N₂) (e₀ : M₀ ≃ₗ[R] N₀) (e₁ : M₁ ≃ₗ[R] N₁) (e₂ : M₂ ≃ₗ[R] N₂)
    (h₀ : e₁.toLinearMap ∘ₗ d₀ = d₀' ∘ₗ e₀.toLinearMap)
    (h₁ : e₂.toLinearMap ∘ₗ d₁ = d₁' ∘ₗ e₁.toLinearMap) :
    midHomology d₀ d₁ ≃ₗ[R] midHomology d₀' d₁' := by
  have hker : (LinearMap.ker d₁).map e₁.toLinearMap = LinearMap.ker d₁' := by
    ext y
    rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker,
      ← LinearEquiv.map_eq_zero_iff e₂]
    change (e₂.toLinearMap ∘ₗ d₁) (e₁.symm y) = 0 ↔ _
    rw [h₁, LinearMap.comp_apply]
    simp
  let eK : LinearMap.ker d₁ ≃ₗ[R] LinearMap.ker d₁' := e₁.ofSubmodules _ _ hker
  refine Submodule.Quotient.equiv _ _ eK ?_
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.subtype_apply,
    LinearMap.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨e₀ x, ?_⟩
    have := congrArg e₁ hx
    change (e₁.toLinearMap ∘ₗ d₀) x = _ at this
    rw [h₀, LinearMap.comp_apply, LinearEquiv.coe_coe] at this
    rw [this]
    simp [eK]
  · rintro ⟨x, hx⟩
    refine ⟨e₀.symm x, e₁.injective ?_⟩
    change (e₁.toLinearMap ∘ₗ d₀) (e₀.symm x) = e₁ (eK.symm ⟨y, hy⟩).1
    rw [h₀, LinearMap.comp_apply]
    simp [eK, hx, LinearEquiv.ofSubmodules_symm_apply]

end Transport

section Finiteness

variable [Finite I] [LinearOrder I] [IsSeparated f] [IsProper f] [F.IsCoherent]
  [F.IsQuasicoherent]
  (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))

omit [Finite I] [F.IsQuasicoherent] in
include hU hUaff in
/-- The middle cohomology of `C⁰ ⟶ C¹ ⟶ C²` is a finite `A`-module. -/
theorem finite_midHomology [IsNoetherianRing A] :
    Module.Finite A (midHomology (d₀ f U F) (d₁ f U F)) := by
  have h := finite_homology_cech f U F hU hUaff 1
  let C := Stacks.Cech.alternatingCechModuleComplex f U F
  have e := C.homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    (C.sc' 0 1 2).moduleCatHomologyIso
  have h2 : Module.Finite A (LinearMap.ker (d₁ f U F) ⧸
      (LinearMap.range (C.sc' 0 1 2).moduleCatToCycles :
        Submodule A (LinearMap.ker (d₁ f U F)))) :=
    Module.Finite.equiv e.toLinearEquiv
  have hrange : (LinearMap.range (C.sc' 0 1 2).moduleCatToCycles :
      Submodule A (LinearMap.ker (d₁ f U F))) =
      (LinearMap.range (d₀ f U F)).comap (LinearMap.ker (d₁ f U F)).subtype := by
    ext ⟨y, hy⟩
    simp only [LinearMap.mem_range, Submodule.mem_comap, Submodule.subtype_apply]
    exact ⟨fun ⟨x, hx⟩ => ⟨x, congrArg Subtype.val hx⟩, fun ⟨x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩
  exact Module.Finite.equiv (Submodule.quotEquivOfEq _ _ hrange)

omit [Finite I] [F.IsQuasicoherent] in
include hU hUaff in
/-- The kernel of the first Čech differential `d₀ : C⁰ ⟶ C¹` is a finite `A`-module. -/
theorem finite_ker_d₀ [IsNoetherianRing A] :
    Module.Finite A (LinearMap.ker (d₀ f U F)) := by
  have h := finite_homology_cech f U F hU hUaff 0
  let C := Stacks.Cech.alternatingCechModuleComplex f U F
  have e : C.homology 0 ≅ ModuleCat.of A (LinearMap.ker (d₀ f U F)) :=
    C.isoHomologyπ₀.symm ≪≫
      IsLimit.conePointUniqueUpToIso (C.cyclesIsKernel 0 1 (by simp)) (kernelIsKernel _) ≪≫
      ModuleCat.kernelIsoKer _
  exact Module.Finite.equiv e.toLinearEquiv

end Finiteness

section BaseChangeFinite

variable [Finite I] [LinearOrder I] [IsSeparated f] [IsProper f] [F.IsCoherent]
  [F.IsQuasicoherent]
  (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))

include hU hUaff in
/-- For a ring map `φ : A →+* S` with `S` Noetherian, the middle cohomology of
`S ⊗_A C⁰ ⟶ S ⊗_A C¹ ⟶ S ⊗_A C²` is a finite `S`-module, for the algebra structure given by
`φ`. -/
theorem finite_homology_baseChange_core {S : Type u} [CommRing S] [IsNoetherianRing S]
    (φ : A →+* S) :
    letI : Algebra A S := φ.toAlgebra
    Module.Finite S (Stacks.FlatComplexNakayama.homology (d₀ f U F) (d₁ f U F) S) := by
  let : Algebra A S := φ.toAlgebra
  set g := pullback.fst f (Spec.map (CommRingCat.ofHom φ))
  set f' := pullback.snd f (Spec.map (CommRingCat.ofHom φ))
  obtain ⟨_, _, _, hU', hUaff'⟩ := pullback_cover_data f U F hU hUaff φ
  have hfin := finite_midHomology f' (fun i => g ⁻¹ᵁ U i) ((Scheme.Modules.pullback g).obj F)
    hU' hUaff'
  exact Module.Finite.equiv (midHomologyEquiv _ _ _ _ (bcEquiv f U F hUaff φ 0)
    (bcEquiv f U F hUaff φ 1) (bcEquiv f U F hUaff φ 2) (bcEquiv_comm f U F hUaff φ 0)
    (bcEquiv_comm f U F hUaff φ 1)).symm

include hU hUaff in
/-- For a ring map `φ : A →+* S` with `S` Noetherian, the kernel of `S ⊗_A C⁰ ⟶ S ⊗_A C¹` is a
finite `S`-module, for the algebra structure given by `φ`. -/
theorem finite_ker_baseChange_core {S : Type u} [CommRing S] [IsNoetherianRing S]
    (φ : A →+* S) :
    letI : Algebra A S := φ.toAlgebra
    Module.Finite S (LinearMap.ker ((d₀ f U F).baseChange S)) := by
  let : Algebra A S := φ.toAlgebra
  set g := pullback.fst f (Spec.map (CommRingCat.ofHom φ))
  set f' := pullback.snd f (Spec.map (CommRingCat.ofHom φ))
  obtain ⟨_, _, _, hU', hUaff'⟩ := pullback_cover_data f U F hU hUaff φ
  have hfin := finite_ker_d₀ f' (fun i => g ⁻¹ᵁ U i) ((Scheme.Modules.pullback g).obj F)
    hU' hUaff'
  have hker : (LinearMap.ker ((d₀ f U F).baseChange S)).map
      (bcEquiv f U F hUaff φ 0).toLinearMap = LinearMap.ker (d₀ f' _ _) :=
    map_ker_eq_ker_of_linearEquiv_comp_eq _ _ _ _ (bcEquiv_comm f U F hUaff φ 0)
  exact Module.Finite.equiv ((bcEquiv f U F hUaff φ 0).ofSubmodules _ _ hker).symm

include hU hUaff in
/-- **The middle cohomology of the base change of the Čech complex is finite**, over any
Noetherian algebra. -/
theorem finite_homology_baseChange (S : Type u) [CommRing S] [Algebra A S] [IsNoetherianRing S] :
    Module.Finite S (Stacks.FlatComplexNakayama.homology (d₀ f U F) (d₁ f U F) S) := by
  have h := finite_homology_baseChange_core f U F hU hUaff (algebraMap A S)
  have e : (algebraMap A S).toAlgebra = ‹Algebra A S› := Algebra.algebra_ext _ _ fun _ => rfl
  exact e ▸ h

include hU hUaff in
/-- **The kernel of the base change of the first Čech differential is finite**, over any
Noetherian algebra. -/
theorem finite_ker_baseChange (S : Type u) [CommRing S] [Algebra A S] [IsNoetherianRing S] :
    Module.Finite S (LinearMap.ker ((d₀ f U F).baseChange S)) := by
  have h := finite_ker_baseChange_core f U F hU hUaff (algebraMap A S)
  have e : (algebraMap A S).toAlgebra = ‹Algebra A S› := Algebra.algebra_ext _ _ fun _ => rfl
  exact e ▸ h

end BaseChangeFinite

end Stacks.CechBaseChange

end
