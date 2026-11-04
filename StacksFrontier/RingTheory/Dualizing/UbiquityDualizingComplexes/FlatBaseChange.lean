module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Jacobson.Radical
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.InjectiveDimension.Noetherian
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.Homology.Perfect.Duality
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.Normalized
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldShift
public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.SingleComplexHomology

import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.FaithfullyFlatDescent

/-!
# Flat base change of a dualizing complex

A dualizing complex remains dualizing after a flat base change which is an isomorphism modulo
an ideal whose extension lies in the Jacobson radical. For a flat local homomorphism of
Noetherian local rings whose source maximal ideal generates the target maximal ideal, the base
change of a *normalized* dualizing complex is again normalized.

## Main results

* `Dualizing.isDualizingComplex_extendScalars_of_flat` states that flat extension of scalars
  preserves a dualizing complex under the stated quotient and Jacobson-radical hypotheses.
* `Dualizing.isNormalizedDualizingComplex_extendScalars_of_flat` states that a flat local
  homomorphism of Noetherian local rings with `m_A · B = m_B` carries a normalized dualizing
  complex over `A` to a normalized dualizing complex over `B`.

## Implementation notes

The equality `A/I = B/IB` in the source is expressed by bijectivity of the canonical map
`A ⧸ I → B ⧸ I.map (algebraMap A B)`. Since the ring map is flat, ordinary extension of
scalars is exact, so its functor on derived categories represents the source's tensor product
with `B`.

The ring and input-module universes are independent. Mathlib's tensor product places the
resulting `B`-modules in the maximum of the universes of `B` and the input modules, so the
three parts of the conclusion — finiteness of cohomology, finiteness of injective dimension,
and the homothety quasi-isomorphism — are each established after lifting into a common
universe and then descended again.

The normalized statement replaces the quotient hypothesis of the general flat base change by
`m_A · B = m_B`, which no longer forces the residue fields to agree. Accordingly its finite
injective dimension is obtained from the residue-field criterion of [Stacks, Tag 0AVJ]
rather than from the quotient criterion: the normalization of `K` makes `RHom_A(κ_A, K)`
concentrated in degree zero, and both the vanishing and the nonvanishing of
`Hom(κ[0], -)` transfer across the base change because the extension is faithfully flat.

## References

* [Stacks Project, Tag 0AWD](https://stacks.math.columbia.edu/tag/0AWD)
* [Stacks Project, Tag 0DWC](https://stacks.math.columbia.edu/tag/0DWC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Dualizing

noncomputable section

/-- Extension of scalars along a ring homomorphism is an additive functor. -/
local instance extendScalars_additive {A : Type u} {B : Type w}
    [CommRing A] [CommRing B] (f : A →+* B) :
    (ModuleCat.extendScalars.{u, w, v} f).Additive where
  map_add := by
    intro X Y g h
    let _ := f.toAlgebra
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change (LinearMap.baseChange B (g.hom + h.hom)) (1 ⊗ₜ[A] x) =
      (LinearMap.baseChange B g.hom + LinearMap.baseChange B h.hom) (1 ⊗ₜ[A] x)
    rw [LinearMap.baseChange_add]

private theorem extendScalars_exact_of_flat
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] :
    Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, w, v} (algebraMap A B)) ∧
    Limits.PreservesFiniteColimits
      (ModuleCat.extendScalars.{u, w, v} (algebraMap A B)) := by
  let f := algebraMap A B
  have hf : f.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  let := f.toAlgebra
  have : Module.Flat A B := hf
  let F := ModuleCat.extendScalars.{u, w, v} f
  let : F.Additive := extendScalars_additive _
  have h : ∀ S : ShortComplex (ModuleCat.{v} A), S.Exact → (S.map F).Exact := by
    intro S hS
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    exact Module.Flat.lTensor_exact (R := A) (M := B) (f := S.f.hom) (g := S.g.hom) hS
  exact ((Functor.exact_tfae F).out 2 4).mp h

/-- Extension of scalars along a flat algebra preserves finite limits. -/
local instance extendScalars_preservesFiniteLimits_of_flat
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] :
    Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, w, v} (algebraMap A B)) :=
  extendScalars_exact_of_flat.1

/-- Extension of scalars along a flat algebra preserves finite colimits. -/
local instance extendScalars_preservesFiniteColimits_of_flat
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] :
    Limits.PreservesFiniteColimits
      (ModuleCat.extendScalars.{u, w, v} (algebraMap A B)) :=
  extendScalars_exact_of_flat.2

private theorem finite_extendScalars
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (M : ModuleCat.{v} A) (hM : Module.Finite A M) :
    Module.Finite B ((ModuleCat.extendScalars.{u, w, v} f).obj M) := by
  let : Module.Finite A M := hM
  let : Algebra A B := f.toAlgebra
  have heq : (inferInstance : Module A B) = Module.compHom B f :=
    Module.ext' _ _ (by intro a b; rfl)
  cases heq
  exact Module.Finite.base_change A B M

private theorem finiteCohomology_extendScalars
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B]
    (K : DerivedCategory (ModuleCat.{v} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K)) :
    ∀ i : ℤ, Module.Finite B
      ((DerivedCategory.homologyFunctor (ModuleCat.{max w v} B) i).obj
        ((ModuleCat.extendScalars.{u, w, v} (algebraMap A B)).mapDerivedCategory.obj K)) := by
  let F := ModuleCat.extendScalars.{u, w, v} (algebraMap A B)
  let : F.Additive := extendScalars_additive _
  let : Limits.PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat
  let : Limits.PreservesFiniteColimits F := extendScalars_preservesFiniteColimits_of_flat
  intro i
  let e := (StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso F i).app K
  have hF : Module.Finite B (F.obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K)) :=
    finite_extendScalars (algebraMap A B) _ (hK i)
  have : Module.Finite B (F.obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K)) := hF
  exact @Module.Finite.equiv B _ _ inferInstance inferInstance inferInstance
    inferInstance inferInstance hF e.symm.toLinearEquiv

/-- An exact functor between module categories preserves the lower bound on cohomology. -/
private theorem isGE_mapDerivedCategory_obj {R : Type u} {S : Type*} [CommRing R] [CommRing S]
    (F : ModuleCat.{v} R ⥤ ModuleCat.{w} S) [F.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    (K : DerivedCategory (ModuleCat.{v} R)) (a : ℤ) (h : K.IsGE a) :
    (F.mapDerivedCategory.obj K).IsGE a := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact (F.map_isZero (DerivedCategory.isZero_of_isGE K a i hi)).of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso F i).app K)

/-- Lifting along `uliftFunctor` preserves finiteness of cohomology. -/
private theorem finiteCohomology_ulift {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{v} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K)) :
    ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max (max u v) w} A) i).obj
        ((ModuleCat.uliftFunctor.{max u w, v} A).mapDerivedCategory.obj K)) := by
  intro i
  let U := ModuleCat.uliftFunctor.{max u w, v} A
  let e := (StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso U i).app K
  have := hK i
  have hU : Module.Finite A (U.obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K)) :=
    Module.Finite.equiv (ULift.moduleEquiv (R := A)).symm
  exact @Module.Finite.equiv A _ _ _ _ _ _ _ hU e.symm.toLinearEquiv

private theorem exists_tStructure_bounds_of_finiteInjectiveDimension
    {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{v} R))
    (hK : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K) :
    ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b := by
  obtain ⟨a, b, ⟨J, hJGE, hJLE, _, ⟨e⟩⟩⟩ := hK
  exact ⟨a, b,
    DerivedCategory.TStructure.t.isGE_of_iso e.symm a,
    DerivedCategory.TStructure.t.isLE_of_iso e.symm b⟩

private theorem finiteInjectiveDimension_ulift
    {R : Type u} [CommRing R] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R))
    (hK : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K) :
    StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension
      (((ModuleCat.uliftFunctor.{max u w, v} R).mapDerivedCategory).obj K) := by
  let U := ModuleCat.uliftFunctor.{max u w, v} R
  let : U.PreservesInjectiveObjects := inferInstance
  obtain ⟨a, b, ⟨J, hJGE, hJLE, hJinj, ⟨e⟩⟩⟩ := hK
  refine ⟨a, b, ⟨(U.mapHomologicalComplex (ComplexShape.up ℤ)).obj J,
    ?_, ?_, ?_, ?_⟩⟩
  · exact (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff
      (K := J) U a).2 hJGE
  · exact (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff
      (K := J) U b).2 hJLE
  · intro i
    exact U.injective_obj_of_injective (hJinj i)
  · exact ⟨U.mapDerivedCategory.mapIso e ≪≫ U.mapDerivedCategoryFactors.app J⟩

private theorem pseudoCoherent_ulift_of_dualizing
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{v} A))
    (hK : IsDualizingComplex K) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      (((ModuleCat.uliftFunctor.{max u w, v} A).mapDerivedCategory).obj K) := by
  let U := ModuleCat.uliftFunctor.{max u w, v} A
  let : Limits.PreservesFiniteLimits U := inferInstance
  let : Limits.PreservesFiniteColimits U := inferInstance
  let F := U.mapDerivedCategory
  let : F.Additive := inferInstance
  obtain ⟨_, b, _, hLE⟩ :=
    exists_tStructure_bounds_of_finiteInjectiveDimension K hK.finiteInjectiveDimension
  have hLE' : F.obj K |>.IsLE b := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    let e := (StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso U i).app K
    have hz := U.map_isZero ((DerivedCategory.isLE_iff K b).mp hLE i hi)
    exact hz.of_iso e
  have hfinite := finiteCohomology_ulift.{u, v, w} K hK.finiteCohomology
  let : Small.{max (max u v) w} A := inferInstance
  exact (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      (F.obj K) 0 (ULift.{max (max u v) w} A)).2.1.mpr
    ⟨⟨b, fun i hi => DerivedCategory.isZero_of_isLE (F.obj K) b i hi⟩, hfinite⟩

private theorem derivedHomBaseChange_isIso_of_flat_pseudoCoherent
    {A : Type u} {B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B]
    (X M : DerivedCategory (ModuleCat.{max u v w} A))
    (hX : StacksDraft.PseudoCoherence.IsPseudoCoherent X)
    (hM : ∃ b : ℤ, M.IsGE b) :
    let E := ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)
    let F := E.mapDerivedCategory
    let α := E.mapDerivedCategoryFactors.hom
    let W := HomologicalComplex.quasiIso (ModuleCat.{max u v w} A) (ComplexShape.up ℤ)
    letI : F.IsLeftDerivedFunctor α W :=
      Functor.isLeftDerivedFunctor_of_inverts W F E.mapDerivedCategoryFactors
    IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, w, max u v w} (algebraMap A
      B) F α X M) := by
  let E := ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)
  let F := E.mapDerivedCategory
  let α := E.mapDerivedCategoryFactors.hom
  let W := HomologicalComplex.quasiIso (ModuleCat.{max u v w} A) (ComplexShape.up ℤ)
  let : F.IsLeftDerivedFunctor α W :=
    Functor.isLeftDerivedFunctor_of_inverts W F E.mapDerivedCategoryFactors
  apply Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange.{u, w, max u v w}
  exact Or.inr (Or.inr (Or.inl ⟨
    RingHom.flat_algebraMap_iff.mpr inferInstance, hX, hM⟩))
/-- After a flat base change, morphisms between a pseudo-coherent object and a bounded below one
form a trivial group exactly when the base change of the zeroth `RHom` homology vanishes. -/
private theorem subsingleton_mapDerivedHom_iff_isZero_extendScalars
    {A : Type u} {B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B]
    (X M : DerivedCategory (ModuleCat.{max u v w} A))
    (hX : StacksDraft.PseudoCoherence.IsPseudoCoherent X)
    (hM : ∃ b : ℤ, M.IsGE b) :
    Subsingleton
      ((ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)).mapDerivedCategory.obj X ⟶
        (ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)).mapDerivedCategory.obj M) ↔
    IsZero ((ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} A) 0).obj
        ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, max u v w} A).obj
          (Opposite.op X, M)))) := by
  let E := ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)
  let F := E.mapDerivedCategory
  let α := E.mapDerivedCategoryFactors.hom
  let W := HomologicalComplex.quasiIso (ModuleCat.{max u v w} A) (ComplexShape.up ℤ)
  let : E.Additive := extendScalars_additive _
  let : F.Additive := inferInstance
  let : Limits.PreservesFiniteLimits E := extendScalars_preservesFiniteLimits_of_flat
  let : Limits.PreservesFiniteColimits E := extendScalars_preservesFiniteColimits_of_flat
  let : F.IsLeftDerivedFunctor α W :=
    Functor.isLeftDerivedFunctor_of_inverts W F E.mapDerivedCategoryFactors
  let HA := (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, max u v w} A).obj
    (Opposite.op X, M)
  let φ := Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, w, max u v w}
    (algebraMap A B) F α X M
  have : IsIso φ := derivedHomBaseChange_isIso_of_flat_pseudoCoherent.{u, v, w} X M hX hM
  let e := (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) 0).map φ)).symm ≪≫
    (StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso E 0).app HA
  rw [hom_subsingleton_iff_derivedInternalHom_homology_isZero.{w, max u v w} (F.obj X) (F.obj M)]
  exact ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩

private theorem subsingleton_mapDerivedHom_of_flat_pseudoCoherent
    {A : Type u} {B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B]
    (X M : DerivedCategory (ModuleCat.{max u v w} A))
    (hX : StacksDraft.PseudoCoherence.IsPseudoCoherent X)
    (hM : ∃ b : ℤ, M.IsGE b)
    (hXM : Subsingleton (X ⟶ M)) :
    Subsingleton
      ((ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)).mapDerivedCategory.obj X ⟶
        (ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)).mapDerivedCategory.obj M) := by
  exact (subsingleton_mapDerivedHom_iff_isZero_extendScalars.{u, v, w} X M hX hM).2
    (Functor.map_isZero _
      ((hom_subsingleton_iff_derivedInternalHom_homology_isZero.{u, max u v w} X M).mp hXM))

/-- Base change along a flat map preserves the vanishing of `Hom(X, K⟦i⟧)` for `X` pseudo-coherent
and `K` bounded below, up to an isomorphism of the base changed source. -/
private theorem subsingleton_hom_shift_of_flat_pseudoCoherent
    {A : Type u} {B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B]
    (X K : DerivedCategory (ModuleCat.{max u v w} A)) (a i : ℤ) (hK : K.IsGE a)
    (hX : StacksDraft.PseudoCoherence.IsPseudoCoherent X)
    {Y : DerivedCategory (ModuleCat.{max u v w} B)}
    (eX : (ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)).mapDerivedCategory.obj X
      ≅ Y)
    (h : Subsingleton (X ⟶ K⟦i⟧)) :
    Subsingleton (Y ⟶ ((ModuleCat.extendScalars.{u, w, max u v w}
      (algebraMap A B)).mapDerivedCategory.obj K)⟦i⟧) := by
  let F := (ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)).mapDerivedCategory
  have hMi : (K⟦i⟧).IsGE (a - i) :=
    DerivedCategory.TStructure.t.isGE_shift K a i (a - i) (by omega)
  have h0 : Subsingleton (F.obj X ⟶ F.obj (K⟦i⟧)) :=
    subsingleton_mapDerivedHom_of_flat_pseudoCoherent.{u, v, w} X (K⟦i⟧) hX ⟨a - i, hMi⟩ h
  have : Subsingleton (F.obj X ⟶ (shiftFunctor _ i ⋙ F).obj K) := h0
  exact Equiv.subsingleton (Linear.homCongr B eX ((F.commShiftIso i).app K)).symm.toEquiv

private theorem ideal_map_comap_eq_of_quotient_bijective
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A)
    (hquotient : Function.Bijective
      (Ideal.quotientMap (I.map f) f Ideal.le_comap_map))
    (J : Ideal B) (hIJ : I.map f ≤ J) : (J.comap f).map f = J := by
  apply le_antisymm
  · exact Ideal.map_comap_le
  · intro b hb
    obtain ⟨y, hy⟩ := hquotient.2 (Ideal.Quotient.mk (I.map f) b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hrepresent : Ideal.Quotient.mk (I.map f) (f a) =
        Ideal.Quotient.mk (I.map f) b := by
      simpa only [Ideal.quotientMap_mk] using hy
    have hdiff : f a - b ∈ I.map f :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 hrepresent
    have hI' : I ≤ J.comap f := Ideal.map_le_iff_le_comap.mp hIJ
    have hdiff' : f a - b ∈ (J.comap f).map f := Ideal.map_mono hI' hdiff
    have hfa : f a ∈ J := by
      have h := J.add_mem hb (hIJ hdiff)
      simpa [add_comm] using h
    have hfa' : f a ∈ (J.comap f).map f :=
      Ideal.mem_map_of_mem f (Ideal.mem_comap.mpr hfa)
    have hb' : f a - (f a - b) ∈ (J.comap f).map f :=
      ((J.comap f).map f).sub_mem hfa' hdiff'
    simpa using hb'

private noncomputable def quotient_module_iso_extendScalars
    {A : Type u} {B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (J : Ideal B) (hEq : I.map (algebraMap A B) = J) :
    (ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)).obj
      (ModuleCat.of A (Shrink.{max u v w} (A ⧸ I))) ≅
        ModuleCat.of B (Shrink.{max u v w} (B ⧸ J)) := by
  let B_A := (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)
  letI : IsScalarTower A B B_A :=
    IsScalarTower.of_algebraMap_smul (by intro r x; rfl)
  let eB : B_A ≃ₗ[B] B := {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := by intro a x; rfl }
  apply LinearEquiv.toModuleIso
  change TensorProduct A B_A (Shrink.{max u v w} (A ⧸ I)) ≃ₗ[B] Shrink.{max u v w} (B ⧸ J)
  exact ((TensorProduct.AlgebraTensorModule.congr eB
      (Shrink.linearEquiv.{max u v w, u, u} A (A ⧸ I))).trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm.toLinearEquiv).trans
      ((Ideal.quotientEquivAlgOfEq B hEq).toLinearEquiv.trans
        (Shrink.linearEquiv.{max u v w, w, w} B (B ⧸ J)).symm)

private theorem finiteInjectiveDimension_extendScalars_common
    {A : Type u} {B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [IsNoetherianRing A] [IsNoetherianRing B]
    (I : Ideal A)
    (hquotient : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
        Ideal.le_comap_map))
    (hjacobson : I.map (algebraMap A B) ≤ Ring.jacobson B)
    (K : DerivedCategory (ModuleCat.{max u v w} A))
    (hfid : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K)
    (hfinite : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} A) i).obj K)) :
    StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension
      ((ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)).mapDerivedCategory.obj K) := by
  let F := ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)
  have hsmallA : Small.{max u v w} A := inferInstance
  have hsmallB : Small.{max u v w} B := inferInstance
  obtain ⟨a, b, hAmp⟩ := hfid
  have hAmpKeep := hAmp
  obtain ⟨J₀, hJGE, hJLE, hJinj, ⟨eJ⟩⟩ := hAmpKeep
  have hGE : K.IsGE a :=
    DerivedCategory.TStructure.t.isGE_of_iso eJ.symm a
  have hGE' := isGE_mapDerivedCategory_obj F K a hGE
  have hfinite' : ∀ i : ℤ, Module.Finite B
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).obj
        (F.mapDerivedCategory.obj K)) := finiteCohomology_extendScalars K hfinite
  let Kplus : DerivedCategory.Plus (ModuleCat.{max u v w} B) :=
    ⟨F.mapDerivedCategory.obj K, ⟨a, hGE'⟩⟩
  have hfinitePlus : ∀ i : ℤ, Module.Finite B
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).obj
        (DerivedCategory.Plus.ι.obj Kplus)) := by
    simpa [Kplus] using hfinite'
  have hIBjac : I.map (algebraMap A B) ≤ Ideal.jacobson (⊥ : Ideal B) := by
    rw [Ideal.jacobson_bot]
    exact hjacobson
  apply (StacksDraft.InjectiveDimension.hasFiniteInjectiveDimension_iff_quotient_ext_vanishing
    (I.map (algebraMap A B)) hIBjac Kplus hfinitePlus).2
  refine ⟨b, ?_⟩
  intro J hIJ i hi
  let J' := J.comap (algebraMap A B)
  let QA := ModuleCat.of A (Shrink.{max u v w} (A ⧸ J'))
  let QB := ModuleCat.of B (Shrink.{max u v w} (B ⧸ J))
  let XA := (DerivedCategory.singleFunctor (ModuleCat.{max u v w} A) 0).obj QA
  let XB := (DerivedCategory.singleFunctor (ModuleCat.{max u v w} B) 0).obj QB
  have hQAfinite : Module.Finite A QA := by infer_instance
  have hXApc : StacksDraft.PseudoCoherence.IsPseudoCoherent XA := by
    have hGE_X : XA.IsGE 0 := inferInstance
    have hLE_X : XA.IsLE 0 := inferInstance
    have hXfinite : ∀ n : ℤ, Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} A) n).obj XA) := by
      intro n
      by_cases hn : n = 0
      · subst n
        let e := (asIso
            ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v w} A) 0).inv.app
            ((CochainComplex.singleFunctor (ModuleCat.{max u v w} A) 0).obj QA))).symm ≪≫
          (asIso ((HomologicalComplex.homologyFunctorSingleIso (ModuleCat.{max u v w} A)
            (ComplexShape.up ℤ) 0).hom.app QA))
        let : Module.Finite A ((𝟭 (ModuleCat.{max u v w} A)).obj QA) := by
          simpa using hQAfinite
        exact Module.Finite.equiv e.toLinearEquiv.symm
      · have hz : Limits.IsZero
            ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} A) n).obj XA) := by
          by_cases h0n : 0 < n
          · exact DerivedCategory.isZero_of_isLE XA 0 n (by omega)
          · exact DerivedCategory.isZero_of_isGE XA 0 n (by omega)
        let : Subsingleton
            ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} A) n).obj XA :
              Type max u v w) :=
          ModuleCat.isZero_iff_subsingleton.mp hz
        exact Module.Finite.of_finite
    exact (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      XA 0 (QA : Type max u v w)).2.1.mpr
        ⟨⟨0, fun n hn => DerivedCategory.isZero_of_isLE XA 0 n hn⟩, hXfinite⟩
  have hExtA : Subsingleton (XA ⟶ K⟦i⟧) :=
    (StacksDraft.InjectiveDimension.hasInjectiveAmplitude_iff_ext_vanishing_iff_quotient_vanishing
      K a b).1.1 hAmp QA i (Or.inr hi)
  have hExtB := subsingleton_hom_shift_of_flat_pseudoCoherent.{u, v, w} XA K a i hGE hXApc
    ((F.mapDerivedCategorySingleFunctor 0).app QA ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{max u v w} B) 0).mapIso
        (quotient_module_iso_extendScalars.{u, v, w} (J.comap (algebraMap A B)) J
          (ideal_map_comap_eq_of_quotient_bijective _ I hquotient J hIJ))) hExtA
  simpa [XB, Kplus, DerivedCategory.Ext] using hExtB

private lemma exists_injective_representative
    {R : Type u} [CommRing R] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (a : ℤ) [K.IsGE a] :
    ∃ (I : CochainComplex (ModuleCat.{v} R) ℤ) (_ : I.IsStrictlyGE a),
      (∀ n, Injective (I.X n)) ∧ Nonempty (K ≅ DerivedCategory.Q.obj I) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K a
  obtain ⟨I, hI, f, hf⟩ := CochainComplex.Plus.exists_quasiIso_injective
    ⟨L, a, hL⟩ a
  refine ⟨((InjectiveObject.ι (ModuleCat.{v} R)).mapHomologicalComplex (.up ℤ)).obj I.obj,
    inferInstance, ?_, ⟨e ≪≫ @asIso _ _ _ _ (DerivedCategory.Q.map f.hom)
      ((DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{v} R) f.hom).2 hf)⟩⟩
  intro n
  exact inferInstanceAs (Injective ((InjectiveObject.ι _).obj (I.obj.X n)))

private lemma subsingleton_hom_of_ulift
    {R : Type u} [CommRing R] [Small.{v} R]
    (X Y : DerivedCategory (ModuleCat.{v} R)) (a : ℤ) [Y.IsGE a]
    (h : Subsingleton
      ((ModuleCat.uliftFunctor.{w, v} R).mapDerivedCategory.obj X ⟶
        (ModuleCat.uliftFunctor.{w, v} R).mapDerivedCategory.obj Y)) :
    Subsingleton (X ⟶ Y) := by
  let U := ModuleCat.uliftFunctor.{w, v} R
  let UH := U.mapHomotopyCategory (ComplexShape.up ℤ)
  let q := HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)
  let q' := HomotopyCategory.quotient (ModuleCat.{max w v} R) (ComplexShape.up ℤ)
  obtain ⟨J, hJGE, hJinj, ⟨eY⟩⟩ := exists_injective_representative Y a
  let : J.IsStrictlyGE a := hJGE
  let : ∀ i, Injective (J.X i) := hJinj
  let : J.IsKInjective := CochainComplex.isKInjective_of_injective J a
  let JU : CochainComplex (ModuleCat.{max w v} R) ℤ :=
    (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj J
  let : JU.IsStrictlyGE a := by
    exact (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff (K := J) U a).2 hJGE
  let : ∀ i, Injective (JU.X i) := fun i => U.injective_obj_of_injective (hJinj i)
  let : JU.IsKInjective := CochainComplex.isKInjective_of_injective JU a
  let Xh := DerivedCategory.Qh.objPreimage X
  let eX := DerivedCategory.Qh.objObjPreimageIso X
  let eJ : DerivedCategory.Qh.obj (q.obj J) ≅ Y :=
    (DerivedCategory.quotientCompQhIso _).app J ≪≫ eY.symm
  let eUX : DerivedCategory.Qh.obj (UH.obj Xh) ≅ U.mapDerivedCategory.obj X :=
    (U.mapDerivedCategoryFactorsh.app Xh).symm ≪≫ U.mapDerivedCategory.mapIso eX
  let eUJ : DerivedCategory.Qh.obj (q'.obj JU) ≅ U.mapDerivedCategory.obj Y :=
    (DerivedCategory.quotientCompQhIso _).app JU ≪≫
      (U.mapDerivedCategoryFactors.app J).symm ≪≫ U.mapDerivedCategory.mapIso eY.symm
  let := h
  have : Subsingleton (DerivedCategory.Qh.obj (UH.obj Xh) ⟶
      DerivedCategory.Qh.obj (q'.obj JU)) :=
    Equiv.subsingleton (Iso.homCongr eUX eUJ)
  have : Subsingleton (UH.obj Xh ⟶ q'.obj JU) :=
    (CochainComplex.IsKInjective.Qh_map_bijective (UH.obj Xh) JU).injective.subsingleton
  let ej : UH.obj (q.obj J) ≅ q'.obj JU :=
    (U.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app J
  have : Subsingleton (UH.obj Xh ⟶ UH.obj (q.obj J)) :=
    Equiv.subsingleton (Iso.homCongr (Iso.refl _) ej)
  have : Subsingleton (Xh ⟶ q.obj J) := UH.map_injective.subsingleton
  have : Subsingleton (DerivedCategory.Qh.obj Xh ⟶ DerivedCategory.Qh.obj (q.obj J)) :=
    (CochainComplex.IsKInjective.Qh_map_bijective Xh J).surjective.subsingleton
  exact Equiv.subsingleton (Iso.homCongr eX eJ).symm

private theorem finiteInjectiveDimension_of_ulift
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (a : ℤ) [K.IsGE a]
    (hfinite : ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K))
    (h : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension
      ((ModuleCat.uliftFunctor.{w, v} R).mapDerivedCategory.obj K)) :
    StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K := by
  let U := ModuleCat.uliftFunctor.{w, v} R
  let : Small.{max v w} R := small_lift.{u, w, v} R
  obtain ⟨c, b, hAmp⟩ := h
  let Kplus : DerivedCategory.Plus (ModuleCat.{v} R) := ⟨K, ⟨a, inferInstance⟩⟩
  apply (StacksDraft.InjectiveDimension.hasFiniteInjectiveDimension_iff_quotient_ext_vanishing
    (⊥ : Ideal R) bot_le Kplus hfinite).2
  refine ⟨b, ?_⟩
  intro J hJ i hi
  let M := ModuleCat.of R (Shrink.{v} (R ⧸ J))
  let X := (DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M
  have hvan :=
    (StacksDraft.InjectiveDimension.hasInjectiveAmplitude_iff_ext_vanishing_iff_quotient_vanishing
      (U.mapDerivedCategory.obj K) c b).1.1 hAmp (U.obj M) i (Or.inr hi)
  change Subsingleton ((DerivedCategory.singleFunctor (ModuleCat.{max v w} R) 0).obj
    (U.obj M) ⟶ (U.mapDerivedCategory.obj K)⟦i⟧) at hvan
  let eX := (U.mapDerivedCategorySingleFunctor 0).app M
  let eY := (U.mapDerivedCategory.commShiftIso i).app K
  let := hvan
  have : Subsingleton (U.mapDerivedCategory.obj X ⟶ U.mapDerivedCategory.obj (K⟦i⟧)) :=
    ⟨fun f g => (Iso.homCongr eX eY).injective (@Subsingleton.elim _ hvan _ _)⟩
  have : (K⟦i⟧).IsGE (a - i) :=
    DerivedCategory.TStructure.t.isGE_shift K a i (a - i) (by omega)
  exact subsingleton_hom_of_ulift X (K⟦i⟧) (a - i) inferInstance

private noncomputable def extendScalarsULiftLinearEquiv
    {A : Type u} {B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    (M : ModuleCat.{v} A) :
    ((ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)).obj
      ((ModuleCat.uliftFunctor.{max u w, v} A).obj M)) ≃ₗ[B]
      ((ModuleCat.uliftFunctor.{u, max w v} B).obj
        ((ModuleCat.extendScalars.{u, w, v} (algebraMap A B)).obj M)) := by
  let B_A := (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)
  letI : IsScalarTower A B B_A :=
    IsScalarTower.of_algebraMap_smul (by intro r x; rfl)
  change TensorProduct A B_A (ULift.{max u w} M) ≃ₗ[B]
    ULift.{u} (TensorProduct A B_A M)
  exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B_A)
    (ULift.moduleEquiv (R := A))).trans (ULift.moduleEquiv (R := B)).symm

private noncomputable def extendScalarsULiftComplexIso
    {A : Type u} {B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    (P : CochainComplex (ModuleCat.{v} A) ℤ) :
    ((ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (((ModuleCat.uliftFunctor.{max u w, v} A).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≅
    ((ModuleCat.uliftFunctor.{u, max w v} B).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{u, w, v} (algebraMap A B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) := by
  apply HomologicalComplex.Hom.isoOfComponents
    (fun i => (extendScalarsULiftLinearEquiv (B := B) (P.X i)).toModuleIso)

private noncomputable def extendScalarsULiftDerivedIso
    {A : Type u} {B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (K : DerivedCategory (ModuleCat.{v} A)) :
    (ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)).mapDerivedCategory.obj
      ((ModuleCat.uliftFunctor.{max u w, v} A).mapDerivedCategory.obj K) ≅
    (ModuleCat.uliftFunctor.{u, max w v} B).mapDerivedCategory.obj
      ((ModuleCat.extendScalars.{u, w, v} (algebraMap A B)).mapDerivedCategory.obj K) := by
  let U := ModuleCat.uliftFunctor.{max u w, v} A
  let V := ModuleCat.uliftFunctor.{u, max w v} B
  let F := ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)
  let E := ModuleCat.extendScalars.{u, w, v} (algebraMap A B)
  let P := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  exact F.mapDerivedCategory.mapIso (U.mapDerivedCategory.mapIso e.symm) ≪≫
    F.mapDerivedCategory.mapIso (U.mapDerivedCategoryFactors.app P) ≪≫
    F.mapDerivedCategoryFactors.app ((U.mapHomologicalComplex (.up ℤ)).obj P) ≪≫
    DerivedCategory.Q.mapIso (extendScalarsULiftComplexIso (B := B) P) ≪≫
    (V.mapDerivedCategoryFactors.app ((E.mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
    V.mapDerivedCategory.mapIso (E.mapDerivedCategoryFactors.app P).symm ≪≫
    V.mapDerivedCategory.mapIso (E.mapDerivedCategory.mapIso e)

private theorem homothetyQuasiIso_extendScalars_of_flat
    {A : Type u} {B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDualizingComplex K) :
    IsDerivedHomothetyQuasiIso
      ((ModuleCat.extendScalars.{u, w, v} (algebraMap A B)).mapDerivedCategory.obj K) := by
  let : Small.{v} A := small_base_from_dualizing K hK
  let U := ModuleCat.uliftFunctor.{max u w, v} A
  let V := ModuleCat.uliftFunctor.{u, max w v} B
  let F := ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)
  let KU := U.mapDerivedCategory.obj K
  let D := F.mapDerivedCategory
  let α := F.mapDerivedCategoryFactors.hom
  let W := HomologicalComplex.quasiIso (ModuleCat.{max u v w} A) (.up ℤ)
  let : D.IsLeftDerivedFunctor α W :=
    Functor.isLeftDerivedFunctor_of_inverts W D F.mapDerivedCategoryFactors
  obtain ⟨a, b, I, hGE, hLE, hIinj, ⟨eI⟩⟩ := hK.finiteInjectiveDimension
  let Iu : CochainComplex (ModuleCat.{max u v w} A) ℤ := (U.mapHomologicalComplex (.up ℤ)).obj I
  let eK : KU ≅ DerivedCategory.Q.obj Iu :=
    U.mapDerivedCategory.mapIso eI ≪≫ U.mapDerivedCategoryFactors.app I
  have hIuGE : Iu.IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff (K := I) U a).2 hGE
  have hIuInj : ∀ i, Injective (Iu.X i) := fun i => U.injective_obj_of_injective (hIinj i)
  let : Iu.IsStrictlyGE a := hIuGE
  have hKUge : KU.IsGE a := DerivedCategory.TStructure.t.isGE_of_iso eK.symm a
  have hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent KU :=
    pseudoCoherent_ulift_of_dualizing K hK
  have : IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, w, max u v w}
      (algebraMap A B) D α KU KU) :=
    derivedHomBaseChange_isIso_of_flat_pseudoCoherent.{u, v, w} KU KU hpc ⟨a, hKUge⟩
  have : QuasiIso (sourceHomothetyAtCommonUniverse.{u, v, w} I) :=
    sourceHomothetyAtCommonUniverse_quasiIso I
      (hK.homothetyQuasiIso I ⟨eI.symm⟩ hIinj ⟨a, b, hGE, hLE⟩)
  let HRA := Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, max u v w} A
  let U₂ := ModuleCat.uliftFunctor.{w, max u v} A
  let M₁ := ModuleCat.of A (ULift.{v} A)
  let R₀ := (U₂.mapHomologicalComplex (.up ℤ)).obj
    ((CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0).obj M₁)
  let eSource : HRA.obj (Opposite.op KU, KU) ≅ DerivedCategory.Q.obj R₀ :=
    HRA.mapIso (eK.symm.op.prod eK) ≪≫
      derivedInternalHomModelIso.{u, max v w} Iu a hIuGE hIuInj ≪≫
        (asIso (DerivedCategory.Q.map
          (sourceHomothetyAtCommonUniverse.{u, v, w} I))).symm
  let HRB := Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{w, max u v w} B
  let eTarget := (asIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, w, max u v w}
      (algebraMap A B) D α KU KU)).symm ≪≫
    D.mapIso eSource ≪≫ F.mapDerivedCategoryFactors.app R₀
  let eSingle : (F.mapHomologicalComplex (.up ℤ)).obj R₀ ≅
      (CochainComplex.singleFunctor (ModuleCat.{max u v w} B) 0).obj
        (F.obj (U₂.obj M₁)) :=
    (F.mapHomologicalComplex (.up ℤ)).mapIso
        ((Functor.mapCochainComplexSingleFunctor U₂ 0).app M₁) ≪≫
      (Functor.mapCochainComplexSingleFunctor F 0).app (U₂.obj M₁)
  let eTargetSingle := eTarget ≪≫ DerivedCategory.Q.mapIso eSingle
  intro J hJ hJinj hJbound
  obtain ⟨c, d, hJGE, hJLE⟩ := hJbound
  let Ju : CochainComplex (ModuleCat.{max u v w} B) ℤ := (V.mapHomologicalComplex (.up ℤ)).obj J
  let eJ : DerivedCategory.Q.obj Ju ≅ D.obj KU :=
    (V.mapDerivedCategoryFactors.app J).symm ≪≫
      V.mapDerivedCategory.mapIso hJ.some ≪≫ (extendScalarsULiftDerivedIso K).symm
  have hJuGE : Ju.IsStrictlyGE c :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff (K := J) V c).2 hJGE
  have hJuInj : ∀ i, Injective (Ju.X i) := fun i => V.injective_obj_of_injective (hJinj i)
  let eJModel := derivedInternalHomModelIso.{w, max u v} Ju c hJuGE hJuInj
  let HJ := CochainComplex.HomComplexR B J J
  let HJu := CochainComplex.HomComplexR B Ju Ju
  let MB := F.obj (U₂.obj M₁)
  let SB := (CochainComplex.singleFunctor (ModuleCat.{max u v w} B) 0).obj MB
  let eJSingle : DerivedCategory.Q.obj HJu ≅ DerivedCategory.Q.obj SB :=
    eJModel.symm ≪≫ HRB.mapIso (eJ.symm.op.prod eJ) ≪≫ eTargetSingle
  let eHom (n : ℤ) : V.obj (HJ.homology n) ≅ SB.homology n :=
    ((HJ.sc n).mapHomologyIso V).symm ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} B) (.up ℤ) n).mapIso
        (homComplexULiftIso.{w, max w v, u} J J) ≪≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v w} B) n).app HJu).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) n).mapIso eJSingle ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v w} B) n).app SB
  let eH₀ : HJ.homology 0 ≃ₗ[B] B :=
    (ULift.moduleEquiv (R := B)).symm.trans
      (((eHom 0) ≪≫ HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 MB).toLinearEquiv.trans
        (localized_baseModuleEquiv.{u, v, w}))
  have hHjZero (n : ℤ) (hn : n ≠ 0) : IsZero (HJ.homology n) := by
    have h : IsZero (V.obj (HJ.homology n)) :=
      (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 MB n hn).of_iso (eHom n)
    have hsub : Subsingleton (V.obj (HJ.homology n)) :=
      ModuleCat.isZero_iff_subsingleton.mp h
    apply ModuleCat.isZero_iff_subsingleton.mpr
    refine ⟨fun x y => ?_⟩
    have hxy : (ULift.up x : V.obj (HJ.homology n)) = ULift.up y :=
      @Subsingleton.elim _ hsub _ _
    exact congrArg ULift.down hxy
  let : J.IsStrictlyGE c := hJGE
  let : ∀ i, Injective (J.X i) := hJinj
  let : J.IsKInjective := CochainComplex.isKInjective_of_injective J c
  exact quasiIso_homothety_of_rankOne J eH₀ hHjZero

/-- Let `A → B` be a flat map of Noetherian commutative rings. If the induced map `A/I → B/IB`
is bijective and `IB` is contained in the Jacobson radical of `B`, then extending a dualizing
complex from `A` to `B` gives a dualizing complex over `B`. -/
@[stacks 0DWC]
public theorem isDualizingComplex_extendScalars_of_flat
    {A : Type u} {B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [IsNoetherianRing A] [IsNoetherianRing B]
    (I : Ideal A)
    (hquotient : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
        Ideal.le_comap_map))
    (hjacobson : I.map (algebraMap A B) ≤ Ring.jacobson B)
    (K : DerivedCategory (ModuleCat.{v} A))
    (hK : IsDualizingComplex K) :
    IsDualizingComplex
      ((ModuleCat.extendScalars.{u, w, v} (algebraMap A B)).mapDerivedCategory.obj K) := by
  let F := ModuleCat.extendScalars.{u, w, v} (algebraMap A B)
  let U := ModuleCat.uliftFunctor.{max u w, v} A
  let V := ModuleCat.uliftFunctor.{u, max w v} B
  let : Small.{v} A := small_base_from_dualizing K hK
  have hfinite := finiteCohomology_extendScalars (B := B) K hK.finiteCohomology
  refine ⟨?_, hfinite, homothetyQuasiIso_extendScalars_of_flat K hK⟩
  obtain ⟨a, b, hGE, hLE⟩ :=
    exists_tStructure_bounds_of_finiteInjectiveDimension K hK.finiteInjectiveDimension
  have := isGE_mapDerivedCategory_obj F K a hGE
  have hKUfid : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension
      (U.mapDerivedCategory.obj K) := finiteInjectiveDimension_ulift K hK.finiteInjectiveDimension
  have hbig := finiteInjectiveDimension_extendScalars_common.{u, v, w} I hquotient hjacobson
    (U.mapDerivedCategory.obj K) hKUfid (finiteCohomology_ulift.{u, v, w} K hK.finiteCohomology)
  have hlift : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension
      (V.mapDerivedCategory.obj (F.mapDerivedCategory.obj K)) := by
    obtain ⟨c, d, J, hJGE, hJLE, hJinj, ⟨eJ⟩⟩ := hbig
    exact ⟨c, d, J, hJGE, hJLE, hJinj,
      ⟨(extendScalarsULiftDerivedIso K).symm ≪≫ eJ⟩⟩
  exact finiteInjectiveDimension_of_ulift (F.mapDerivedCategory.obj K) a hfinite hlift

/-- A faithfully flat extension of scalars only kills the zero module. -/
private theorem isZero_of_isZero_extendScalars_of_faithfullyFlat
    {A : Type u} {B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (M : ModuleCat.{v} A)
    (hM : IsZero ((ModuleCat.extendScalars.{u, w, v} (algebraMap A B)).obj M)) :
    IsZero M := by
  let eLeft : ((ModuleCat.restrictScalars (algebraMap A B)).obj
      (ModuleCat.of B B)) ≃ₗ[A] B :=
    { AddEquiv.refl B with
      map_smul' := fun a b ↦ (Algebra.smul_def (R := A) (A := B) a b).symm }
  let : Subsingleton (TensorProduct A
      ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) M) :=
    ModuleCat.isZero_iff_subsingleton.mp hM
  let : Subsingleton (TensorProduct A B M) :=
    Equiv.subsingleton (TensorProduct.congr eLeft (LinearEquiv.refl A M)).symm.toEquiv
  let z : M →ₗ[A] M := 0
  have hz : Function.Bijective (z.lTensor B) :=
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  have hz' : Function.Bijective z :=
    (Module.FaithfullyFlat.lTensor_bijective_iff_bijective (R := A) (M := B) (f := z)).1 hz
  exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y => hz'.1 (show z x = z y from rfl)⟩

/-- For a faithfully flat extension of scalars, a nonzero morphism group out of a
pseudo-coherent object stays nonzero after base change. -/
private theorem not_subsingleton_mapDerivedHom_of_faithfullyFlat
    {A : Type u} {B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B]
    (X M : DerivedCategory (ModuleCat.{max u v w} A))
    (hX : StacksDraft.PseudoCoherence.IsPseudoCoherent X)
    (hM : ∃ b : ℤ, M.IsGE b)
    (hXM : ¬ Subsingleton (X ⟶ M)) :
    ¬ Subsingleton
      ((ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)).mapDerivedCategory.obj X ⟶
        (ModuleCat.extendScalars.{u, w, max u v w}
          (algebraMap A B)).mapDerivedCategory.obj M) := by
  intro hSub
  exact hXM ((hom_subsingleton_iff_derivedInternalHom_homology_isZero.{u, max u v w} X M).mpr
    (isZero_of_isZero_extendScalars_of_faithfullyFlat _
      ((subsingleton_mapDerivedHom_iff_isZero_extendScalars.{u, v, w} X M hX hM).1 hSub)))

/-- The residue field, viewed as a module over the ring, is the restriction of scalars of the
residue field as a module over itself, both placed in degree zero. -/
private theorem nonempty_single_residue_iso_restrictScalars
    (R : Type u) [CommRing R] [IsLocalRing R] :
    Nonempty ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
        (ModuleCat.of R (Shrink.{max v u} (R ⧸ IsLocalRing.maximalIdeal R))) ≅
      (ModuleCat.restrictScalars.{max v u} (IsLocalRing.residue R)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor
          (ModuleCat.{max v u} (IsLocalRing.ResidueField R)) 0).obj
            ((ModuleCat.uliftFunctor.{v} (IsLocalRing.ResidueField R)).obj
              (ModuleCat.of (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R))))) := by
  let k := IsLocalRing.ResidueField R
  let G := ModuleCat.restrictScalars.{max v u} (IsLocalRing.residue R)
  let sMod := (ModuleCat.uliftFunctor.{v} k).obj (ModuleCat.of k k)
  let e : Shrink.{max v u} k ≃ₗ[R] ULift.{v} k :=
    (Shrink.linearEquiv R k).trans ULift.moduleEquiv.symm
  exact ⟨(DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).mapIso e.toModuleIso ≪≫
    ((G.mapDerivedCategorySingleFunctor 0).app sMod).symm⟩

/-- Normalization makes `RHom(κ, K)` concentrated in degree zero, hence the Ext groups from
the residue field into `K` vanish in all positive degrees. -/
private theorem residueExtVanish_of_normalization
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (hNorm : Nonempty
      ((derivedHom.{u, v} (IsLocalRing.residue R)).obj K ≅
        (DerivedCategory.singleFunctor
          (ModuleCat.{max v u} (IsLocalRing.ResidueField R)) 0).obj
            ((ModuleCat.uliftFunctor.{v} (IsLocalRing.ResidueField R)).obj
              (ModuleCat.of (IsLocalRing.ResidueField R)
                (IsLocalRing.ResidueField R))))) :
    ∃ b : ℤ, ∀ i : ℤ, b < i → Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
        (ModuleCat.of R (Shrink.{max v u}
          (R ⧸ IsLocalRing.maximalIdeal R)))) K i) := by
  obtain ⟨eNorm⟩ := hNorm
  let k := IsLocalRing.ResidueField R
  let H := derivedHom.{u, v} (IsLocalRing.residue R)
  let sMod := (ModuleCat.uliftFunctor.{v} k).obj (ModuleCat.of k k)
  let S := (DerivedCategory.singleFunctor (ModuleCat.{max v u} k) 0).obj sMod
  obtain ⟨eQ⟩ := nonempty_single_residue_iso_restrictScalars.{u, v} R
  obtain ⟨adj⟩ := restrictScalarsDerived_adj_derivedHom.{u, v} (IsLocalRing.residue R)
  let : H.CommShift ℤ := by
    dsimp [H, derivedHom]
    infer_instance
  refine ⟨0, fun i hi => ?_⟩
  let heShift : H.obj (K⟦i⟧) ≅ S⟦i⟧ :=
    (H.commShiftIso i).app K ≪≫ (shiftFunctor _ i).mapIso eNorm
  have hFieldHom : ∀ f : S ⟶ S⟦i⟧, f = 0 :=
    residueSingle_shift_hom_eq_zero.{u, v} k i (by omega)
  let : Subsingleton (S ⟶ S⟦i⟧) := ⟨fun f g => by rw [hFieldHom f, hFieldHom g]⟩
  exact Equiv.subsingleton
    (((Iso.homCongr eQ (Iso.refl (K⟦i⟧))).trans (adj.homEquiv S (K⟦i⟧))).trans
      (Iso.homCongr (Iso.refl S) heShift))

/-- Normalization makes the degree-zero part of `RHom(κ, K)` nonzero, so some morphism from the
residue field in degree zero to `K` is nonzero. -/
private theorem residueHom_nontrivial_of_normalization
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (hNorm : Nonempty
      ((derivedHom.{u, v} (IsLocalRing.residue R)).obj K ≅
        (DerivedCategory.singleFunctor
          (ModuleCat.{max v u} (IsLocalRing.ResidueField R)) 0).obj
            ((ModuleCat.uliftFunctor.{v} (IsLocalRing.ResidueField R)).obj
              (ModuleCat.of (IsLocalRing.ResidueField R)
                (IsLocalRing.ResidueField R))))) :
    ¬ Subsingleton
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
        (ModuleCat.of R (Shrink.{max v u}
          (R ⧸ IsLocalRing.maximalIdeal R))) ⟶ K) := by
  obtain ⟨eNorm⟩ := hNorm
  let k := IsLocalRing.ResidueField R
  let G := ModuleCat.restrictScalars.{max v u} (IsLocalRing.residue R)
  let sMod := (ModuleCat.uliftFunctor.{v} k).obj (ModuleCat.of k k)
  let S := (DerivedCategory.singleFunctor (ModuleCat.{max v u} k) 0).obj sMod
  obtain ⟨eK₀⟩ := nonempty_single_residue_iso_restrictScalars.{u, v} R
  obtain ⟨adj⟩ := restrictScalarsDerived_adj_derivedHom.{u, v} (IsLocalRing.residue R)
  let t : G.mapDerivedCategory.obj S ⟶ K := (adj.homEquiv S K).symm eNorm.inv
  have ht : t ≠ 0 := by
    have hS : (𝟙 S : S ⟶ S) ≠ 0 := residueSingle_id_ne_zero.{u, v} k
    have heNorm : eNorm.inv ≠ 0 := by
      intro h
      exact hS (by simpa [h] using eNorm.inv_hom_id.symm)
    intro h
    exact heNorm ((adj.homEquiv S K).symm.injective (by simpa [t] using h))
  have ht₀ : eK₀.hom ≫ t ≠ 0 :=
    fun h => ht ((Preadditive.IsIso.comp_left_eq_zero _ _).mp h)
  intro hSub
  exact ht₀ (hSub.elim _ _)

/-- **[Stacks, Tag 0AVJ].** Over a Noetherian local ring, a bounded below object with finite
cohomology has finite injective dimension as soon as the Ext groups from the residue field
vanish in large degrees. -/
private theorem hasFiniteInjectiveDimension_of_residueExtVanish
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (hGE : ∃ a : ℤ, K.IsGE a)
    (hfinite : ∀ i : ℤ, Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) i).obj K))
    (hExt : ∃ b : ℤ, ∀ i : ℤ, b < i →
      Subsingleton (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (ModuleCat.of R (Shrink.{max v u}
            (R ⧸ IsLocalRing.maximalIdeal R)))) K i)) :
    StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K := by
  obtain ⟨a, ha⟩ := hGE
  exact (StacksDraft.InjectiveDimension.hasFiniteInjectiveDimension_iff_residueField_ext_vanishing
    (ObjectProperty.FullSubcategory.mk K ⟨a, ha⟩) hfinite).2 hExt

/-- A dualizing complex over a Noetherian local ring is normalized as soon as some morphism
from the residue field in degree zero to it is nonzero. -/
private theorem isNormalizedDualizingComplex_of_residueHom_nontrivial
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (hDual : IsDualizingComplex K)
    (hHom : ¬ Subsingleton
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
        (ModuleCat.of R (Shrink.{max v u}
          (R ⧸ IsLocalRing.maximalIdeal R))) ⟶ K)) :
    IsNormalizedDualizingComplex.{u, v} K := by
  obtain ⟨n, ⟨eShift⟩⟩ := derivedHom_localResidueField_iso_shift.{u, v} K hDual
  let k := IsLocalRing.ResidueField R
  let G := ModuleCat.restrictScalars.{max v u} (IsLocalRing.residue R)
  let sMod := (ModuleCat.uliftFunctor.{v} k).obj (ModuleCat.of k k)
  let S := (DerivedCategory.singleFunctor (ModuleCat.{max v u} k) 0).obj sMod
  obtain ⟨eK₀⟩ := nonempty_single_residue_iso_restrictScalars.{u, v} R
  obtain ⟨adj⟩ := restrictScalarsDerived_adj_derivedHom.{u, v} (IsLocalRing.residue R)
  have hn : n = 0 := by
    by_contra hn
    have hFieldHom : ∀ f : S ⟶ S⟦n⟧, f = 0 :=
      residueSingle_shift_hom_eq_zero.{u, v} k n hn
    let : Subsingleton (S ⟶ S⟦n⟧) := ⟨fun f g => by rw [hFieldHom f, hFieldHom g]⟩
    exact hHom (Equiv.subsingleton
      (((Iso.homCongr eK₀ (Iso.refl K)).trans (adj.homEquiv S K)).trans
        (Iso.homCongr (Iso.refl S) eShift)))
  subst n
  exact ⟨hDual, ⟨eShift ≪≫ (shiftZero ℤ _)⟩⟩

/-- Let `A → B` be a flat local homomorphism of Noetherian local rings for which the maximal
ideal of `A` generates the maximal ideal of `B`. Then the base change to `B` of a normalized
dualizing complex over `A` is a normalized dualizing complex over `B`. -/
@[stacks 0AWD]
public theorem isNormalizedDualizingComplex_extendScalars_of_flat
    {A : Type u} {B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    (K : DerivedCategory (ModuleCat.{max u v w} A))
    (hK : IsNormalizedDualizingComplex.{u, max v w} K) :
    IsNormalizedDualizingComplex.{w, max u v}
      ((ModuleCat.extendScalars.{u, w, max u v w}
        (algebraMap A B)).mapDerivedCategory.obj K) := by
  let F := ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A B)
  let : F.Additive := extendScalars_additive _
  let : Limits.PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat
  let : Limits.PreservesFiniteColimits F := extendScalars_preservesFiniteColimits_of_flat
  let QA := ModuleCat.of A (Shrink.{max u v w} (A ⧸ IsLocalRing.maximalIdeal A))
  let QB := ModuleCat.of B (Shrink.{max u v w} (B ⧸ IsLocalRing.maximalIdeal B))
  let XA := (DerivedCategory.singleFunctor (ModuleCat.{max u v w} A) 0).obj QA
  let XB := (DerivedCategory.singleFunctor (ModuleCat.{max u v w} B) 0).obj QB
  have hXApc : StacksDraft.PseudoCoherence.IsPseudoCoherent XA :=
    pseudoCoherent_single_of_finite QA
  let eX : F.mapDerivedCategory.obj XA ≅ XB :=
    (F.mapDerivedCategorySingleFunctor 0).app QA ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{max u v w} B) 0).mapIso
        (quotient_module_iso_extendScalars.{u, v, w} _ _ hmax)
  obtain ⟨a, b, hGE, hLE⟩ := exists_tStructure_bounds_of_finiteInjectiveDimension K
    hK.1.finiteInjectiveDimension
  have hGE' := isGE_mapDerivedCategory_obj F K a hGE
  have hfinite := finiteCohomology_extendScalars (B := B) K hK.1.finiteCohomology
  obtain ⟨c, hc⟩ := residueExtVanish_of_normalization.{u, max v w} K hK.2
  have hExtB : ∃ e : ℤ, ∀ i : ℤ, e < i →
      Subsingleton (DerivedCategory.Ext XB (F.mapDerivedCategory.obj K) i) := by
    refine ⟨c, fun i hi => ?_⟩
    exact subsingleton_hom_shift_of_flat_pseudoCoherent.{u, v, w} XA K a i hGE hXApc eX (hc i hi)
  have hDual : IsDualizingComplex (F.mapDerivedCategory.obj K) :=
    ⟨hasFiniteInjectiveDimension_of_residueExtVanish.{w, max u v} _ ⟨a, hGE'⟩ hfinite hExtB,
      hfinite, homothetyQuasiIso_extendScalars_of_flat K hK.1⟩
  let : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hNT : ¬ Subsingleton (XB ⟶ F.mapDerivedCategory.obj K) := by
    have h0 := not_subsingleton_mapDerivedHom_of_faithfullyFlat.{u, v, w} (B := B) XA K hXApc
      ⟨a, hGE⟩ (residueHom_nontrivial_of_normalization.{u, max v w} K hK.2)
    intro hSub
    exact h0 (Equiv.subsingleton (Iso.homCongr eX (Iso.refl (F.mapDerivedCategory.obj K))))
  exact isNormalizedDualizingComplex_of_residueHom_nontrivial.{w, max u v} _ hDual hNT

end

end Dualizing
