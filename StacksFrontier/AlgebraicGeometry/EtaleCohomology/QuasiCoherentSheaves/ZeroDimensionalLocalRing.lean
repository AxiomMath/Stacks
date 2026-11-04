module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.Free
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.LocallyFree
public import StacksCore.FieldTheory.Galois.Basic
public import StacksCore.FieldTheory.Normal.Closure
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf
public import StacksFrontier.RingTheory.Etale.Basic
public import StacksFrontier.RingTheory.Henselian.Criteria
public import StacksFrontier.RingTheory.Henselian.FiniteEtale
public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic
public import StacksFrontier.RingTheory.Ideal.JacobsonIntegral

/-!
# Quasi-coherence of modules on the étale site of a zero-dimensional local ring

If `R` is a local ring of dimension zero and `S = Spec R`, then every `𝒪_S`-module on `S_étale`
is quasi-coherent.  Such an `R` is henselian, an étale `S`-scheme is a disjoint union of
one-point affine schemes finite étale over `R`, and over a Galois such extension the sections of
a module are spanned by its global sections: a dual family for the Galois action writes every
section as a combination of invariant ones, and an invariant section descends.

## Main results

* `Stacks.EtaleCohomology.SmallEtaleModules.allModules_isQuasicoherent`: every module over the
  structure sheaf of the small étale site of `Spec R` is quasi-coherent.
* `Stacks.EtaleCohomology.SmallEtaleModules.hasWeakSheafifyOverSmallEtale` and
  `Stacks.EtaleCohomology.SmallEtaleModules.wEqualsLocallyBijectiveOverSmallEtale`: abelian
  presheaves on a slice of the small étale site sheafify, and its weak equivalences are the
  locally bijective maps.  These are what the quasi-coherence predicate consumes.

## Implementation notes

The small étale site and its structure sheaf use a chosen big étale site containing `Spec R`.
Quasi-coherence is Mathlib's predicate for modules on a ringed site, expressed by local
presentations; over a site with a final object a presentation over that object suffices, so the
statement reduces to the unit object being a separator on the slice at the final object.

## References

* [Stacks Project, Tag 0D1W](https://stacks.math.columbia.edu/tag/0D1W)
* [Stacks Project, Tag 04GJ](https://stacks.math.columbia.edu/tag/04GJ)
* [Stacks Project, Tag 06RS](https://stacks.math.columbia.edu/tag/06RS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings BigOperators TensorProduct

universe u v w

namespace Stacks.EtaleCohomology.SmallEtaleModules

private noncomputable def actionTensorMap
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    {G : Type*} [Group G] (ρ : G →* (A ≃ₐ[R] A)) :
    A ⊗[R] A →ₐ[A] (G → A) :=
  AlgHom.liftEquiv R A A _ (AlgHom.pi fun g ↦ (ρ g).toAlgHom)

private lemma actionTensorMap_tmul
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    {G : Type*} [Group G] (ρ : G →* (A ≃ₐ[R] A)) (a b : A) (g : G) :
    actionTensorMap R A ρ (a ⊗ₜ[R] b) g = a * ρ g b := rfl

private lemma actionTensorMap_id_surjective
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    Function.Surjective (actionTensorMap K L (MonoidHom.id (L ≃ₐ[K] L))) := by
  have hlin : LinearIndependent L (fun σ : L ≃ₐ[K] L ↦ (σ : L → L)) :=
    (linearIndependent_monoidHom L L).comp
      (fun σ : L ≃ₐ[K] L ↦ σ.toMonoidHom)
      (fun σ τ h ↦ AlgEquiv.ext fun x ↦ congrArg (fun f : L →* L ↦ f x) h)
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← span_flip_eq_top_iff_linearIndependent.mpr hlin]
  apply Submodule.span_le.mpr
  rintro _ ⟨b, rfl⟩
  refine ⟨1 ⊗ₜ[K] b, ?_⟩
  ext σ
  simp [Function.flip_def]

/-- A morphism of residue-field base changes induced by `f` sends `1 ⊗ a` to `1 ⊗ f a`. -/
private lemma tmul_apply_of_map_eq
    (R A T : Type u) [CommRing R] [IsLocalRing R]
    [CommRing A] [Algebra R A] [CommRing T] [Algebra R T]
    {f : A →ₐ[R] T}
    {g : (IsLocalRing.ResidueField R ⊗[R] A) →ₐ[IsLocalRing.ResidueField R]
      (IsLocalRing.ResidueField R ⊗[R] T)}
    (h : Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField R) _) f = g) (a : A) :
    (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f a =
      g ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] a) := by
  rw [← h, Algebra.TensorProduct.map_tmul, map_one]

private lemma exists_lift_residue_algHom
    (R A T : Type u) [CommRing R] [HenselianLocalRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A]
    [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T]
    (g : (IsLocalRing.ResidueField R ⊗[R] A) →ₐ[IsLocalRing.ResidueField R]
      (IsLocalRing.ResidueField R ⊗[R] T)) :
    ∃ f : A →ₐ[R] T, ∀ a,
      (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f a =
        g ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] a) := by
  let E := CommAlgCat.FiniteEtale.baseChange R (IsLocalRing.ResidueField R)
  let g' : E.obj (CommAlgCat.FiniteEtale.of R A) ⟶
      E.obj (CommAlgCat.FiniteEtale.of R T) := CommAlgCat.FiniteEtale.ofHom g
  exact ⟨(E.preimage g').hom.hom,
    tmul_apply_of_map_eq R A T (congrArg (fun f ↦ f.hom.hom) (E.map_preimage g'))⟩

private lemma finiteEtale_algHom_ext_of_residue
    (R A T : Type u) [CommRing R] [HenselianLocalRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A]
    [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T]
    {f g : A →ₐ[R] T}
    (h : ∀ a, (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f a =
      (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] g a) : f = g := by
  let E := CommAlgCat.FiniteEtale.baseChange R (IsLocalRing.ResidueField R)
  have he : E.map (CommAlgCat.FiniteEtale.ofHom f) =
      E.map (CommAlgCat.FiniteEtale.ofHom g) := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    show Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField R) _) f =
      Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField R) _) g
    apply Algebra.TensorProduct.ext
    · ext
    · exact AlgHom.ext fun a ↦ by simpa using h a
  exact congrArg (fun t ↦ t.hom.hom) (E.map_injective he)

private lemma exists_lift_residue_algEquiv
    (R A T : Type u) [CommRing R] [HenselianLocalRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A]
    [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T]
    (e : (IsLocalRing.ResidueField R ⊗[R] A) ≃ₐ[IsLocalRing.ResidueField R]
      (IsLocalRing.ResidueField R ⊗[R] T)) :
    ∃ f : A ≃ₐ[R] T, ∀ a,
      (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f a =
        e ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] a) := by
  let E := CommAlgCat.FiniteEtale.baseChange R (IsLocalRing.ResidueField R)
  let e' : E.obj (CommAlgCat.FiniteEtale.of R A) ≅
      E.obj (CommAlgCat.FiniteEtale.of R T) := CommAlgCat.FiniteEtale.isoMk e
  let f := CommAlgCat.algEquivOfIso
    ((CommAlgCat.finiteEtale R).ι.mapIso (E.preimageIso e'))
  exact ⟨f, tmul_apply_of_map_eq R A T (f := f.toAlgHom) (g := e.toAlgHom)
    (congrArg (fun t ↦ t.hom.hom) (E.map_preimage e'.hom))⟩

private noncomputable def liftResidueAlgEquiv
    (R A T : Type u) [CommRing R] [HenselianLocalRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A]
    [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T]
    (e : (IsLocalRing.ResidueField R ⊗[R] A) ≃ₐ[IsLocalRing.ResidueField R]
      (IsLocalRing.ResidueField R ⊗[R] T)) : A ≃ₐ[R] T :=
  (exists_lift_residue_algEquiv R A T e).choose

private lemma liftResidueAlgEquiv_apply
    (R A T : Type u) [CommRing R] [HenselianLocalRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A]
    [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T]
    (e : (IsLocalRing.ResidueField R ⊗[R] A) ≃ₐ[IsLocalRing.ResidueField R]
      (IsLocalRing.ResidueField R ⊗[R] T)) (a : A) :
    (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] liftResidueAlgEquiv R A T e a =
      e ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] a) :=
  (exists_lift_residue_algEquiv R A T e).choose_spec a

private noncomputable def residueAutLift
    (R A : Type u) [CommRing R] [HenselianLocalRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A] :
    ((IsLocalRing.ResidueField R ⊗[R] A) ≃ₐ[IsLocalRing.ResidueField R]
      (IsLocalRing.ResidueField R ⊗[R] A)) →* (A ≃ₐ[R] A) where
  toFun := liftResidueAlgEquiv R A A
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply finiteEtale_algHom_ext_of_residue R A A
    intro a
    change (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] liftResidueAlgEquiv R A A 1 a =
      (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] a
    rw [liftResidueAlgEquiv_apply]
    rfl
  map_mul' e f := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply finiteEtale_algHom_ext_of_residue R A A
    intro a
    change (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] liftResidueAlgEquiv R A A (e * f) a =
      (1 : IsLocalRing.ResidueField R) ⊗ₜ[R]
        liftResidueAlgEquiv R A A e (liftResidueAlgEquiv R A A f a)
    rw [liftResidueAlgEquiv_apply, liftResidueAlgEquiv_apply, liftResidueAlgEquiv_apply]
    rfl

private lemma residueAutLift_apply
    (R A : Type u) [CommRing R] [HenselianLocalRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A]
    (e : (IsLocalRing.ResidueField R ⊗[R] A) ≃ₐ[IsLocalRing.ResidueField R]
      (IsLocalRing.ResidueField R ⊗[R] A)) (a : A) :
    (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] residueAutLift R A e a =
      e ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] a) :=
  liftResidueAlgEquiv_apply R A A e a

private lemma exists_finiteEtale_lift
    (R L : Type u) [CommRing R] [HenselianLocalRing R]
    [Field L] [Algebra (IsLocalRing.ResidueField R) L]
    [FiniteDimensional (IsLocalRing.ResidueField R) L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) L] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
      (_ : Algebra.Etale R A),
      Nonempty ((IsLocalRing.ResidueField R ⊗[R] A) ≃ₐ[IsLocalRing.ResidueField R] L) := by
  have : Algebra.FormallyEtale (IsLocalRing.ResidueField R) L :=
    Algebra.FormallyEtale.of_isSeparable _ _
  have : Algebra.FinitePresentation (IsLocalRing.ResidueField R) L :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale (IsLocalRing.ResidueField R) L := ⟨inferInstance, inferInstance⟩
  let E := CommAlgCat.FiniteEtale.baseChange R (IsLocalRing.ResidueField R)
  let L' := CommAlgCat.FiniteEtale.of (IsLocalRing.ResidueField R) L
  let A := E.objPreimage L'
  exact ⟨A.obj, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨CommAlgCat.algEquivOfIso
      ((CommAlgCat.finiteEtale (IsLocalRing.ResidueField R)).ι.mapIso (E.objObjPreimageIso L'))⟩⟩

private lemma exists_galois_finiteEtale_extension
    (R A K : Type u) [CommRing R] [HenselianLocalRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    [FiniteDimensional (IsLocalRing.ResidueField R) K]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) K]
    (e : (IsLocalRing.ResidueField R ⊗[R] A) ≃ₐ[IsLocalRing.ResidueField R] K) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B)
      (_ : Module.Finite R B) (_ : Algebra.Etale R B)
      (L : Type u) (_ : Field L)
      (_ : Algebra (IsLocalRing.ResidueField R) L)
      (_ : FiniteDimensional (IsLocalRing.ResidueField R) L)
      (_ : IsGalois (IsLocalRing.ResidueField R) L),
      Nonempty ((IsLocalRing.ResidueField R ⊗[R] B) ≃ₐ[IsLocalRing.ResidueField R] L) ∧
        Nonempty (A →ₐ[R] B) := by
  have hfd : FiniteDimensional (IsLocalRing.ResidueField R)
      (NormalClosure (IsLocalRing.ResidueField R) K) :=
    IsNormalClosure.finiteDimensional (IsLocalRing.ResidueField R) K
      (NormalClosure (IsLocalRing.ResidueField R) K)
  obtain ⟨B, _, _, _, _, ⟨eB⟩⟩ :=
    @exists_finiteEtale_lift R (NormalClosure (IsLocalRing.ResidueField R) K)
      _ _ _ _ hfd _
  let h : (IsLocalRing.ResidueField R ⊗[R] A) →ₐ[IsLocalRing.ResidueField R]
      (IsLocalRing.ResidueField R ⊗[R] B) :=
    eB.symm.toAlgHom.comp ((IsScalarTower.toAlgHom (IsLocalRing.ResidueField R) K
      (NormalClosure (IsLocalRing.ResidueField R) K)).comp e.toAlgHom)
  obtain ⟨g, _⟩ := exists_lift_residue_algHom R A B h
  exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    NormalClosure (IsLocalRing.ResidueField R) K, inferInstance, inferInstance, hfd,
    inferInstance, ⟨⟨eB⟩, ⟨g⟩⟩⟩

private lemma residue_tensor_mk_surjective
    (R A : Type*) [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A] :
    Function.Surjective (fun a : A ↦ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] a) :=
  TensorProduct.mk_surjective R A (IsLocalRing.ResidueField R)
    IsLocalRing.residue_surjective

private lemma pi_mem_smul_top_of_mem
    {A ι : Type*} [CommRing A] [Finite ι] (I : Ideal A) (x : ι → A)
    (hx : ∀ i, x i ∈ I) : x ∈ I • (⊤ : Submodule A (ι → A)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rw [← Finset.univ_sum_single x]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  convert Submodule.smul_mem_smul (hx i)
    (show Pi.single i (1 : A) ∈ (⊤ : Submodule A (ι → A)) from trivial) using 1
  ext j
  by_cases hij : i = j
  · subst j
    simp
  · simp [Pi.single_eq_of_ne (Ne.symm hij)]

private lemma surjective_pi_of_surjective_mod_jacobson
    {A L M ι : Type*} [CommRing A] [CommRing L] [AddCommGroup M] [Module A M]
    [Finite ι] (q : A →+* L) (hJ : RingHom.ker q ≤ Ideal.jacobson (⊥ : Ideal A))
    (f : M →ₗ[A] (ι → A))
    (hf : ∀ y : ι → L, ∃ m : M, ∀ i, q (f m i) = y i) :
    Function.Surjective f := by
  apply f.surjective_of_surjective_comp_mkQ (RingHom.ker q) hJ
  intro y
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨m, hm⟩ := hf (fun i ↦ q (z i))
  refine ⟨m, (Submodule.Quotient.eq _).mpr (pi_mem_smul_top_of_mem _ _ fun i ↦ ?_)⟩
  show q (f m i - z i) = 0
  rw [map_sub, hm, sub_self]

private lemma actionTensorMap_surjective_of_residue
    (R A K L : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (q : A →+* L) (hq : Function.Surjective q)
    (hJ : RingHom.ker q ≤ Ideal.jacobson (⊥ : Ideal A))
    (ρ : (L ≃ₐ[K] L) →* (A ≃ₐ[R] A))
    (hρ : ∀ σ a, q (ρ σ a) = σ (q a)) :
    Function.Surjective (actionTensorMap R A ρ) := by
  classical
  apply surjective_pi_of_surjective_mod_jacobson q hJ
  intro y
  obtain ⟨t, ht⟩ := actionTensorMap_id_surjective K L y
  obtain ⟨n, a, b, rfl⟩ := TensorProduct.exists_sum_tmul_eq t
  choose a' ha using fun i ↦ hq (a i)
  choose b' hb using fun i ↦ hq (b i)
  refine ⟨∑ i, a' i ⊗ₜ[R] b' i, fun σ ↦ ?_⟩
  show q (actionTensorMap R A ρ (∑ i, a' i ⊗ₜ[R] b' i) σ) = y σ
  simpa only [map_sum, Finset.sum_apply, actionTensorMap_tmul, map_mul, hρ, ha, hb,
    MonoidHom.id_apply] using congrFun ht σ

private lemma actionTensorMap_bijective_of_residue
    (R A K L : Type*) [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Flat R A]
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (q : A →+* L) (hq : Function.Surjective q)
    (hJ : RingHom.ker q ≤ Ideal.jacobson (⊥ : Ideal A))
    (ρ : (L ≃ₐ[K] L) →* (A ≃ₐ[R] A))
    (hρ : ∀ σ a, q (ρ σ a) = σ (q a))
    (hdim : Module.finrank R A = Module.finrank K L) :
    Function.Bijective (actionTensorMap R A ρ) := by
  classical
  have : Nontrivial A := q.domain_nontrivial
  have : Module.Free R A := Module.free_of_flat_of_isLocalRing
  apply OrzechProperty.bijective_of_surjective_of_finrank_le
    (actionTensorMap R A ρ).toLinearMap
    (actionTensorMap_surjective_of_residue R A K L q hq hJ ρ hρ)
  rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card, hdim,
    ← IsGalois.card_aut_eq_finrank K L, Nat.card_eq_fintype_card]

private noncomputable def residueLiftMap
    (R A L : Type*) [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A]
    [CommRing L] [Algebra (IsLocalRing.ResidueField R) L]
    (e : (IsLocalRing.ResidueField R ⊗[R] A) ≃ₐ[IsLocalRing.ResidueField R] L) :
    A →+* L := e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom

private lemma residueLiftMap_ker
    (R A L : Type*) [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A]
    [CommRing L] [Algebra (IsLocalRing.ResidueField R) L]
    (e : (IsLocalRing.ResidueField R ⊗[R] A) ≃ₐ[IsLocalRing.ResidueField R] L) :
    RingHom.ker (residueLiftMap R A L e) =
      (IsLocalRing.maximalIdeal R).map (algebraMap R A) := by
  ext a
  show e ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] a) = 0 ↔ _
  rw [map_eq_zero_iff e e.injective]
  show ((1 : R ⧸ IsLocalRing.maximalIdeal R) ⊗ₜ[R] a) = 0 ↔ _
  rw [← Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk A (IsLocalRing.maximalIdeal R)]
  exact (map_eq_zero_iff _ (AlgEquiv.injective _)).trans (Ideal.Quotient.eq_zero_iff_mem)

private noncomputable def liftedResidueAction
    (R A L : Type u) [CommRing R] [HenselianLocalRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A]
    [CommRing L] [Algebra (IsLocalRing.ResidueField R) L]
    (e : (IsLocalRing.ResidueField R ⊗[R] A) ≃ₐ[IsLocalRing.ResidueField R] L) :
    (L ≃ₐ[IsLocalRing.ResidueField R] L) →* (A ≃ₐ[R] A) :=
  (residueAutLift R A).comp e.symm.autCongr.toMonoidHom

private lemma liftedResidueAction_apply
    (R A L : Type u) [CommRing R] [HenselianLocalRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A]
    [CommRing L] [Algebra (IsLocalRing.ResidueField R) L]
    (e : (IsLocalRing.ResidueField R ⊗[R] A) ≃ₐ[IsLocalRing.ResidueField R] L)
    (σ : L ≃ₐ[IsLocalRing.ResidueField R] L) (a : A) :
    residueLiftMap R A L e (liftedResidueAction R A L e σ a) =
      σ (residueLiftMap R A L e a) := by
  show e ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R]
    residueAutLift R A (e.symm.autCongr σ) a) = σ (e (1 ⊗ₜ[R] a))
  rw [residueAutLift_apply]
  simp [AlgEquiv.autCongr]

private lemma liftedResidueAction_tensorMap_bijective
    (R A L : Type u) [CommRing R] [HenselianLocalRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A]
    [Field L] [Algebra (IsLocalRing.ResidueField R) L]
    [FiniteDimensional (IsLocalRing.ResidueField R) L]
    [IsGalois (IsLocalRing.ResidueField R) L]
    (e : (IsLocalRing.ResidueField R ⊗[R] A) ≃ₐ[IsLocalRing.ResidueField R] L) :
    Function.Bijective (actionTensorMap R A (liftedResidueAction R A L e)) := by
  have : Module.Free R A := Module.free_of_flat_of_isLocalRing
  apply actionTensorMap_bijective_of_residue R A (IsLocalRing.ResidueField R) L
    (residueLiftMap R A L e)
  · exact e.surjective.comp (residue_tensor_mk_surjective R A)
  · rw [residueLiftMap_ker]
    exact map_maximalIdeal_le_jacobson R A
  · exact liftedResidueAction_apply R A L e
  · rw [← e.toLinearEquiv.finrank_eq, Module.finrank_baseChange]

@[instance_reducible] private def sectionRingAction
    {C : Type w} [Category.{v} C] (A : Cᵒᵖ ⥤ RingCat.{u})
    {G : Type*} [Group G] {X : Cᵒᵖ} (a : G →* Aut X) :
    MulSemiringAction G (A.obj X) where
  smul g x := A.map (a g).hom x
  one_smul x := by
    change A.map (a 1).hom x = x
    rw [a.map_one]
    change A.map (𝟙 X) x = x
    rw [A.map_id]
    rfl
  mul_smul g h x := by
    change A.map (a (g * h)).hom x = _
    rw [a.map_mul]
    exact Functor.map_comp_apply A (a h).hom (a g).hom x
  smul_zero g := map_zero (A.map (a g).hom).hom
  smul_add g x y := map_add (A.map (a g).hom).hom x y
  smul_one g := map_one (A.map (a g).hom).hom
  smul_mul g x y := map_mul (A.map (a g).hom).hom x y

@[instance_reducible] private noncomputable def sectionModuleAction
    {C : Type w} [Category.{v} C] (A : Cᵒᵖ ⥤ RingCat.{u})
    (P : PresheafOfModules.{u} A)
    {G : Type*} [Group G] {X : Cᵒᵖ} (a : G →* Aut X) :
    DistribMulAction G (P.obj X) where
  smul g x := P.map (a g).hom x
  one_smul x := by
    change P.map (a 1).hom x = x
    rw [a.map_one]
    change P.map (𝟙 X) x = x
    rw [P.map_id]
    rfl
  mul_smul g h x := by
    change P.map (a (g * h)).hom x = _
    rw [a.map_mul]
    exact P.map_comp_apply (a h).hom (a g).hom x
  smul_zero g := map_zero (P.map (a g).hom).hom
  smul_add g x y := map_add (P.map (a g).hom).hom x y

private lemma sectionAction_smulDistribClass
    {C : Type w} [Category.{v} C] (A : Cᵒᵖ ⥤ RingCat.{u})
    (P : PresheafOfModules.{u} A)
    {G : Type*} [Group G] {X : Cᵒᵖ} (a : G →* Aut X) :
    letI := sectionRingAction A a
    letI := sectionModuleAction A P a
    SMulDistribClass G (A.obj X) (P.obj X) := by
  let := sectionRingAction A a
  let := sectionModuleAction A P a
  exact ⟨fun g r m ↦ P.map_smul (a g).hom r m⟩

private lemma smul_sum_smul_orbit
    {G A M : Type*} [Group G] [Fintype G] [Semiring A]
    [AddCommMonoid M] [Module A M] [MulSemiringAction G A]
    [DistribMulAction G M] [SMulDistribClass G A M]
    (g : G) (a : A) (m : M) :
    g • (∑ h : G, (h • a) • (h • m)) = ∑ h : G, (h • a) • (h • m) := by
  simp_rw [Finset.smul_sum, smul_distrib_smul, ← mul_smul]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ ↦ rfl)

private lemma exists_fixedPoints_sum_eq
    {G A M : Type*} [Group G] [Finite G] [DecidableEq G] [Semiring A]
    [AddCommMonoid M] [Module A M] [MulSemiringAction G A]
    [DistribMulAction G M] [SMulDistribClass G A M]
    {ι : Type*} [Fintype ι] (a b : ι → A)
    (h : ∀ g : G, ∑ i, a i * (g • b i) = if g = 1 then 1 else 0) (m : M) :
    ∃ y : ι → M, (∀ (i : ι) (g : G), g • y i = y i) ∧ ∑ i, a i • y i = m := by
  classical
  let : Fintype G := Fintype.ofFinite G
  refine ⟨fun i ↦ ∑ g : G, (g • b i) • (g • m),
    fun i g ↦ smul_sum_smul_orbit g (b i) m, ?_⟩
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, h]
  simp

private lemma existsUnique_section_of_invariant
    {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
    (F : Sheaf J (Type u)) {X S : C} (f : X ⟶ S) [HasPullback f f]
    (hf : Sieve.generate (Presieve.singleton f) ∈ J S)
    {ι : Type*} (a : ι → (X ⟶ X)) (ha : ∀ i, a i ≫ f = f)
    (hg : Sieve.ofArrows (fun _ : ι ↦ X)
      (fun i ↦ pullback.lift (𝟙 X) (a i) (by simp [ha i])) ∈ J (pullback f f))
    (x : F.obj.obj (op X)) (hx : ∀ i, F.obj.map (a i).op x = x) :
    ∃! y, F.obj.map f.op y = x := by
  have hF := (isSheaf_iff_isSheaf_of_type J F.obj).mp F.property
  apply (Presieve.isSheafFor_singleton).mp
    ((Presieve.isSheafFor_iff_generate _).mpr (hF _ hf)) x
  intro Z p q hpq
  have hpx : F.obj.map (pullback.fst f f).op x =
      F.obj.map (pullback.snd f f).op x := by
    apply ((Presieve.isSheafFor_iff_generate _).mpr (hF _ hg)).isSeparatedFor.ext
    rintro Y k ⟨i⟩
    simp only [← Functor.map_comp_apply, ← op_comp,
      pullback.lift_fst, pullback.lift_snd, op_id]
    rw [F.obj.map_id]
    exact (hx i).symm
  simpa only [← Functor.map_comp_apply, ← op_comp,
    pullback.lift_fst, pullback.lift_snd] using
    congrArg (F.obj.map (pullback.lift p q hpq).op) hpx

private lemma small_sections_of_hasTerminal
    {C : Type w} [Category.{v} C] [HasTerminal C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    (F : SheafOfModules.{u} R) : Small.{u} F.sections := by
  refine small_of_injective (f := fun s : F.sections ↦ s.val (op (⊤_ C))) fun s t h ↦ ?_
  refine PresheafOfModules.sections_ext _ _ fun X ↦ ?_
  rw [← s.property (terminal.from X.unop).op,
    ← t.property (terminal.from X.unop).op]
  exact congrArg (F.val.map (terminal.from X.unop).op) h

private lemma range_restriction_subset_range_sections
    {C : Type w} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (P : PresheafOfModules.{u} R) {T X : C} (hT : IsTerminal T) (f : X ⟶ T) :
    Set.range (P.map f.op) ⊆ Set.range (fun s : P.sections ↦ s.val (op X)) := by
  rintro _ ⟨m, rfl⟩
  let s : P.sections := PresheafOfModules.sectionsMk
    (fun V ↦ P.map (hT.from V.unop).op m) (by
      intro V W a
      rw [← P.map_comp_apply]
      exact P.congr_map_apply (Quiver.Hom.unop_inj (hT.hom_ext _ _)) m)
  exact ⟨s, P.congr_map_apply (congrArg Quiver.Hom.op (hT.hom_ext _ _)) m⟩

private noncomputable def generatingSections_of_isSeparator
    {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (h : IsSeparator (SheafOfModules.unit R))
    (F : SheafOfModules.{u} R) [Small.{u} F.sections] : F.GeneratingSections where
  I := Shrink.{u} F.sections
  s := (equivShrink F.sections).symm
  epi := by
    refine ⟨fun {N} f g hfg ↦ h.def f g fun k ↦ ?_⟩
    let i : Shrink.{u} F.sections := equivShrink F.sections (F.unitHomEquiv k)
    have hi := congrArg (fun q ↦ N.freeHomEquiv q i) hfg
    simp only [SheafOfModules.freeHomEquiv_comp_apply, Equiv.apply_symm_apply] at hi
    rw [show (equivShrink F.sections).symm i = F.unitHomEquiv k from
      Equiv.symm_apply_apply _ _] at hi
    exact N.unitHomEquiv.injective hi

private noncomputable def presentation_of_isSeparator
    {C : Type w} [Category.{v} C] [HasTerminal C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (h : IsSeparator (SheafOfModules.unit R))
    (F : SheafOfModules.{u} R) : F.Presentation := by
  have := small_sections_of_hasTerminal F
  let gen := generatingSections_of_isSeparator h F
  have := small_sections_of_hasTerminal (kernel gen.π)
  exact ⟨gen, generatingSections_of_isSeparator h (kernel gen.π)⟩

/-- Every slice of the small étale site of `S` is essentially `u`-small, the site itself
being so. -/
public instance essentiallySmallOverSmallEtale (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicGeometry.SmallEtale B S hS) :
    EssentiallySmall.{u} (Over X) :=
  CostructuredArrow.essentiallySmall (S := 𝟭 (AlgebraicGeometry.SmallEtale B S hS)) (T := X)

/-- Abelian presheaves on a slice of the small étale site of `S` have a sheafification. -/
public instance hasWeakSheafifyOverSmallEtale (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicGeometry.SmallEtale B S hS) :
    HasWeakSheafify ((AlgebraicGeometry.SmallEtale.topology B S hS).over X)
      AddCommGrpCat.{u} :=
  have : HasSheafify ((AlgebraicGeometry.SmallEtale.topology B S hS).over X)
      AddCommGrpCat.{u} := hasSheafifyEssentiallySmallSite.{u} _ _
  inferInstance

/-- Weak equivalences of abelian presheaves on a slice of the small étale site of `S` are the
locally bijective maps. -/
public instance wEqualsLocallyBijectiveOverSmallEtale (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicGeometry.SmallEtale B S hS) :
    ((AlgebraicGeometry.SmallEtale.topology B S hS).over X).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

private lemma isQuasicoherent_of_isSeparator_over_terminal
    {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {T : C} (hT : IsTerminal T)
    (h : IsSeparator (SheafOfModules.unit (R.over T)))
    (F : SheafOfModules.{u} R) : F.IsQuasicoherent := by
  apply SheafOfModules.QuasicoherentData.isQuasicoherent
  refine {
    I := PUnit.{1}
    X := fun _ ↦ T
    coversTop := fun _ ↦ J.covering_of_eq_top (top_unique fun V _ _ ↦ ⟨PUnit.unit, ⟨hT.from V⟩⟩)
    presentation := fun _ ↦ presentation_of_isSeparator h (F.over T) }

private lemma ringKrullDimLE_zero_of_eq_zero (R : Type u) [CommRing R]
    (hdim : ringKrullDim R = 0) : Ring.KrullDimLE 0 R :=
  Ring.krullDimLE_iff.mpr (by rw [hdim]; norm_num)

private lemma baseSpectrum_subsingleton (R : Type u) [CommRing R] [IsLocalRing R]
    (hdim : ringKrullDim R = 0) : Subsingleton (PrimeSpectrum R) :=
  have := ringKrullDimLE_zero_of_eq_zero R hdim
  Ring.KrullDimLE.subsingleton_primeSpectrum R

private lemma henselian_of_ringKrullDim_eq_zero (R : Type u) [CommRing R]
    [IsLocalRing R] (hdim : ringKrullDim R = 0) : HenselianLocalRing R :=
  have := ringKrullDimLE_zero_of_eq_zero R hdim
  henselianLocalRing_of_krullDimLE_zero R

private lemma discreteTopology_of_locallyQuasiFinite
    {X S : Scheme.{u}} [DiscreteTopology S] (f : X ⟶ S) [LocallyQuasiFinite f] :
    DiscreteTopology X := by
  apply isDiscrete_univ_iff.mp
  simpa using f.isDiscrete_preimage (s := Set.univ) (isDiscrete_univ_iff.mpr inferInstance)

private lemma locallyQuasiFinite_of_etale
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] : LocallyQuasiFinite f := by
  rw [locallyQuasiFinite_iff]
  intro U hU V hV e
  have hφ : (f.appLE U V e).hom.Etale := f.etale_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  exact Algebra.IsUnramifiedAt.instQuasiFiniteOfEssFiniteTypeOfFormallyUnramified

private lemma smallEtale_discreteTopology
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hdim : ringKrullDim R = 0)
    (B : BigEtaleSite.{u}) (hS : B.Contains (Spec (.of R)))
    (U : AlgebraicGeometry.SmallEtale B (Spec (.of R)) hS) :
    DiscreteTopology ((AlgebraicGeometry.SmallEtale.toScheme B (Spec (.of R)) hS).obj U) := by
  have : Subsingleton (Spec (.of R)) := baseSpectrum_subsingleton R hdim
  let f : ((AlgebraicGeometry.SmallEtale.toScheme B (Spec (.of R)) hS).obj U) ⟶
      Spec (.of R) := B.inclusion.map U.obj.hom
  have : Etale f := U.property
  have : LocallyQuasiFinite f := locallyQuasiFinite_of_etale f
  exact discreteTopology_of_locallyQuasiFinite f

private lemma finite_of_quasiFinite_of_krullDimLE_zero
    (R : Type u) [CommRing R] [IsLocalRing R] [Ring.KrullDimLE 0 R]
    (S : Type u) [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] : Module.Finite R S := by
  have : HenselianLocalRing R := henselianLocalRing_of_krullDimLE_zero R
  obtain ⟨A, _, _, T, _, _, hA, hT, ⟨e⟩⟩ := exists_prod_finite_not_quasiFiniteAt R S
  have hsurj : Function.Surjective ((AlgHom.snd R A T).comp e.toAlgHom) :=
    fun t ↦ ⟨e.symm (0, t), by simp⟩
  have : Algebra.QuasiFinite R T :=
    Algebra.QuasiFinite.of_surjective_algHom _ hsurj
  have : Subsingleton T := by
    by_contra h
    have : Nontrivial T := not_subsingleton_iff_nontrivial.mp h
    obtain ⟨q, hq⟩ := Ideal.exists_maximal T
    have := hq.isPrime
    have hqR : q.LiesOver (IsLocalRing.maximalIdeal R) :=
      ⟨(Ring.KrullDimLE.eq_maximalIdeal_of_isPrime (q.under R)).symm⟩
    exact hT q hqR inferInstance
  exact Module.Finite.equiv e.symm.toLinearEquiv

private lemma finite_appTop_of_etale_of_affine
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hdim : ringKrullDim R = 0)
    {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of R)) [Etale f] : (f.appTop).hom.Finite := by
  let O := Γ(Spec (.of R), ⊤)
  let A := Γ(X, ⊤)
  let e : O ≃+* R := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  have : IsLocalRing O := e.symm.isLocalRing
  have : Ring.KrullDimLE 0 O := ringKrullDimLE_zero_of_eq_zero O (by rw [e.ringKrullDim, hdim])
  let : Algebra O A := (f.appTop).hom.toAlgebra
  have he : (f.appTop).hom.Etale :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp inferInstance
  have : Algebra.Etale O A := he
  have : Algebra.QuasiFinite O A := RingHom.Etale.quasiFinite (f.appTop).hom he
  exact finite_of_quasiFinite_of_krullDimLE_zero O A

private lemma finiteEtale_globalSections_of_affine
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hdim : ringKrullDim R = 0)
    {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of R)) [Etale f] :
    let φ : R →+* Γ(X, ⊤) :=
      (f.appTop).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    φ.Finite ∧ φ.Etale := by
  have hfinite : (f.appTop).hom.Finite := finite_appTop_of_etale_of_affine R hdim f
  have hetale : (f.appTop).hom.Etale :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp inferInstance
  let e := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm
  have hefinite : ((Scheme.ΓSpecIso (.of R)).inv.hom).Finite := e.finite
  have heetale : ((Scheme.ΓSpecIso (.of R)).inv.hom).Etale :=
    RingHom.Etale.of_bijective e.bijective
  exact ⟨hfinite.comp hefinite, RingHom.Etale.stableUnderComposition _ _ heetale hetale⟩

/-- A finite étale algebra determines an object of the chosen small étale site. -/
private noncomputable def finiteEtaleSpec
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A]
    (B : BigEtaleSite.{u}) (hS : B.Contains (Spec (.of R))) :
    AlgebraicGeometry.SmallEtale B (Spec (.of R)) hS := by
  let f : Spec (.of A) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R A))
  have : Etale f := by
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    exact HasRingHomProperty.Spec_iff.mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  have : IsFinite f := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    exact (IsFinite.SpecMap_iff
      (CommRingCat.ofHom (algebraMap R A))).mpr
      (RingHom.finite_algebraMap.mpr inferInstance)
  let hA : B.Contains (Spec (.of A)) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact f hS
  let g : B.obj (Spec (.of A)) hA ⟶ B.obj (Spec (.of R)) hS :=
    ObjectProperty.homMk f
  refine ⟨Over.mk g, ?_⟩
  change Etale f
  infer_instance

/-- An algebra map induces the corresponding arrow in the small étale site. -/
private noncomputable def finiteEtaleSpecMap
    (R A T : Type u) [CommRing R] [CommRing A] [CommRing T]
    [Algebra R A] [Algebra R T]
    [Module.Finite R A] [Algebra.Etale R A]
    [Module.Finite R T] [Algebra.Etale R T]
    (B : BigEtaleSite.{u}) (hS : B.Contains (Spec (.of R)))
    (φ : A →ₐ[R] T) :
    finiteEtaleSpec R T B hS ⟶ finiteEtaleSpec R A B hS := by
  let p : (finiteEtaleSpec R T B hS).obj.left ⟶
      (finiteEtaleSpec R A B hS).obj.left :=
    ObjectProperty.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom))
  apply ObjectProperty.homMk
  refine Over.homMk p ?_
  apply B.inclusion.map_injective
  change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) =
    Spec.map (CommRingCat.ofHom (algebraMap R T))
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact φ.commutes r

private lemma finiteEtaleSpecMap_id
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A]
    (B : BigEtaleSite.{u}) (hS : B.Contains (Spec (.of R))) :
    finiteEtaleSpecMap R A A B hS (AlgHom.id R A) = 𝟙 _ := by
  apply (AlgebraicGeometry.SmallEtale.toScheme B (Spec (.of R)) hS).map_injective
  show Spec.map (𝟙 (.of A)) = 𝟙 _
  exact Spec.map_id _

private lemma finiteEtaleSpecMap_comp
    (R A D E : Type u) [CommRing R] [CommRing A] [CommRing D] [CommRing E]
    [Algebra R A] [Algebra R D] [Algebra R E]
    [Module.Finite R A] [Algebra.Etale R A]
    [Module.Finite R D] [Algebra.Etale R D]
    [Module.Finite R E] [Algebra.Etale R E]
    (B : BigEtaleSite.{u}) (hS : B.Contains (Spec (.of R)))
    (f : A →ₐ[R] D) (g : D →ₐ[R] E) :
    finiteEtaleSpecMap R D E B hS g ≫ finiteEtaleSpecMap R A D B hS f =
      finiteEtaleSpecMap R A E B hS (g.comp f) := by
  apply (AlgebraicGeometry.SmallEtale.toScheme B (Spec (.of R)) hS).map_injective
  show Spec.map (CommRingCat.ofHom g.toRingHom) ≫
    Spec.map (CommRingCat.ofHom f.toRingHom) = _
  exact (Spec.map_comp _ _).symm

private noncomputable def finiteEtaleSpecAction
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A]
    (B : BigEtaleSite.{u}) (hS : B.Contains (Spec (.of R)))
    {G : Type*} [Group G] (ρ : G →* (A ≃ₐ[R] A)) :
    G →* Aut (op (finiteEtaleSpec R A B hS)) where
  toFun g := {
    hom := (finiteEtaleSpecMap R A A B hS (ρ g).toAlgHom).op
    inv := (finiteEtaleSpecMap R A A B hS (ρ g).symm.toAlgHom).op
    hom_inv_id := by
      rw [← op_comp, finiteEtaleSpecMap_comp,
        show (ρ g).symm.toAlgHom.comp (ρ g).toAlgHom = AlgHom.id R A by ext; simp,
        finiteEtaleSpecMap_id]
      rfl
    inv_hom_id := by
      rw [← op_comp, finiteEtaleSpecMap_comp,
        show (ρ g).toAlgHom.comp (ρ g).symm.toAlgHom = AlgHom.id R A by ext; simp,
        finiteEtaleSpecMap_id]
      rfl }
  map_one' := by
    apply Iso.ext
    change (finiteEtaleSpecMap R A A B hS (ρ 1).toAlgHom).op = 𝟙 _
    rw [ρ.map_one]
    change (finiteEtaleSpecMap R A A B hS (AlgHom.id R A)).op = _
    rw [finiteEtaleSpecMap_id]
    rfl
  map_mul' g h := by
    apply Iso.ext
    change (finiteEtaleSpecMap R A A B hS (ρ (g * h)).toAlgHom).op =
      (finiteEtaleSpecMap R A A B hS (ρ h).toAlgHom).op ≫
        (finiteEtaleSpecMap R A A B hS (ρ g).toAlgHom).op
    rw [← op_comp, finiteEtaleSpecMap_comp, ρ.map_mul]
    rfl

private lemma exists_galois_graph_point
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    {G : Type u} [Group G] [Finite G] (ρ : G →* (A ≃ₐ[R] A))
    (hc : Function.Bijective (actionTensorMap R A ρ))
    (x : ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))))) :
    ∃ (g : G) (y : Spec (.of A)),
      (pullback.lift (𝟙 (Spec (.of A)))
        (Spec.map (CommRingCat.ofHom (ρ g).toRingHom))
        (by rw [Category.id_comp, ← Spec.map_comp]; congr 1; ext r
            exact ((ρ g).commutes r).symm)) y = x := by
  let e := pullbackSpecIso R A A
  obtain ⟨q, hq⟩ :=
    (PrimeSpectrum.isHomeomorph_comap_of_bijective hc).surjective (e.hom x)
  obtain ⟨⟨g, y⟩, rfl⟩ := (PrimeSpectrum.sigmaToPi_bijective (fun _ : G ↦ A)).2 q
  refine ⟨g, y, ?_⟩
  apply e.hom.homeomorph.injective
  have heq : pullback.lift (𝟙 (Spec (.of A)))
      (Spec.map (CommRingCat.ofHom (ρ g).toRingHom))
      (by
        rw [Category.id_comp, ← Spec.map_comp]
        congr 1
        ext r
        exact ((ρ g).commutes r).symm) ≫ e.hom =
      Spec.map (CommRingCat.ofHom ((Pi.evalRingHom (fun _ : G ↦ A) g).comp
        (actionTensorMap R A ρ).toRingHom)) := by
    apply (cancel_mono e.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, Category.assoc, e, pullbackSpecIso_inv_fst,
        ← Spec.map_comp]
      rw [← Spec.map_id (.of A)]
      congr 1
      ext a
      show a = a * ρ g 1
      simp
    · simp only [pullback.lift_snd, Category.assoc, e, pullbackSpecIso_inv_snd,
        ← Spec.map_comp]
      congr 1
      ext a
      show ρ g a = 1 * ρ g a
      simp
  exact (congrArg (fun k : Spec (.of A) ⟶ Spec (.of (A ⊗[R] A)) ↦ k y) heq).trans hq

private lemma smallEtale_generate_mem_of_etaleCovering
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.SmallEtale B S hS)
    {I : Type (u + 1)} (V : I → AlgebraicGeometry.SmallEtale B S hS)
    (f : ∀ i, V i ⟶ T)
    (h : Presieve.ofArrows
      (fun i ↦ (AlgebraicGeometry.SmallEtale.toScheme B S hS).obj (V i))
      (fun i ↦ (AlgebraicGeometry.SmallEtale.toScheme B S hS).map (f i)) ∈
        Scheme.etalePrecoverage
          ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj T)) :
    Sieve.ofArrows V f ∈ AlgebraicGeometry.SmallEtale.topology B S hS T := by
  let K := AlgebraicGeometry.SmallEtale.inclusion B S hS ⋙
    AlgebraicGeometry.BigEtaleOver.forget B S hS
  let T₀ := K.obj T
  let E : PreZeroHypercover.{u + 1} T₀ :=
    ⟨I, fun i ↦ K.obj (V i), fun i ↦ K.map (f i)⟩
  have hE : IsEtaleCovering ⟨T₀, E⟩ := by
    simpa [IsEtaleCovering, PreZeroHypercover.presieve₀_map,
      PreZeroHypercover.presieve₀, PreZeroHypercover.map, K, E,
      AlgebraicGeometry.SmallEtale.toScheme, AlgebraicGeometry.BigEtaleOver.toScheme, T₀] using h
  obtain ⟨⟨Wtarget, Wfamily⟩, hW, hTarget, hCE⟩ := B.exists_covering_rep ⟨T₀, E⟩ hE
  change T₀ = Wtarget at hTarget
  cases hTarget
  obtain ⟨β, hβsrc, hβeq⟩ := hCE.2
  let Wsmall : PreZeroHypercover T :=
    ⟨Wfamily.I₀, fun j ↦ V (β j), fun j ↦ f (β j)⟩
  have hmap : Wsmall.map K = Wfamily := by
    refine PreZeroHypercover.ext rfl ?_ ?_
    · exact Function.hfunext rfl fun j j' hj ↦ by
        cases eq_of_heq hj
        show E.X (β j) ≍ Wfamily.X j
        exact heq_of_eq (hβsrc j).symm
    · exact Function.hfunext rfl fun j j' hj ↦ by
        cases eq_of_heq hj
        show E.f (β j) ≍ Wfamily.f j
        exact ((heq_of_eq (hβeq j)).trans
          (CategoryTheory.eqToHom_comp_heq _ _)).symm
  have hmap' :
      (Wsmall.map (AlgebraicGeometry.SmallEtale.inclusion B S hS)).map
        (AlgebraicGeometry.BigEtaleOver.forget B S hS) = Wfamily := by
    simpa [PreZeroHypercover.map, K] using hmap
  have hWsite : Sieve.ofArrows Wsmall.X Wsmall.f ∈
      AlgebraicGeometry.SmallEtale.topology B S hS T := by
    apply Precoverage.generate_mem_toGrothendieck
    refine ⟨Wsmall, rfl, ?_⟩
    show B.IsCovering ⟨T₀,
      (Wsmall.map (AlgebraicGeometry.SmallEtale.inclusion B S hS)).map
        (AlgebraicGeometry.BigEtaleOver.forget B S hS)⟩
    rwa [hmap']
  apply (AlgebraicGeometry.SmallEtale.topology B S hS).superset_covering ?_ hWsite
  intro Y g hg
  obtain ⟨j, a, rfl⟩ := (Sieve.mem_ofArrows_iff Wsmall.X Wsmall.f g).1 hg
  exact (Sieve.mem_ofArrows_iff V f (a ≫ f (β j))).2 ⟨β j, a, rfl⟩

private lemma smallEtale_exists_onePoint_cover
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hdim : ringKrullDim R = 0)
    (B : BigEtaleSite.{u}) (hS : B.Contains (Spec (.of R)))
    (T : AlgebraicGeometry.SmallEtale B (Spec (.of R)) hS) :
    ∃ (I : Type (u + 1))
      (V : I → AlgebraicGeometry.SmallEtale B (Spec (.of R)) hS)
      (f : ∀ i, V i ⟶ T),
      Sieve.ofArrows V f ∈ AlgebraicGeometry.SmallEtale.topology B (Spec (.of R)) hS T ∧
      ∀ i, Nonempty ((AlgebraicGeometry.SmallEtale.toScheme B (Spec (.of R)) hS).obj
        (V i)) ∧
        Subsingleton ((AlgebraicGeometry.SmallEtale.toScheme B (Spec (.of R)) hS).obj
          (V i)) := by
  let X := (AlgebraicGeometry.SmallEtale.toScheme B (Spec (.of R)) hS).obj T
  have : DiscreteTopology X := smallEtale_discreteTopology R hdim B hS T
  let O (x : X) : X.Opens := ⟨{x}, isOpen_discrete _⟩
  let V (i : ULift.{u + 1, u} X) :
      AlgebraicGeometry.SmallEtale B (Spec (.of R)) hS := by
    let hs : B.Contains (O i.down).toScheme :=
      Scheme.size_lt_of_isOpenImmersion (O i.down).ι T.obj.left.property
    let g : B.obj (O i.down).toScheme hs ⟶ B.obj (Spec (.of R)) hS :=
      ObjectProperty.homMk ((O i.down).ι ≫ B.inclusion.map T.obj.hom)
    refine ⟨Over.mk g, ?_⟩
    show Etale ((O i.down).ι ≫ B.inclusion.map T.obj.hom)
    infer_instance
  let f (i : ULift.{u + 1, u} X) : V i ⟶ T := by
    let hs : B.Contains (O i.down).toScheme :=
      Scheme.size_lt_of_isOpenImmersion (O i.down).ι T.obj.left.property
    let p : B.obj (O i.down).toScheme hs ⟶ T.obj.left :=
      ObjectProperty.homMk (O i.down).ι
    exact ObjectProperty.homMk
      (Over.homMk p (by
        show p ≫ T.obj.hom =
          ObjectProperty.homMk ((O i.down).ι ≫ B.inclusion.map T.obj.hom)
        rfl))
  refine ⟨_, V, f, ?_, ?_⟩
  · apply smallEtale_generate_mem_of_etaleCovering B (Spec (.of R)) hS T V f
    apply (Scheme.ofArrows_mem_precoverage_iff (@Etale)).2
    refine ⟨fun x ↦ ⟨ULift.up x, ⟨⟨x, by simp [O]⟩, rfl⟩⟩, fun i ↦ ?_⟩
    show Etale (O i.down).ι
    infer_instance
  · intro i
    constructor
    · show Nonempty (O i.down).toScheme
      exact ⟨⟨i.down, by simp [O]⟩⟩
    · show Subsingleton (O i.down).toScheme
      exact (Set.subsingleton_singleton : Set.Subsingleton ({i.down} : Set X)).coe_sort

private lemma smallEtale_ofArrows_mem_of_jointly_surjective
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y : AlgebraicGeometry.SmallEtale B S hS} {I : Type u}
    (X : I → AlgebraicGeometry.SmallEtale B S hS) (f : ∀ i, X i ⟶ Y)
    (h : ∀ y : (AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Y,
      ∃ i x, (AlgebraicGeometry.SmallEtale.toScheme B S hS).map (f i) x = y) :
    Sieve.ofArrows X f ∈ AlgebraicGeometry.SmallEtale.topology B S hS Y := by
  let P := AlgebraicGeometry.SmallEtale.toScheme B S hS
  have hc : Sieve.ofArrows (fun i : ULift.{u + 1} I ↦ X i.down)
      (fun i ↦ f i.down) ∈ AlgebraicGeometry.SmallEtale.topology B S hS Y := by
    apply smallEtale_generate_mem_of_etaleCovering
    apply (Scheme.ofArrows_mem_precoverage_iff (@Etale)).2
    refine ⟨fun y ↦ ?_, fun i ↦ ?_⟩
    · obtain ⟨i, x, hx⟩ := h y
      exact ⟨⟨i⟩, x, hx⟩
    · have heq : P.map (f i.down) ≫ B.inclusion.map Y.obj.hom =
          B.inclusion.map (X i.down).obj.hom := by
        show B.inclusion.map ((f i.down).hom.left ≫ Y.obj.hom) = _
        rw [Over.w]
      have : Etale (P.map (f i.down) ≫ B.inclusion.map Y.obj.hom) := by
        rw [heq]
        exact (X i.down).property
      exact Etale.of_comp _ (B.inclusion.map Y.obj.hom)
  apply (AlgebraicGeometry.SmallEtale.topology B S hS).superset_covering ?_ hc
  intro Z k hk
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ k).mp hk
  exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨i.down, a, rfl⟩

private lemma smallEtaleOver_ofArrows_mem_of_jointly_surjective
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.SmallEtale B S hS)
    {Y : Over T} {I : Type u} (X : I → Over T) (f : ∀ i, X i ⟶ Y)
    (h : ∀ y : (AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Y.left,
      ∃ i x, (AlgebraicGeometry.SmallEtale.toScheme B S hS).map (f i).left x = y) :
    Sieve.ofArrows X f ∈ (AlgebraicGeometry.SmallEtale.topology B S hS).over T Y := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact smallEtale_ofArrows_mem_of_jointly_surjective B S hS
    (fun i ↦ (X i).left) (fun i ↦ (f i).left) h

private lemma smallEtaleOver_generate_singleton_mem_of_surjective
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.SmallEtale B S hS)
    {Y W : Over T} (f : W ⟶ Y)
    (h : ∀ y : (AlgebraicGeometry.SmallEtale.toScheme B S hS).obj Y.left,
      ∃ x, (AlgebraicGeometry.SmallEtale.toScheme B S hS).map f.left x = y) :
    Sieve.generate (Presieve.singleton f) ∈
      (AlgebraicGeometry.SmallEtale.topology B S hS).over T Y := by
  simpa only [Sieve.ofArrows, Presieve.ofArrows_pUnit] using
    smallEtaleOver_ofArrows_mem_of_jointly_surjective B S hS T
      (fun _ : PUnit.{u + 1} ↦ W) (fun _ ↦ f) fun y ↦ ⟨PUnit.unit, h y⟩

private lemma smallEtale_toScheme_to_final
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicGeometry.SmallEtale B S hS}
    (f : X ⟶ AlgebraicGeometry.SmallEtale.final B S hS) :
    (AlgebraicGeometry.SmallEtale.toScheme B S hS).map f = B.inclusion.map X.obj.hom := by
  have h := f.hom.w
  change f.hom.left ≫ 𝟙 _ = X.obj.hom at h
  exact congrArg B.inclusion.map ((Category.comp_id _).symm.trans h)

private lemma span_eq_top_of_fixedPoints_mem
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    {G : Type*} [Group G] [Finite G] (ρ : G →* (A ≃ₐ[R] A))
    (hc : Function.Bijective (actionTensorMap R A ρ))
    {S M : Type*} [Semiring S] [MulSemiringAction G S] [AddCommMonoid M] [Module S M]
    [DistribMulAction G M] [SMulDistribClass G S M]
    (e : A ≃+* S) (he : ∀ (g : G) (b : A), g • e b = e (ρ g b))
    {X : Set M} (hX : ∀ m : M, (∀ g : G, g • m = m) → m ∈ X) :
    Submodule.span S X = ⊤ := by
  classical
  obtain ⟨t, ht⟩ := hc.2 (fun g ↦ if g = 1 then 1 else 0)
  obtain ⟨n, b, d, rfl⟩ := TensorProduct.exists_sum_tmul_eq t
  have hd (g : G) : ∑ i, e (b i) * (g • e (d i)) = if g = 1 then 1 else 0 := by
    simp_rw [he, ← map_mul, ← map_sum]
    have h := congrFun ht g
    simp only [map_sum, Finset.sum_apply, actionTensorMap_tmul] at h
    rw [h]
    split_ifs <;> simp
  refine top_unique fun m _ ↦ ?_
  obtain ⟨y, hyfix, hysum⟩ :=
    exists_fixedPoints_sum_eq (fun i ↦ e (b i)) (fun i ↦ e (d i)) hd m
  rw [← hysum]
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span (hX (y i) (hyfix i)))

private lemma span_sections_finiteEtale_galois
    (R A : Type u) [CommRing R] [CommRing A] [Nontrivial A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A] [Subsingleton (Spec (.of R))]
    (B : BigEtaleSite.{u}) (hS : B.Contains (Spec (.of R)))
    {G : Type u} [Group G] [Finite G] (ρ : G →* (A ≃ₐ[R] A))
    (hc : Function.Bijective (actionTensorMap R A ρ))
    (F : SheafOfModules.{u} ((AlgebraicGeometry.SmallEtale.structureSheaf B (Spec (.of R)) hS).over
      (AlgebraicGeometry.SmallEtale.final B (Spec (.of R)) hS))) :
    let E := Over.equivalenceOfIsTerminal
      (AlgebraicGeometry.SmallEtale.finalIsTerminal B (Spec (.of R)) hS)
    let W := E.inverse.obj (finiteEtaleSpec R A B hS)
    Submodule.span (M := F.val.obj (op W))
      (((AlgebraicGeometry.SmallEtale.structureSheaf B (Spec (.of R)) hS).over
        (AlgebraicGeometry.SmallEtale.final B (Spec (.of R)) hS)).obj.obj (op W))
      (Set.range (fun s : F.sections ↦ (s.val (op W) : F.val.obj (op W)))) = ⊤ := by
  classical
  intro E W
  let T := AlgebraicGeometry.SmallEtale.final B (Spec (.of R)) hS
  let J := (AlgebraicGeometry.SmallEtale.topology B (Spec (.of R)) hS).over T
  let P := Over.forget T ⋙ AlgebraicGeometry.SmallEtale.toScheme B (Spec (.of R)) hS
  let Q := ((AlgebraicGeometry.SmallEtale.structureSheaf B (Spec (.of R)) hS).over T).obj
  let α : G →* Aut (op W) := (E.inverse.op.mapAut (op (finiteEtaleSpec R A B hS))).comp
    (finiteEtaleSpecAction R A B hS ρ)
  let a (g : G) : W ⟶ W := (α g).hom.unop
  let f : W ⟶ Over.mk (𝟙 T) := Over.mkIdTerminal.from W
  have ha (g : G) : a g ≫ f = f := Over.mkIdTerminal.hom_ext _ _
  have hp : P.map f = Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
    smallEtale_toScheme_to_final B (Spec (.of R)) hS f.left
  have hf : Sieve.generate (Presieve.singleton f) ∈ J (Over.mk (𝟙 T)) :=
    smallEtaleOver_generate_singleton_mem_of_surjective B (Spec (.of R)) hS T f fun _ ↦
      ⟨Classical.choice (inferInstance : Nonempty (Spec (.of A))),
        (show Subsingleton (Spec (.of R)) from inferInstance).elim _ _⟩
  have hg : Sieve.ofArrows (fun _ : G ↦ W)
      (fun g ↦ pullback.lift (𝟙 W) (a g) (by simp [ha g])) ∈ J (pullback f f) := by
    apply smallEtaleOver_ofArrows_mem_of_jointly_surjective
    have hpoints : ∀ x : ↥(pullback (P.map f) (P.map f)),
        ∃ (g : G) (y : P.obj W),
          (pullback.lift (𝟙 (P.obj W)) (P.map (a g))
            (by rw [Category.id_comp, ← P.map_comp, ha])) y = x := by
      generalize_proofs hpb hcomm
      revert hpb hcomm
      rw [hp]
      exact fun _ _ ↦ exists_galois_graph_point R A ρ hc
    intro x
    obtain ⟨g, y, hy⟩ := hpoints (pullbackComparison P f f x)
    refine ⟨g, y, (pullbackComparison P f f).homeomorph.injective ?_⟩
    show (pullbackComparison P f f) (P.map _ y) = (pullbackComparison P f f) x
    rw [← Scheme.Hom.comp_apply, map_lift_pullbackComparison]
    simpa only [P.map_id] using hy
  let := sectionRingAction Q α
  let := sectionModuleAction Q F.val α
  have := sectionAction_smulDistribClass Q F.val α
  let e : A ≃+* Q.obj (op W) := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm
  have he (g : G) (b : A) : g • e b = e (ρ g b) := by
    show (Spec.map (CommRingCat.ofHom (ρ g).toRingHom)).appTop
      ((Scheme.ΓSpecIso (.of A)).inv b) = (Scheme.ΓSpecIso (.of A)).inv (ρ g b)
    exact (congrArg (fun k : CommRingCat.of A ⟶ Γ(Spec (.of A), ⊤) ↦ k b)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (ρ g).toRingHom))).symm
  let Ft : Sheaf J (Type u) := ⟨F.val.presheaf ⋙ forget AddCommGrpCat,
    Presheaf.isSheaf_comp_of_isSheaf J _ (forget AddCommGrpCat) F.isSheaf⟩
  exact span_eq_top_of_fixedPoints_mem R A ρ hc e he fun m hm ↦ by
    obtain ⟨m₀, hm₀, _⟩ := existsUnique_section_of_invariant Ft f hf a ha hg m hm
    exact range_restriction_subset_range_sections F.val Over.mkIdTerminal f ⟨m₀, hm₀⟩

private lemma isSeparator_unit_of_locally_span_sections
    {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    (hgen : ∀ (F : SheafOfModules.{u} R) (U : C) (m : F.val.obj (op U)),
      Sieve.generate (fun {V} (f : V ⟶ U) ↦
        F.val.map f.op m ∈ Submodule.span (M := F.val.obj (op V)) (R.obj.obj (op V))
          (Set.range (fun s : F.sections ↦ (s.val (op V) : F.val.obj (op V))))) ∈ J U) :
    IsSeparator (SheafOfModules.unit R) := by
  apply (isSeparator_def _).mpr
  intro F H f g hfg
  have heq (V : Cᵒᵖ) : Set.EqOn (f.val.app V).hom (g.val.app V).hom
      (Set.range (fun s : F.sections ↦ s.val V)) := by
    rintro _ ⟨s, rfl⟩
    simpa [SheafOfModules.unitHomEquiv_comp_apply, SheafOfModules.sectionsMap,
      PresheafOfModules.sectionsMap] using
      congrArg (fun q ↦ (H.unitHomEquiv q).val V) (hfg (F.unitHomEquiv.symm s))
  ext U m
  let Ht : Sheaf J (Type u) := ⟨H.val.presheaf ⋙ forget AddCommGrpCat,
    Presheaf.isSheaf_comp_of_isSheaf J _ (forget AddCommGrpCat) H.isSheaf⟩
  have hH := (isSheaf_iff_isSheaf_of_type J Ht.obj).mp Ht.property
  refine ((Presieve.isSheafFor_iff_generate _).mpr
    (hH _ (hgen F U.unop m))).isSeparatedFor.ext fun V a ha ↦ ?_
  show H.val.map a.op (f.val.app U m) = H.val.map a.op (g.val.app U m)
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  exact LinearMap.eqOn_span (heq (op V)) ha

private lemma isLocalRing_of_subsingleton_primeSpectrum
    (A : Type*) [CommRing A] [Nontrivial A] [Subsingleton (PrimeSpectrum A)] :
    IsLocalRing A := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal A
  exact IsLocalRing.of_unique_max_ideal ⟨I, hI, fun J hJ ↦ (congrArg PrimeSpectrum.asIdeal
    (Subsingleton.elim (⟨I, hI.isPrime⟩ : PrimeSpectrum A) ⟨J, hJ.isPrime⟩)).symm⟩

private lemma exists_galois_finiteEtale_extension_of_isLocalRing
    (R A : Type u) [CommRing R] [HenselianLocalRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A] [IsLocalRing A] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B)
      (_ : Module.Finite R B) (_ : Algebra.Etale R B)
      (L : Type u) (_ : Field L)
      (_ : Algebra (IsLocalRing.ResidueField R) L)
      (_ : FiniteDimensional (IsLocalRing.ResidueField R) L)
      (_ : IsGalois (IsLocalRing.ResidueField R) L),
      Nonempty ((IsLocalRing.ResidueField R ⊗[R] B) ≃ₐ[IsLocalRing.ResidueField R] L) ∧
        Nonempty (A →ₐ[R] B) := by
  have : IsLocalHom (algebraMap R A) := by
    have hm : ((IsLocalRing.maximalIdeal A).comap (algebraMap R A)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
    exact ((IsLocalRing.local_hom_TFAE (algebraMap R A)).out 5 1 rfl rfl).mp
      (IsLocalRing.eq_maximalIdeal hm)
  let K := A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)
  let : Algebra (IsLocalRing.ResidueField R) K :=
    Ideal.Quotient.algebraQuotientMapQuotient
  have : IsScalarTower R (IsLocalRing.ResidueField R) K :=
    Ideal.Quotient.tower_quotient_map_quotient
  let e : (IsLocalRing.ResidueField R ⊗[R] A) ≃ₐ[IsLocalRing.ResidueField R] K :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A (IsLocalRing.maximalIdeal R)).symm
  let : Field K :=
    (Algebra.FormallyUnramified.isField_quotient_map_maximalIdeal (R := R) (S := A)).toField
  have : Module.Finite (IsLocalRing.ResidueField R) K :=
    Module.Finite.of_restrictScalars_finite R _ _
  have : Algebra.IsSeparable (IsLocalRing.ResidueField R) K := by
    have : Algebra.FormallyUnramified (IsLocalRing.ResidueField R) K :=
      Algebra.FormallyUnramified.of_restrictScalars R _ _
    exact Algebra.FormallyUnramified.isSeparable _ _
  exact exists_galois_finiteEtale_extension R A K e

private lemma exists_cover_span_sections_of_onePoint
    (R : Type u) [CommRing R] [HenselianLocalRing R] (hdim : ringKrullDim R = 0)
    (B : BigEtaleSite.{u}) (hS : B.Contains (Spec (.of R)))
    (M : SheafOfModules.{u} ((AlgebraicGeometry.SmallEtale.structureSheaf B (Spec (.of R)) hS).over
      (AlgebraicGeometry.SmallEtale.final B (Spec (.of R)) hS)))
    (V : Over (AlgebraicGeometry.SmallEtale.final B (Spec (.of R)) hS))
    [Nonempty ((AlgebraicGeometry.SmallEtale.toScheme B (Spec (.of R)) hS).obj V.left)]
    [Subsingleton ((AlgebraicGeometry.SmallEtale.toScheme B (Spec (.of R)) hS).obj V.left)] :
    ∃ (W : Over (AlgebraicGeometry.SmallEtale.final B (Spec (.of R)) hS)) (f : W ⟶ V),
      Sieve.generate (Presieve.singleton f) ∈
        ((AlgebraicGeometry.SmallEtale.topology B (Spec (.of R)) hS).over
          (AlgebraicGeometry.SmallEtale.final B (Spec (.of R)) hS)) V ∧
      Submodule.span (M := M.val.obj (op W))
        (((AlgebraicGeometry.SmallEtale.structureSheaf B (Spec (.of R)) hS).over
          (AlgebraicGeometry.SmallEtale.final B (Spec (.of R)) hS)).obj.obj (op W))
        (Set.range (fun s : M.sections ↦ (s.val (op W) : M.val.obj (op W)))) = ⊤ := by
  let T := AlgebraicGeometry.SmallEtale.final B (Spec (.of R)) hS
  let X := (AlgebraicGeometry.SmallEtale.toScheme B (Spec (.of R)) hS).obj V.left
  let A := Γ(X, ⊤)
  let p : X ⟶ Spec (.of R) := B.inclusion.map V.left.obj.hom
  let φ : R →+* A := (p.appTop).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  have hφ : φ.Finite ∧ φ.Etale := finiteEtale_globalSections_of_affine R hdim p
  let : Algebra R A := φ.toAlgebra
  have : Module.Finite R A := RingHom.finite_algebraMap.mp hφ.1
  have : Algebra.Etale R A := RingHom.etale_algebraMap.mp hφ.2
  have : Subsingleton (PrimeSpectrum A) := by
    show Subsingleton (Spec (.of A))
    exact X.isoSpec.inv.homeomorph.subsingleton
  have : Nontrivial A :=
    PrimeSpectrum.nontrivial (X.isoSpec.hom (Classical.choice inferInstance))
  have : IsLocalRing A := isLocalRing_of_subsingleton_primeSpectrum A
  obtain ⟨D, _, _, _, _, L, _, _, _, _, hD, hAD⟩ :=
    exists_galois_finiteEtale_extension_of_isLocalRing R A
  let ψ : A →ₐ[R] D := Classical.choice hAD
  let W := finiteEtaleSpec R D B hS
  let g := finiteEtaleSpecMap R A D B hS ψ
  let j : finiteEtaleSpec R A B hS ⟶ V.left := by
    refine ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk X.isoSpec.inv) ?_)
    apply B.inclusion.map_injective
    show X.isoSpec.inv ≫ p = Spec.map (CommRingCat.ofHom φ)
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  let E := Over.equivalenceOfIsTerminal
    (AlgebraicGeometry.SmallEtale.finalIsTerminal B (Spec (.of R)) hS)
  let W' := E.inverse.obj W
  let q : W' ⟶ V := Over.homMk (g ≫ j)
    ((AlgebraicGeometry.SmallEtale.finalIsTerminal B (Spec (.of R)) hS).hom_ext _ _)
  let eD := Classical.choice hD
  have : Nontrivial D := (residueLiftMap R D L eD).domain_nontrivial
  have : Subsingleton (Spec (.of R)) := baseSpectrum_subsingleton R hdim
  refine ⟨W', q, ?_, span_sections_finiteEtale_galois R D B hS (liftedResidueAction R D L eD)
    (liftedResidueAction_tensorMap_bijective R D L eD) M⟩
  exact smallEtaleOver_generate_singleton_mem_of_surjective B (Spec (.of R)) hS T q fun _ ↦
    ⟨Classical.choice (inferInstance : Nonempty (Spec (.of D))), Subsingleton.elim _ _⟩

/-- Every module on the small étale site of a zero-dimensional local ring is
quasi-coherent. -/
@[stacks 0D1W]
public theorem allModules_isQuasicoherent
    (R : Type u) [CommRing R] [IsLocalRing R] (hdim : ringKrullDim R = 0)
    (B : BigEtaleSite.{u})
    (hS : B.Contains (Spec (.of R)))
    (F : SheafOfModules.{u}
      (AlgebraicGeometry.SmallEtale.structureSheaf B (Spec (.of R)) hS)) :
    F.IsQuasicoherent := by
  have : HenselianLocalRing R := henselian_of_ringKrullDim_eq_zero R hdim
  have : HasFiniteLimits (AlgebraicGeometry.SmallEtale B (Spec (.of R)) hS) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  refine isQuasicoherent_of_isSeparator_over_terminal
    (R := AlgebraicGeometry.SmallEtale.structureSheaf B (Spec (.of R)) hS)
    (AlgebraicGeometry.SmallEtale.finalIsTerminal B (Spec (.of R)) hS) ?_ F
  apply isSeparator_unit_of_locally_span_sections
  intro M U m
  let J := AlgebraicGeometry.SmallEtale.topology B (Spec (.of R)) hS
  let T := AlgebraicGeometry.SmallEtale.final B (Spec (.of R)) hS
  obtain ⟨I, V, f, hcover, hsub⟩ :=
    smallEtale_exists_onePoint_cover R hdim B hS U.left
  let W (i : I) : Over T := Over.mk (f i ≫ U.hom)
  let g (i : I) : W i ⟶ U := Over.homMk (f i) rfl
  have hcover' : Sieve.ofArrows W g ∈ (J.over T) U := by
    rwa [J.mem_over_iff, Sieve.overEquiv_ofArrows]
  apply (J.over T).transitive hcover'
  intro Z k hk
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff W g k).1 hk
  rw [Sieve.pullback_comp]
  apply (J.over T).pullback_stable a
  have : Nonempty ((AlgebraicGeometry.SmallEtale.toScheme B (Spec (.of R)) hS).obj
      (W i).left) := (hsub i).1
  have : Subsingleton ((AlgebraicGeometry.SmallEtale.toScheme B (Spec (.of R)) hS).obj
      (W i).left) := (hsub i).2
  let P : Presieve U := fun {V : Over T} (f : V ⟶ U) ↦
      M.val.map f.op m ∈
        Submodule.span (M := M.val.obj (op V))
          (((AlgebraicGeometry.SmallEtale.structureSheaf B (Spec (.of R)) hS).over T).obj.obj
            (op V))
          (Set.range (fun s : M.sections ↦
            (s.val (op V) : M.val.obj (op V))))
  obtain ⟨W', q, hq, hspan⟩ := exists_cover_span_sections_of_onePoint R hdim B hS M (W i)
  refine (J.over T).superset_covering ((Sieve.generate_le_iff _ _).mpr ?_) hq
  rintro Z k ⟨⟩
  exact Sieve.le_generate P _ (q ≫ g i) (Submodule.eq_top_iff'.mp hspan _)

end Stacks.EtaleCohomology.SmallEtaleModules
