module

public import StacksFrontier.RingTheory.Dualizing.FiniteLengthMatlisDuality.DerivedHomHeart
import all StacksFrontier.RingTheory.Dualizing.FiniteLengthMatlisDuality.DerivedHomHeart
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Duality on finite-length modules

For a normalized dualizing complex over a Noetherian local ring, derived Hom into the
dualizing complex agrees, functorially on finite-length modules, with Matlis duality.

## Main results

* `Dualizing.derivedHomFiniteLengthIsoMatlisDual` identifies these two functors when the
  fixed object is a normalized dualizing complex and `E` is an injective hull of the residue
  field.

## Implementation notes

Derived Hom is the canonical derived internal-Hom bifunctor, rather than a functor attached
to a chosen injective representative. The module universe is independent of the universe of
the ring. Normalization is expressed by `Dualizing.IsNormalizedDualizingComplex`, the
normalization predicate shared with the rest of the dualizing-complex development.

The derived category is taken at the standard model. The pin is forced rather than chosen: the
model is baked into the types of `Dualizing.dualizingDerivedHomFunctor` and
`Dualizing.IsNormalizedDualizingComplex`. No statement here mentions coproducts of the derived
category, and the standard model is a legitimate derived category of `ModuleCat A`, so nothing
is weakened by it.

## References

* [Stacks Project, Tag 0A7Q](https://stacks.math.columbia.edu/tag/0A7Q)
-/

@[expose] public noncomputable section

open CategoryTheory
open StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

universe u v u' v' w'

namespace Dualizing

private lemma finiteLength_factors_through_maximalIdeal_power
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (hM : IsFiniteLength A M) :
    ∃ n : ℕ, ∃ hT : Module.IsTorsionBySet A M
      ((IsLocalRing.maximalIdeal A ^ (n + 1) : Ideal A) : Set A),
      letI := hT.module
      IsFiniteLength (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)) M := by
  obtain ⟨n, hn⟩ := finiteLength_annihilated_by_maximalIdeal_power A M hM
  have hI : IsLocalRing.maximalIdeal A ^ (n + 1) ≤ Module.annihilator A M :=
    (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn
  let hT : Module.IsTorsionBySet A M
      ((IsLocalRing.maximalIdeal A ^ (n + 1) : Ideal A) : Set A) := by
    intro x a
    exact Module.mem_annihilator.mp (hI a.2) x
  refine ⟨n, hT, ?_⟩
  let := hT.module
  exact finiteLength_over_artinian_quotient A _ M hM hI
    (maximalIdeal_power_quotient_isArtinianRing A n)

private noncomputable def homToMaximalIdealPowerTorsionEquiv
    (A : Type u) [CommRing A]
    (I : Ideal A)
    (M E : Type (max v u)) [AddCommGroup M] [Module A M]
    [AddCommGroup E] [Module A E]
    (hT : Module.IsTorsionBySet A M (I : Set A)) :
    (M →ₗ[A] E) ≃ₗ[A]
      (M →ₗ[A] Submodule.torsionBySet A E (I : Set A)) where
  toFun f := f.codRestrict _ (by
    intro x
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    rw [← f.map_smul, hT (x := x) (a := a), map_zero])
  invFun g := (Submodule.torsionBySet A E (I : Set A)).subtype.comp g
  left_inv f := by
    ext x
    rfl
  right_inv g := by
    ext x
    rfl
  map_add' f g := by
    ext x
    rfl
  map_smul' a f := by
    ext x
    rfl

private lemma finiteLength_hom_factors_through_maximalIdealPowerTorsion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M E : Type (max v u)) [AddCommGroup M] [Module A M]
    [AddCommGroup E] [Module A E] (hM : IsFiniteLength A M) :
    ∃ n : ℕ, Nonempty ((M →ₗ[A] E) ≃ₗ[A]
      (M →ₗ[A] Submodule.torsionBySet A E
        ((IsLocalRing.maximalIdeal A ^ (n + 1) : Ideal A) : Set A))) := by
  obtain ⟨n, hT, _⟩ := finiteLength_factors_through_maximalIdeal_power A M hM
  exact ⟨n, ⟨homToMaximalIdealPowerTorsionEquiv A _ M E hT⟩⟩

private lemma annihilator_le_linearMap_annihilator
    (A : Type u) [CommRing A]
    (M E : Type (max v u)) [AddCommGroup M] [Module A M]
    [AddCommGroup E] [Module A E] :
    Module.annihilator A M ≤ Module.annihilator A (M →ₗ[A] E) := by
  intro a ha
  rw [Module.mem_annihilator] at ha ⊢
  intro f
  ext x
  show a • f x = 0
  rw [← f.map_smul, ha x, map_zero]

private lemma finiteLength_hom_of_finiteLength_torsion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M E : Type (max v u)) [AddCommGroup M] [Module A M]
    [AddCommGroup E] [Module A E] (hM : IsFiniteLength A M)
    (n : ℕ)
    (hT : Module.IsTorsionBySet A M
      ((IsLocalRing.maximalIdeal A ^ (n + 1) : Ideal A) : Set A))
    (hE : IsFiniteLength A
      (Submodule.torsionBySet A E
        ((IsLocalRing.maximalIdeal A ^ (n + 1) : Ideal A) : Set A))) :
    IsFiniteLength A (M →ₗ[A] E) := by
  let T := Submodule.torsionBySet A E
    ((IsLocalRing.maximalIdeal A ^ (n + 1) : Ideal A) : Set A)
  let : IsNoetherian A M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  let : Module.Finite A M := inferInstance
  let : IsNoetherian A T :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hE).1
  let : IsNoetherian A (M →ₗ[A] T) := inferInstance
  let e := homToMaximalIdealPowerTorsionEquiv A _ M E hT
  let : IsNoetherian A (M →ₗ[A] E) :=
    isNoetherian_of_linearEquiv e.symm
  let : Module.Finite A (M →ₗ[A] E) := inferInstance
  apply finiteLength_of_supportDim_le_zero
  have hsupp : Module.support A (M →ₗ[A] E) ⊆ Module.support A M := fun p hp =>
    (Module.mem_support_iff_of_finite (R := A) (M := M)).mpr
      ((annihilator_le_linearMap_annihilator A M E).trans
        ((Module.mem_support_iff_of_finite (R := A) (M := M →ₗ[A] E)).mp hp))
  exact (supportDim_le_of_support_subset hsupp).trans
    (finiteLength_supportDim_le_zero A M hM)

private lemma maximalIdealPowerTorsion_residueHull
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) (n : ℕ) :
    let B := A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)
    letI : IsLocalRing B := maximalIdeal_power_quotient_isLocalRing A n
    let T := maximalIdealPowTorsion A E n
    ∃ (j : residueFieldModule.{u, v} B ⟶ ModuleCat.of B T),
      ∃ hj : Mono j, letI := hj; Module.IsInjectiveHull j := by
  let I : Ideal A := IsLocalRing.maximalIdeal A ^ (n + 1)
  let B := A ⧸ I
  let : IsLocalRing B := maximalIdeal_power_quotient_isLocalRing A n
  let K : ModuleCat.{max v u} A :=
    (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A))
  let e : IsLocalRing.ResidueField A ≃ₗ[A] K :=
    (ULift.moduleEquiv : K ≃ₗ[A] IsLocalRing.ResidueField A).symm
  let hT := residueFieldModelIsTorsionByMaximalIdealPow A K e n
  let := hT.module
  have : IsSimpleModule A (IsLocalRing.ResidueField A) :=
    (isSimpleModule_iff_isCoatom).mpr
      (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal A))
  have : IsSimpleModule A K :=
    IsSimpleModule.congr (ULift.moduleEquiv : K ≃ₗ[A] IsLocalRing.ResidueField A)
  have : IsSimpleModule B K :=
    isSimpleModule_quotient_of_torsion A I K hT
  obtain ⟨eB⟩ := simple_module_linearEquiv_residueField B K
  let q : residueFieldModule.{u, v} B ≃ₗ[B] K :=
    (ULift.moduleEquiv :
      residueFieldModule.{u, v} B ≃ₗ[B]
        IsLocalRing.ResidueField B).trans eB.symm
  let j := residueFieldToMaximalIdealPowTorsion A e i n
  let : Mono (ModuleCat.ofHom j) :=
    (ModuleCat.mono_iff_injective _).2
      (residueFieldToMaximalIdealPowTorsion_injective A e i
        ((ModuleCat.mono_iff_injective i).1 (by infer_instance)) n)
  have hj : Module.IsInjectiveHull (ModuleCat.ofHom j) :=
    maximalIdealPowTorsion_isInjectiveHull A K E e i hi n
  refine ⟨q.toModuleIso.hom ≫ ModuleCat.ofHom j, inferInstance, ?_⟩
  exact injectiveHull_comp_iso q.toModuleIso (ModuleCat.ofHom j) hj

private lemma maximalIdealPowerTorsion_isFiniteLength
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) (n : ℕ) :
    IsFiniteLength A (maximalIdealPowTorsion A E n) := by
  let I : Ideal A := IsLocalRing.maximalIdeal A ^ (n + 1)
  let B := A ⧸ I
  let T := maximalIdealPowTorsion A E n
  let : IsLocalRing B := maximalIdeal_power_quotient_isLocalRing A n
  let : IsNoetherianRing B := inferInstance
  let : IsArtinianRing B := maximalIdeal_power_quotient_isArtinianRing A n
  let : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
    isAdicComplete_of_nilpotentIdeal B _
      ((isArtinianRing_iff_isNilpotent_maximalIdeal B).mp inferInstance)
  obtain ⟨j, hj, hHull⟩ := maximalIdealPowerTorsion_residueHull A E i hi n
  let : Mono j := hj
  let E' : ModuleCat.{max v u} B := ModuleCat.of B T
  let F := matlisDuality B E' j hHull
  let η := matlisDualityFunctorIso B E' j hHull
  let X : ArtinianModules.{u, v} B :=
    ⟨(ModuleCat.uliftFunctor.{v} B).obj (ModuleCat.of B B),
      isArtinian_of_linearEquiv
        (ULift.moduleEquiv : ULift.{v} B ≃ₗ[B] B).symm⟩
  have : IsNoetherian B
      ((F.functor ⋙ ObjectProperty.ι
        (fun M : ModuleCat.{max v u} B ↦ IsNoetherian B M)).obj (.op X)) :=
    (F.functor.obj (.op X)).property
  have : IsNoetherian B (X.obj ⟶ E') :=
    isNoetherian_of_linearEquiv (η.app (.op X)).toLinearEquiv
  let e : (X.obj ⟶ E') ≃ₗ[B] T :=
    ModuleCat.homLinearEquiv.trans
      ((LinearEquiv.arrowCongr
        (ULift.moduleEquiv : ULift.{v} B ≃ₗ[B] B)
        (LinearEquiv.refl B T)).trans (LinearMap.ringLmapEquivSelf B B T))
  have : IsNoetherian B T := isNoetherian_of_linearEquiv e
  have : Module.Finite B T := inferInstance
  have : Module.Finite A T := Module.Finite.trans B T
  have : IsArtinian A T :=
    isArtinian_of_surjective_algebraMap
      (Ideal.Quotient.mk_surjective (I := I))
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨inferInstance, inferInstance⟩

private lemma finiteLength_matlisDual
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) (hM : IsFiniteLength A M) :
    IsFiniteLength A (M →ₗ[A] E) := by
  obtain ⟨n, hT, _⟩ := finiteLength_factors_through_maximalIdeal_power A M hM
  exact finiteLength_hom_of_finiteLength_torsion A M E hM n hT
    (maximalIdealPowerTorsion_isFiniteLength A E i hi n)

private def quotientLinearMapEquiv
    (A : Type u) [CommRing A] (I : Ideal A)
    (M N : Type (max v u)) [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (hM : Module.IsTorsionBySet A M (I : Set A))
    (hN : Module.IsTorsionBySet A N (I : Set A)) :
    letI := hM.module
    letI := hN.module
    (M →ₗ[A] N) ≃ₗ[A] (M →ₗ[A ⧸ I] N) := by
  letI := hM.module
  letI := hN.module
  refine {
    toFun := fun f =>
      { toFun := f
        map_add' := f.map_add
        map_smul' := fun q x => Quotient.inductionOn' q fun r => f.map_smul r x }
    invFun := fun g => g.restrictScalars A
    left_inv := fun f => by ext; rfl
    right_inv := fun g => by ext; rfl
    map_add' := fun f g => by ext; rfl
    map_smul' := fun a f => by ext; rfl }

private def quotientLinearEquivOfLinearEquiv
    (A : Type u) [CommRing A] (I : Ideal A)
    (M N : Type (max v u)) [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (hM : Module.IsTorsionBySet A M (I : Set A))
    (hN : Module.IsTorsionBySet A N (I : Set A))
    (e : M ≃ₗ[A] N) :
    letI := hM.module
    letI := hN.module
    M ≃ₗ[A ⧸ I] N := by
  letI := hM.module
  letI := hN.module
  exact {
    toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := fun q x => Quotient.inductionOn' q fun r => e.map_smul r x }

private def matlisDualQuotientLinearEquiv
    (A : Type u) [CommRing A] (I : Ideal A)
    (M E : Type (max v u)) [AddCommGroup M] [Module A M]
    [AddCommGroup E] [Module A E]
    (hM : Module.IsTorsionBySet A M (I : Set A)) :
    letI := hM.module
    (M →ₗ[A] E) ≃ₗ[A]
      (M →ₗ[A ⧸ I] Submodule.torsionBySet A E (I : Set A)) := by
  let hT := Submodule.torsionBySet_isTorsionBySet (R := A) (M := E) (I : Set A)
  exact (homToMaximalIdealPowerTorsionEquiv A I M E hM).trans
    (quotientLinearMapEquiv A I M _ hM hT)

private lemma matlisDual_isTorsionBySet
    (A : Type u) [CommRing A] (I : Ideal A)
    (M E : Type (max v u)) [AddCommGroup M] [Module A M]
    [AddCommGroup E] [Module A E]
    (hM : Module.IsTorsionBySet A M (I : Set A)) :
    Module.IsTorsionBySet A (M →ₗ[A] E) (I : Set A) := by
  intro f a
  have hI : I ≤ Module.annihilator A M := fun r hr =>
    Module.mem_annihilator.mpr fun x => hM (x := x) (a := ⟨r, hr⟩)
  exact Module.mem_annihilator.mp
    ((hI.trans (annihilator_le_linearMap_annihilator A M E)) a.2) f

private def matlisDualQuotientLinearEquivOverQuotient
    (A : Type u) [CommRing A] (I : Ideal A)
    (M E : Type (max v u)) [AddCommGroup M] [Module A M]
    [AddCommGroup E] [Module A E]
    (hM : Module.IsTorsionBySet A M (I : Set A)) :
    letI := hM.module
    let hD := matlisDual_isTorsionBySet A I M E hM
    letI := hD.module
    (M →ₗ[A] E) ≃ₗ[A ⧸ I]
      (M →ₗ[A ⧸ I] Submodule.torsionBySet A E (I : Set A)) := by
  letI := hM.module
  let hD := matlisDual_isTorsionBySet A I M E hM
  letI := hD.module
  let e := matlisDualQuotientLinearEquiv A I M E hM
  exact {
    toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := fun q f => Quotient.inductionOn' q fun r => e.map_smul r f }

private def matlisBidualQuotientLinearEquiv
    (A : Type u) [CommRing A] (I : Ideal A)
    (M E : Type (max v u)) [AddCommGroup M] [Module A M]
    [AddCommGroup E] [Module A E]
    (hM : Module.IsTorsionBySet A M (I : Set A)) :
    letI := hM.module
    ((M →ₗ[A] E) →ₗ[A] E) ≃ₗ[A]
      ((M →ₗ[A ⧸ I] Submodule.torsionBySet A E (I : Set A)) →ₗ[A ⧸ I]
        Submodule.torsionBySet A E (I : Set A)) := by
  letI := hM.module
  let hD := matlisDual_isTorsionBySet A I M E hM
  letI := hD.module
  let e₁ := matlisDualQuotientLinearEquivOverQuotient A I M E hM
  let e₂ := matlisDualQuotientLinearEquiv A I (M →ₗ[A] E) E hD
  exact e₂.trans
    ((LinearEquiv.arrowCongr e₁
      (LinearEquiv.refl (A ⧸ I) (Submodule.torsionBySet A E (I : Set A)))).restrictScalars A)

private def matlisEvaluationLinear
    (A : Type u) [CommRing A]
    (M E : Type (max v u)) [AddCommGroup M] [Module A M]
    [AddCommGroup E] [Module A E] :
    M →ₗ[A] ((M →ₗ[A] E) →ₗ[A] E) where
  toFun m :=
    { toFun := fun f => f m
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

/-- Bijectivity transfers along a bijection `q` with `q ∘ f = g`. -/
private lemma bijective_iff_of_bijective_comp_eq {α β γ : Type*} (f : α → β) (g : α → γ)
    (q : β → γ) (hq : Function.Bijective q) (h : ∀ a, q (f a) = g a) :
    Function.Bijective f ↔ Function.Bijective g := by
  rw [show g = q ∘ f from funext fun a => (h a).symm, hq.of_comp_iff']

private lemma matlisEvaluationLinear_bijective_iff_isIso
    (A : Type u) [CommRing A]
    (M E : ModuleCat.{max v u} A) :
    Function.Bijective (matlisEvaluationLinear A M E) ↔
      IsIso ((matlisEvaluation A E).app M) := by
  let p : (M →ₗ[A] E) ≃ₗ[A] (M ⟶ E) :=
    ModuleCat.homLinearEquiv.symm
  let q : ((M →ₗ[A] E) →ₗ[A] E) ≃ₗ[A]
      (ModuleCat.of A (M ⟶ E) ⟶ E) :=
    (LinearEquiv.arrowCongr p (LinearEquiv.refl A E)).trans
      (ModuleCat.homLinearEquiv
        (M := ModuleCat.of A (M ⟶ E)) (N := E) (S := A)).symm
  have hq (m : M) : q (matlisEvaluationLinear A M E m) =
      (matlisEvaluation A E).app M m := by
    ext f
    rfl
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_iff_of_bijective_comp_eq _ _ q q.bijective hq

private lemma matlisBidualQuotientLinearEquiv_evaluation
    (A : Type u) [CommRing A] (I : Ideal A)
    (M E : Type (max v u)) [AddCommGroup M] [Module A M]
    [AddCommGroup E] [Module A E]
    (hM : Module.IsTorsionBySet A M (I : Set A)) (m : M) :
    letI := hM.module
    (matlisBidualQuotientLinearEquiv A I M E hM)
      (matlisEvaluationLinear A M E m) =
        matlisEvaluationLinear (A ⧸ I) M
          (Submodule.torsionBySet A E (I : Set A)) m := by
  let := hM.module
  ext f
  show ((matlisDualQuotientLinearEquivOverQuotient A I M E hM).symm f) m =
    (f m).val
  rfl

private lemma finiteLength_matlisEvaluationLinear_bijective
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) (hM : IsFiniteLength A M) :
    Function.Bijective (matlisEvaluationLinear A M E) := by
  obtain ⟨n, hT, hB⟩ := finiteLength_factors_through_maximalIdeal_power A M hM
  let I : Ideal A := IsLocalRing.maximalIdeal A ^ (n + 1)
  let B := A ⧸ I
  let T := maximalIdealPowTorsion A E n
  let := hT.module
  let : IsLocalRing B := maximalIdeal_power_quotient_isLocalRing A n
  let : IsNoetherianRing B := inferInstance
  let : IsArtinianRing B := maximalIdeal_power_quotient_isArtinianRing A n
  let : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
    isAdicComplete_of_nilpotentIdeal B _
      ((isArtinianRing_iff_isNilpotent_maximalIdeal B).mp inferInstance)
  let : IsArtinian B M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hB).2
  obtain ⟨j, hj, hHull⟩ := maximalIdealPowerTorsion_residueHull A E i hi n
  let : Mono j := hj
  let E' : ModuleCat.{max v u} B := ModuleCat.of B T
  let : IsIso ((matlisEvaluation B E').app
      (ModuleCat.of B M)) :=
    isIso_matlisEvaluation_of_isArtinian B E'
      (ModuleCat.of B M) j hHull
  have hb := (matlisEvaluationLinear_bijective_iff_isIso B (ModuleCat.of B M) E').mpr
    inferInstance
  exact (bijective_iff_of_bijective_comp_eq _ _ _
    (matlisBidualQuotientLinearEquiv A I M E hT).bijective
    (matlisBidualQuotientLinearEquiv_evaluation A I M E hT)).mpr hb

private lemma finiteLength_matlisEvaluation_isIso
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) (hM : IsFiniteLength A M) :
    IsIso ((matlisEvaluation A E).app (ModuleCat.of A M)) :=
  (matlisEvaluationLinear_bijective_iff_isIso A (ModuleCat.of A M) E).mp
    (finiteLength_matlisEvaluationLinear_bijective A M E i hi hM)

private noncomputable def matlisDualFiniteLengthHeartFunctor
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    (FiniteLengthModules.{u, v} A)ᵒᵖ ⥤ FiniteLengthModules.{u, v} A := by
  let F := (ObjectProperty.ι
      (P := fun M : ModuleCat.{max v u} A => IsFiniteLength A M)).op ⋙
    (linearYoneda A (ModuleCat.{max v u} A)).obj E
  exact {
    obj := fun N => ⟨F.obj N, by
      change IsFiniteLength A (N.unop.obj ⟶ E)
      exact (ModuleCat.homLinearEquiv
        (M := N.unop.obj) (N := E) (S := A)).symm.isFiniteLength
          (finiteLength_matlisDual A N.unop.obj E i hi N.unop.property)⟩
    map := fun f => ⟨F.map f⟩
    map_id := by intro N; ext; simp
    map_comp := by intro X Y Z f g; ext; simp [Functor.map_comp] }

private noncomputable def matlisFiniteLengthEvaluationIso
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    𝟭 (FiniteLengthModules.{u, v} A) ≅
      opOp (FiniteLengthModules.{u, v} A) ⋙
        (matlisDualFiniteLengthHeartFunctor A E i hi).op ⋙
        matlisDualFiniteLengthHeartFunctor A E i hi := by
  refine NatIso.ofComponents (fun M => ?_) ?_
  · letI : IsIso ((matlisEvaluation A E).app M.obj) :=
      finiteLength_matlisEvaluation_isIso A M.obj E i hi M.property
    let e : M.obj ≅ (matlisBidual A E).obj M.obj :=
      asIso ((matlisEvaluation A E).app M.obj)
    apply ObjectProperty.isoMk
      (P := fun N : ModuleCat.{max v u} A => IsFiniteLength A N)
    exact e
  · intro X Y f
    apply ObjectProperty.hom_ext
    exact (matlisEvaluation A E).naturality f.hom

@[sga "2 IV 5.1" "special case"]
private lemma matlisDualFiniteLengthHeartFunctor_isEquivalence
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    (matlisDualFiniteLengthHeartFunctor A E i hi).IsEquivalence := by
  let C := FiniteLengthModules.{u, v} A
  let H := matlisDualFiniteLengthHeartFunctor A E i hi
  let G := opOp C ⋙ H.op
  let η := matlisFiniteLengthEvaluationIso A E i hi
  have u : 𝟭 Cᵒᵖ ≅ H ⋙ G := by
    refine NatIso.ofComponents (fun X => ?_) ?_
    · exact (η.app X.unop).op.symm
    · intro X Y f
      apply Quiver.Hom.unop_inj
      convert (η.inv.naturality f.unop).symm using 1
      all_goals simp [H, G]
  exact Functor.IsEquivalence.mk' G u η.symm

private lemma matlisDualFiniteLengthFunctor_eq_singleHeart
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    matlisDualFiniteLengthFunctor A E =
      (matlisDualFiniteLengthHeartFunctor A E i hi ⋙
        ObjectProperty.ι
          (P := fun M : ModuleCat.{max v u} A => IsFiniteLength A M)) ⋙
        DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0 := by
  rfl

private instance oppositeLinear
    {A : Type u} [CommRing A] {C : Type u'}
    [Category.{v'} C] [Preadditive C] [CategoryTheory.Linear A C] :
    CategoryTheory.Linear A Cᵒᵖ where
  homModule X Y := by
    let e : (X ⟶ Y) ≃+ (Y.unop ⟶ X.unop) :=
      { toEquiv := CategoryTheory.opEquiv X Y, map_add' := by intros; rfl }
    exact e.module A
  smul_comp X Y Z r f g := Quiver.Hom.unop_inj (CategoryTheory.Linear.comp_smul _ _ _ _ _ _)
  comp_smul X Y Z f r g := Quiver.Hom.unop_inj (CategoryTheory.Linear.smul_comp _ _ _ _ _ _)

private lemma matlisDualFiniteLengthHeartFunctor_linear
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    (matlisDualFiniteLengthHeartFunctor A E i hi).Linear A := by
  constructor
  intro X Y f r
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext g
  show (Linear.leftComp A E (r • f.unop.hom)) g =
    r • (Linear.leftComp A E f.unop.hom) g
  simp [Linear.leftComp, CategoryTheory.Linear.smul_comp]

private lemma derivedHomFiniteLengthHeartFunctor_linear
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K) :
    (derivedHomFiniteLengthHeartFunctor A K hK).Linear A := by
  apply (Functor.linear_iff A _).2
  intro X r
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext y
  let M := X.unop.obj
  let e := extIntoOmegaAtLinearEquiv A K 0 M
  obtain ⟨x, rfl⟩ := e.surjective y
  have hn := extIntoOmegaAtLinearEquiv_naturality A K 0
    (r • (𝟙 M)) x
  change e ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
      (r • (𝟙 M)) ≫ x) =
    ((derivedHomFiniteLengthHeartFunctor A K hK).map
      (r • (𝟙 X))) (e x) at hn
  rw [Functor.map_smul,
    (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map_id M] at hn
  simp only [CategoryTheory.Linear.smul_comp, Category.id_comp, map_smul] at hn
  show ((derivedHomFiniteLengthHeartFunctor A K hK).map
      (r • (𝟙 X))).hom (e x) = r • e x
  exact hn.symm

private lemma finiteLength_restrictScalars_ringEquiv
    {R : Type u} {S : Type u'} [CommRing R] [CommRing S]
    (e : R ≃+* S) (M : ModuleCat.{v'} S) :
    IsFiniteLength R ((ModuleCat.restrictScalars e.toRingHom).obj M) ↔
      IsFiniteLength S M := by
  let : Algebra R S := e.toRingHom.toAlgebra
  let : Module R M := Module.compHom M e.toRingHom
  let : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  let q := Submodule.orderIsoOfAlgebraMapSurjective
    (R := R) (S := S) (M := M) e.surjective
  rw [isFiniteLength_iff_isNoetherian_isArtinian,
    isFiniteLength_iff_isNoetherian_isArtinian]
  constructor
  · intro h
    exact ⟨isNoetherian_mk (q.dual.toOrderEmbedding.wellFounded h.1.wf),
      q.toOrderEmbedding.wellFounded h.2⟩
  · intro h
    exact ⟨isNoetherian_mk (q.symm.dual.toOrderEmbedding.wellFounded h.1.wf),
      q.symm.toOrderEmbedding.wellFounded h.2⟩

private noncomputable def finiteLengthRingEquiv
    {R : Type u} {S : Type u'} [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    ObjectProperty.FullSubcategory
        (fun M : ModuleCat.{v'} S => IsFiniteLength S M) ≌
      ObjectProperty.FullSubcategory
        (fun M : ModuleCat.{v'} R => IsFiniteLength R M) := by
  let F := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u', v'} e
  let P : ObjectProperty (ModuleCat.{v'} S) := fun M => IsFiniteLength S M
  let Q : ObjectProperty (ModuleCat.{v'} R) := fun M => IsFiniteLength R M
  letI : Q.IsClosedUnderIsomorphisms :=
    ⟨fun e h => e.toLinearEquiv.isFiniteLength h⟩
  have h : Q.inverseImage F.functor = P := by
    ext M
    exact finiteLength_restrictScalars_ringEquiv e M
  exact F.congrFullSubcategory h

private lemma finiteLengthRingEquiv_functor_map_smul
    {R : Type u} {S : Type u'} [CommRing R] [CommRing S]
    (e : R ≃+* S)
    {X Y : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{v'} S => IsFiniteLength S M)}
    (f : X ⟶ Y) (r : R) :
    (finiteLengthRingEquiv.{u, u', v'} e).functor.map ((e r) • f) =
      r • (finiteLengthRingEquiv.{u, u', v'} e).functor.map f := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext x
  rfl

private lemma finiteLengthRingEquiv_inverse_map_smul
    {R : Type u} {S : Type u'} [CommRing R] [CommRing S]
    (e : R ≃+* S)
    {X Y : ObjectProperty.FullSubcategory
      (fun M : ModuleCat.{v'} R => IsFiniteLength R M)}
    (f : X ⟶ Y) (r : R) :
    (finiteLengthRingEquiv.{u, u', v'} e).inverse.map (r • f) =
      (e r) • (finiteLengthRingEquiv.{u, u', v'} e).inverse.map f := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext x
  simp only [finiteLengthRingEquiv, Equivalence.congrFullSubcategory, ObjectProperty.ι,
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv, RingEquiv.toRingHom_eq_coe,
    ModuleCat.restrictScalars, ObjectProperty.lift, Functor.comp_obj, inducedFunctor_obj,
    ModuleCat.RestrictScalars.obj', Functor.comp_map, inducedFunctor_map,
    ModuleCat.RestrictScalars.map', Lean.Elab.WF.paramLet]
  show (r • f.hom.hom) x = (e.symm (e r) • f.hom.hom) x
  simp

private noncomputable def conjugateIsoIdentity
    {C : Type u'} {D : Type w'}
    [Category.{v'} C] [Category.{v} D]
    (e : C ≌ D) (F : C ⥤ C)
    (η : (e.inverse ⋙ F ⋙ e.functor) ≅ 𝟭 D) :
    F ≅ 𝟭 C := by
  let α (X : C) : F.obj X ≅ X :=
    e.functor.preimageIso
      (e.functor.mapIso (F.mapIso (e.unitIso.app X)) ≪≫
        η.app (e.functor.obj X))
  refine NatIso.ofComponents α ?_
  intro X Y f
  apply e.functor.map_injective
  simp only [Functor.map_comp]
  dsimp [α]
  simp only [Functor.preimageIso_hom, Functor.map_preimage]
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  have hunit := congrArg (fun h => e.functor.map (F.map h))
    (e.unitIso.hom.naturality f)
  have hη := η.hom.naturality (e.functor.map f)
  simp only [Functor.comp_map, Functor.id_map] at hunit hη
  calc
    e.functor.map (F.map f) ≫ e.functor.map (F.map (e.unitIso.hom.app Y)) ≫
        η.hom.app (e.functor.obj Y) =
      e.functor.map (F.map (e.unitIso.hom.app X)) ≫
        e.functor.map (F.map (e.inverse.map (e.functor.map f))) ≫
          η.hom.app (e.functor.obj Y) := by
            simpa only [Functor.map_comp, Category.assoc, Iso.app_hom] using
              congrArg (fun h => h ≫ η.hom.app (e.functor.obj Y)) hunit
    _ = _ := by
      simpa only [Functor.map_comp, Category.assoc, Iso.app_hom] using
        congrArg (fun h => e.functor.map (F.map (e.unitIso.hom.app X)) ≫ h) hη

private lemma finiteLengthEquivalenceIsoIdentity
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (F : FiniteLengthModules.{u, v} A ≌ FiniteLengthModules.{u, v} A)
    [F.functor.Linear A] : Nonempty (F.functor ≅ 𝟭 _) := by
  let B := ULift.{v} A
  let e : B ≃+* A := ULift.ringEquiv
  let : IsNoetherianRing B := isNoetherianRing_of_ringEquiv A e.symm
  let : IsLocalRing B := e.symm.isLocalRing
  let T := finiteLengthRingEquiv.{max u v, u, max u v} e
  let G := (T.symm.trans F).trans T
  have : G.functor.Linear B := by
    constructor
    intro X Y f r
    show T.functor.map (F.functor.map (T.inverse.map (r • f))) =
      r • T.functor.map (F.functor.map (T.inverse.map f))
    rw [finiteLengthRingEquiv_inverse_map_smul e f r,
      F.functor.map_smul, finiteLengthRingEquiv_functor_map_smul e]
  obtain ⟨η⟩ := linearEquivalenceFiniteLengthIsoIdentity B G
  exact ⟨conjugateIsoIdentity T F.functor η⟩

private noncomputable def matlisFiniteLengthOpEvaluationIso
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    let C := FiniteLengthModules.{u, v} A
    let H := matlisDualFiniteLengthHeartFunctor A E i hi
    𝟭 Cᵒᵖ ≅ H ⋙ opOp C ⋙ H.op := by
  let C := FiniteLengthModules.{u, v} A
  let H := matlisDualFiniteLengthHeartFunctor A E i hi
  let η := matlisFiniteLengthEvaluationIso A E i hi
  refine NatIso.ofComponents (fun X => ?_) ?_
  · exact (η.app X.unop).op.symm
  · intro X Y f
    apply Quiver.Hom.unop_inj
    convert (η.inv.naturality f.unop).symm using 1
    all_goals simp

private lemma derivedHomFiniteLengthHeartIsoMatlis
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    Nonempty (derivedHomFiniteLengthHeartFunctor A K hK ≅
      matlisDualFiniteLengthHeartFunctor A E i hi) := by
  let C := FiniteLengthModules.{u, v} A
  let D := derivedHomFiniteLengthHeartFunctor A K hK
  let H := matlisDualFiniteLengthHeartFunctor A E i hi
  let J := opOp C ⋙ H.op
  have : D.IsEquivalence := derivedHomFiniteLengthHeartFunctor_isEquivalence A K hK
  have : H.IsEquivalence := matlisDualFiniteLengthHeartFunctor_isEquivalence A E i hi
  have : J.IsEquivalence := inferInstance
  have : (J ⋙ D).IsEquivalence := inferInstance
  let F := (J ⋙ D).asEquivalence
  have : D.Linear A := derivedHomFiniteLengthHeartFunctor_linear A K hK
  have : H.Linear A := matlisDualFiniteLengthHeartFunctor_linear A E i hi
  have : J.Linear A := by
    constructor
    intro X Y f r
    apply Quiver.Hom.unop_inj
    show H.map (r • f.op) = r • H.map f.op
    exact H.map_smul r f.op
  have : F.functor.Linear A := by
    show (J ⋙ D).Linear A
    infer_instance
  obtain ⟨α⟩ := finiteLengthEquivalenceIsoIdentity A F
  let μ := matlisFiniteLengthOpEvaluationIso A E i hi
  exact ⟨(Functor.leftUnitor D).symm ≪≫
    Functor.isoWhiskerRight μ D ≪≫
    Functor.associator H J D ≪≫
    Functor.isoWhiskerLeft H α ≪≫
    Functor.rightUnitor H⟩

/-- **Stacks Project, Tag 0A7Q.** Derived Hom into a normalized dualizing complex agrees
naturally, on finite-length modules, with Matlis duality into an injective hull of the residue
field. -/
@[stacks 0A7Q]
public theorem derivedHomFiniteLengthIsoMatlisDual
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (E : ModuleCat.{max v u} A)
    (i : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    Nonempty
      (derivedHomFiniteLengthFunctor A K ≅ matlisDualFiniteLengthFunctor A E) := by
  obtain ⟨β⟩ := derivedHomFiniteLengthHeartIsoMatlis A K hK E i hi
  let J := ObjectProperty.ι
    (P := fun M : ModuleCat.{max v u} A => IsFiniteLength A M)
  let S := DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0
  exact ⟨derivedHomFiniteLengthIsoSingleHomology A K hK ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight β J) S⟩

end Dualizing

end
