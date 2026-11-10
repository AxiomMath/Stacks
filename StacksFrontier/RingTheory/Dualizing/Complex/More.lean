module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Order.Ideal
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.RingTheory.Dualizing.Artinian
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldHull
public import StacksFrontier.RingTheory.Length.Comparison
public import StacksFrontier.RingTheory.Length.FlatLocalHom

/-!
# Injective hulls under flat local base change

For a flat local homomorphism `A → B` of Noetherian local rings whose target maximal ideal is
extended from the source, tensoring an injective hull `E` of the source residue field with `B`
gives an injective hull of the target residue field.

The base change `B ⊗[A] E` is again an injective `B`-module and the socle of `B ⊗[A] E` is
one-dimensional over the target residue field, so `B ⊗[A] E` embeds in an injective hull `E'`
of the target residue field. Both modules are power-torsion for the target maximal ideal, and
flat base change computes the length of each torsion layer `(B ⊗[A] E)[𝔪_B ^ (n + 1)]` to be
that of `E'[𝔪_B ^ (n + 1)]`; since those layers have finite length, the embedding is onto each
of them, hence onto. Transporting the hull structure of `E'` back along the resulting
isomorphism exhibits `B ⊗[A] E` as an injective hull.

## Main results

* `Dualizing.exists_isInjectiveHull_tensorProduct`: the base change of an injective hull of
  the residue field is an injective hull of the target residue field.

## Implementation notes

The assertion that a module is an injective hull is represented by the existence of a
monomorphism from the residue field satisfying `Module.IsInjectiveHull`. The equality of
maximal ideals is expressed as equality with the extension of the source maximal ideal. We
write the base change as `B ⊗[A] E`, canonically isomorphic to `E ⊗[A] B`, so that its
`B`-module structure is directly available.

## References

* [Stacks Project, Tag 0E4E](https://stacks.math.columbia.edu/tag/0E4E)
-/

@[expose] public section

namespace Dualizing

section FlatLocalBaseChange

open CategoryTheory
open scoped TensorProduct

universe u

private noncomputable def residueFieldTensorEquiv
    (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] (hmax : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B) :
    IsLocalRing.ResidueField B ≃ₐ[B]
      B ⊗[A] IsLocalRing.ResidueField A := by
  let e : (B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) ≃+*
      IsLocalRing.ResidueField B :=
    Ideal.quotientEquiv _ _ (RingEquiv.refl B) (by simpa using hmax.symm)
  let e' : (B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) ≃ₐ[B]
      IsLocalRing.ResidueField B :=
    AlgEquiv.ofRingEquiv (f := e) (by intro b; rfl)
  exact e'.symm.trans <|
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (IsLocalRing.maximalIdeal A)

private noncomputable def tensorBaseChangeMap
    (A B E : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B]
    [AddCommGroup E] [Module A E]
    (i : IsLocalRing.ResidueField A →ₗ[A] E) :
    (B ⊗[A] IsLocalRing.ResidueField A) →ₗ[B] (B ⊗[A] E) where
  toFun := TensorProduct.map (LinearMap.id : B →ₗ[A] B) i
  map_add' := map_add _
  map_smul' b x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul b' a => simp [TensorProduct.smul_tmul']

private noncomputable def residueFieldToTensor
    (A B E : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [AddCommGroup E] [Module A E]
    (hmax : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B)
    (i : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ ModuleCat.of A E) :
    ModuleCat.of B (IsLocalRing.ResidueField B) ⟶ ModuleCat.of B (B ⊗[A] E) :=
  ModuleCat.ofHom <| (tensorBaseChangeMap A B E i.hom).comp
    (residueFieldTensorEquiv A B hmax).toLinearMap

private theorem mono_residueFieldToTensor
    (A B E : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [Module.Flat A B] [AddCommGroup E] [Module A E]
    (hmax : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B)
    (i : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ ModuleCat.of A E) [Mono i] :
    Mono (residueFieldToTensor A B E hmax i) := by
  rw [ModuleCat.mono_iff_injective]
  change Function.Injective ((tensorBaseChangeMap A B E i.hom).comp
    (residueFieldTensorEquiv A B hmax).toLinearMap)
  have hmap : Function.Injective (tensorBaseChangeMap A B E i.hom) := by
    change Function.Injective (i.hom.lTensor B)
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := B) i.hom
      (ModuleCat.mono_iff_injective i |>.mp inferInstance)
  exact hmap.comp (residueFieldTensorEquiv A B hmax).injective

private theorem length_injectiveHull_eq_length_ring
    (R E : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (IsLocalRing.ResidueField R) ⟶ ModuleCat.of R E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    Module.length R E = Module.length R R := by
  simpa only [(LinearMap.ringLmapEquivSelf R R E).length_eq] using
    length_linearMap_eq R E i hi R

private theorem length_eq_length_quotient_action
    (R : Type u) [CommRing R] (I : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M]
    (hM : Module.IsTorsionBySet R M (I : Set R)) :
    letI : Module (R ⧸ I) M := hM.module
    Module.length R M = Module.length (R ⧸ I) M := by
  let : Module (R ⧸ I) M := hM.module
  have hTower : IsScalarTower R (R ⧸ I) M := hM.isScalarTower
  let e : Submodule (R ⧸ I) M ≃o Submodule R M :=
    { toFun := Submodule.restrictScalars R
      invFun := fun N =>
        { carrier := N
          add_mem' := N.add_mem
          zero_mem' := N.zero_mem
          smul_mem' := fun q x hx => by
            obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
            exact (IsScalarTower.algebraMap_smul (R ⧸ I) r x).symm ▸ N.smul_mem r hx }
      left_inv := by intro N; ext; rfl
      right_inv := by intro N; ext; rfl
      map_rel_iff' := by intros; rfl }
  unfold Module.length
  congr 1
  exact (Order.krullDim_eq_of_orderIso e).symm

/-- The quotient-ring module structure on a module killed by an ideal. -/
@[instance_reducible]
private noncomputable def torsionQuotientModule
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hM : Module.IsTorsionBySet R M (I : Set R)) :
    letI : Semiring (R ⧸ I) := (Ideal.Quotient.ring I).toSemiring
    Module (R ⧸ I) M := hM.module

private noncomputable def torsionLinearEquiv
    (R X Y : Type u) [CommRing R] (I : Ideal R)
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (hX : Module.IsTorsionBySet R X (I : Set R))
    (hY : Module.IsTorsionBySet R Y (I : Set R))
    (e : X ≃ₗ[R] Y) :
    letI : Module (R ⧸ I) X := torsionQuotientModule R X I hX
    letI : Module (R ⧸ I) Y := torsionQuotientModule R Y I hY
    X ≃ₗ[R ⧸ I] Y := by
  letI : Module (R ⧸ I) X := torsionQuotientModule R X I hX
  letI : Module (R ⧸ I) Y := torsionQuotientModule R Y I hY
  refine
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := ?_ }
  intro q x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  change e (r • x) = r • e x
  exact e.map_smul r x

/-- Every element of an injective hull of the residue field lies in some torsion layer
`maximalIdealPowTorsion R E n`. -/
private theorem exists_mem_maximalIdealPowTorsion
    (R E : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (IsLocalRing.ResidueField R) ⟶ ModuleCat.of R E) [Mono i]
    (hi : Module.IsInjectiveHull i) (x : E) :
    ∃ n : ℕ, x ∈ maximalIdealPowTorsion R (ModuleCat.of R E) n := by
  have hx : x ∈ (⊤ : Submodule R (ModuleCat.of R E)) := Submodule.mem_top
  rw [← iSup_maximalIdealPowTorsion_eq_top R (ModuleCat.of R (IsLocalRing.ResidueField R))
    (ModuleCat.of R E) (LinearEquiv.refl R (IsLocalRing.ResidueField R)) i hi] at hx
  have hmono : Monotone (maximalIdealPowTorsion R (ModuleCat.of R E)) := fun m n hmn ↦
    Submodule.torsionBySet_le_torsionBySet_pow (m + 1) (n + 1) (Nat.add_le_add_right hmn 1) _
  exact (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hx

/-- An injective hull of the residue field is power-torsion for the maximal ideal: every
element is killed by some power of it. -/
private theorem injectiveHull_maximalIdealPowerTorsion
    (R E : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (IsLocalRing.ResidueField R) ⟶ ModuleCat.of R E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    ∀ x : E, ∃ n : ℕ, ∀ r ∈ (IsLocalRing.maximalIdeal R ^ n : Ideal R), r • x = 0 := by
  intro x
  obtain ⟨n, hn⟩ := exists_mem_maximalIdealPowTorsion R E i hi x
  exact ⟨n + 1, fun r hr ↦ (Submodule.mem_torsionBySet_iff _ _).1 hn ⟨r, hr⟩⟩

private noncomputable def residueFieldSocleEquiv
    (R E : Type u) [CommRing R] [IsLocalRing R]
    [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (IsLocalRing.ResidueField R) ⟶ ModuleCat.of R E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    let S := Submodule.torsionBySet R E (IsLocalRing.maximalIdeal R : Set R)
    IsLocalRing.ResidueField R ≃ₗ[R] S := by
  let S := Submodule.torsionBySet R E (IsLocalRing.maximalIdeal R : Set R)
  let f : IsLocalRing.ResidueField R →ₗ[R] S :=
    { toFun := fun x ↦ ⟨i.hom x, by
        apply (Submodule.mem_torsionBySet_iff _ _).2
        intro a
        have ha0 : (a : R) • x = 0 := by
          rw [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq,
            (IsLocalRing.residue_eq_zero_iff (a : R)).2 a.property, zero_mul]
        rw [← i.hom.map_smul, ha0, map_zero]⟩
      map_add' := fun x y ↦ Subtype.ext (i.hom.map_add x y)
      map_smul' := fun r y ↦ Subtype.ext (i.hom.map_smul r y) }
  have hf : Function.Injective f := fun x y hxy ↦
    (ModuleCat.mono_iff_injective i).mp inferInstance (congrArg Subtype.val hxy)
  have hsurj : Function.Surjective f := by
    intro x
    by_cases hx0 : x.1 = 0
    · exact ⟨0, by ext; simp [hx0]⟩
    · let V : Submodule R E := Submodule.span R {x.1}
      let q : ModuleCat.of R V ⟶ ModuleCat.of R E := ModuleCat.ofHom V.subtype
      have : Mono q := (ModuleCat.mono_iff_injective q).2 V.subtype_injective
      let so := ModuleCat.subobjectModule (ModuleCat.of R E)
      have hqRange : so (Subobject.mk q) = V :=
        (subobjectModule_mk_eq_range q).trans (Submodule.range_subtype _)
      have hq : Subobject.mk q ≠ ⊥ := by
        intro h
        have hv : V = ⊥ := by rw [← hqRange, h, so.map_bot]
        have hxV : x.1 ∈ V := Submodule.mem_span_singleton_self _
        rw [hv] at hxV
        exact hx0 (by simpa using hxV)
      have hess := hi.2 (Subobject.mk q) hq
      have hInf : so (Subobject.mk q ⊓ Subobject.mk i) =
          V ⊓ LinearMap.range i.hom := by
        rw [so.map_inf, hqRange, subobjectModule_mk_eq_range i]
      have hmeet : V ⊓ LinearMap.range i.hom ≠ ⊥ := by
        intro hbot
        apply hess
        apply so.injective
        rw [hInf, hbot, so.map_bot]
      obtain ⟨z, hz, hz0⟩ := (V ⊓ LinearMap.range i.hom).ne_bot_iff.mp hmeet
      have hzV : z ∈ V := hz.1
      have hzI : z ∈ LinearMap.range i.hom := hz.2
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hzV
      have haNot : a ∉ IsLocalRing.maximalIdeal R := by
        intro ha
        apply hz0
        have hxax := (Submodule.mem_torsionBySet_iff _ _).1 x.property ⟨a, ha⟩
        simpa using hxax
      have hau : IsUnit a := IsLocalRing.notMem_maximalIdeal.mp haNot
      obtain ⟨u, rfl⟩ := hau
      have hxI : x.1 ∈ LinearMap.range i.hom := by
        have hzu : (↑(u⁻¹) : R) • (u • x.1) = x.1 := by
          calc
            (↑(u⁻¹) : R) • ((u : R) • x.1) =
                ((↑(u⁻¹) : R) * (u : R)) • x.1 := by rw [smul_smul]
            _ = x.1 := by rw [Units.inv_mul, one_smul]
        rw [← hzu]
        exact (LinearMap.range i.hom).smul_mem _ hzI
      obtain ⟨y, hy⟩ := hxI
      exact ⟨y, Subtype.ext hy⟩
  exact LinearEquiv.ofBijective f ⟨hf, hsurj⟩

/-- An element killed by a family of scalars is killed by the ideal they span. -/
private theorem smul_eq_zero_of_mem_span_range {R M ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (a : ι → R) (x : M) (h : ∀ j, a j • x = 0) :
    ∀ r ∈ Submodule.span R (Set.range a), r • x = 0 := fun _ hr ↦
  Submodule.span_le.2 (Set.range_subset_iff.2 h : Set.range a ⊆ LinearMap.ker
    (LinearMap.toSpanSingleton R M x)) hr

/-- An element killed by an ideal of `A` is killed by its extension to `B`. -/
private theorem smul_eq_zero_of_mem_map {A B N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] (I : Ideal A) (x : N)
    (h : ∀ a ∈ I, a • x = 0) : ∀ b ∈ Ideal.map (algebraMap A B) I, b • x = 0 := by
  intro b hb
  have hle : Ideal.map (algebraMap A B) I ≤ LinearMap.ker (LinearMap.toSpanSingleton B N x) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    simpa [algebraMap_smul] using h a ha
  simpa using hle hb

private noncomputable def torsionByIdealTensorEquiv
    (A B E : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [Algebra A B] [Module.Flat A B]
    [AddCommGroup E] [Module A E]
    (I : Ideal A) (J : Ideal B)
    (hIJ : Ideal.map (algebraMap A B) I = J) :
    let S := Submodule.torsionBySet A E (I : Set A)
    let T := Submodule.torsionBySet B (B ⊗[A] E) (J : Set B)
    B ⊗[A] S ≃ₗ[B] T := by
  classical
  let mA : Ideal A := I
  let mB : Ideal B := J
  let N := B ⊗[A] E
  let S : Submodule A E := Submodule.torsionBySet A E (mA : Set A)
  let T : Submodule B N := Submodule.torsionBySet B N (mB : Set B)
  let hgen := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian mA)
  let n : ℕ := hgen.choose
  let a : Fin n → A := hgen.choose_spec.choose
  have ha : Submodule.span A (Set.range a) = mA := hgen.choose_spec.choose_spec
  let f : E →ₗ[A] (Fin n → E) :=
    { toFun := fun x j => a j • x
      map_add' := by intro x y; funext j; simp [smul_add]
      map_smul' := by intro r x; funext j; simp [smul_smul, mul_comm] }
  let ePi := TensorProduct.piRight A B B (fun _ : Fin n => E)
  let ltf := TensorProduct.AlgebraTensorModule.lTensor B B f
  let g : N →ₗ[B] (Fin n → N) := ePi.toLinearMap.comp ltf
  have hg_apply (x : N) (j : Fin n) : g x j = (algebraMap A B (a j : A)) • x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul b x =>
      change (TensorProduct.piRight A B B (fun _ : Fin n => E)
        (b ⊗ₜ[A] f x)) j = (algebraMap A B (a j : A)) • (b ⊗ₜ[A] x)
      rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
      change b ⊗ₜ[A] (a j • x) = (algebraMap A B (a j : A)) • (b ⊗ₜ[A] x)
      simp [TensorProduct.smul_tmul']
  have hfker : LinearMap.ker f = S := by
    ext x
    change (f x = 0) ↔ x ∈ Submodule.torsionBySet A E (mA : Set A)
    rw [Submodule.mem_torsionBySet_iff]
    constructor
    · intro hx r
      have hx' : ∀ j, a j • x = 0 := fun j => by simpa [f] using congrFun hx j
      have hr' : (r : A) ∈ Submodule.span A (Set.range a) := ha.symm ▸ r.property
      exact smul_eq_zero_of_mem_span_range a x hx' r hr'
    · intro hx
      have hx' : ∀ r : mA, (r : A) • x = 0 := hx
      funext j
      exact hx' ⟨a j, ha ▸ Submodule.subset_span ⟨j, rfl⟩⟩
  have hkerEq (x : N) : g x = 0 ↔ ltf x = 0 := by
    constructor
    · exact fun hx ↦ ePi.injective (by simpa [g] using hx)
    · intro hx
      simp [g, ltf, hx]
  let eKer : LinearMap.ker ltf ≃ₗ[B] LinearMap.ker g :=
    { toFun := fun x => ⟨x.1, (hkerEq x.1).2 x.2⟩
      invFun := fun x => ⟨x.1, (hkerEq x.1).1 x.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }
  have hgker : LinearMap.ker g = T := by
    ext x
    change (g x = 0) ↔ x ∈ Submodule.torsionBySet B N (mB : Set B)
    rw [Submodule.mem_torsionBySet_iff]
    constructor
    · intro hx b
      have hx' : ∀ j, a j • x = 0 := fun j => by
        have hj := congrFun hx j
        rw [hg_apply, algebraMap_smul] at hj
        exact hj
      have hkillA : ∀ r ∈ mA, r • x = 0 := fun r hr =>
        smul_eq_zero_of_mem_span_range a x hx' r (ha.symm ▸ hr)
      exact smul_eq_zero_of_mem_map (B := B) mA x hkillA b (hIJ.symm ▸ b.property)
    · intro hx
      funext j
      have hx' : ∀ b : mB, (b : B) • x = 0 := hx
      have haj : a j ∈ mA := ha ▸ Submodule.subset_span ⟨j, rfl⟩
      have hbjMap : (algebraMap A B (a j : A)) ∈ Ideal.map (algebraMap A B) mA :=
        Ideal.mem_map_of_mem (algebraMap A B) haj
      have hbj : (algebraMap A B (a j : A)) ∈ mB := by
        change (algebraMap A B (a j : A)) ∈ J
        rw [← hIJ]
        exact hbjMap
      have h := hx' ⟨algebraMap A B (a j), hbj⟩
      rw [hg_apply]
      exact h
  let eKS : LinearMap.ker f ≃ₗ[A] S :=
    { toFun := fun x => ⟨x.1, hfker ▸ x.2⟩
      invFun := fun x => ⟨x.1, hfker.symm ▸ x.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }
  let eGT : LinearMap.ker g ≃ₗ[B] T :=
    { toFun := fun x => ⟨x.1, hgker ▸ x.2⟩
      invFun := fun x => ⟨x.1, hgker.symm ▸ x.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }
  let e : B ⊗[A] S ≃ₗ[B] T :=
    ((LinearEquiv.baseChange A B (LinearMap.ker f) S eKS).symm.trans
      (LinearMap.tensorKerEquiv B B f)).trans eKer |>.trans eGT
  exact e

private theorem tensor_maximalIdealPowerTorsion
    (A B E : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [Algebra A B] [Module.Flat A B]
    (hmax : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B)
    [AddCommGroup E] [Module A E]
    (i : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ ModuleCat.of A E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    ∀ x : B ⊗[A] E,
      ∃ n : ℕ, ∀ r ∈ (IsLocalRing.maximalIdeal B ^ n : Ideal B), r • x = 0 := by
  classical
  let mA : Ideal A := IsLocalRing.maximalIdeal A
  let mB : Ideal B := IsLocalRing.maximalIdeal B
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨max n m, ?_⟩
    intro r hr
    have hrn : r ∈ (mB ^ n : Ideal B) :=
      Ideal.pow_le_pow_right (Nat.le_max_left n m) hr
    have hrm : r ∈ (mB ^ m : Ideal B) :=
      Ideal.pow_le_pow_right (Nat.le_max_right n m) hr
    rw [smul_add, hn r hrn, hm r hrm, zero_add]
  | tmul b e =>
    obtain ⟨n, hn⟩ := injectiveHull_maximalIdealPowerTorsion A E i hi e
    refine ⟨n, ?_⟩
    intro r hr
    have hpow : Ideal.map (algebraMap A B) (mA ^ n) = mB ^ n := by
      rw [Ideal.map_pow, hmax]
    exact smul_eq_zero_of_mem_map (B := B) (mA ^ n) (b ⊗ₜ[A] e)
      (fun a ha => by rw [← TensorProduct.tmul_smul, hn a ha, TensorProduct.tmul_zero])
      r (hpow ▸ hr)

/-- The quotient of a local ring by a positive power of its maximal ideal is local. -/
private theorem isLocalRing_quotient_maximalIdealPow
    (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) (hn : 0 < n) :
    IsLocalRing (R ⧸ (IsLocalRing.maximalIdeal R ^ n : Ideal R)) := by
  have hIlt : (IsLocalRing.maximalIdeal R ^ n : Ideal R) < ⊤ :=
    (Ideal.pow_le_self (Nat.ne_zero_of_lt hn)).trans_lt
      (IsLocalRing.maximalIdeal.isMaximal R).lt_top
  have := (Ideal.Quotient.nontrivial_iff).mpr hIlt.ne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

private theorem artinian_quotient_maximalIdealPow
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)
    (hn : 0 < n) : IsArtinianRing (R ⧸ (IsLocalRing.maximalIdeal R ^ n : Ideal R)) := by
  classical
  let I : Ideal R := IsLocalRing.maximalIdeal R ^ n
  let Q := R ⧸ I
  have := isLocalRing_quotient_maximalIdealPow R n hn
  have hmap : Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal Q :=
    IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
  refine ⟨n, ?_⟩
  rw [← hmap, ← Ideal.map_pow]
  apply (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk I)).2
  rw [Ideal.mk_ker]

private noncomputable def residueFieldQuotientEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)
    (hn : 0 < n) [IsLocalRing (R ⧸ (IsLocalRing.maximalIdeal R ^ n : Ideal R))] :
    IsLocalRing.ResidueField R ≃ₗ[R]
      IsLocalRing.ResidueField (R ⧸ (IsLocalRing.maximalIdeal R ^ n : Ideal R)) := by
  classical
  let I : Ideal R := IsLocalRing.maximalIdeal R ^ n
  let Q := R ⧸ I
  have hIle : I ≤ IsLocalRing.maximalIdeal R :=
    Ideal.pow_le_self (I := IsLocalRing.maximalIdeal R) (Nat.ne_zero_of_lt hn)
  have hmap : Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal Q :=
    IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let e1 : Q ⧸ IsLocalRing.maximalIdeal Q ≃+* Q ⧸
      Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal R) :=
    Ideal.quotEquivOfEq hmap.symm
  let e2 : Q ⧸ Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal R) ≃+*
      IsLocalRing.ResidueField R := DoubleQuot.quotQuotEquivQuotOfLE hIle
  let e : IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField Q :=
    (e1.trans e2).symm
  have hcomm (r : R) : e (algebraMap R (IsLocalRing.ResidueField R) r) =
      algebraMap R (IsLocalRing.ResidueField Q) r := by
    apply (e1.trans e2).injective
    simp only [e]
    change e2 (e1 (Ideal.Quotient.mk _ (Ideal.Quotient.mk I r))) =
      Ideal.Quotient.mk _ r
    simp only [e1, Ideal.quotEquivOfEq_mk]
    change DoubleQuot.quotQuotEquivQuotOfLE hIle
      (DoubleQuot.quotQuotMk I (IsLocalRing.maximalIdeal R) r) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) r
    exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk r hIle
  refine
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := ?_ }
  intro r x
  simp only [Algebra.smul_def, e.map_mul, hcomm, RingHom.id_apply]
  rfl

/-- Precomposing an injective hull with the inverse of a linear equivalence gives an injective
hull. -/
private theorem exists_mono_isInjectiveHull_comp_symm
    {R K K' E : Type u} [CommRing R] [AddCommGroup K] [Module R K] [AddCommGroup K']
    [Module R K'] [AddCommGroup E] [Module R E] (e : K ≃ₗ[R] K')
    (i : ModuleCat.of R K ⟶ ModuleCat.of R E) [Mono i] (hi : Module.IsInjectiveHull i) :
    ∃ _ : Mono (ModuleCat.ofHom (i.hom.comp e.symm.toLinearMap)),
      Module.IsInjectiveHull (ModuleCat.ofHom (i.hom.comp e.symm.toLinearMap)) := by
  have : Mono (ModuleCat.ofHom (i.hom.comp e.symm.toLinearMap)) :=
    (ModuleCat.mono_iff_injective _).2
      (((ModuleCat.mono_iff_injective i).1 inferInstance).comp e.symm.injective)
  refine ⟨this, hi.1, fun q hq => ?_⟩
  have hmk : Subobject.mk (ModuleCat.ofHom (i.hom.comp e.symm.toLinearMap)) = Subobject.mk i :=
    Subobject.mk_eq_mk_of_comm _ _ e.symm.toModuleIso (by ext; simp)
  rw [hmk]
  exact hi.2 q hq

private theorem length_maximalIdealPowTorsion_eq_quotient
    (R E : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (IsLocalRing.ResidueField R) ⟶ ModuleCat.of R E) [Mono i]
    (hi : Module.IsInjectiveHull i) (n : ℕ) :
    Module.length R
        (Submodule.torsionBySet R E
          ((IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R) : Set R)) =
      Module.length R (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R)) := by
  classical
  let I : Ideal R := IsLocalRing.maximalIdeal R ^ (n + 1)
  let Q := R ⧸ I
  have hn : 0 < n + 1 := Nat.succ_pos n
  have := isLocalRing_quotient_maximalIdealPow R (n + 1) hn
  let : IsArtinianRing Q := artinian_quotient_maximalIdealPow R (n + 1) hn
  let e := residueFieldQuotientEquiv R (n + 1) hn
  let iQ : ModuleCat.of R (IsLocalRing.ResidueField Q) ⟶ ModuleCat.of R E :=
    ModuleCat.ofHom (i.hom.comp e.symm.toLinearMap)
  obtain ⟨_ : Mono iQ, hIQ⟩ := exists_mono_isInjectiveHull_comp_symm e i hi
  let hK := residueFieldModelIsTorsionByMaximalIdealPow R
    (ModuleCat.of R (IsLocalRing.ResidueField Q)) e n
  let EA : Submodule R (ModuleCat.of R E) :=
    maximalIdealPowTorsion R (ModuleCat.of R E) n
  let hEA : Module.IsTorsionBySet R EA (I : Set R) :=
    Submodule.torsionBySet_isTorsionBySet _
  let : Module Q EA := hEA.module
  let j := residueFieldToMaximalIdealPowTorsion R
    (K := ModuleCat.of R (IsLocalRing.ResidueField Q)) (E := ModuleCat.of R E) e iQ n
  have hHull := maximalIdealPowTorsion_isInjectiveHull R
    (ModuleCat.of R (IsLocalRing.ResidueField Q)) (ModuleCat.of R E) e iQ hIQ n
  have hLenHull : Module.length Q EA = Module.length Q Q := by
    let : Module Q (IsLocalRing.ResidueField Q) :=
      IsLocalRing.instModuleResidueFieldOfAlgebra Q
    have hImem (x : IsLocalRing.ResidueField Q) : iQ.hom x ∈ EA := by
      apply (Submodule.mem_torsionBySet_iff _ _).2
      intro a
      have hx := congrArg iQ.hom (@hK x a)
      calc
        (a : R) • iQ.hom x = iQ.hom ((a : R) • x) :=
          (iQ.hom.map_smul (a : R) x).symm
        _ = iQ.hom 0 := hx
        _ = 0 := iQ.hom.map_zero
    let jStd : IsLocalRing.ResidueField Q →ₗ[Q] EA :=
      { toFun := fun x => ⟨iQ.hom x, hImem x⟩
        map_add' := fun x y => Subtype.ext (iQ.hom.map_add x y)
        map_smul' := fun q x => by
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
          apply Subtype.ext
          have hmap : algebraMap Q (IsLocalRing.ResidueField Q)
              (Ideal.Quotient.mk I r) = algebraMap R (IsLocalRing.ResidueField Q) r := by
            change algebraMap Q (IsLocalRing.ResidueField Q) (algebraMap R Q r) = _
            exact IsScalarTower.algebraMap_apply R Q (IsLocalRing.ResidueField Q) r
          have hx : (Ideal.Quotient.mk I r : Q) • x = r • x := by
            rw [Algebra.smul_def, hmap, Algebra.smul_def]
          calc
            iQ.hom ((Ideal.Quotient.mk I r : Q) • x) = iQ.hom (r • x) := by rw [hx]
            _ = r • iQ.hom x := iQ.hom.map_smul r x
            _ = ((Ideal.Quotient.mk I r : Q) • (⟨iQ.hom x, hImem x⟩ : EA)).val := by
              rw [Module.IsTorsionBySet.mk_smul hEA r]
              rfl }
    let jStdCat := ModuleCat.ofHom jStd
    let : Mono jStdCat := (ModuleCat.mono_iff_injective _).2 fun x y hxy ↦
      (ModuleCat.mono_iff_injective iQ).1 inferInstance (congrArg Subtype.val hxy)
    let jCat : _ := by
      let : Module Q (IsLocalRing.ResidueField Q) := hK.module
      exact ModuleCat.ofHom j
    let : Mono jCat := by
      let : Module Q (IsLocalRing.ResidueField Q) := hK.module
      exact (ModuleCat.mono_iff_injective _).2 <|
        residueFieldToMaximalIdealPowTorsion_injective R
          (K := ModuleCat.of R (IsLocalRing.ResidueField Q)) (E := ModuleCat.of R E)
          e iQ ((ModuleCat.mono_iff_injective iQ).1 inferInstance) n
    have hHullStd : Module.IsInjectiveHull jStdCat := by
      refine ⟨hHull.1, ?_⟩
      let so := ModuleCat.subobjectModule (ModuleCat.of Q EA)
      have hRangeSet : Set.range jStd = Set.range j := by
        ext y
        constructor <;> rintro ⟨x, rfl⟩ <;> exact ⟨x, rfl⟩
      have hmk : Subobject.mk jStdCat = Subobject.mk jCat := by
        apply so.injective
        rw [subobjectModule_mk_eq_range jStdCat, subobjectModule_mk_eq_range jCat]
        exact Submodule.ext (Set.ext_iff.mp hRangeSet)
      intro q hq
      rw [hmk]
      exact hHull.2 q hq
    exact length_injectiveHull_eq_length_ring Q EA jStdCat hHullStd
  have hLenEA : Module.length R EA = Module.length Q EA :=
    length_eq_length_quotient_action R I EA hEA
  have hLenQ : Module.length R Q = Module.length Q Q :=
    length_restrictScalars_eq_of_surjective R Q (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective Q
  exact hLenEA.trans (hLenHull.trans hLenQ.symm)

private theorem length_maximalIdealPowTorsion_ne_top
    (R E : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R (IsLocalRing.ResidueField R) ⟶ ModuleCat.of R E) [Mono i]
    (hi : Module.IsInjectiveHull i) (n : ℕ) :
    Module.length R
        (Submodule.torsionBySet R E
          ((IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R) : Set R)) ≠ ⊤ := by
  classical
  rw [length_maximalIdealPowTorsion_eq_quotient R E i hi n]
  let I : Ideal R := IsLocalRing.maximalIdeal R ^ (n + 1)
  let Q := R ⧸ I
  have hn : 0 < n + 1 := Nat.succ_pos n
  have := isLocalRing_quotient_maximalIdealPow R (n + 1) hn
  let : IsArtinianRing Q := artinian_quotient_maximalIdealPow R (n + 1) hn
  have hLen : Module.length R Q = Module.length Q Q :=
    length_restrictScalars_eq_of_surjective R Q (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective Q
  rw [hLen]
  exact Module.length_ne_top

private theorem length_residueField_eq_one
    (R : Type u) [CommRing R] [IsLocalRing R] :
    Module.length R (IsLocalRing.ResidueField R) = 1 := by
  rw [Module.length_eq_one_iff]
  change IsSimpleModule R (R ⧸ IsLocalRing.maximalIdeal R)
  exact (isSimpleModule_iff_isCoatom (R := R) (M := R)
      (m := IsLocalRing.maximalIdeal R)).2
      (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal R))

private theorem length_tensor_quotient_eq
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) :
    Module.length B (B ⊗[A] (A ⧸ I)) =
      Module.length B (B ⧸ Ideal.map (algebraMap A B) I) := by
  let e1 := Algebra.TensorProduct.tensorQuotientEquiv (R := A) B A B I
  let r := Algebra.TensorProduct.rid A B B
  let J : Ideal (B ⊗[A] A) :=
    Ideal.map (Algebra.TensorProduct.includeRight : A →ₐ[A] B ⊗[A] A).toRingHom I
  have hJ : Ideal.map (algebraMap A B) I =
      Ideal.map (r : (B ⊗[A] A) →+* B) J := by
    change Ideal.map (algebraMap A B) I = Ideal.map (r : (B ⊗[A] A) →+* B)
      (Ideal.map (Algebra.TensorProduct.includeRight : A →ₐ[A] B ⊗[A] A).toRingHom I)
    rw [Ideal.map_map]
    congr 1
    ext a
    change algebraMap A B a = r (Algebra.TensorProduct.includeRight a)
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.rid_tmul]
    change algebraMap A B a = a • (1 : B)
    rw [Algebra.smul_def, mul_one]
  let e2 := Ideal.quotientEquivAlg (R₁ := B) J (Ideal.map (algebraMap A B) I) r hJ
  let e : (B ⊗[A] (A ⧸ I)) ≃ₐ[B] (B ⧸ Ideal.map (algebraMap A B) I) := e1.trans e2
  rw [e.toLinearEquiv.length_eq]

private theorem length_tensorMaximalIdealPowTorsion_eq
    (A B E E' : Type u) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (hmax : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B)
    [AddCommGroup E] [Module A E]
    (i : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ ModuleCat.of A E) [Mono i]
    (hi : Module.IsInjectiveHull i)
    [AddCommGroup E'] [Module B E']
    (i' : ModuleCat.of B (IsLocalRing.ResidueField B) ⟶ ModuleCat.of B E') [Mono i']
    (hi' : Module.IsInjectiveHull i') (n : ℕ) :
    Module.length B
        (Submodule.torsionBySet B (B ⊗[A] E)
          ((IsLocalRing.maximalIdeal B ^ (n + 1) : Ideal B) : Set B)) =
      Module.length B
        (Submodule.torsionBySet B E'
          ((IsLocalRing.maximalIdeal B ^ (n + 1) : Ideal B) : Set B)) := by
  classical
  let mA : Ideal A := IsLocalRing.maximalIdeal A
  let mB : Ideal B := IsLocalRing.maximalIdeal B
  let IA : Ideal A := mA ^ (n + 1)
  let IB : Ideal B := mB ^ (n + 1)
  let EA : Submodule A E := Submodule.torsionBySet A E (IA : Set A)
  let NB : Submodule B (B ⊗[A] E) := Submodule.torsionBySet B
    (B ⊗[A] E) (IB : Set B)
  let EB : Submodule B E' := Submodule.torsionBySet B E' (IB : Set B)
  have hmap : Ideal.map (algebraMap A B) IA = IB := by
    dsimp only [IA, IB, mA, mB]
    rw [Ideal.map_pow, hmax]
  let eT := torsionByIdealTensorEquiv A B E IA IB hmap
  have hResidueLength : Module.length B (B ⧸ extendedMaximalIdeal A B) = 1 := by
    unfold extendedMaximalIdeal
    rw [hmax]
    change Module.length B (IsLocalRing.ResidueField B) = 1
    exact length_residueField_eq_one B
  have hbc (M : Type u) [AddCommGroup M] [Module A M] :
      Module.length A M = Module.length B (B ⊗[A] M) := by
    have h := length_baseChange_eq_length_mul_length_quotient A B M
    rwa [hResidueLength, mul_one] at h
  have hquot : Module.length A (A ⧸ IA) = Module.length B (B ⧸ IB) := by
    calc
      Module.length A (A ⧸ IA) = Module.length B (B ⊗[A] (A ⧸ IA)) := hbc _
      _ = Module.length B (B ⧸ Ideal.map (algebraMap A B) IA) :=
        length_tensor_quotient_eq A B IA
      _ = Module.length B (B ⧸ IB) := by rw [hmap]
  calc
    Module.length B NB = Module.length B (B ⊗[A] EA) := eT.length_eq.symm
    _ = Module.length A EA := (hbc EA).symm
    _ = Module.length A (A ⧸ IA) :=
      length_maximalIdealPowTorsion_eq_quotient A E i hi n
    _ = Module.length B (B ⧸ IB) := hquot
    _ = Module.length B EB :=
      (length_maximalIdealPowTorsion_eq_quotient B E' i' hi' n).symm

/-- Under a flat local homomorphism of Noetherian local rings whose target maximal ideal is
extended from the source, the base change of an injective hull of the source residue field is an
injective hull of the target residue field. -/
@[stacks 0E4E]
theorem exists_isInjectiveHull_tensorProduct
    (A B E : Type u) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (hmax : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B)
    [AddCommGroup E] [Module A E]
    (i : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ ModuleCat.of A E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    ∃ j : ModuleCat.of B (IsLocalRing.ResidueField B) ⟶
        ModuleCat.of B (TensorProduct A B E),
      ∃ _ : Mono j, Module.IsInjectiveHull j := by
  classical
  let N := B ⊗[A] E
  let mA : Ideal A := IsLocalRing.maximalIdeal A
  let mB : Ideal B := IsLocalRing.maximalIdeal B
  let SA : Submodule A E := Submodule.torsionBySet A E (mA : Set A)
  let SB : Submodule B N := Submodule.torsionBySet B N (mB : Set B)
  let hSB : Module.IsTorsionBySet B SB (mB : Set B) :=
    Submodule.torsionBySet_isTorsionBySet _
  let hDom : Module.IsTorsionBySet B (B ⊗[A] SA) (mB : Set B) := by
    let eT := torsionByIdealTensorEquiv A B E mA mB hmax
    intro x b
    apply eT.injective
    rw [eT.map_smul, @hSB (eT x) b, eT.map_zero]
  let hkB : Module.IsTorsionBySet B (IsLocalRing.ResidueField B) (mB : Set B) := by
    intro x b
    rw [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq,
      (IsLocalRing.residue_eq_zero_iff (b : B)).2 b.property, zero_mul]
  let : Semiring (B ⧸ mB) := (Ideal.Quotient.ring mB).toSemiring
  let : Module (B ⧸ mB) SB := torsionQuotientModule B SB mB hSB
  let : Module (B ⧸ mB) (B ⊗[A] SA) :=
    torsionQuotientModule B (B ⊗[A] SA) mB hDom
  let : Module (B ⧸ mB) (IsLocalRing.ResidueField B) :=
    torsionQuotientModule B (IsLocalRing.ResidueField B) mB hkB
  let eA := residueFieldSocleEquiv A E i hi
  let eTensor := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl B B) eA
  let eBase := (residueFieldTensorEquiv A B hmax).toLinearEquiv.trans eTensor
  let eT := torsionByIdealTensorEquiv A B E mA mB hmax
  let eBaseK := torsionLinearEquiv B (IsLocalRing.ResidueField B)
    (B ⊗[A] SA) mB hkB hDom eBase
  let eTK := torsionLinearEquiv B (B ⊗[A] SA) SB mB hDom hSB eT
  let eSocle : SB ≃ₗ[B ⧸ mB] IsLocalRing.ResidueField B := eTK.symm.trans eBaseK.symm
  have hResModule : torsionQuotientModule B (IsLocalRing.ResidueField B) mB hkB =
      (Semiring.toModule : Module (B ⧸ mB) (B ⧸ mB)) := by
    apply Module.ext
    funext q x
    induction q using Quotient.inductionOn' with
    | h b => rfl
  have hResFinite : Module.Finite (B ⧸ mB) (IsLocalRing.ResidueField B) := by
    change @Module.Finite (B ⧸ mB) (IsLocalRing.ResidueField B) _ _
      (torsionQuotientModule B (IsLocalRing.ResidueField B) mB hkB)
    have hself : @Module.Finite (B ⧸ mB) (IsLocalRing.ResidueField B)
        _ _ (Semiring.toModule : Module (B ⧸ mB) (B ⧸ mB)) :=
      Module.Finite.self (B ⧸ mB)
    exact hResModule ▸ hself
  have hSocleFinite : Module.Finite (B ⧸ mB) SB :=
    Module.Finite.of_surjective eSocle.symm.toLinearMap eSocle.symm.surjective
  let : Module.Finite (B ⧸ mB) SB := hSocleFinite
  have hResDim : Module.finrank (B ⧸ mB) (IsLocalRing.ResidueField B) = 1 := by
    have hfr := congrArg
      (fun M : Module (B ⧸ mB) (IsLocalRing.ResidueField B) =>
        @Module.finrank (B ⧸ mB) (IsLocalRing.ResidueField B) _ _ M) hResModule
    exact hfr.trans (Module.finrank_self (B ⧸ mB))
  have hSocleDim : Module.finrank (B ⧸ mB) SB = 1 := by
    rw [eSocle.finrank_eq]
    exact hResDim
  have hSBModule : torsionQuotientModule B SB mB hSB = hSB.module := rfl
  have hSocleFiniteCanonical : @Module.Finite (B ⧸ mB) SB _ _ hSB.module :=
    hSBModule ▸ hSocleFinite
  have hSocleDimCanonical :
      @Module.finrank (B ⧸ mB) SB _ _ hSB.module = 1 := by
    have hfr := congrArg
      (fun M : Module (B ⧸ mB) SB => @Module.finrank (B ⧸ mB) SB _ _ M) hSBModule
    exact hfr.symm.trans hSocleDim
  let eRes : (B ⧸ mB) ≃ₗ[B] IsLocalRing.ResidueField B :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r x
        rfl }
  obtain ⟨E', jQ, hjQ, hEQ⟩ :=
    Module.exists_isInjectiveHull B (ModuleCat.of B (B ⧸ mB))
  let : Mono jQ := hjQ
  let j' : ModuleCat.of B (IsLocalRing.ResidueField B) ⟶ E' :=
    ModuleCat.ofHom (jQ.hom.comp eRes.symm.toLinearMap)
  obtain ⟨_ : Mono j', hEHull⟩ := exists_mono_isInjectiveHull_comp_symm eRes jQ hEQ
  have hTorsion : ∀ x : N, ∃ e : ℕ,
      ∀ r ∈ (mB ^ e : Ideal B), r • x = 0 :=
    tensor_maximalIdealPowerTorsion A B E hmax i hi
  have hEmbed : ∃ fPi : N →ₗ[B] (Fin 1 → E'), Function.Injective fPi := by
    let moduleKS : Module (B ⧸ mB) SB := by
      dsimp only [SB, mB]
      infer_instance
    let : Module (B ⧸ mB) SB := moduleKS
    let : Module.Finite (B ⧸ mB) SB := hSocleFiniteCanonical
    exact exists_injective_to_pi_injectiveHull
      B N E' (i := jQ) hEQ hTorsion 1 hSocleDimCanonical
  obtain ⟨fPi, hfPi⟩ := hEmbed
  let ePi := LinearEquiv.funUnique (Fin 1) B E'
  let f : N →ₗ[B] E' := ePi.toLinearMap.comp fPi
  have hf : Function.Injective f := ePi.injective.comp hfPi
  let Nn (n : ℕ) : Submodule B N :=
    Submodule.torsionBySet B N ((mB ^ (n + 1) : Ideal B) : Set B)
  let E'n (n : ℕ) : Submodule B E' :=
    Submodule.torsionBySet B E' ((mB ^ (n + 1) : Ideal B) : Set B)
  let fN (n : ℕ) : Nn n →ₗ[B] E'n n :=
    (LinearMap.codRestrict (E'n n) (f.comp (Nn n).subtype) (by
      intro x
      apply (Submodule.mem_torsionBySet_iff _ _).2
      intro r
      have hx := (Submodule.mem_torsionBySet_iff _ _).1 x.property r
      change (r : B) • f (x : N) = 0
      calc
        (r : B) • f (x : N) = f ((r : B) • (x : N)) := (f.map_smul _ _).symm
        _ = f 0 := congrArg f hx
        _ = 0 := f.map_zero))
  have hLayerSurj (n : ℕ) : Function.Surjective (fN n) := by
    have hfN : Function.Injective (fN n) := fun x y hxy ↦
      Subtype.ext (hf (congrArg Subtype.val hxy))
    have hlen : Module.length B (Nn n) = Module.length B (E'n n) :=
      length_tensorMaximalIdealPowTorsion_eq A B E E' hmax i hi j' hEHull n
    have hlenRange :
        Module.length B (LinearMap.range (fN n)) = Module.length B (E'n n) :=
      (LinearEquiv.ofInjective (fN n) hfN).length_eq.symm.trans hlen
    have hnotTop : Module.length B (E'n n) ≠ ⊤ :=
      length_maximalIdealPowTorsion_ne_top B E' j' hEHull n
    have hFinite := (Module.length_ne_top_iff).1 hnotTop
    let : IsNoetherian B (E'n n) :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp hFinite).1
    let : IsArtinian B (E'n n) :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp hFinite).2
    have hRangeTop : LinearMap.range (fN n) = ⊤ := by
      by_contra hproper
      have hlt := Submodule.length_lt (R := B) (M := E'n n) hproper
      rw [hlenRange] at hlt
      exact lt_irrefl _ hlt
    exact LinearMap.range_eq_top.mp hRangeTop
  have hfSurj : Function.Surjective f := by
    intro y
    obtain ⟨n, hyn⟩ := exists_mem_maximalIdealPowTorsion B E' j' hEHull y
    obtain ⟨x, hx⟩ := hLayerSurj n ⟨y, hyn⟩
    exact ⟨x.1, congrArg Subtype.val hx⟩
  let e : N ≃ₗ[B] E' := LinearEquiv.ofBijective f ⟨hf, hfSurj⟩
  let j : ModuleCat.of B (IsLocalRing.ResidueField B) ⟶ ModuleCat.of B N :=
    ModuleCat.ofHom (e.symm.toLinearMap.comp j'.hom)
  have hj : Mono j := (ModuleCat.mono_iff_injective j).2
    (e.symm.injective.comp ((ModuleCat.mono_iff_injective j').1 inferInstance))
  let : Mono j := hj
  have hInjectiveModule : Module.Injective B N := by
    apply (Module.injective_iff_injective_object B N).mpr
    have hObjE : CategoryTheory.Injective (ModuleCat.of B E') := hEHull.1
    exact CategoryTheory.Injective.of_iso e.toModuleIso.symm hObjE
  have hEssential : Module.IsEssentialMono j := by
    let qIso := Subobject.mapIsoToOrderIso e.toModuleIso
    have hmk : qIso (Subobject.mk j) = Subobject.mk j' := by
      change (Subobject.map e.toModuleIso.hom).obj (Subobject.mk j) =
        Subobject.mk j'
      rw [Subobject.map_mk]
      apply Subobject.mk_eq_mk_of_comm _ _ (Iso.refl _)
      ext x
      change j'.hom x = e (e.symm (j'.hom x))
      exact (e.apply_symm_apply (j'.hom x)).symm
    intro q hq
    have hq' : qIso q ≠ ⊥ := fun hz ↦
      hq (qIso.injective (by simpa only [qIso.map_bot] using hz))
    have hmeet := hEHull.2 (qIso q) hq'
    have hmap : qIso (q ⊓ Subobject.mk j) = qIso q ⊓ Subobject.mk j' := by
      rw [qIso.map_inf, hmk]
    intro hz
    apply hmeet
    rw [← hmap, hz, qIso.map_bot]
  have hHull : Module.IsInjectiveHull j :=
    ⟨(Module.injective_iff_injective_object B N).mp hInjectiveModule, hEssential⟩
  exact ⟨j, hj, hHull⟩

end FlatLocalBaseChange

end Dualizing
