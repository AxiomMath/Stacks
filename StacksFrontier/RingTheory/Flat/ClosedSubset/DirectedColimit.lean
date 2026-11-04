module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Algebra.DirectLimit.Descent

/-!
# Ideals, tensor products and localizations in a directed colimit of rings

Auxiliary results on a directed colimit `A` of commutative rings `A i`, used to descend flatness
along a closed subset to a stage of the colimit.

## Main results

* `Ideal.exists_ge_sup_map_eq_top`: a unit-ideal relation between the colimit of a compatible
  family of ideals and an ideal of a fixed stage already holds at a later stage.
* `IsDirectedColimit.tensorLeft`, `IsDirectedColimit.restrict_Ici`,
  `IsDirectedColimit.localizationAway`: directed colimits are preserved by tensoring, by
  restricting to an upper set of indices and by localizing at an element.
* `TensorProduct.exists_rep_and_eventually_zero_of_directedColimit`: elements of a tensor product
  over a directed colimit come from a stage, and relations hold at a later stage.
* `Algebra.FinitePresentation.tensorProduct_right`: finite presentation is stable under base
  change.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x uS uM uL uT uA uB uLam

/-! ### Ideals in a directed colimit -/

/-- Compatible base ideals remain compatible after tensoring with a fixed algebra. -/
theorem Ideal.map_includeRight_le_of_map_le
    {R : Type u} {S : Type v} {T U : Type w}
    [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra R U]
    (f : T →ₐ[R] U) (I : Ideal T) (J : Ideal U)
    (hI : Ideal.map f.toRingHom I ≤ J) :
    Ideal.map (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom
      (Ideal.map
        (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := T)).toRingHom I) ≤
    Ideal.map
      (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := U)).toRingHom J := by
  let incT : T →ₐ[R] S ⊗[R] T := Algebra.TensorProduct.includeRight
  let incU : U →ₐ[R] S ⊗[R] U := Algebra.TensorProduct.includeRight
  let g : S ⊗[R] T →ₐ[R] S ⊗[R] U :=
    Algebra.TensorProduct.map (AlgHom.id R S) f
  have hcomm : g.toRingHom.comp incT.toRingHom = incU.toRingHom.comp f.toRingHom :=
    congrArg AlgHom.toRingHom
      (Algebra.TensorProduct.map_comp_includeRight (AlgHom.id R S) f)
  show Ideal.map g.toRingHom (Ideal.map incT.toRingHom I) ≤ Ideal.map incU.toRingHom J
  rw [Ideal.map_map, hcomm, ← Ideal.map_map]
  exact Ideal.map_mono hI

/-- An element of a compatible colimit ideal is the image of an element of a stage ideal. -/
theorem Ideal.exists_mem_of_mem_iSup_map
    {R : Type*} [CommRing R] {Λ : Type*} [Preorder Λ] [Nonempty Λ]
    [IsDirected Λ (· ≤ ·)]
    {A : Λ → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {f : ∀ ⦃i j⦄, i ≤ j → A i →ₐ[R] A j}
    {L : Type*} [CommRing L] [Algebra R L] {ρ : ∀ i, A i →ₐ[R] L}
    (hc : IsDirectedColimit A f L ρ) (I : ∀ i, Ideal (A i))
    (hI : ∀ ⦃i j⦄ (h : i ≤ j), Ideal.map (f h).toRingHom (I i) ≤ I j)
    {z : L} (hz : z ∈ ⨆ i, Ideal.map (ρ i).toRingHom (I i)) :
    ∃ i, ∃ y ∈ I i, ρ i y = z := by
  let J : Ideal L :=
    { carrier := {z | ∃ i, ∃ y ∈ I i, ρ i y = z}
      zero_mem' := by
        obtain ⟨i⟩ := ‹Nonempty Λ›
        exact ⟨i, 0, (I i).zero_mem, map_zero _⟩
      add_mem' := by
        rintro z y ⟨i, a, ha, rfl⟩ ⟨j, b, hb, rfl⟩
        obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
        refine ⟨k, f hik a + f hjk b, (I k).add_mem
          (hI hik (Ideal.mem_map_of_mem _ ha))
          (hI hjk (Ideal.mem_map_of_mem _ hb)), ?_⟩
        rw [map_add, hc.comp, hc.comp]
      smul_mem' := by
        rintro c z ⟨i, a, ha, rfl⟩
        obtain ⟨j, b, rfl⟩ := hc.jointly_surjective c
        obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
        refine ⟨k, f hjk b * f hik a,
          (I k).mul_mem_left _ (hI hik (Ideal.mem_map_of_mem _ ha)), ?_⟩
        rw [map_mul, hc.comp, hc.comp]
        rfl }
  have hle : (⨆ i, Ideal.map (ρ i).toRingHom (I i)) ≤ J :=
    iSup_le fun i => Ideal.map_le_iff_le_comap.mpr fun a ha => ⟨i, a, ha, rfl⟩
  exact hle hz

set_option backward.isDefEq.respectTransparency false in
/-- A compatible colimit ideal is the unit ideal only if a stage ideal is the unit ideal. -/
theorem Ideal.iSup_map_eq_top_iff
    {R : Type*} [CommRing R] {Λ : Type*} [Preorder Λ] [Nonempty Λ]
    [IsDirected Λ (· ≤ ·)]
    {A : Λ → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {f : ∀ ⦃i j⦄, i ≤ j → A i →ₐ[R] A j}
    {L : Type*} [CommRing L] [Algebra R L] {ρ : ∀ i, A i →ₐ[R] L}
    (hc : IsDirectedColimit A f L ρ) (I : ∀ i, Ideal (A i))
    (hI : ∀ ⦃i j⦄ (h : i ≤ j), Ideal.map (f h).toRingHom (I i) ≤ I j) :
    (⨆ i, Ideal.map (ρ i).toRingHom (I i)) = ⊤ ↔ ∃ i, I i = ⊤ := by
  constructor
  · intro htop
    obtain ⟨i, a, ha, hea⟩ := Ideal.exists_mem_of_mem_iSup_map hc I hI
      (show (1 : L) ∈ ⨆ i, Ideal.map (ρ i).toRingHom (I i) by
        rw [htop]; exact Submodule.mem_top)
    obtain ⟨j, hij, hj⟩ := hc.exists_eq_zero (a - 1) (by simp [hea])
    have hj' : f hij a = 1 := by simpa only [map_sub, map_one, sub_eq_zero] using hj
    refine ⟨j, Ideal.eq_top_of_isUnit_mem (I j) ?_ isUnit_one⟩
    rw [← hj']
    exact hI hij (Ideal.mem_map_of_mem _ ha)
  · rintro ⟨i, hi⟩
    apply top_unique
    calc
      ⊤ = Ideal.map (ρ i).toRingHom (I i) := by rw [hi, Ideal.map_top]
      _ ≤ ⨆ i, Ideal.map (ρ i).toRingHom (I i) :=
        le_iSup (fun i => Ideal.map (ρ i).toRingHom (I i)) i

set_option backward.isDefEq.respectTransparency false in
/-- A unit-ideal relation between the colimit ideal and a fixed stage ideal holds at some later
stage. -/
theorem Ideal.exists_ge_sup_map_eq_top
    {R : Type*} [CommRing R] {Λ : Type*} [Preorder Λ] [Nonempty Λ]
    [IsDirected Λ (· ≤ ·)]
    {A : Λ → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {f : ∀ ⦃i j⦄, i ≤ j → A i →ₐ[R] A j}
    {L : Type*} [CommRing L] [Algebra R L] {ρ : ∀ i, A i →ₐ[R] L}
    (hc : IsDirectedColimit A f L ρ) (I : ∀ i, Ideal (A i))
    (hI : ∀ ⦃i j⦄ (h : i ≤ j), Ideal.map (f h).toRingHom (I i) ≤ I j)
    (i₀ : Λ) (K : Ideal (A i₀))
    (hcover : (⨆ i, Ideal.map (ρ i).toRingHom (I i)) ⊔
      Ideal.map (ρ i₀).toRingHom K = ⊤) :
    ∃ j, ∃ h : i₀ ≤ j, I j ⊔ Ideal.map (f h).toRingHom K = ⊤ := by
  let J : ∀ i, Ideal (A i) := fun i => I i ⊔ ⨆ h : i₀ ≤ i, Ideal.map (f h).toRingHom K
  have hfcomp {i j k} (hij : i ≤ j) (hjk : j ≤ k) :
      (f hjk).toRingHom.comp (f hij).toRingHom = (f (hij.trans hjk)).toRingHom :=
    RingHom.ext (hc.map_comp hij hjk)
  have hJ : ∀ ⦃i j⦄ (h : i ≤ j), Ideal.map (f h).toRingHom (J i) ≤ J j := by
    intro i j h
    dsimp only [J]
    rw [Ideal.map_sup, Ideal.map_iSup]
    refine sup_le ((hI h).trans le_sup_left) (iSup_le fun hi => ?_)
    rw [Ideal.map_map, hfcomp]
    exact (le_iSup (fun h : i₀ ≤ j => Ideal.map (f h).toRingHom K) (hi.trans h)).trans
      le_sup_right
  have htop : (⨆ i, Ideal.map (ρ i).toRingHom (J i)) = ⊤ := by
    apply top_unique
    rw [← hcover]
    refine sup_le (iSup_le fun i => ?_) ?_
    · exact (Ideal.map_mono (show I i ≤ J i from le_sup_left)).trans
        (le_iSup (fun i => Ideal.map (ρ i).toRingHom (J i)) i)
    · have hself : (f (le_refl i₀)).toRingHom = RingHom.id _ :=
        RingHom.ext (hc.map_id i₀)
      have hK : K ≤ J i₀ := by
        apply le_trans _ (show (⨆ h : i₀ ≤ i₀, Ideal.map (f h).toRingHom K) ≤ J i₀ from
          le_sup_right)
        have hmem := le_iSup (fun h : i₀ ≤ i₀ => Ideal.map (f h).toRingHom K) (le_refl i₀)
        simpa only [hself, Ideal.map_id] using hmem
      exact (Ideal.map_mono hK).trans
        (le_iSup (fun i => Ideal.map (ρ i).toRingHom (J i)) i₀)
  obtain ⟨j, hj⟩ := (Ideal.iSup_map_eq_top_iff hc J hJ).mp htop
  obtain ⟨k, hjk, hik⟩ := directed_of (· ≤ ·) j i₀
  refine ⟨k, hik, ?_⟩
  have hk : J k = ⊤ := by
    have hmap := hJ hjk
    rw [hj, Ideal.map_top] at hmap
    exact top_le_iff.mp hmap
  simpa only [J, iSup_pos hik, sup_idem] using hk

/-- Base change commutes with the compatible colimit ideal. -/
theorem Ideal.map_includeRight_iSup_map
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {Λ : Type*} {A : Λ → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {L : Type*} [CommRing L] [Algebra R L] (ρ : ∀ i, A i →ₐ[R] L)
    (I : ∀ i, Ideal (A i)) :
    Ideal.map (Algebra.TensorProduct.includeRight : L →ₐ[R] S ⊗[R] L).toRingHom
        (⨆ i, Ideal.map (ρ i).toRingHom (I i)) =
      ⨆ i, Ideal.map (Algebra.TensorProduct.map (AlgHom.id R S) (ρ i)).toRingHom
        (Ideal.map (Algebra.TensorProduct.includeRight : A i →ₐ[R] S ⊗[R] A i).toRingHom
          (I i)) := by
  rw [Ideal.map_iSup]
  congr 1
  funext i
  rw [Ideal.map_map, Ideal.map_map]
  congr 1

/-! ### Directed colimits after tensoring and localizing -/

/-- Tensoring with a fixed algebra preserves the elementwise directed-colimit property. -/
theorem IsDirectedColimit.tensorLeft
    {R : Type*} [CommRing R] {Λ : Type*} [Preorder Λ] [Nonempty Λ]
    [IsDirected Λ (· ≤ ·)]
    {A : Λ → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {f : ∀ ⦃i j⦄, i ≤ j → A i →ₐ[R] A j}
    {L : Type*} [CommRing L] [Algebra R L] {ρ : ∀ i, A i →ₐ[R] L}
    (hc : IsDirectedColimit A f L ρ)
    (S : Type*) [CommRing S] [Algebra R S] :
    IsDirectedColimit (fun i => S ⊗[R] A i)
      (fun {_ _} h => Algebra.TensorProduct.map (AlgHom.id R S) (f h))
      (S ⊗[R] L) (fun i => Algebra.TensorProduct.map (AlgHom.id R S) (ρ i)) := by
  have ht := Stacks.DirectLimit.FiniteDescent.IsDirectedColimit.tensor_right S hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j k hij hjk z
    apply (Algebra.TensorProduct.comm R S (A k)).injective
    simpa only [Algebra.TensorProduct.comm_comp_map_apply,
      Stacks.DirectLimit.FiniteDescent.tensorF, Stacks.DirectLimit.FiniteDescent.tensorG] using
        ht.map_comp hij hjk
      (Algebra.TensorProduct.comm R S (A i) z)
  · intro i z
    apply (Algebra.TensorProduct.comm R S (A i)).injective
    simpa only [Algebra.TensorProduct.comm_comp_map_apply,
      Stacks.DirectLimit.FiniteDescent.tensorF, Stacks.DirectLimit.FiniteDescent.tensorG] using
      ht.map_id i (Algebra.TensorProduct.comm R S (A i) z)
  · intro i j hij z
    apply (Algebra.TensorProduct.comm R S L).injective
    simpa only [Algebra.TensorProduct.comm_comp_map_apply,
      Stacks.DirectLimit.FiniteDescent.tensorF, Stacks.DirectLimit.FiniteDescent.tensorG] using
      ht.comp hij (Algebra.TensorProduct.comm R S (A i) z)
  · intro z
    obtain ⟨i, y, hy⟩ := ht.jointly_surjective (Algebra.TensorProduct.comm R S L z)
    refine ⟨i, Algebra.TensorProduct.comm R (A i) S y, ?_⟩
    apply (Algebra.TensorProduct.comm R S L).injective
    rwa [Algebra.TensorProduct.comm_comp_map_apply,
      ← Algebra.TensorProduct.comm_symm R S (A i), AlgEquiv.apply_symm_apply]
  · intro i z hz
    obtain ⟨j, hij, hj⟩ := ht.exists_eq_zero (Algebra.TensorProduct.comm R S (A i) z)
      (by change Algebra.TensorProduct.map (ρ i) (AlgHom.id R S) _ = 0
          rw [← Algebra.TensorProduct.comm_comp_map_apply, hz, map_zero])
    refine ⟨j, hij, ?_⟩
    apply (Algebra.TensorProduct.comm R S (A j)).injective
    simpa only [Algebra.TensorProduct.comm_comp_map_apply,
      Stacks.DirectLimit.FiniteDescent.tensorF, Stacks.DirectLimit.FiniteDescent.tensorG, map_zero]
        using hj

/-- Passing to the stages above a fixed index does not change a directed colimit. -/
theorem IsDirectedColimit.restrict_Ici
    {R : Type*} [CommRing R] {Λ : Type*} [Preorder Λ] [Nonempty Λ]
    [IsDirected Λ (· ≤ ·)]
    {A : Λ → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {f : ∀ ⦃i j⦄, i ≤ j → A i →ₐ[R] A j}
    {L : Type*} [CommRing L] [Algebra R L] {ρ : ∀ i, A i →ₐ[R] L}
    (hc : IsDirectedColimit A f L ρ) (i : Λ) :
    IsDirectedColimit (fun j : Set.Ici i => A j.1)
      (fun {_ _} h => f h) L (fun j => ρ j.1) := by
  refine ⟨fun {_ _ _} hij hjk z => hc.map_comp hij hjk z, fun j => hc.map_id j.1,
    fun {_ _} hij z => hc.comp hij z, ?_, ?_⟩
  · intro z
    obtain ⟨j, y, hy⟩ := hc.jointly_surjective z
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    exact ⟨⟨k, hik⟩, f hjk y, (hc.comp hjk y).trans hy⟩
  · intro j z hz
    obtain ⟨k, hjk, hk⟩ := hc.exists_eq_zero z hz
    exact ⟨⟨k, j.2.trans hjk⟩, hjk, hk⟩

/-- Tensoring an elementwise directed colimit of modules preserves representatives and eventual
vanishing. -/
theorem TensorProduct.exists_rep_and_eventually_zero_of_directedColimit
    {R : Type*} [CommRing R] {Λ : Type*} [Preorder Λ] [Nonempty Λ]
    [IsDirected Λ (· ≤ ·)]
    {A : Λ → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    (f : ∀ i j, i ≤ j → A i →ₗ[R] A j) [DirectedSystem A (fun i j h => f i j h)]
    {L : Type*} [AddCommGroup L] [Module R L] (ρ : ∀ i, A i →ₗ[R] L)
    (hcomp : ∀ i j (h : i ≤ j) z, ρ j (f i j h z) = ρ i z)
    (hsurj : ∀ z : L, ∃ i y, ρ i y = z)
    (hzero : ∀ i z, ρ i z = 0 → ∃ j, ∃ h : i ≤ j, f i j h z = 0)
    (M : Type*) [AddCommGroup M] [Module R M] :
    (∀ z : L ⊗[R] M, ∃ i y, (ρ i).rTensor M y = z) ∧
      (∀ i (z : A i ⊗[R] M), (ρ i).rTensor M z = 0 →
        ∃ j, ∃ h : i ≤ j, (f i j h).rTensor M z = 0) := by
  classical
  let l : Module.DirectLimit A f →ₗ[R] L :=
    Module.DirectLimit.lift R Λ A f ρ hcomp
  have hl : Function.Bijective l := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨i, a, rfl⟩ := Module.DirectLimit.exists_of z
      obtain ⟨j, hij, hj⟩ := hzero i a (by simpa [l] using hz)
      rw [← Module.DirectLimit.of_f (hij := hij), hj, map_zero]
    · intro z
      obtain ⟨i, a, ha⟩ := hsurj z
      exact ⟨Module.DirectLimit.of R Λ A f i a, by simpa [l] using ha⟩
  let e := LinearEquiv.ofBijective l hl
  let t : (Module.DirectLimit (fun i => A i ⊗[R] M)
      (fun i j h => (f i j h).rTensor M)) ≃ₗ[R] L ⊗[R] M :=
    (TensorProduct.directLimitLeft f M).symm.trans
      (TensorProduct.congr e (LinearEquiv.refl R M))
  have ht (i : Λ) (z : A i ⊗[R] M) :
      t (Module.DirectLimit.of R Λ _ (fun i j h => (f i j h).rTensor M) i z) =
        (ρ i).rTensor M z := by
    induction z with
    | zero => simp
    | add z y hz hy => simp only [map_add, hz, hy]
    | tmul a m => simp [t, e, l]
  constructor
  · intro z
    obtain ⟨i, y, hy⟩ := Module.DirectLimit.exists_of (t.symm z)
    refine ⟨i, y, ?_⟩
    rw [← ht, hy, t.apply_symm_apply]
  · intro i z hz
    have hzz : Module.DirectLimit.of R Λ _ (fun i j h => (f i j h).rTensor M) i z = 0 := by
      apply t.injective
      rw [ht, hz, map_zero]
    exact Module.DirectLimit.of.zero_exact hzz

/-- The scalar extension of a module along an algebra homomorphism, as a semilinear map. -/
noncomputable def AlgHom.rTensorSemilinear
    {S B C : Type*} [CommSemiring S] [CommSemiring B] [CommSemiring C]
    [Algebra S B] [Algebra S C] (f : B →ₐ[S] C)
    (M : Type*) [AddCommMonoid M] [Module S M] :
    B ⊗[S] M →ₛₗ[f.toRingHom] C ⊗[S] M where
  __ := (f.toLinearMap.rTensor M).toAddHom
  map_smul' b z := by
    induction z with
    | zero => simp
    | tmul c m => simp [TensorProduct.smul_tmul']
    | add z y hz hy => simp_all

/-- The scalar extension `f.rTensorSemilinear M` sends `b ⊗ₜ m` to `f b ⊗ₜ m`. -/
@[simp]
theorem AlgHom.rTensorSemilinear_tmul
    {S B C : Type*} [CommSemiring S] [CommSemiring B] [CommSemiring C]
    [Algebra S B] [Algebra S C] (f : B →ₐ[S] C)
    (M : Type*) [AddCommMonoid M] [Module S M] (b : B) (m : M) :
    f.rTensorSemilinear M (b ⊗ₜ[S] m) = f b ⊗ₜ[S] m := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The scalar extension of a module along an algebra homomorphism is a base change. -/
theorem AlgHom.isBaseChange_rTensorSemilinear
    {S B C : Type*} [CommSemiring S] [CommSemiring B] [CommSemiring C]
    [Algebra S B] [Algebra S C] (f : B →ₐ[S] C)
    (M : Type*) [AddCommMonoid M] [Module S M] :
    letI : Algebra B C := f.toRingHom.toAlgebra
    letI : Module B (C ⊗[S] M) := Module.compHom (C ⊗[S] M) f.toRingHom
    letI : IsScalarTower B C (C ⊗[S] M) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    IsBaseChange C
      (⟨(f.rTensorSemilinear M).toAddHom, fun z y => (f.rTensorSemilinear M).map_smul' z y⟩ :
        B ⊗[S] M →ₗ[B] C ⊗[S] M) := by
  let : Algebra B C := f.toRingHom.toAlgebra
  let : Module B (C ⊗[S] M) := Module.compHom (C ⊗[S] M) f.toRingHom
  let : IsScalarTower B C (C ⊗[S] M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower S B C := IsScalarTower.of_algebraMap_eq fun z => (f.commutes z).symm
  let : IsScalarTower S B (C ⊗[S] M) := IsScalarTower.to₁₂₄ S B C _
  apply IsBaseChange.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange S B C C M)
  intro z
  show (TensorProduct.AlgebraTensorModule.cancelBaseChange S B C C M)
    (1 ⊗ₜ[B] z) = f.rTensorSemilinear M z
  induction z with
  | zero => simp
  | tmul b m =>
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      AlgHom.rTensorSemilinear_tmul]
    simp only [Algebra.smul_def, mul_one]
    rfl
  | add z y hz hy => rw [TensorProduct.tmul_add, map_add, hz, hy, map_add]

/-- The canonical homomorphism between principal localizations induced by an algebra map
carrying one element to the other. -/
@[ega "0 1.5.1" "special case"]
noncomputable def AlgHom.localizationAwayMap
    {S B C : Type*} [CommRing S] [CommRing B] [CommRing C]
    [Algebra S B] [Algebra S C] (f : B →ₐ[S] C) (z : B) (y : C) (h : f z = y) :
    Localization.Away z →ₐ[S] Localization.Away y := by
  letI : IsLocalization.Away (f z) (Localization.Away y) := h ▸ inferInstance
  exact IsLocalization.Away.mapₐ _ _ f z

/-- The map `f.localizationAwayMap z y h` sends the image of `t` in `B[1/z]` to the image of
`f t` in `C[1/y]`. -/
theorem AlgHom.localizationAwayMap_algebraMap
    {S B C : Type*} [CommRing S] [CommRing B] [CommRing C]
    [Algebra S B] [Algebra S C] (f : B →ₐ[S] C) (z : B) (y : C) (h : f z = y)
    (t : B) : f.localizationAwayMap z y h (algebraMap B (Localization.Away z) t) =
      algebraMap C (Localization.Away y) (f t) := by
  subst y
  simp [AlgHom.localizationAwayMap, IsLocalization.Away.mapₐ, IsLocalization.Away.map]

/-- The map `f.localizationAwayMap z y h` sends the fraction `t / z ^ n` to `f t / y ^ n`. -/
theorem AlgHom.localizationAwayMap_mk'
    {S B C : Type*} [CommRing S] [CommRing B] [CommRing C]
    [Algebra S B] [Algebra S C] (f : B →ₐ[S] C) (z : B) (y : C) (h : f z = y)
    (t : B) (n : ℕ) :
    f.localizationAwayMap z y h (IsLocalization.mk' (M := Submonoid.powers z)
      (Localization.Away z) t ⟨z ^ n, ⟨n, rfl⟩⟩) =
      IsLocalization.mk' (M := Submonoid.powers y)
        (Localization.Away y) (f t) ⟨y ^ n, ⟨n, rfl⟩⟩ := by
  subst y
  simp [AlgHom.localizationAwayMap, IsLocalization.Away.mapₐ, IsLocalization.Away.map,
    IsLocalization.map_mk']

/-- Two algebra maps out of a principal localization agree if they agree on the base ring. -/
private theorem localizationAway_algHom_apply_eq
    {S B X : Type*} [CommRing S] [CommRing B] [CommRing X] [Algebra S B] [Algebra S X]
    (z : B) (φ ψ : Localization.Away z →ₐ[S] X)
    (h : ∀ t, φ (algebraMap B (Localization.Away z) t) = ψ (algebraMap B (Localization.Away z) t))
    (x : Localization.Away z) : φ x = ψ x :=
  RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers z) (RingHom.ext h)) x

set_option backward.isDefEq.respectTransparency false in
/-- Localizing at a compatible family of elements commutes with a directed colimit. -/
theorem IsDirectedColimit.localizationAway
    {S : Type*} [CommRing S] {Λ : Type*} [Preorder Λ] [Nonempty Λ]
    [IsDirected Λ (· ≤ ·)]
    {B : Λ → Type*} [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)]
    {b : ∀ ⦃i j⦄, i ≤ j → B i →ₐ[S] B j}
    {T : Type*} [CommRing T] [Algebra S T] {σ : ∀ i, B i →ₐ[S] T}
    (hc : IsDirectedColimit B b T σ)
    (z : ∀ i, B i) (y : T)
    (hz : ∀ ⦃i j⦄ (h : i ≤ j), b h (z i) = z j)
    (hy : ∀ i, σ i (z i) = y) :
    IsDirectedColimit (fun i => Localization.Away (z i))
      (fun {_ _} h => (b h).localizationAwayMap _ _ (hz h))
      (Localization.Away y) (fun i => (σ i).localizationAwayMap _ _ (hy i)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j k hij hjk t
    exact localizationAway_algHom_apply_eq (z i)
      (((b hjk).localizationAwayMap _ _ (hz hjk)).comp ((b hij).localizationAwayMap _ _ (hz hij)))
      ((b (hij.trans hjk)).localizationAwayMap _ _ (hz (hij.trans hjk)))
      (fun t => by simp only [AlgHom.comp_apply, AlgHom.localizationAwayMap_algebraMap,
        hc.map_comp]) t
  · intro i t
    exact localizationAway_algHom_apply_eq (z i) ((b (le_refl i)).localizationAwayMap _ _ (hz _))
      (AlgHom.id S _)
      (fun t => by simp only [AlgHom.localizationAwayMap_algebraMap, hc.map_id, AlgHom.id_apply]) t
  · intro i j hij t
    exact localizationAway_algHom_apply_eq (z i)
      (((σ j).localizationAwayMap _ _ (hy j)).comp ((b hij).localizationAwayMap _ _ (hz hij)))
      ((σ i).localizationAwayMap _ _ (hy i))
      (fun t => by simp only [AlgHom.comp_apply, AlgHom.localizationAwayMap_algebraMap,
        hc.comp]) t
  · intro t
    obtain ⟨a, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers y) t
    obtain ⟨i, a, rfl⟩ := hc.jointly_surjective a
    exact ⟨i, IsLocalization.mk' (M := Submonoid.powers (z i))
      (Localization.Away (z i)) a ⟨z i ^ n, ⟨n, rfl⟩⟩,
      AlgHom.localizationAwayMap_mk' (σ i) _ _ (hy i) a n⟩
  · intro i t ht
    obtain ⟨a, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (z i)) t
    rw [AlgHom.localizationAwayMap_mk'] at ht
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp ht
    obtain ⟨j, hij, hj⟩ := hc.exists_eq_zero ((z i) ^ m * a) (by
      simpa only [map_mul, map_pow, hy] using hm)
    refine ⟨j, hij, ?_⟩
    rw [AlgHom.localizationAwayMap_mk', IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨z j ^ m, ⟨m, rfl⟩⟩, ?_⟩
    simpa only [map_mul, map_pow, hz] using hj

set_option backward.isDefEq.respectTransparency false in
/-- Localizing the top and bottom of a pushout square at corresponding elements again gives a
pushout square. -/
theorem Algebra.IsPushout.localizationAway_of_algebraMap_eq
    {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra R U] [Algebra S U] [Algebra T U]
    [IsScalarTower R S U] [IsScalarTower R T U] [Algebra.IsPushout R S T U]
    (z : T) (y : U) (h : algebraMap T U z = y) :
    letI : Algebra (Localization.Away z) (Localization.Away y) :=
      ((IsScalarTower.toAlgHom R T U).localizationAwayMap z y h).toRingHom.toAlgebra
    letI : IsScalarTower R (Localization.Away z) (Localization.Away y) :=
      IsScalarTower.of_algHom ((IsScalarTower.toAlgHom R T U).localizationAwayMap z y h)
    Algebra.IsPushout R S (Localization.Away z) (Localization.Away y) := by
  let : Algebra (Localization.Away z) (Localization.Away y) :=
    ((IsScalarTower.toAlgHom R T U).localizationAwayMap z y h).toRingHom.toAlgebra
  let : IsScalarTower R (Localization.Away z) (Localization.Away y) :=
    IsScalarTower.of_algHom ((IsScalarTower.toAlgHom R T U).localizationAwayMap z y h)
  have : IsScalarTower T (Localization.Away z) (Localization.Away y) :=
    IsScalarTower.of_algebraMap_eq fun t => by
      show algebraMap T (Localization.Away y) t =
        (IsScalarTower.toAlgHom R T U).localizationAwayMap z y h
          (algebraMap T (Localization.Away z) t)
      rw [AlgHom.localizationAwayMap_algebraMap]
      exact IsScalarTower.algebraMap_apply T U _ t
  have : Algebra.IsPushout R T S U := Algebra.IsPushout.symm inferInstance
  have : IsLocalization (Algebra.algebraMapSubmonoid U (Submonoid.powers z))
      (Localization.Away y) := by
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers, h] using
      (inferInstance : IsLocalization (Submonoid.powers y) (Localization.Away y))
  exact Algebra.IsPushout.symm ((Algebra.IsPushout.comp_iff R T S U).mpr
    (Algebra.IsPushout.symm (Algebra.isPushout_of_isLocalization
      (Submonoid.powers z) (Localization.Away z) U (Localization.Away y))))

set_option backward.isDefEq.respectTransparency false in
/-- A further extension of scalars gives the expected tensor-product pushout. -/
theorem Algebra.IsPushout.tensorProduct_map
    {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra R U] (f : T →ₐ[R] U) :
    letI : Algebra T U := f.toRingHom.toAlgebra
    letI : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra U (S ⊗[R] U) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra T (S ⊗[R] U) :=
      (Algebra.TensorProduct.includeRight.comp f).toRingHom.toAlgebra
    letI : Algebra (S ⊗[R] T) (S ⊗[R] U) :=
      (Algebra.TensorProduct.map (AlgHom.id S S) f).toRingHom.toAlgebra
    letI : IsScalarTower T U (S ⊗[R] U) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI : IsScalarTower T (S ⊗[R] T) (S ⊗[R] U) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    Algebra.IsPushout T U (S ⊗[R] T) (S ⊗[R] U) := by
  let : Algebra T U := f.toRingHom.toAlgebra
  let : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  let : Algebra U (S ⊗[R] U) := Algebra.TensorProduct.rightAlgebra
  let : Algebra T (S ⊗[R] U) :=
    (Algebra.TensorProduct.includeRight.comp f).toRingHom.toAlgebra
  let : Algebra (S ⊗[R] T) (S ⊗[R] U) :=
    (Algebra.TensorProduct.map (AlgHom.id S S) f).toRingHom.toAlgebra
  have : IsScalarTower T U (S ⊗[R] U) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower T (S ⊗[R] T) (S ⊗[R] U) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower S (S ⊗[R] T) (S ⊗[R] U) :=
    IsScalarTower.of_algHom (Algebra.TensorProduct.map (AlgHom.id S S) f)
  have : IsScalarTower R (S ⊗[R] T) (S ⊗[R] U) :=
    IsScalarTower.of_algHom ((Algebra.TensorProduct.map (AlgHom.id S S) f).restrictScalars R)
  exact (Algebra.IsPushout.comp_iff R T S (S ⊗[R] T)).mp inferInstance

/-- A finitely presented algebra remains finitely presented after base change, with the factors
written in the opposite order. -/
@[ega "IV 1.4.1"]
theorem Algebra.FinitePresentation.tensorProduct_right
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra.FinitePresentation R S] :
    letI : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
    Algebra.FinitePresentation T (S ⊗[R] T) := by
  let : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  exact Algebra.FinitePresentation.equiv (Algebra.IsPushout.equiv R T S (S ⊗[R] T))

/-- Localizing an extended module agrees with extending it to the localized algebra. -/
theorem Module.flat_localizedModule_away_tensor_iff
    {A S B : Type*} [CommRing A] [CommRing S] [CommRing B]
    [Algebra S B] [Algebra A B] (M : Type*) [AddCommGroup M] [Module S M] (g : B) :
    Module.Flat A (LocalizedModule.Away g (B ⊗[S] M)) ↔
      Module.Flat A (Localization.Away g ⊗[S] M) := by
  let e := (LocalizedModule.equivTensorProduct (Submonoid.powers g) (B ⊗[S] M)).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S B (Localization.Away g)
      (Localization.Away g) M)
  exact ⟨fun _ => Module.Flat.of_linearEquiv (e.symm.restrictScalars A),
    fun _ => Module.Flat.of_linearEquiv (e.restrictScalars A)⟩
