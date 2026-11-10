module

public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent of surjectivity to a finite stage of a directed colimit

Let `A = colim_i Aᵢ` be a directed colimit of `A₀`-algebras for a base commutative ring `A₀`,
and let `φ₀` be the structure map `IsScalarTower.toAlgHom A₀ B₀ C₀` of a `B₀`-algebra `C₀`. If
the base change `id_A ⊗ φ₀ : A ⊗_{A₀} B₀ → A ⊗_{A₀} C₀` is surjective, then so is
`id_{Aᵢ} ⊗ φ₀` for some stage `i`.

## Main results

* `surjective_baseChange_of_colimit`: if `id_A ⊗ φ₀` is surjective and `φ₀` is of finite
  type, then some `id_{Aᵢ} ⊗ φ₀` is surjective.

## Implementation notes

The colimit is described concretely by the predicate `IsRingColimit`, with the base ring `A₀`
playing the role of the base stage and the index set restricted to the stages above it.

## References

* [Stacks Project, Tag 07RH](https://stacks.math.columbia.edu/tag/07RH)
-/

@[expose] public section


open scoped TensorProduct

section Colimit

variable
  (A₀ : Type*) [CommRing A₀]
  {I : Type*} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (Aᵢ : I → Type*) [(i : I) → CommRing (Aᵢ i)] [(i : I) → Algebra A₀ (Aᵢ i)]
  (f : (i j : I) → i ≤ j → (Aᵢ i →ₐ[A₀] Aᵢ j))
  (A : Type*) [CommRing A] [Algebra A₀ A]
  (g : (i : I) → (Aᵢ i →ₐ[A₀] A))

/-- `A`, together with the cocone maps `g`, is the directed colimit of the directed system of
`A₀`-algebras `(Aᵢ, f)`: the transition maps are functorial, the cocone is compatible with them,
every element of `A` comes from some stage, and two elements of a stage that become equal in `A`
already become equal at a later stage. -/
@[ega "IV 8.5.2.1"]
structure IsRingColimit : Prop where
  /-- `f i i` is the identity. -/
  map_id : ∀ (i : I) (h : i ≤ i) (a : Aᵢ i), f i i h a = a
  /-- The transition maps compose. -/
  map_comp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (a : Aᵢ i),
    f j k hjk (f i j hij a) = f i k (le_trans hij hjk) a
  /-- The cocone maps are compatible with the transition maps. -/
  fac : ∀ (i j : I) (hij : i ≤ j) (a : Aᵢ i), g j (f i j hij a) = g i a
  /-- Every element of the colimit is the image of an element of some stage. -/
  jointly_surjective : ∀ x : A, ∃ i a, g i a = x
  /-- An equality in the colimit is witnessed at a finite stage. -/
  exists_eq : ∀ (i : I) (a b : Aᵢ i), g i a = g i b →
    ∃ (j : I) (hij : i ≤ j), f i j hij a = f i j hij b

end Colimit

section Statement

variable
  (A₀ : Type*) [CommRing A₀]
  {I : Type*} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (Aᵢ : I → Type*) [(i : I) → CommRing (Aᵢ i)] [(i : I) → Algebra A₀ (Aᵢ i)]
  (f : (i j : I) → i ≤ j → (Aᵢ i →ₐ[A₀] Aᵢ j))
  (A : Type*) [CommRing A] [Algebra A₀ A]
  (g : (i : I) → (Aᵢ i →ₐ[A₀] A))
  (B₀ C₀ : Type*) [CommRing B₀] [CommRing C₀]
  [Algebra A₀ B₀] [Algebra A₀ C₀] [Algebra B₀ C₀] [IsScalarTower A₀ B₀ C₀]

/-- The base-change `A₀`-algebra map `id_{Aᵢ} ⊗ φ₀ : Aᵢ ⊗_{A₀} B₀ → Aᵢ ⊗_{A₀} C₀`,
where `φ₀ = IsScalarTower.toAlgHom A₀ B₀ C₀ : B₀ → C₀` is the structure map of `C₀` as a
`B₀`-algebra. -/
@[ega "I 3.3.7" "special case", ega "I 3.5.1" "special case", ega "III 6.1.1" "special case"]
noncomputable def baseChange (i : I) :
    Aᵢ i ⊗[A₀] B₀ →ₐ[A₀] Aᵢ i ⊗[A₀] C₀ :=
  Algebra.TensorProduct.map (AlgHom.id A₀ (Aᵢ i)) (IsScalarTower.toAlgHom A₀ B₀ C₀)

/-- The base-change `A₀`-algebra map `id_A ⊗ φ₀ : A ⊗_{A₀} B₀ → A ⊗_{A₀} C₀`. -/
@[ega "I 3.5.1" "special case", ega "IV 11.2.9" "partial"]
noncomputable def baseChangeColim :
    A ⊗[A₀] B₀ →ₐ[A₀] A ⊗[A₀] C₀ :=
  Algebra.TensorProduct.map (AlgHom.id A₀ A) (IsScalarTower.toAlgHom A₀ B₀ C₀)

/-- The cocone map on the `B₀`-tensors: `g i ⊗ id_{B₀} : Aᵢ ⊗_{A₀} B₀ → A ⊗_{A₀} B₀`. -/
noncomputable def tensorCoconeB (i : I) :
    Aᵢ i ⊗[A₀] B₀ →ₐ[A₀] A ⊗[A₀] B₀ :=
  Algebra.TensorProduct.map (g i) (AlgHom.id A₀ B₀)

/-- The cocone map on the `C₀`-tensors: `g i ⊗ id_{C₀} : Aᵢ ⊗_{A₀} C₀ → A ⊗_{A₀} C₀`. -/
noncomputable def tensorCoconeC (i : I) :
    Aᵢ i ⊗[A₀] C₀ →ₐ[A₀] A ⊗[A₀] C₀ :=
  Algebra.TensorProduct.map (g i) (AlgHom.id A₀ C₀)

/-- The transition map on the `B₀`-tensors: `f i j h ⊗ id_{B₀}`. -/
noncomputable def tensorTransB (i j : I) (h : i ≤ j) :
    Aᵢ i ⊗[A₀] B₀ →ₐ[A₀] Aᵢ j ⊗[A₀] B₀ :=
  Algebra.TensorProduct.map (f i j h) (AlgHom.id A₀ B₀)

/-- The transition map on the `C₀`-tensors: `f i j h ⊗ id_{C₀}`. -/
noncomputable def tensorTransC (i j : I) (h : i ≤ j) :
    Aᵢ i ⊗[A₀] C₀ →ₐ[A₀] Aᵢ j ⊗[A₀] C₀ :=
  Algebra.TensorProduct.map (f i j h) (AlgHom.id A₀ C₀)

omit [Nonempty I] [IsDirected I fun x1 x2 ↦ x1 ≤ x2] in
/-- The base-change maps commute with the transition maps:
`(f i j ⊗ id_C) ∘ (id_{Aᵢ} ⊗ φ₀) = (id_{Aⱼ} ⊗ φ₀) ∘ (f i j ⊗ id_B)`. -/
theorem baseChange_naturality_trans (i j : I) (h : i ≤ j) :
    (tensorTransC A₀ Aᵢ f C₀ i j h).comp (baseChange A₀ Aᵢ B₀ C₀ i)
      = (baseChange A₀ Aᵢ B₀ C₀ j).comp (tensorTransB A₀ Aᵢ f B₀ i j h) := by
  simp only [baseChange, tensorTransB, tensorTransC]
  ext x <;> simp

omit [Nonempty I] [IsDirected I fun x1 x2 ↦ x1 ≤ x2] [Preorder I] in
/-- The base-change maps commute with the cocone maps:
`(g i ⊗ id_C) ∘ (id_{Aᵢ} ⊗ φ₀) = (id_A ⊗ φ₀) ∘ (g i ⊗ id_B)`. -/
theorem baseChange_naturality_cocone (i : I) :
    (tensorCoconeC A₀ Aᵢ A g C₀ i).comp (baseChange A₀ Aᵢ B₀ C₀ i)
      = (baseChangeColim A₀ A B₀ C₀).comp (tensorCoconeB A₀ Aᵢ A g B₀ i) := by
  simp only [baseChange, baseChangeColim, tensorCoconeB, tensorCoconeC]
  ext x <;> simp

omit [Nonempty I] [IsDirected I fun x1 x2 ↦ x1 ≤ x2] in
/-- The tensored cocone is compatible with the tensored transition maps:
`tensorCoconeB j ∘ tensorTransB i j = tensorCoconeB i`. -/
theorem tensorCoconeB_comp_tensorTransB
    (hcolim : IsRingColimit A₀ Aᵢ f A g) (i j : I) (h : i ≤ j) :
    (tensorCoconeB A₀ Aᵢ A g B₀ j).comp (tensorTransB A₀ Aᵢ f B₀ i j h)
      = tensorCoconeB A₀ Aᵢ A g B₀ i := by
  have hfac : (g j).comp (f i j h) = g i := AlgHom.ext (hcolim.fac i j h)
  simp only [tensorCoconeB, tensorTransB]
  rw [← Algebra.TensorProduct.map_comp, hfac, AlgHom.comp_id]

omit [Nonempty I] in
/-- Every element of `A ⊗ B₀` is the image under `tensorCoconeB i` of an element of
`Aᵢ ⊗ B₀` for some `i`. -/
@[ega "IV 11.2.2" "partial"]
theorem tensorCoconeB_jointly_surjective
    (hcolim : IsRingColimit A₀ Aᵢ f A g) (z : A ⊗[A₀] B₀) :
    ∃ (i : I) (y : Aᵢ i ⊗[A₀] B₀), tensorCoconeB A₀ Aᵢ A g B₀ i y = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    obtain ⟨i, a', ha⟩ := hcolim.jointly_surjective a
    refine ⟨i, a' ⊗ₜ[A₀] b, ?_⟩
    simp [tensorCoconeB, ha]
  | add x y hx hy =>
    obtain ⟨ix, yx, hx⟩ := hx
    obtain ⟨iy, yy, hy⟩ := hy
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) ix iy
    refine ⟨k, tensorTransB A₀ Aᵢ f B₀ ix k hik yx
              + tensorTransB A₀ Aᵢ f B₀ iy k hjk yy, ?_⟩
    rw [map_add, ← AlgHom.comp_apply, tensorCoconeB_comp_tensorTransB A₀ Aᵢ f A g B₀ hcolim,
      ← AlgHom.comp_apply, tensorCoconeB_comp_tensorTransB A₀ Aᵢ f A g B₀ hcolim, hx, hy]

omit [Nonempty I] [IsDirected I fun x1 x2 ↦ x1 ≤ x2] in
/-- The transition maps of a ring colimit form a directed system of `A₀`-modules. -/
theorem IsRingColimit.directedSystem (hcolim : IsRingColimit A₀ Aᵢ f A g) :
    DirectedSystem Aᵢ fun i j h => ((f i j h).toLinearMap : Aᵢ i → Aᵢ j) :=
  ⟨fun i x => hcolim.map_id i le_rfl x, fun i j k hij hjk x => hcolim.map_comp k j i hij hjk x⟩

/-- The map `colim Aᵢ → A` of `A₀`-modules induced by the cocone `g` is bijective. -/
theorem IsRingColimit.bijective_lift [DecidableEq I] (hcolim : IsRingColimit A₀ Aᵢ f A g) :
    Function.Bijective (Module.DirectLimit.lift A₀ I Aᵢ (fun i j h => (f i j h).toLinearMap)
      (fun i => (g i).toLinearMap) fun i j hij x => by simp [hcolim.fac]) := by
  have := hcolim.directedSystem
  refine ⟨?_, fun x => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    induction z using Module.DirectLimit.induction_on with
    | _ i a =>
      simp only [Module.DirectLimit.lift_of] at hz
      obtain ⟨j, hij, hfa⟩ := hcolim.exists_eq i a 0 (by rwa [map_zero])
      rw [map_zero] at hfa
      rw [← Module.DirectLimit.of_f (hij := hij)]
      simp [hfa]
  · obtain ⟨i, a, rfl⟩ := hcolim.jointly_surjective x
    exact ⟨Module.DirectLimit.of A₀ I Aᵢ _ i a, by simp⟩

/-- A ring colimit `A` of `(Aᵢ, f)` is the direct limit of the underlying `A₀`-modules. -/
noncomputable def IsRingColimit.linearEquivDirectLimit [DecidableEq I]
    (hcolim : IsRingColimit A₀ Aᵢ f A g) :
    Module.DirectLimit Aᵢ (fun i j h => (f i j h).toLinearMap) ≃ₗ[A₀] A :=
  LinearEquiv.ofBijective _ hcolim.bijective_lift

/-- The equivalence `colim Aᵢ ≃ A` sends `of i a` to `g i a`. -/
@[simp]
theorem IsRingColimit.linearEquivDirectLimit_of [DecidableEq I]
    (hcolim : IsRingColimit A₀ Aᵢ f A g) (i : I) (a : Aᵢ i) :
    IsRingColimit.linearEquivDirectLimit A₀ Aᵢ f A g hcolim
      (Module.DirectLimit.of A₀ I Aᵢ _ i a) = g i a := by
  simp [IsRingColimit.linearEquivDirectLimit]

/-- Under `A ⊗ C₀ ≃ colim (Aᵢ ⊗ C₀)`, the cocone map `tensorCoconeC i` is the structure map
`of i` of the module direct limit. -/
theorem directLimitLeft_tensorCoconeC [DecidableEq I] (hcolim : IsRingColimit A₀ Aᵢ f A g)
    (i : I) (w : Aᵢ i ⊗[A₀] C₀) :
    TensorProduct.directLimitLeft _ C₀
        (LinearEquiv.rTensor C₀ hcolim.linearEquivDirectLimit.symm
          (tensorCoconeC A₀ Aᵢ A g C₀ i w)) =
      Module.DirectLimit.of A₀ I _
        (fun i j h => LinearMap.rTensor C₀ (f i j h).toLinearMap) i w := by
  induction w using TensorProduct.inductionOn with
  | tmul a c =>
    have h := (IsRingColimit.linearEquivDirectLimit A₀ Aᵢ f A g hcolim).symm_apply_apply
      (Module.DirectLimit.of A₀ I Aᵢ _ i a)
    rw [IsRingColimit.linearEquivDirectLimit_of] at h
    simp [tensorCoconeC, h]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- If two elements `u v : Aᵢ ⊗ C₀` become equal in `A ⊗ C₀` under the cocone map, then they
already become equal at some finite stage `j ≥ i`. -/
@[ega "IV 11.2.2" "partial"]
theorem tensorCoconeC_exists_eq
    (hcolim : IsRingColimit A₀ Aᵢ f A g) (i : I) (u v : Aᵢ i ⊗[A₀] C₀)
    (heq : tensorCoconeC A₀ Aᵢ A g C₀ i u = tensorCoconeC A₀ Aᵢ A g C₀ i v) :
    ∃ (j : I) (hij : i ≤ j),
      tensorTransC A₀ Aᵢ f C₀ i j hij u = tensorTransC A₀ Aᵢ f C₀ i j hij v := by
  classical
  have := hcolim.directedSystem
  have hzero : Module.DirectLimit.of A₀ I _
      (fun i j h => LinearMap.rTensor C₀ (f i j h).toLinearMap) i (u - v) = 0 := by
    rw [map_sub, ← directLimitLeft_tensorCoconeC A₀ Aᵢ f A g C₀ hcolim,
      ← directLimitLeft_tensorCoconeC A₀ Aᵢ f A g C₀ hcolim, heq, sub_self]
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact hzero
  refine ⟨j, hij, ?_⟩
  rw [map_sub, sub_eq_zero] at hj
  have hT : (tensorTransC A₀ Aᵢ f C₀ i j hij).toLinearMap =
      LinearMap.rTensor C₀ (f i j hij).toLinearMap := TensorProduct.ext' fun _ _ => rfl
  simpa only [← hT, AlgHom.toLinearMap_apply] using hj

omit [Nonempty I] [IsDirected I fun x1 x2 ↦ x1 ≤ x2] [Preorder I] in
/-- If `1 ⊗ x` lies in the range of `baseChange i` for every `x` in a set `s` generating `C₀`
as a `B₀`-algebra, then `baseChange i` is surjective. -/
theorem surjective_baseChange_of_generators_in_range
    (i : I) (s : Finset C₀)
    (hs : Algebra.adjoin B₀ (s : Set C₀) = ⊤)
    (hmem : ∀ x ∈ s, (1 : Aᵢ i) ⊗ₜ[A₀] x ∈ (baseChange A₀ Aᵢ B₀ C₀ i).range) :
    Function.Surjective (baseChange A₀ Aᵢ B₀ C₀ i) := by
  rw [← AlgHom.range_eq_top]
  set S := (baseChange A₀ Aᵢ B₀ C₀ i).range with hS
  have hrange : ∀ (a : Aᵢ i) (b : B₀), a ⊗ₜ[A₀] (algebraMap B₀ C₀ b) ∈ S := fun a b =>
    ⟨a ⊗ₜ[A₀] b, by simp [baseChange, Algebra.TensorProduct.map_tmul,
      IsScalarTower.toAlgHom_apply]⟩
  have key1 : ∀ c : C₀, (1 : Aᵢ i) ⊗ₜ[A₀] c ∈ S := by
    intro c
    refine Algebra.adjoin_induction (p := fun c _ => (1 : Aᵢ i) ⊗ₜ[A₀] c ∈ S) hmem (hrange 1)
      (fun x y _ _ hxs hys => ?_) (fun x y _ _ hxs hys => ?_) (hs ▸ Algebra.mem_top)
    · rw [TensorProduct.tmul_add]
      exact S.add_mem hxs hys
    · rw [← one_mul (1 : Aᵢ i), ← Algebra.TensorProduct.tmul_mul_tmul]
      exact S.mul_mem hxs hys
  have key2 : ∀ a : Aᵢ i, a ⊗ₜ[A₀] (1 : C₀) ∈ S := fun a => by simpa using hrange a 1
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.inductionOn with
  | tmul a c =>
    rw [← mul_one a, ← one_mul c, ← Algebra.TensorProduct.tmul_mul_tmul]
    exact S.mul_mem (key2 a) (key1 c)
  | add x y hx hy => exact Subalgebra.add_mem S hx hy


/-- Let `A = colim_i Aᵢ` be a directed colimit of `A₀`-algebras, and let `C₀` be an
`A₀`-algebra that is of finite type over the `A₀`-algebra `B₀` (via the structure map
`φ₀ : B₀ → C₀`). If the base change `id_A ⊗ φ₀ : A ⊗_{A₀} B₀ → A ⊗_{A₀} C₀` is
surjective, then there is some index `i` for which the base change
`id_{Aᵢ} ⊗ φ₀ : Aᵢ ⊗_{A₀} B₀ → Aᵢ ⊗_{A₀} C₀` is already surjective. -/
@[stacks 07RH, sga "3 VIB 10.1" "special case"]
theorem surjective_baseChange_of_colimit
    (hcolim : IsRingColimit A₀ Aᵢ f A g)
    (hsurj : Function.Surjective (baseChangeColim A₀ A B₀ C₀))
    (hft : Algebra.FiniteType B₀ C₀) :
    ∃ i : I, Function.Surjective (baseChange A₀ Aᵢ B₀ C₀ i) := by
  obtain ⟨s, hs⟩ := hft.out
  classical
  have hstep : ∀ (j k : I) (h : j ≤ k) (y : Aᵢ j ⊗[A₀] B₀),
      baseChange A₀ Aᵢ B₀ C₀ k (tensorTransB A₀ Aᵢ f B₀ j k h y)
        = tensorTransC A₀ Aᵢ f C₀ j k h (baseChange A₀ Aᵢ B₀ C₀ j y) := fun j k h y =>
    (DFunLike.congr_fun (baseChange_naturality_trans A₀ Aᵢ f B₀ C₀ j k h) y).symm
  have hone : ∀ (j k : I) (h : j ≤ k) (x : C₀),
      tensorTransC A₀ Aᵢ f C₀ j k h ((1 : Aᵢ j) ⊗ₜ[A₀] x) = (1 : Aᵢ k) ⊗ₜ[A₀] x := by
    simp [tensorTransC]
  have hstage : ∀ x ∈ s, ∃ j : I, (1 : Aᵢ j) ⊗ₜ[A₀] x ∈ (baseChange A₀ Aᵢ B₀ C₀ j).range := by
    intro x hx
    obtain ⟨bx, hbx⟩ := hsurj ((1 : A) ⊗ₜ[A₀] x)
    obtain ⟨i₀, y, hy⟩ := tensorCoconeB_jointly_surjective A₀ Aᵢ f A g B₀ hcolim bx
    have hcoc : tensorCoconeC A₀ Aᵢ A g C₀ i₀ (baseChange A₀ Aᵢ B₀ C₀ i₀ y)
        = tensorCoconeC A₀ Aᵢ A g C₀ i₀ ((1 : Aᵢ i₀) ⊗ₜ[A₀] x) := by
      have hnat := DFunLike.congr_fun (baseChange_naturality_cocone A₀ Aᵢ A g B₀ C₀ i₀) y
      simp only [AlgHom.coe_comp, Function.comp_apply] at hnat
      rw [hnat, hy, hbx]
      simp [tensorCoconeC]
    obtain ⟨j, hij, heq⟩ := tensorCoconeC_exists_eq A₀ Aᵢ f A g C₀ hcolim i₀
      (baseChange A₀ Aᵢ B₀ C₀ i₀ y) ((1 : Aᵢ i₀) ⊗ₜ[A₀] x) hcoc
    exact ⟨j, tensorTransB A₀ Aᵢ f B₀ i₀ j hij y, (hstep _ _ hij y).trans (by rw [heq, hone])⟩
  have hmono : ∀ (x : C₀) (j k : I), j ≤ k →
      (1 : Aᵢ j) ⊗ₜ[A₀] x ∈ (baseChange A₀ Aᵢ B₀ C₀ j).range →
      (1 : Aᵢ k) ⊗ₜ[A₀] x ∈ (baseChange A₀ Aᵢ B₀ C₀ k).range := by
    rintro x j k hjk ⟨p, hp⟩
    exact ⟨tensorTransB A₀ Aᵢ f B₀ j k hjk p,
      (hstep _ _ hjk p).trans ((congrArg _ hp).trans (hone _ _ _ x))⟩
  choose! jfun hjfun using hstage
  obtain ⟨M, hM⟩ := Finset.exists_le (s.image jfun)
  refine ⟨M, ?_⟩
  exact surjective_baseChange_of_generators_in_range A₀ Aᵢ B₀ C₀ M s hs fun x hx =>
    hmono x (jfun x) M (hM _ (Finset.mem_image_of_mem jfun hx)) (hjfun x hx)

end Statement

end
