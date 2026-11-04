module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Base change of a square-zero ideal, detected on the reductions

Let `A → A₀` and `B → B₀` be surjective ring maps with kernels `I` and `J`, compatible with an
`A`-algebra structure on `B` and an `A₀`-algebra structure on `B₀`, and let `B₀` act on `J`
compatibly with `B`, so that `J² = 0`. Let `f : I → J` be the injective `A`-linear map induced by
`A → B`, and let `M ⊆ J` be its image, an `A₀`-submodule. If `B₀ ⊗_{A₀} M → J` is bijective, then
`B ⊗_A I → J` is bijective: `J` is the base change of `I` along `A → B`.

This is the descent step for ideals of square-zero thickenings used by the first-order case of
Stacks 05ZR: the ideal of the thickening upstairs is computed from that of the thickening
downstairs once it is known after reduction.

## Main results

* `IsBaseChange.of_bijective_liftBaseChange_reduction`: the statement above.

## Implementation notes

Write `Λ : B ⊗_A I → J` and `L : B₀ ⊗_{A₀} M → J` for the two multiplication maps, and
`ρ : B ⊗_A I → B₀ ⊗_{A₀} M` for `b ⊗ i ↦ b̄ ⊗ f(i)`. Then `Λ = L ∘ ρ`, and `ρ` is surjective on
generators, so it suffices that `ρ` is injective. Its left inverse `ζ` sends `s ⊗ m` to
`b ⊗ f⁻¹(m)` for any lift `b` of `s`; it is well defined because `j ⊗ i = 0` in `B ⊗_A I` for
`j ∈ J`: writing `j = Λ(t)`, which is possible because `Λ = L ∘ ρ` is surjective, this reduces to
`(b · i') ⊗ i = b ⊗ i' i = 0`, and `I² = 0` because `f` is injective and `J² = 0`.

## References

* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
-/

@[expose] public section

open TensorProduct

section

variable {A A₀ B B₀ : Type*} [CommRing A] [CommRing A₀] [CommRing B] [CommRing B₀]
  [Algebra A A₀] [Algebra A B] [Algebra A₀ B₀] [Algebra B B₀] [Algebra A B₀]
  [IsScalarTower A A₀ B₀] [IsScalarTower A B B₀]

local notation "I" => RingHom.ker (algebraMap A A₀)
local notation "J" => RingHom.ker (algebraMap B B₀)

/-- **A square-zero ideal is the base change of its reduction.** Let `A → A₀` and `B → B₀` be
surjective, with `B₀` acting on `J = ker(B → B₀)` compatibly with `B`. Let
`f : I = ker(A → A₀) → J` be injective and induced by `A → B`, and let `M` be its image, an
`A₀`-submodule of `J`. If the multiplication map `B₀ ⊗_{A₀} M → J` is bijective, then `f`
exhibits `J` as the base change of `I` along `A → B`. -/
theorem IsBaseChange.of_bijective_liftBaseChange_reduction
    (hA : Function.Surjective (algebraMap A A₀)) (hB : Function.Surjective (algebraMap B B₀))
    [Module B₀ J] (hJs : ∀ (b : B) (j : J), algebraMap B B₀ b • j = b • j)
    [Module A₀ J] [IsScalarTower A₀ B₀ J]
    (f : I →ₗ[A] J) (hf : ∀ x, (f x : B) = algebraMap A B (x : A)) (hfinj : Function.Injective f)
    (M : Submodule A₀ J) (hM : ∀ j, j ∈ M ↔ ∃ x, f x = j)
    (hbij : Function.Bijective (M.subtype.liftBaseChange B₀)) :
    IsBaseChange B f := by
  -- `J² = 0` and `I² = 0`.
  have hJ2 : ∀ x y : J, (x : B) * y = 0 := fun x y => by
    have h := hJs x y
    rw [RingHom.mem_ker.mp x.2, zero_smul] at h
    simpa using (congrArg Subtype.val h).symm
  have hI2 : ∀ x y : I, (x : A) * y = 0 := fun x y => by
    have h : f ((x : A) • y) = 0 := by
      apply Subtype.ext
      have h := hJ2 (f x) (f y)
      rw [hf, hf] at h
      rw [hf, Submodule.coe_smul, smul_eq_mul, map_mul, h]
      rfl
    simpa using congrArg Subtype.val (hfinj (h.trans (map_zero f).symm))
  -- The action of `A` on `J` through `A₀`.
  have hA0 : ∀ (a : A) (j : J), algebraMap A A₀ a • j = a • j := fun a j => by
    rw [← smul_one_smul B₀ (algebraMap A A₀ a) j, Algebra.smul_def, mul_one,
      ← IsScalarTower.algebraMap_apply A A₀ B₀, IsScalarTower.algebraMap_apply A B B₀, hJs,
      algebraMap_smul]
  have hbar : ∀ (a : A) (b : B), algebraMap B B₀ (a • b) = algebraMap A A₀ a • algebraMap B B₀ b :=
    fun a b => by
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply A B B₀,
        IsScalarTower.algebraMap_apply A A₀ B₀, Algebra.smul_def]
  -- The point of `M` named by an element of `I`, and its inverse.
  let mI : I →+ M :=
    { toFun := fun i => ⟨f i, (hM _).2 ⟨i, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp }
  have hmI : ∀ i, ((mI i : J) : B) = f i := fun _ => rfl
  have hmIsmul : ∀ (a : A) (i : I), mI (a • i) = algebraMap A A₀ a • mI i := fun a i => by
    apply Subtype.ext
    change f (a • i) = algebraMap A A₀ a • f i
    rw [hA0, map_smul]
  have hmIbij : Function.Bijective mI :=
    ⟨fun _ _ h => hfinj (congrArg Subtype.val h), fun m => by
      obtain ⟨i, hi⟩ := (hM m).1 m.2
      exact ⟨i, Subtype.ext hi⟩⟩
  -- The two multiplication maps.
  let Λ : B ⊗[A] I →ₗ[B] J := f.liftBaseChange B
  let L : B₀ ⊗[A₀] M →ₗ[B₀] J := M.subtype.liftBaseChange B₀
  -- `ρ : b ⊗ i ↦ b̄ ⊗ f(i)`.
  let ρ : B ⊗[A] I →+ B₀ ⊗[A₀] M := TensorProduct.liftAddHom
    { toFun := fun b =>
        { toFun := fun i => algebraMap B B₀ b ⊗ₜ[A₀] mI i
          map_zero' := by simp
          map_add' := fun _ _ => by simp [tmul_add] }
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_tmul] }
    (fun a b i => by
      change algebraMap B B₀ (a • b) ⊗ₜ[A₀] mI i = algebraMap B B₀ b ⊗ₜ[A₀] mI (a • i)
      rw [hbar, hmIsmul, smul_tmul])
  have hρ : ∀ b i, ρ (b ⊗ₜ i) = algebraMap B B₀ b ⊗ₜ[A₀] mI i := fun _ _ => rfl
  have hLρ : ∀ t, L (ρ t) = Λ t := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b i =>
      rw [hρ]
      simp only [L, Λ, LinearMap.liftBaseChange_tmul, Submodule.subtype_apply]
      exact hJs b (f i)
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  -- `ρ`, hence `Λ`, is surjective.
  have hρsurj : Function.Surjective ρ := fun u => by
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero ρ⟩
    | tmul s m =>
      obtain ⟨b, rfl⟩ := hB s
      obtain ⟨i, rfl⟩ := hmIbij.2 m
      exact ⟨b ⊗ₜ i, hρ _ _⟩
    | add x y hx hy =>
      obtain ⟨tx, rfl⟩ := hx
      obtain ⟨ty, rfl⟩ := hy
      exact ⟨tx + ty, map_add ρ _ _⟩
  have hΛsurj : Function.Surjective Λ := fun j => by
    obtain ⟨u, rfl⟩ := hbij.2 j
    obtain ⟨t, rfl⟩ := hρsurj u
    exact ⟨t, (hLρ t).symm⟩
  -- Elements of `J` are killed in `B ⊗_A I`.
  have hK : ∀ (j : J) (i : I), (j : B) ⊗ₜ[A] i = 0 := fun j i => by
    obtain ⟨t, rfl⟩ := hΛsurj j
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b i' =>
      have h0 : (i' : A) • i = 0 := Subtype.ext (by simpa using hI2 i' i)
      have : ((Λ (b ⊗ₜ i') : J) : B) = (i' : A) • b := by
        simp only [Λ, LinearMap.liftBaseChange_tmul, Submodule.coe_smul, hf, smul_eq_mul,
          Algebra.smul_def]
        ring
      rw [this, smul_tmul, h0, tmul_zero]
    | add x y hx hy => rw [map_add, Submodule.coe_add, add_tmul, hx, hy, add_zero]
  -- Lifts of the same element of `B₀` agree in `B ⊗_A I`.
  have hlift : ∀ (b : B) (s : B₀) (i : I), algebraMap B B₀ b = s →
      Function.surjInv hB s ⊗ₜ[A] i = b ⊗ₜ[A] i := fun b s i h => by
    subst h
    have := hK ⟨Function.surjInv hB (algebraMap B B₀ b) - b, by
      rw [RingHom.mem_ker, map_sub, Function.surjInv_eq hB, sub_self]⟩ i
    rwa [sub_tmul, sub_eq_zero] at this
  -- The inverse of `f` on `M`.
  let e : I ≃+ M := AddEquiv.ofBijective mI hmIbij
  have hfinvsmul : ∀ (a : A) m, e.symm (algebraMap A A₀ a • m) = a • e.symm m := fun a m =>
    e.symm_apply_eq.2 (by
      change _ = mI (a • e.symm m)
      rw [hmIsmul]
      exact congrArg _ (e.apply_symm_apply m).symm)
  -- The left inverse `ζ : s ⊗ m ↦ b ⊗ f⁻¹(m)`.
  let ζ : B₀ ⊗[A₀] M →+ B ⊗[A] I := TensorProduct.liftAddHom
    { toFun := fun s =>
        { toFun := fun m => Function.surjInv hB s ⊗ₜ[A] e.symm m
          map_zero' := by rw [map_zero, tmul_zero]
          map_add' := fun m m' => by rw [map_add, tmul_add] }
      map_zero' := by
        ext m
        exact (hlift 0 0 _ (map_zero _)).trans (zero_tmul _ _)
      map_add' := fun s s' => by
        ext m
        refine (hlift (Function.surjInv hB s + Function.surjInv hB s') _ _ ?_).trans
          (add_tmul _ _ _)
        rw [map_add, Function.surjInv_eq hB, Function.surjInv_eq hB] }
    (fun a₀ s m => by
      change Function.surjInv hB (a₀ • s) ⊗ₜ[A] e.symm m =
        Function.surjInv hB s ⊗ₜ[A] e.symm (a₀ • m)
      obtain ⟨a, rfl⟩ := hA a₀
      rw [hfinvsmul, ← smul_tmul]
      exact hlift _ _ _ (by rw [hbar, Function.surjInv_eq hB]))
  have hζρ : ∀ t, ζ (ρ t) = t := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b i =>
      rw [hρ]
      change Function.surjInv hB (algebraMap B B₀ b) ⊗ₜ[A] e.symm (e i) = b ⊗ₜ[A] i
      rw [e.symm_apply_apply]
      exact hlift _ _ _ rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hΛinj : Function.Injective Λ := fun t t' h => by
    rw [← hLρ, ← hLρ] at h
    rw [← hζρ t, ← hζρ t', hbij.1 h]
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective Λ ⟨hΛinj, hΛsurj⟩)
    (fun x => LinearMap.liftBaseChange_one_tmul _ _ x)

end

end
