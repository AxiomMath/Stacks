module

public import StacksFrontier.RingTheory.Module.DirectLimit.FinitePresentation

/-!
# Finite modules along a base-changed directed system of algebras

For a directed system of `R`-algebras `T_i` with colimit `Tlim` and an `R`-algebra `A`, the system
`A ⊗[R] T_i` of `A`-algebras has colimit `A ⊗[R] Tlim`. Algebra, Lemma 05LI part (1) holds along
it: two `A`-linear maps out of a finite `A`-module whose base changes to `A ⊗[R] Tlim` agree
already have equal base changes to some `A ⊗[R] T_i`.

## Main definitions

* `Stacks.FinitePresentation.ColimitDescent.baseChangedMap`: the transition maps
  `A ⊗[R] T_i → A ⊗[R] T_j`.
* `Stacks.FinitePresentation.ColimitDescent.baseChangedLeg`: the legs `A ⊗[R] T_j → A ⊗[R] Tlim`.

## Main results

* `Stacks.FinitePresentation.ColimitDescent.exists_algebraMap_eq_baseChanged` and
  `Stacks.FinitePresentation.ColimitDescent.exists_map_eq_zero_baseChanged`: the two elementwise
  colimit conditions for the base-changed system `A ⊗[R] T_i → A ⊗[R] Tlim`, deduced from the
  same two conditions for `T_i → Tlim`.
* `Stacks.FinitePresentation.ColimitDescent.statement_one_baseChanged`: if `M` is a finite
  `A`-module and two `A`-linear maps `M → N` have equal base changes to `A ⊗[R] Tlim`, their base
  changes to `A ⊗[R] T_i` agree for some `i`.
* `Stacks.FinitePresentation.ColimitDescent.exists_baseChange_eq_zero_baseChanged`: if the base
  change of `u : M → N` to `A ⊗[R] Tlim` vanishes, so does its base change to some `A ⊗[R] T_i`.

## References

* [Stacks Project, Tag 05LI](https://stacks.math.columbia.edu/tag/05LI)
-/

@[expose] public noncomputable section

universe u w t t'

open scoped TensorProduct

namespace Stacks.FinitePresentation.ColimitDescent

section BaseChanged

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {J : Type w} [Preorder J] [Nonempty J] [IsDirectedOrder J]
  {T : J → Type u} [∀ j, CommRing (T j)] [∀ j, Algebra R (T j)]
  (f : ∀ i j, i ≤ j → T i →ₐ[R] T j) [DirectedSystem T fun i j h ↦ ⇑(f i j h)]
  {Tlim : Type u} [CommRing Tlim] [Algebra R Tlim] [∀ j, Algebra (T j) Tlim]
  [∀ j, IsScalarTower R (T j) Tlim]

/-- The transition maps of the base-changed system `A ⊗[R] T_i`, as `A`-algebra maps. -/
def baseChangedMap (i j : J) (h : i ≤ j) : (A ⊗[R] T i) →ₐ[A] (A ⊗[R] T j) :=
  Algebra.TensorProduct.map (AlgHom.id A A) (f i j h)

omit [Nonempty J] [IsDirectedOrder J] [DirectedSystem T fun i j h ↦ ⇑(f i j h)] in
/-- The transition map of the base-changed system on a pure tensor. -/
@[simp]
theorem baseChangedMap_tmul (i j : J) (h : i ≤ j) (a : A) (x : T i) :
    baseChangedMap (A := A) f i j h (a ⊗ₜ[R] x) = a ⊗ₜ[R] f i j h x :=
  rfl

/-- The legs of the base-changed system, as `A`-algebra maps into `A ⊗[R] Tlim`. -/
def baseChangedLeg (j : J) : (A ⊗[R] T j) →ₐ[A] (A ⊗[R] Tlim) :=
  Algebra.TensorProduct.map (AlgHom.id A A) (IsScalarTower.toAlgHom R (T j) Tlim)

omit [Preorder J] [Nonempty J] [IsDirectedOrder J] in
/-- The leg of the base-changed system on a pure tensor. -/
@[simp]
theorem baseChangedLeg_tmul (j : J) (a : A) (x : T j) :
    baseChangedLeg (A := A) (Tlim := Tlim) j (a ⊗ₜ[R] x) = a ⊗ₜ[R] algebraMap (T j) Tlim x :=
  rfl

omit [Nonempty J] [IsDirectedOrder J] in
/-- The transition maps of the base-changed system form a directed system. -/
theorem directedSystem_baseChangedMap :
    DirectedSystem (fun j ↦ A ⊗[R] T j) fun i j h ↦ ⇑(baseChangedMap (A := A) f i j h) := by
  refine ⟨fun i z ↦ ?_, fun i j k hij hjk z ↦ ?_⟩
  · refine TensorProduct.inductionOn z (fun a x ↦ ?_) fun x y hx hy ↦ by simp [hx, hy]
    simp [DirectedSystem.map_self' f x]
  · refine TensorProduct.inductionOn z (fun a x ↦ ?_) fun x y hx hy ↦ by simp [hx, hy]
    simp [DirectedSystem.map_map' f hij hjk x]

omit [Preorder J] [Nonempty J] [IsDirectedOrder J] in
/-- Exchanging the two tensor factors turns a leg of the base-changed system into the canonical
map `canonMod` of the system `T_i` at the module `A`. -/
theorem commBaseChanged_leg (j : J) (z : A ⊗[R] T j) :
    TensorProduct.comm R A Tlim (baseChangedLeg (A := A) (Tlim := Tlim) j z) =
      canonMod (fun i ↦ IsScalarTower.toAlgHom R (T i) Tlim) A j
        (TensorProduct.comm R A (T j) z) := by
  refine TensorProduct.inductionOn z (fun a x ↦ rfl) fun x y hx hy ↦ ?_
  simp only [map_add, hx, hy]

omit [Nonempty J] [IsDirectedOrder J] [DirectedSystem T fun i j h ↦ ⇑(f i j h)] in
/-- Exchanging the two tensor factors turns a transition map of the base-changed system into the
transition map `transMod` of the system `T_i` at the module `A`. -/
theorem commBaseChanged_map (i j : J) (h : i ≤ j) (z : A ⊗[R] T i) :
    TensorProduct.comm R A (T j) (baseChangedMap (A := A) f i j h z) =
      transMod (fun i j (h : i ≤ j) ↦ f i j h) A h (TensorProduct.comm R A (T i) z) := by
  refine TensorProduct.inductionOn z (fun a x ↦ rfl) fun x y hx hy ↦ ?_
  simp only [map_add, hx, hy]

variable
  (hf : ∀ i j (h : i ≤ j) (x : T i), algebraMap (T j) Tlim (f i j h x) = algebraMap (T i) Tlim x)
  (hsurj : ∀ r : Tlim, ∃ (j : J) (s : T j), algebraMap (T j) Tlim s = r)
  (hinj : ∀ (j : J) (s : T j), algebraMap (T j) Tlim s = 0 →
    ∃ (k : J) (hjk : j ≤ k), f j k hjk s = 0)

include hf hsurj hinj in
/-- **Joint surjectivity for the base-changed system**: every element of `A ⊗[R] Tlim` is the image
of an element of some `A ⊗[R] T_j`. -/
theorem exists_algebraMap_eq_baseChanged (z : A ⊗[R] Tlim) :
    ∃ (j : J) (y : A ⊗[R] T j), baseChangedLeg (A := A) (Tlim := Tlim) j y = z := by
  obtain ⟨j, y, hy⟩ := (Stacks.ColimitPresentation.FPModules.isModuleColimit f hf hsurj hinj
    A).jointly_surjective (TensorProduct.comm R A Tlim z)
  refine ⟨j, (TensorProduct.comm R A (T j)).symm y, (TensorProduct.comm R A Tlim).injective ?_⟩
  rw [commBaseChanged_leg, LinearEquiv.apply_symm_apply, hy]

include hf hsurj hinj in
/-- **Detection of zero at a stage for the base-changed system**: an element of `A ⊗[R] T_j` whose
image in `A ⊗[R] Tlim` vanishes already vanishes at a later stage. -/
theorem exists_map_eq_zero_baseChanged (j : J) (y : A ⊗[R] T j)
    (h : baseChangedLeg (A := A) (Tlim := Tlim) j y = 0) :
    ∃ (k : J) (hjk : j ≤ k), baseChangedMap (A := A) f j k hjk y = 0 := by
  have hy : canonMod (fun i ↦ IsScalarTower.toAlgHom R (T i) Tlim) A j
      (TensorProduct.comm R A (T j) y) =
      canonMod (fun i ↦ IsScalarTower.toAlgHom R (T i) Tlim) A j 0 := by
    rw [← commBaseChanged_leg, h, map_zero, map_zero]
  obtain ⟨k, hjk, hk⟩ := (Stacks.ColimitPresentation.FPModules.isModuleColimit f hf hsurj hinj
    A).exists_eq_of_canonMod_eq j (TensorProduct.comm R A (T j) y) 0 hy
  refine ⟨k, hjk, (TensorProduct.comm R A (T k)).injective ?_⟩
  rw [commBaseChanged_map, hk, map_zero, map_zero]

variable {M N : Type t} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

include hf hsurj hinj in
/-- **Algebra 05LI part (1) along the base-changed system.**  If `M` is a finite `A`-module and
two `A`-linear maps `M → N` have equal base changes to `A ⊗[R] Tlim`, then their base changes to
`A ⊗[R] T_i` agree for some `i`. -/
theorem statement_one_baseChanged (hM : Module.Finite A M) (u u' : M →ₗ[A] N)
    (h : LinearMap.baseChange (A ⊗[R] Tlim) u = LinearMap.baseChange (A ⊗[R] Tlim) u') :
    ∃ i : J, LinearMap.baseChange (A ⊗[R] T i) u = LinearMap.baseChange (A ⊗[R] T i) u' := by
  let : ∀ j : J, Algebra (A ⊗[R] T j) (A ⊗[R] Tlim) := fun j ↦
    (baseChangedLeg (A := A) (Tlim := Tlim) j).toRingHom.toAlgebra
  let : ∀ j : J, IsScalarTower A (A ⊗[R] T j) (A ⊗[R] Tlim) := fun j ↦
    IsScalarTower.of_algebraMap_eq fun a ↦
      ((baseChangedLeg (A := A) (Tlim := Tlim) j).commutes a).symm
  have := directedSystem_baseChangedMap (A := A) f
  exact statement_one (fun i j (h : i ≤ j) ↦ baseChangedMap (A := A) f i j h)
    (fun j ↦ IsScalarTower.toAlgHom A (A ⊗[R] T j) (A ⊗[R] Tlim))
    (Stacks.ColimitPresentation.FPModules.isModuleColimit
      (fun i j (h : i ≤ j) ↦ baseChangedMap (A := A) f i j h)
      (fun i j h x ↦ by
        show baseChangedLeg (A := A) (Tlim := Tlim) j (baseChangedMap (A := A) f i j h x) =
          baseChangedLeg (A := A) (Tlim := Tlim) i x
        induction x with
        | tmul a y => simp [hf i j h y]
        | add x y hx hy => simp only [map_add, hx, hy])
      (exists_algebraMap_eq_baseChanged f hf hsurj hinj)
      (exists_map_eq_zero_baseChanged f hf hsurj hinj) N)
    hM u u' h

include hf hsurj hinj in
/-- **The vanishing case of Algebra 05LI part (1) along the base-changed system.**  If `M` is a
finite `A`-module and the base change of `u : M → N` to `A ⊗[R] Tlim` vanishes, then its base
change to `A ⊗[R] T_i` vanishes for some `i`. -/
theorem exists_baseChange_eq_zero_baseChanged (hM : Module.Finite A M) (u : M →ₗ[A] N)
    (h : LinearMap.baseChange (A ⊗[R] Tlim) u = 0) :
    ∃ i : J, LinearMap.baseChange (A ⊗[R] T i) u = 0 := by
  obtain ⟨i, hi⟩ := statement_one_baseChanged f hf hsurj hinj hM u 0 (by
    rw [h, LinearMap.baseChange_zero])
  exact ⟨i, by rw [hi, LinearMap.baseChange_zero]⟩

end BaseChanged

end Stacks.FinitePresentation.ColimitDescent

end
