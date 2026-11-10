module

public import StacksFrontier.Homology.DerivedComplete

/-!
# Maps into derived complete objects

Let `A` be a commutative ring and `D` an `A`-linear pre-triangulated category with countable
products, for instance the derived category of sheaves of `A`-modules on a site. Let `E` be an
object of `D` with `T(E, f) = 0`, that is, derived complete at `f ∈ A`.

* If `f` acts bijectively on `Hom(M, E)` (by precomposition with `f • 𝟙 M`), then
  `Hom(M, E) = 0`: a map `φ` gives the family `(f⁻ⁿ φ)ₙ` into `∏ₙ E`, which is killed by
  `1 - f · shift`.
* Consequently, if `M ⟶ M ⟶ M' ⟶ M⟦1⟧` is a distinguished triangle whose first map is
  `f • 𝟙 M` and every map from a shift of `M'` to `E` vanishes, then every map from a shift
  of `M` to `E` vanishes.

Iterating over a finite family `f₀, …, f_{r-1}`: if `E` is derived complete at every `fᵢ` and the
iterated cone `M/(f₀, …, f_{r-1})` admits no nonzero map to a shift of `E`, then neither does
`M`. With `M = E` this is the derived Nakayama lemma: an object derived complete at every `fᵢ`
whose iterated cone vanishes is zero.

## Main results

* `eq_zero_of_isDerivedCompleteAt_of_bijective`: maps into a complete object from an object on
  which `f` acts bijectively vanish.
* `eq_zero_of_isDerivedCompleteAt_of_distTriang`: the same through a cone of `f`.
* `isLeftOrthogonalShifts_of_coneChain`: the iterated form, for maps from all shifts.
* `isZero_of_isDerivedCompleteAt_of_coneChain`: the derived Nakayama lemma.

## References

* [Stacks Project, Tag 091N](https://stacks.math.columbia.edu/tag/091N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedComplete

variable {A : Type*} [CommRing A]
  {D : Type*} [Category D] [Preadditive D] [Linear A D] [HasProductsOfShape ℕ D]

/-- **Maps into a derived complete object.** If `T(E, f) = 0` and `f` acts bijectively on
`Hom(M, E)`, then every map `M ⟶ E` is zero. -/
theorem eq_zero_of_isDerivedCompleteAt_of_bijective {E M : D} {f : A}
    (hE : IsDerivedCompleteAt E f)
    (hbij : Function.Bijective fun φ : M ⟶ E => (f • 𝟙 M) ≫ φ) (φ : M ⟶ E) : φ = 0 := by
  obtain ⟨g, hg⟩ := Function.bijective_iff_has_inverse.1 hbij
  let ψ : ℕ → (M ⟶ E) := fun n => g^[n] φ
  have hψ : ∀ n, (f • 𝟙 M) ≫ ψ (n + 1) = ψ n := fun n => by
    simp only [ψ, Function.iterate_succ_apply']
    exact hg.2 _
  have hzero : Pi.lift ψ ≫ oneSubSmulShift E f = 0 := by
    apply Limits.Pi.hom_ext
    intro n
    rw [Category.assoc, oneSubSmulShift_π, Preadditive.comp_sub, Linear.comp_smul, Pi.lift_comp_π,
      Pi.lift_comp_π, zero_comp, ← hψ n, Linear.smul_comp, Category.id_comp, sub_self]
  have : IsIso (oneSubSmulShift E f) := hE
  have hlift : Pi.lift ψ = 0 := by
    rw [← cancel_mono (oneSubSmulShift E f), hzero, zero_comp]
  simpa [ψ] using congrArg (· ≫ Pi.π (fun _ : ℕ => E) 0) hlift

/-- The same, for precomposition with `± f • 𝟙 M`. -/
theorem eq_zero_of_isDerivedCompleteAt_of_bijective' {E M : D} {f : A}
    (hE : IsDerivedCompleteAt E f) {u : M ⟶ M} (hu : u = f • 𝟙 M ∨ u = -(f • 𝟙 M))
    (hbij : Function.Bijective fun φ : M ⟶ E => u ≫ φ) (φ : M ⟶ E) : φ = 0 := by
  rcases hu with rfl | rfl
  · exact eq_zero_of_isDerivedCompleteAt_of_bijective hE hbij φ
  · refine eq_zero_of_isDerivedCompleteAt_of_bijective hE ?_ φ
    have h : (fun φ : M ⟶ E => (f • 𝟙 M) ≫ φ) =
        Neg.neg ∘ fun φ : M ⟶ E => (-(f • 𝟙 M)) ≫ φ := by
      funext φ
      simp
    rw [h]
    exact neg_bijective.comp hbij

variable [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- **Maps into a derived complete object through a cone of `f`.** Let `M ⟶ M ⟶ M' ⟶ M⟦1⟧` be
a distinguished triangle whose first map is `± f • 𝟙 M`. If `T(E, f) = 0` and the maps from `M'`
and from `M'⟦-1⟧` to `E` all vanish, then every map `M ⟶ E` vanishes. -/
theorem eq_zero_of_isDerivedCompleteAt_of_distTriang {E M M' : D} {f : A}
    (hE : IsDerivedCompleteAt E f) {u : M ⟶ M} (hu : u = f • 𝟙 M ∨ u = -(f • 𝟙 M))
    {v : M ⟶ M'} {w : M' ⟶ M⟦(1 : ℤ)⟧}
    (hT : Triangle.mk u v w ∈ distTriang D)
    (h₃ : ∀ φ : M' ⟶ E, φ = 0) (h₃' : ∀ φ : M'⟦(-1 : ℤ)⟧ ⟶ E, φ = 0)
    (φ : M ⟶ E) : φ = 0 := by
  refine eq_zero_of_isDerivedCompleteAt_of_bijective' hE hu ⟨fun φ₁ φ₂ h => ?_, fun ψ => ?_⟩ φ
  · rw [← sub_eq_zero]
    obtain ⟨χ, hχ⟩ := Triangle.yoneda_exact₂ _ hT (φ₁ - φ₂) (by
      change u ≫ (φ₁ - φ₂) = 0
      rw [Preadditive.comp_sub]
      exact sub_eq_zero.2 h)
    rw [hχ, h₃ χ, comp_zero]
  · obtain ⟨χ, hχ⟩ := Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang _ hT) ψ (h₃' _)
    exact ⟨χ, hχ.symm⟩

variable [∀ n : ℤ, (shiftFunctor D n).Linear A]

/-- The vanishing of all maps from all shifts of an object to `E`. -/
def IsLeftOrthogonalShifts (E M : D) : Prop :=
  ∀ (k : ℤ) (φ : M⟦k⟧ ⟶ E), φ = 0

/-- **Maps from all shifts into a derived complete object, through a cone of `f`.** Let
`M ⟶ M ⟶ M' ⟶ M⟦1⟧` be a distinguished triangle whose first map is `f • 𝟙 M`. If
`T(E, f) = 0` and no shift of `M'` maps nontrivially to `E`, then no shift of `M` does. -/
theorem isLeftOrthogonalShifts_of_distTriang {E M M' : D} {f : A}
    (hE : IsDerivedCompleteAt E f) {v : M ⟶ M'} {w : M' ⟶ M⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (f • 𝟙 M) v w ∈ distTriang D) (h : IsLeftOrthogonalShifts E M') :
    IsLeftOrthogonalShifts E M := by
  intro k φ
  refine eq_zero_of_isDerivedCompleteAt_of_distTriang hE (u := k.negOnePow • (f • 𝟙 M)⟦k⟧')
    ?_ (Triangle.shift_distinguished _ hT k) (h k) (fun ψ => ?_) φ
  · rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    rcases Int.even_or_odd k with hk | hk
    · left
      rw [Int.negOnePow_even _ hk, one_smul]
    · right
      rw [Int.negOnePow_odd _ hk, Units.neg_smul, one_smul]
  · have := h (k + -1) ((shiftFunctorAdd D k (-1)).hom.app M' ≫ ψ)
    rw [← cancel_epi ((shiftFunctorAdd D k (-1)).hom.app M'), this, comp_zero]

/-- **The iterated form.** Let `f₀, …, f_{r-1}` be elements with `T(E, fᵢ) = 0`, and let
`M₀, …, M_r` be objects with distinguished triangles `Mᵢ ⟶ Mᵢ ⟶ Mᵢ₊₁ ⟶ Mᵢ⟦1⟧` whose first map
is `fᵢ • 𝟙`. If no shift of `M_r` maps nontrivially to `E`, then no shift of `M₀` does. -/
theorem isLeftOrthogonalShifts_of_coneChain {E : D} {r : ℕ} (f : Fin r → A)
    (hE : ∀ i, IsDerivedCompleteAt E (f i)) (M : Fin (r + 1) → D)
    (v : ∀ i : Fin r, M i.castSucc ⟶ M i.succ) (w : ∀ i : Fin r, M i.succ ⟶ (M i.castSucc)⟦(1 : ℤ)⟧)
    (hT : ∀ i, Triangle.mk (f i • 𝟙 (M i.castSucc)) (v i) (w i) ∈ distTriang D)
    (h : IsLeftOrthogonalShifts E (M (Fin.last r))) : IsLeftOrthogonalShifts E (M 0) := by
  induction r with
  | zero => exact h
  | succ r ih =>
    exact ih (fun i => f i.castSucc) (fun i => hE _) (fun i => M i.castSucc)
      (fun i => v i.castSucc) (fun i => w i.castSucc) (fun i => hT i.castSucc)
      (isLeftOrthogonalShifts_of_distTriang (hE (Fin.last r)) (hT (Fin.last r)) h)

/-- **Derived Nakayama.** If `T(E, fᵢ) = 0` for every `i` and the iterated cone of the `fᵢ` on
`E` vanishes, then `E = 0`. -/
theorem isZero_of_isDerivedCompleteAt_of_coneChain {r : ℕ} (f : Fin r → A) (M : Fin (r + 1) → D)
    (hE : ∀ i, IsDerivedCompleteAt (M 0) (f i))
    (v : ∀ i : Fin r, M i.castSucc ⟶ M i.succ) (w : ∀ i : Fin r, M i.succ ⟶ (M i.castSucc)⟦(1 : ℤ)⟧)
    (hT : ∀ i, Triangle.mk (f i • 𝟙 (M i.castSucc)) (v i) (w i) ∈ distTriang D)
    (h : IsZero (M (Fin.last r))) : IsZero (M 0) := by
  have h' := isLeftOrthogonalShifts_of_coneChain f hE M v w hT
    (fun k φ => ((shiftFunctor D k).map_isZero h).eq_of_src _ _)
  have := h' 0 ((shiftFunctorZero D ℤ).hom.app (M 0))
  rw [IsZero.iff_id_eq_zero]
  have e := Iso.inv_hom_id_app (shiftFunctorZero D ℤ) (M 0)
  rw [this, comp_zero] at e
  exact e.symm

end DerivedComplete

end
