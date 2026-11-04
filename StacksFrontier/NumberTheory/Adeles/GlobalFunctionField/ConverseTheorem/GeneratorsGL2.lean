module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.ConverseTheorem.WhittakerSum

/-!
# Right `GL₂(K)`-invariance from invariance under generators

A function `F` on `GL₂(A)` which is right invariant under the diagonal matrices `diag(η, 1)`
(`η ∈ Kˣ`), the unipotent matrices `n(κ)` (`κ ∈ K`), the scalar matrices of `Kˣ` and the Weyl
element `w = (0, -1; 1, 0)` is right `GL₂(K)`-invariant. This is the Bruhat decomposition
`GL₂(K) = B(K) ∪ N(K) w B(K)`, proved in `GL₂(K)` and then mapped to `GL₂(A)`:
`(a, b; 0, d) = d · diag(a d⁻¹, 1) · n(a⁻¹ b)`, and for `c ≠ 0` the matrix
`w n(-a c⁻¹) (a, b; c, d)` is upper triangular.

Applied to the Fourier–Whittaker sum `f = whittakerSum ψ ω c` of
`ConverseTheorem/WhittakerSum.lean`, which is invariant under `diag(η, 1)` and `n(κ)`, this
reduces the right `GL₂(K)`-invariance of `f` (the hypothesis of `isEigenform_whittakerSum`) to
`ω(Kˣ) = 1` and the single identity `f(x w) = f(x)`, the converse theorem proper.

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.mapGLK` — `GL₂(K) → GL₂(A)`.
* `Stacks.Adeles.GlobalFunctionField.weylK` — the Weyl element `w ∈ GL₂(K) ⊆ GL₂(A)`.

## Main results

* `Stacks.Adeles.GlobalFunctionField.right_invariant_of_generators`.
* `Stacks.Adeles.GlobalFunctionField.whittakerSum_right_invariant` — `f` is right
  `GL₂(K)`-invariant if `ω(Kˣ) = 1` and `f(x w) = f(x)`.

## References

* H. Jacquet, R. P. Langlands, *Automorphic forms on GL(2)*, LNM 114, §11.
* [Stacks Project, Tag 03VU](https://stacks.math.columbia.edu/tag/03VU)
-/

@[expose] public noncomputable section

open Matrix

universe u w

namespace Stacks.Adeles.GlobalFunctionField

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
variable {Λ : Type w}

section Bruhat

/-- **Bruhat decomposition, upper triangular cell.** If `g = (a, b; 0, d) ∈ GL₂(K)`, then
`g = d · diag(a d⁻¹, 1) · n(a⁻¹ b)`. -/
public theorem eq_scalar_mul_diagGL_mul_upperRightHom {F : Type*} [Field F] (g : GL (Fin 2) F)
    (h : g 1 0 = 0) :
    ∃ (d η : Fˣ) (b : F), g = GeneralLinearGroup.scalar (Fin 2) d * diagGL η *
      GeneralLinearGroup.upperRightHom b := by
  have hdet : g 0 0 * g 1 1 ≠ 0 := by
    have := ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
    rwa [det_fin_two, h, mul_zero, sub_zero] at this
  have ha : g 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have hd : g 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  refine ⟨Units.mk0 _ hd, Units.mk0 (g 0 0 / g 1 1) (div_ne_zero ha hd), g 0 1 / g 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two, h, Matrix.diagonal_apply] <;>
    field_simp

/-- **Bruhat decomposition, big cell.** If `g = (a, b; c, d) ∈ GL₂(K)` with `c ≠ 0`, then
`w n(-a c⁻¹) g` is upper triangular, `w = (0, -1; 1, 0)`. -/
public theorem gammaK_mul_upperRightHom_mul_apply_one_zero {F : Type*} [Field F]
    (g : GL (Fin 2) F) (hc : g 1 0 ≠ 0) :
    (gammaK (0 : F) one_ne_zero * GeneralLinearGroup.upperRightHom (-(g 0 0 / g 1 0)) * g) 1 0 =
      0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  ring

end Bruhat

variable (K) in
/-- `GL₂(K) → GL₂(A)`, through the diagonal embedding `K → principalAdeles K`. -/
public def mapGLK : GL (Fin 2) K →* GL (Fin 2) (AdeleRing K) :=
  mapK.comp (GeneralLinearGroup.map (diagP k K))

/-- The entries of `mapGLK k K g` are the diagonal images of the entries of `g`. -/
public theorem coe_mapGLK_apply (g : GL (Fin 2) K) (i j : Fin 2) :
    ((mapGLK k K g : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K)) i j =
      diag k K (g i j) := rfl

/-- The diagonal embedding `K → principalAdeles K` is injective. -/
public theorem diagP_injective : Function.Injective (diagP k K) := fun _ _ h =>
  diag_injective k (congrArg Subtype.val h)

/-- The diagonal embedding `K → principalAdeles K` is surjective. -/
public theorem diagP_surjective : Function.Surjective (diagP k K) := fun y => by
  have hy : (y : AdeleRing K) ∈ (diag k K).range := by rw [range_diag k]; exact y.2
  obtain ⟨κ, hκ⟩ := hy
  exact ⟨κ, Subtype.ext hκ⟩

/-- Every element of `GL₂(principalAdeles K)` comes from `GL₂(K)`. -/
public theorem exists_mapGLK_eq (γ : GL (Fin 2) (principalAdeles K)) :
    ∃ g : GL (Fin 2) K, mapGLK k K g = mapK γ := by
  let e : K ≃+* principalAdeles K :=
    RingEquiv.ofBijective (diagP k K) ⟨diagP_injective k, diagP_surjective k⟩
  refine ⟨GeneralLinearGroup.map (e.symm : principalAdeles K →+* K) γ, congrArg mapK ?_⟩
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply]
  exact e.apply_symm_apply _

variable (K) in
/-- The Weyl element `w = (0, -1; 1, 0) ∈ GL₂(K)`, as an element of `GL₂(A)`. -/
public def weylK : GL (Fin 2) (AdeleRing K) :=
  mapGLK k K (gammaK (0 : K) one_ne_zero)

/-- The Weyl element `weylK k K` is the matrix `(0, -1; 1, 0)`. -/
public theorem coe_weylK :
    ((weylK k K : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K)) =
      !![0, -1; 1, 0] := by
  ext i j
  rw [weylK, coe_mapGLK_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- `mapGLK` sends `diag(η, 1)` to `diagK k K η`. -/
public theorem mapGLK_diagGL (η : Kˣ) : mapGLK k K (diagGL η) = diagK k K η := rfl

/-- `mapGLK` sends `n(κ)` to `n(κ)`, with `κ` embedded diagonally in the adeles. -/
public theorem mapGLK_upperRightHom (κ : K) :
    mapGLK k K (GeneralLinearGroup.upperRightHom κ) =
      GeneralLinearGroup.upperRightHom (diag k K κ) := by
  ext i j
  rw [coe_mapGLK_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- `mapGLK` sends the scalar matrix `κ` to the scalar matrix of the diagonal image of `κ`. -/
public theorem mapGLK_scalar (κ : Kˣ) :
    mapGLK k K (GeneralLinearGroup.scalar (Fin 2) κ) =
      scalarGL (Units.map (diag k K).toMonoidHom κ) := by
  ext i j
  rw [coe_mapGLK_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

variable (K) in
/-- The subgroup of `g ∈ GL₂(K)` under which `F` is right invariant. -/
public def rightInvariantSubgroup (F : GL (Fin 2) (AdeleRing K) → Λ) :
    Subgroup (GL (Fin 2) K) where
  carrier := {g | ∀ x, F (x * mapGLK k K g) = F x}
  one_mem' x := by rw [map_one, mul_one]
  mul_mem' {a b} ha hb x := by rw [map_mul, ← mul_assoc, hb, ha]
  inv_mem' {a} ha x := by
    rw [← ha (x * mapGLK k K a⁻¹), mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

/-- **Generators of `GL₂(K)`.** A function right invariant under `diag(η, 1)`, `n(κ)`, the
scalars of `Kˣ` and `w` is right invariant under `GL₂(K)`. -/
public theorem right_invariant_mapGLK_of_generators {F : GL (Fin 2) (AdeleRing K) → Λ}
    (hdiag : ∀ x (η : Kˣ), F (x * diagK k K η) = F x)
    (hn : ∀ x (κ : K), F (x * GeneralLinearGroup.upperRightHom (diag k K κ)) = F x)
    (hscal : ∀ x (κ : Kˣ), F (x * scalarGL (Units.map (diag k K).toMonoidHom κ)) = F x)
    (hw : ∀ x, F (x * weylK k K) = F x) (x : GL (Fin 2) (AdeleRing K)) (g : GL (Fin 2) K) :
    F (x * mapGLK k K g) = F x := by
  let H := rightInvariantSubgroup k K F
  have hnH : ∀ κ : K, GeneralLinearGroup.upperRightHom κ ∈ H := fun κ y => by
    rw [mapGLK_upperRightHom]; exact hn y κ
  have hwH : gammaK (0 : K) one_ne_zero ∈ H := hw
  have hB : ∀ g : GL (Fin 2) K, g 1 0 = 0 → g ∈ H := fun g h => by
    obtain ⟨d, η, b, rfl⟩ := eq_scalar_mul_diagGL_mul_upperRightHom g h
    refine H.mul_mem (H.mul_mem (fun y => ?_) (fun y => hdiag y η)) (hnH b)
    rw [mapGLK_scalar]; exact hscal y d
  suffices g ∈ H from this x
  by_cases hc : g 1 0 = 0
  · exact hB g hc
  · set n := GeneralLinearGroup.upperRightHom (-(g 0 0 / g 1 0))
    have e : g = n⁻¹ * (gammaK (0 : K) one_ne_zero)⁻¹ *
        (gammaK (0 : K) one_ne_zero * n * g) := by
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem (hnH _)) (H.inv_mem hwH))
      (hB _ (gammaK_mul_upperRightHom_mul_apply_one_zero g hc))

/-- **Generators of `GL₂(K)`**, in the form of the right invariance of unramified cusp forms:
a function right invariant under `diag(η, 1)`, `n(κ)`, the scalars of `Kˣ` and `w` is right
invariant under `GL₂(principalAdeles K)`. -/
public theorem right_invariant_of_generators {F : GL (Fin 2) (AdeleRing K) → Λ}
    (hdiag : ∀ x (η : Kˣ), F (x * diagK k K η) = F x)
    (hn : ∀ x (κ : K), F (x * GeneralLinearGroup.upperRightHom (diag k K κ)) = F x)
    (hscal : ∀ x (κ : Kˣ), F (x * scalarGL (Units.map (diag k K).toMonoidHom κ)) = F x)
    (hw : ∀ x, F (x * weylK k K) = F x) (x : GL (Fin 2) (AdeleRing K))
    (γ : GL (Fin 2) (principalAdeles K)) :
    F (x * GeneralLinearGroup.map (principalAdeles K).subtype γ) = F x := by
  obtain ⟨g, hg⟩ := exists_mapGLK_eq k γ
  rw [← mapK, ← hg]
  exact right_invariant_mapGLK_of_generators k hdiag hn hscal hw x g

variable [Field Λ] {ψ : AddChar (AdeleRing K) Λ} {ω : (AdeleRing K)ˣ →* Λˣ}
  {c : (Place K →₀ ℤ) → Λ}

/-- **Right `GL₂(K)`-invariance of `f` from `w`-invariance.** If `ω` is trivial on the principal
ideles and `f(x w) = f(x)`, then `f = whittakerSum ψ ω c` is right `GL₂(K)`-invariant. -/
public theorem whittakerSum_right_invariant (hψ : IsAdelicChar k K ψ)
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1)
    (hωK : ∀ κ : Kˣ, ω (Units.map (diag k K).toMonoidHom κ) = 1)
    (hw : ∀ x, whittakerSum k K ψ ω c (x * weylK k K) = whittakerSum k K ψ ω c x)
    (x : GL (Fin 2) (AdeleRing K)) (γ : GL (Fin 2) (principalAdeles K)) :
    whittakerSum k K ψ ω c (x * GeneralLinearGroup.map (principalAdeles K).subtype γ) =
      whittakerSum k K ψ ω c x :=
  right_invariant_of_generators k (whittakerSum_mul_diagK k)
    (whittakerSum_mul_upperRightHom_diag k hψ hω hc)
    (fun x κ => by
      rw [← scalarGL_mul_comm, whittakerSum_scalarGL_mul k hω hc, hωK, Units.val_one, one_mul])
    hw x γ

end Stacks.Adeles.GlobalFunctionField

end
