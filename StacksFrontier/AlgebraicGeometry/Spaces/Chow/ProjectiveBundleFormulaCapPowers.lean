module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleProjection

/-!
# Composing powers of the cap product with `c₁`, and the triangular argument

Two ingredients of the projective space bundle formula (Stacks 0ERV) that hold before passing
to rational equivalence.

* The `s`-fold cap product `c₁(ℒ)^s ∩ -` on cycles
  (`AlgebraicGeometry.Space.firstChernCapPowCycleMap`) is a composite of single cap products, so
  `c₁(ℒ)^s ∩ (c₁(ℒ)^i ∩ α) = c₁(ℒ)^{s+i} ∩ α` as cycles, up to the identification of the cycle
  groups of equal dimension.
* The injectivity half of Stacks 0ERV is a triangularity argument: the maps
  `Gᵢ = c₁(𝒪_P(1))^i ∩ π^*-` and `Fⱼ = π_*(c₁(𝒪_P(1))^{r-1-j} ∩ -)` satisfy `Fⱼ ∘ Gᵢ = 0` for
  `i < j` and `Fⱼ ∘ Gⱼ = id` (Stacks 0ERU), so `∑ Gᵢ(aᵢ) = 0` forces every `aᵢ = 0`. This is
  `AlgebraicGeometry.Space.eq_zero_of_sum_eq_zero_of_triangular`, stated for arbitrary families of
  abelian groups.

## Main results

* `AlgebraicGeometry.Space.firstChernCapPowCycleMap_firstChernCapPowCycleMap`:
  `c₁(ℒ)^s ∩ c₁(ℒ)^i ∩ α = c₁(ℒ)^{s+i} ∩ α` on cycles.
* `AlgebraicGeometry.Space.eq_zero_of_sum_eq_zero_of_triangular`: the triangular argument.

## References

* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
* [Stacks Project, Tag 0ERU](https://stacks.math.columbia.edu/tag/0ERU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-! ### The triangular argument -/

/-- **The triangular argument of the injectivity half of Stacks 0ERV.** Let `Gᵢ : Aᵢ → B` and
`Fⱼ : B → Aⱼ` be homomorphisms of abelian groups, indexed by `Fin n`, with `Fⱼ ∘ Gᵢ = 0` for
`i < j` and `Fⱼ ∘ Gⱼ = id`. If `∑ᵢ Gᵢ(aᵢ) = 0` then every `aᵢ` is zero: at the largest `j` with
`aⱼ ≠ 0`, applying `Fⱼ` gives `aⱼ = 0`. -/
theorem eq_zero_of_sum_eq_zero_of_triangular {n : ℕ} {A : Fin n → Type*}
    [∀ i, AddCommGroup (A i)] {B : Type*} [AddCommGroup B] (G : ∀ i, A i →+ B)
    (F : ∀ j, B →+ A j) (hlt : ∀ i j, i < j → ∀ a, F j (G i a) = 0)
    (hdiag : ∀ i a, F i (G i a) = a) (a : ∀ i, A i) (h : ∑ i, G i (a i) = 0) : a = 0 := by
  classical
  by_contra hne
  have hs : (Finset.univ.filter fun i => a i ≠ 0).Nonempty :=
    let ⟨i, hi⟩ := Function.ne_iff.1 hne
    ⟨i, (Finset.mem_filter_univ i).2 hi⟩
  set j := (Finset.univ.filter fun i => a i ≠ 0).max' hs
  have hj : a j ≠ 0 := (Finset.mem_filter_univ j).1 (Finset.max'_mem _ hs)
  have hgt : ∀ i, j < i → a i = 0 := fun i hji => by
    by_contra hi
    exact absurd (Finset.le_max' _ i ((Finset.mem_filter_univ i).2 hi)) (not_le.2 hji)
  have hF : F j (∑ i, G i (a i)) = a j := by
    rw [map_sum, Finset.sum_eq_single j (fun i _ hij => ?_) (fun h => absurd
      (Finset.mem_univ j) h), hdiag]
    rcases lt_or_gt_of_ne hij with hij | hij
    · exact hlt i j hij _
    · rw [hgt i hij, map_zero, map_zero]
  exact hj (hF.symm.trans (by rw [h, map_zero]))

/-! ### Composing powers of the cap product -/

section Power

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- The `s`-fold cap product only depends on the underlying cycle and the indices: equal
exponents, equal target dimensions and equal underlying coefficient functions give equal
underlying coefficient functions. -/
theorem coe_firstChernCapPowCycleMap_congr {s s' : ℕ} {m m' : ℤ} (hs : s = s') (hm : m = m')
    (α : CycleGroup D sX (m + s)) (α' : CycleGroup D sX (m' + s')) (hα : α.1 = α'.1) :
    (firstChernCapPowCycleMap D sX hX L hL s m α).1 =
      (firstChernCapPowCycleMap D sX hX L hL s' m' α').1 := by
  subst hs hm
  rw [Subtype.ext hα]

/-- **`c₁(ℒ)^s ∩ c₁(ℒ)^i ∩ α = c₁(ℒ)^{s+i} ∩ α` on cycles**, for `α ∈ Z_{m+s+i}(X)`, up to the
identification `Z_{m+s+i}(X) = Z_{m+(s+i)}(X)`. -/
theorem firstChernCapPowCycleMap_firstChernCapPowCycleMap (s i : ℕ) (m : ℤ)
    (α : CycleGroup D sX (m + s + i)) :
    firstChernCapPowCycleMap D sX hX L hL s m (firstChernCapPowCycleMap D sX hX L hL i (m + s) α) =
      firstChernCapPowCycleMap D sX hX L hL (s + i) m
        (cycleGroupCast D sX (by push_cast; ring) α) := by
  induction s generalizing m with
  | zero =>
    refine Subtype.ext ?_
    change (firstChernCapPowCycleMap D sX hX L hL i (m + (0 : ℕ)) α).1 = _
    exact coe_firstChernCapPowCycleMap_congr D sX hX L hL (by simp) (by simp) _ _ rfl
  | succ s ih =>
    refine Subtype.ext ?_
    refine Eq.trans ?_ (coe_firstChernCapPowCycleMap_congr D sX hX L hL (s := s + i + 1)
      (s' := s + 1 + i) (m := m) (by omega) rfl
      (cycleGroupCast D sX (by push_cast; ring) α) _ rfl)
    simp only [firstChernCapPowCycleMap, AddMonoidHom.coe_comp, Function.comp_apply]
    congr 2
    refine Subtype.ext ?_
    have := ih (m + 1) (cycleGroupCast D sX (by push_cast; ring) α)
    refine Eq.trans ?_ (congrArg Subtype.val this)
    exact coe_firstChernCapPowCycleMap_congr D sX hX L hL rfl rfl _ _
      (coe_firstChernCapPowCycleMap_congr D sX hX L hL (s := i) (s' := i)
        (m := m + ((s + 1 : ℕ) : ℤ)) (m' := m + 1 + (s : ℤ)) rfl (by push_cast; ring) α _ rfl)

end Power

end AlgebraicGeometry.Space

end
