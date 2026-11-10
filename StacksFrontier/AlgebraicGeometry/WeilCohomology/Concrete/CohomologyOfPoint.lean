module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionIntersectionUnit
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TraceDisjointUnion
public import StacksCore.Tactic.StacksAttribute

/-!
# The cohomology of the point

Let `W` be data (D0)–(D3) of Section 45.9 (Tag 0FHA) over the actual category of smooth projective
schemes over `k`. This file proves Stacks 0FHE on it; the first clause of the nonempty case of
Stacks 0FHF, which rests on it, is `Stacks.WeilCohomology.WeilData.cycleClass_fundamentalClass`
in `StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassFundamental`.

* **Stacks 0FHE.** `H^i(Spec k) = 0` for `i ≠ 0`, there is a unique `F`-algebra isomorphism
  `F = H^0(Spec k)`, `γ([Spec k]) = 1` and `∫_{Spec k} 1 = 1`.

## The proofs

For Stacks 0FHE write `P = Spec k`. The fibre product `P ×_k P` has equal projections
`pr₁ = pr₂ : P × P ⟶ P`, and they are isomorphisms. So axiom (B)(a) for `P × P`,
`a ⊗ b ↦ pr₁^*a ∪ pr₂^*b = pr₁^*(a ∪ b)`, says that multiplication `H^*(P) ⊗_F H^*(P) → H^*(P)`
is bijective. Its injectivity gives `a ⊗ 1 = 1 ⊗ a` for every `a`, and applying `id ⊗ φ` for a
linear form `φ` with `φ(1) = 1` gives `a = φ(a) · 1`. Axiom (C)(d) makes `H^0(P)` nonzero, so
`F → H^*(P)` is an isomorphism; as `1` has degree `0`, all other degrees vanish. This is the
source's argument "look at dimensions", which needs no finiteness of `H^*(P)`. Then
`γ([P]) = c · 1` with `c ≠ 0` by (C)(d), and `[P] · [P] = [P]` (the unit law
`Stacks.WeilCohomology.codimensionIntersectionProduct_fundamentalClass_left`) with (C)(c) gives
`c² = c`, so `c = 1`; finally `∫_P 1 = ∫_P γ([P]) = 1` by (C)(d).

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.toPoint`: the structure morphism `X ⟶ Spec k`.
* `Stacks.WeilCohomology.WeilData.pointH0AlgEquiv`: the `F`-algebra isomorphism
  `F ≃ H^0(Spec k)`.

## Main results

* `Stacks.WeilCohomology.WeilData.grade_point_eq_bot`, `pointH0AlgEquiv`,
  `pointH0AlgEquiv_unique`, `cycleClass_fundamentalClass_point`, `trace_unitTw_point`:
  Stacks 0FHE.

## References

* [Stacks Project, Tag 0FHE](https://stacks.math.columbia.edu/tag/0FHE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

namespace SmoothProjectiveScheme

/-- **The structure morphism `X ⟶ Spec k`** of a smooth projective scheme over `k`, as a morphism
to the point. -/
def toPoint (X : (SmoothProjectiveScheme k).FullSubcategory) : X ⟶ point k :=
  ObjectProperty.homMk (Over.homMk (V := (point k).obj) X.obj.hom (Category.comp_id _))

/-- The underlying morphism of schemes of `toPoint X` is the structure morphism of `X`. -/
@[simp]
theorem toPoint_hom_left (X : (SmoothProjectiveScheme k).FullSubcategory) : (toPoint X).hom.left
    = X.obj.hom :=
  rfl

/-- The two projections of `Spec k ×_k Spec k` coincide. -/
theorem fst_point_eq_snd_point : fst (point k) (point k) = snd (point k) (point k) := by
  have : Mono (point k).obj.hom := show Mono (𝟙 (Spec (.of k))) from inferInstance
  exact hom_ext_left ((cancel_mono (point k).obj.hom).mp
    (pullback.condition (f := (point k).obj.hom) (g := (point k).obj.hom)))

/-- The diagonal of `Spec k` is inverse to the first projection of `Spec k ×_k Spec k`. -/
theorem diag_fst_point : diag (point k) ≫ fst (point k) (point k) = 𝟙 _ :=
  hom_ext_left (pullback.diagonal_fst (𝟙 (Spec (.of k))))

/-- The first projection of `Spec k ×_k Spec k` is inverse to the diagonal. -/
theorem fst_diag_point : fst (point k) (point k) ≫ diag (point k) = 𝟙 _ := by
  refine hom_ext_left (pullback.hom_ext ?_ ?_)
  · change (pullback.fst _ _ ≫ pullback.diagonal _) ≫ pullback.fst _ _ = 𝟙 _ ≫ pullback.fst _ _
    rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.id_comp]
  · change (pullback.fst _ _ ≫ pullback.diagonal _) ≫ pullback.snd _ _ = 𝟙 _ ≫ pullback.snd _ _
    rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, Category.id_comp]
    exact congrArg (fun f ↦ f.hom.left) (fst_point_eq_snd_point (k := k))

end SmoothProjectiveScheme

open SmoothProjectiveScheme

namespace WeilData

variable {F : Type w} [Field F] (W : WeilData k F)

/-- Pullback along the first projection of `Spec k ×_k Spec k` is bijective. -/
theorem pull_fst_point_bijective :
    Function.Bijective (W.pull (fst (point k) (point k))) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨W.pull (diag (point k)), fun a ↦ ?_, fun a ↦ ?_⟩
  · rw [← AlgHom.comp_apply, ← W.pull_comp, diag_fst_point, W.pull_id, AlgHom.id_apply]
  · rw [← AlgHom.comp_apply, ← W.pull_comp, fst_diag_point, W.pull_id, AlgHom.id_apply]

/-- On `Spec k`, the Künneth map is pullback along `pr₁` of the multiplication map. -/
theorem kunnethMap_point :
    W.kunnethMap (point k) (point k) =
      (W.pull (fst (point k) (point k))).toLinearMap.comp (LinearMap.mul' F (W.H (point k))) := by
  ext a b
  simp [fst_point_eq_snd_point]

variable {W}

/-- Axiom (C)(d) makes the class of `[Spec k]` nonzero. -/
private theorem cycleClass_fundamentalClass_point_ne_zero (hCd : W.CycleClassPoint) :
    W.cycleClass (point k) 0 (fundamentalClass (point k)) ≠ 0 := fun h ↦ by
  unfold CycleClassPoint at hCd
  rw [h, map_zero] at hCd
  exact zero_ne_one hCd

/-- Axiom (C)(d) makes `H^*(Spec k)` nonzero. -/
theorem nontrivial_point (hCd : W.CycleClassPoint) : Nontrivial (W.H (point k)) := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have : Subsingleton (W.grade (point k) (2 * ((0 : ℕ) : ℤ))) :=
    ⟨fun a b ↦ Subtype.ext (Subsingleton.elim (a : W.H (point k)) b)⟩
  have : Subsingleton (W.Tw (point k) (2 * ((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ)) := by
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    induction x using TensorProduct.inductionOn with
    | tmul a b => rw [Subsingleton.elim a 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact cycleClass_fundamentalClass_point_ne_zero hCd (Subsingleton.elim _ _)

/-- Under axiom (B)(a), every class on `Spec k` is a scalar multiple of the unit. -/
theorem exists_eq_algebraMap_point (hBa : W.KunnethIsomorphism) (hCd : W.CycleClassPoint)
    (a : W.H (point k)) : ∃ c : F, a = algebraMap F (W.H (point k)) c := by
  have := nontrivial_point hCd
  have hinj : Function.Injective (LinearMap.mul' F (W.H (point k))) := by
    have h := (hBa (point k) (point k)).1
    rw [kunnethMap_point, LinearMap.coe_comp] at h
    exact h.of_comp
  have htensor : a ⊗ₜ[F] (1 : W.H (point k)) = (1 : W.H (point k)) ⊗ₜ[F] a :=
    hinj (by simp)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual F (W.H (point k)), φ 1 ≠ 0 := by
    by_contra! h
    exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff F (1 : W.H (point k))).mp h)
  refine ⟨φ a / φ 1, ?_⟩
  have h := congrArg ((TensorProduct.rid F (W.H (point k))).toLinearMap ∘ₗ
    (LinearMap.lTensor (W.H (point k)) φ)) htensor
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.rid_tmul] at h
  rw [Algebra.algebraMap_eq_smul_one, div_eq_mul_inv, mul_comm, mul_smul, ← h, smul_smul,
    inv_mul_cancel₀ hφ, one_smul]

/-- **Stacks 0FHE**, the algebra structure: under (B)(a) and (C)(d), the structure map
`F → H^*(Spec k)` is bijective. -/
theorem algebraMap_point_bijective (hBa : W.KunnethIsomorphism) (hCd : W.CycleClassPoint) :
    Function.Bijective (algebraMap F (W.H (point k))) := by
  have := nontrivial_point hCd
  exact ⟨(algebraMap F (W.H (point k))).injective,
    fun a ↦ (exists_eq_algebraMap_point hBa hCd a).imp fun _ h ↦ h.symm⟩

/-- **Stacks Project, Tag 0FHE**, first clause: `H^i(Spec k) = 0` for `i ≠ 0`. -/
@[stacks 0FHE "H^i(Spec k) = 0 for i ≠ 0, on the actual category of smooth projective schemes"]
theorem grade_point_eq_bot (hBa : W.KunnethIsomorphism) (hCd : W.CycleClassPoint) {i : ℤ}
    (hi : i ≠ 0) : W.grade (point k) i = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_
  obtain ⟨c, rfl⟩ := exists_eq_algebraMap_point hBa hCd x
  have h0 : algebraMap F (W.H (point k)) c ∈ W.grade (point k) 0 :=
    SetLike.algebraMap_mem_graded _ c
  rw [← DirectSum.decompose_of_mem_same (W.grade (point k)) hx,
    DirectSum.decompose_of_mem_ne (W.grade (point k)) h0 (Ne.symm hi)]

/-- The unit of `H^0(Spec k)` spans it. -/
theorem H0_point_bijective (hBa : W.KunnethIsomorphism) (hCd : W.CycleClassPoint) :
    Function.Bijective (algebraMap F (W.H0 (point k))) := by
  have := nontrivial_point hCd
  refine ⟨(algebraMap F (W.H0 (point k))).injective, fun a ↦ ?_⟩
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_point hBa hCd a
  exact ⟨c, Subtype.ext hc.symm⟩

/-- **Stacks 0FHE**: the `F`-algebra isomorphism `F ≃ H^0(Spec k)`. -/
def pointH0AlgEquiv (hBa : W.KunnethIsomorphism) (hCd : W.CycleClassPoint) :
    F ≃ₐ[F] W.H0 (point k) :=
  AlgEquiv.ofBijective (Algebra.ofId F _) (H0_point_bijective hBa hCd)

/-- **Stacks Project, Tag 0FHE**, second clause: there is a unique `F`-algebra isomorphism
`F = H^0(Spec k)`. Existence is `Stacks.WeilCohomology.WeilData.pointH0AlgEquiv`; any other
`F`-algebra isomorphism is equal to it. -/
@[stacks 0FHE "the unique F-algebra isomorphism F = H^0(Spec k)"]
theorem pointH0AlgEquiv_unique (hBa : W.KunnethIsomorphism) (hCd : W.CycleClassPoint)
    (e : F ≃ₐ[F] W.H0 (point k)) : e = pointH0AlgEquiv hBa hCd :=
  AlgEquiv.coe_toAlgHom_injective (Subsingleton.elim _ _)

/-- **Stacks Project, Tag 0FHE**, third clause: `γ([Spec k]) = 1` in `H^0(Spec k)`. -/
@[stacks 0FHE "γ([Spec k]) = 1, from (B)(a), (C)(c), (C)(d) and the unit law [Spec k]·[Spec k] = \
[Spec k] in CH^0(Spec k)"]
theorem cycleClass_fundamentalClass_point (hBa : W.KunnethIsomorphism) (hCc : W.CycleClassMul)
    (hCd : W.CycleClassPoint) :
    W.cycleClass (point k) 0 (fundamentalClass (point k)) =
      W.unitTw (point k) _ _ (by simp) := by
  have := nontrivial_point hCd
  set g := W.cycleClass (point k) 0 (fundamentalClass (point k)) with hg
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_point hBa hCd (W.twCoord (point k) _ _ g : W.H (point k))
  have hmul : codimensionIntersectionProduct k (point k).obj.hom 0 0 (fundamentalClass (point k))
      (fundamentalClass (point k)) = fundamentalClass (point k) := by
    funext d
    rw [codimensionIntersectionProduct_fundamentalClass_left]
    rfl
  have hsq := hCc (point k) 0 0 (fundamentalClass (point k)) (fundamentalClass (point k))
  rw [hmul] at hsq
  have hsq' : g = W.cupTw (point k) (2 * 0) (2 * 0) (2 * 0) (by ring) 0 0 0 (by ring) g g := hsq
  have hcoord : (W.twCoord (point k) _ _ g : W.H (point k)) =
      (W.twCoord (point k) _ _ (W.cupTw (point k) (2 * 0) (2 * 0) (2 * 0) (by ring) 0 0 0 (by ring)
        g g) : W.H (point k)) := congrArg _ (congrArg _ hsq')
  rw [twCoord_cupTw, coe_cup, hc, ← map_mul] at hcoord
  have hcc : c * c = c := (algebraMap F (W.H (point k))).injective hcoord.symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hg0 : g = 0 := (W.twCoord (point k) _ _).injective (Subtype.ext (by simpa using hc))
    exact cycleClass_fundamentalClass_point_ne_zero hCd (hg ▸ hg0)
  have hc1 : c = 1 := by
    have := mul_left_cancel₀ hc0 (hcc.trans (mul_one c).symm)
    exact this
  apply (W.twCoord (point k) _ _).injective
  apply Subtype.ext
  rw [hc, hc1, map_one, coe_twCoord_unitTw]

/-- **Stacks Project, Tag 0FHE**, fourth clause: `∫_{Spec k} 1 = 1`. -/
@[stacks 0FHE "∫_{Spec k} 1 = 1"]
theorem trace_unitTw_point (hBa : W.KunnethIsomorphism) (hCc : W.CycleClassMul)
    (hCd : W.CycleClassPoint) :
    W.trace (point k) 0 isNonemptyEquidimensional_point (W.unitTw (point k) _ _ (by simp)) = 1 := by
  have h := hCd
  unfold CycleClassPoint at h
  rwa [cycleClass_fundamentalClass_point hBa hCc hCd] at h

end WeilData

end Stacks.WeilCohomology

end
