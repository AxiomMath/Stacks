module

public import StacksFrontier.LinearAlgebra.ExteriorPower.WedgeFiltration
public import StacksFrontier.RingTheory.Kaehler.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graded pieces of the filtration of `Ω^•_{B/R}` by the forms pulled back from `A`

Let `R → A → B` be ring maps with `A → B` formally smooth. The sequence

`0 ⟶ B ⊗_A Ω_{A/R} ⟶ Ω_{B/R} ⟶ Ω_{B/A} ⟶ 0`

is split exact ([Stacks, Tag 031K], `KaehlerDifferential.exists_retraction_mapBaseChange`), so
`Ω_{B/R} ≅ (B ⊗_A Ω_{A/R}) × Ω_{B/A}` compatibly with the two maps. Filter `⋀ⁿ_B Ω_{B/R}` by the
wedges with forms pulled back from `A`:

`F^k ⋀ⁿ Ω_{B/R} = ∑_{j ≥ k} ⋀ʲ(B ⊗_A Ω_{A/R}) ∧ ⋀ⁿ⁻ʲ Ω_{B/R}`

(`exteriorPower.wedgeStep` for `KaehlerDifferential.mapBaseChange`). Then

* the kernel of `⋀ⁿ Ω_{B/R} ⟶ ⋀ⁿ Ω_{B/A}` is `F^1`, so `⋀ⁿ Ω_{B/R} / F^1 ≅ ⋀ⁿ Ω_{B/A}`;
* left multiplication induces an isomorphism
  `⋀ᵏ(B ⊗_A Ω_{A/R}) ⊗_B (⋀ᵐ Ω_{B/R} / F^1) ≅ F^k ⋀ᵏ⁺ᵐ Ω_{B/R} / F^{k+1}`.

These are the two facts about the filtration of [Stacks, Section 0FMK] on an affine chart that the
proof of [Stacks, Tag 0FUM] uses (its facts (6)(d) and (6)(e)).

## Main definitions

* `KaehlerDifferential.towerSplitEquiv`: the splitting `Ω_{B/R} ≅ (B ⊗_A Ω_{A/R}) × Ω_{B/A}`.
* `exteriorPower.gradedLeftMul`: the map `⋀ᵏ E ⊗ (⋀ᵐ H / F^1) ⟶ F^k ⋀ⁿ H / F^{k+1}`,
  `a ⊗ [η] ↦ [(⋀ ι) a ∧ η]`, for any linear map `ι : E ⟶ H`.

## Main results

* `KaehlerDifferential.ker_map_exteriorPower_eq_wedgeStep_one`: the kernel of
  `⋀ⁿ Ω_{B/R} ⟶ ⋀ⁿ Ω_{B/A}` is `F^1`.
* `KaehlerDifferential.gradedLeftMul_bijective`: `⋀ᵏ(B ⊗_A Ω_{A/R}) ⊗ (⋀ᵐ Ω_{B/R} / F^1)` is the
  `k`-th graded piece.

## References

* [Stacks Project, Section 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 031K](https://stacks.math.columbia.edu/tag/031K)
* [Stacks Project, Tag 0FUM](https://stacks.math.columbia.edu/tag/0FUM)
-/

@[expose] public section

open scoped TensorProduct

namespace exteriorPower

variable {B : Type*} [CommRing B] {E : Type*} [AddCommGroup E] [Module B E]
  {H : Type*} [AddCommGroup H] [Module B H]

/-- Left multiplication by the image of `a ∈ ⋀ᵏ E` carries the first step of `⋀ᵐ H` into the
`(k+1)`-st step of `⋀ⁿ H`. -/
theorem wedgeLeftMul_mem_wedgeStep_succ (ι : E →ₗ[B] H) {k m n : ℕ} (h : k + m = n)
    (a : ⋀[B]^k E) {y : ⋀[B]^m H} (hy : y ∈ wedgeStep ι 1 m) :
    wedgeLeftMul ι h a y ∈ wedgeStep ι (k + 1) n := by
  suffices hle : wedgeStep ι 1 m ≤ (wedgeStep ι (k + 1) n).comap (wedgeLeftMul ι h a) from hle hy
  rw [wedgeStep_le_iff]
  intro j m' h' hj x y
  rw [Submodule.mem_comap]
  have he : wedgeLeftMul ι h a (wedgeLeftMul ι h' x y) =
      wedgeLeftMul ι (j := k + j) (m := m') (by omega)
        ⟨(a : ExteriorAlgebra B E) * x, mul_mem_of_mem rfl a.2 x.2⟩ y := by
    refine Subtype.ext ?_
    rw [coe_wedgeLeftMul, coe_wedgeLeftMul, coe_wedgeLeftMul, ← mul_assoc, ← map_mul]
  rw [he]
  exact wedgeLeftMul_mem_wedgeStep ι _ (by omega) _ y

variable (ι : E →ₗ[B] H)

/-- The `k`-th graded piece `F^k ⋀ⁿ H / F^{k+1}` of the wedge filtration. -/
abbrev wedgeGraded (k n : ℕ) : Type _ :=
  wedgeStep ι k n ⧸ (wedgeStep ι (k + 1) n).comap (wedgeStep ι k n).subtype

/-- `⋀ᵐ H / F^1`, the zeroth graded piece. -/
abbrev wedgeZeroGraded (m : ℕ) : Type _ := ⋀[B]^m H ⧸ wedgeStep ι 1 m

/-- Left multiplication by the image of `a ∈ ⋀ᵏ E`, read on the graded pieces. -/
noncomputable def gradedLeftMulAux {k m n : ℕ} (h : k + m = n) (a : ⋀[B]^k E) :
    wedgeZeroGraded ι m →ₗ[B] wedgeGraded ι k n :=
  (wedgeStep ι 1 m).liftQ
    (Submodule.mkQ _ ∘ₗ (wedgeLeftMul ι h a).codRestrict _
      (fun y => wedgeLeftMul_mem_wedgeStep ι h le_rfl a y))
    (fun _ hy => (Submodule.Quotient.mk_eq_zero _).2 (wedgeLeftMul_mem_wedgeStep_succ ι h a hy))

/-- `gradedLeftMulAux ι h a` sends the class of `y` to the class of `(⋀ ι) a ∧ y`. -/
@[simp]
theorem gradedLeftMulAux_mk {k m n : ℕ} (h : k + m = n) (a : ⋀[B]^k E) (y : ⋀[B]^m H) :
    gradedLeftMulAux ι h a (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ⟨wedgeLeftMul ι h a y, wedgeLeftMul_mem_wedgeStep ι h le_rfl a y⟩ :=
  rfl

/-- **Left multiplication on the graded pieces**, `⋀ᵏ E ⊗ (⋀ᵐ H / F^1) ⟶ F^k ⋀ⁿ H / F^{k+1}`,
`a ⊗ [η] ↦ [(⋀ ι) a ∧ η]`. -/
noncomputable def gradedLeftMul {k m n : ℕ} (h : k + m = n) :
    TensorProduct B (⋀[B]^k E) (wedgeZeroGraded ι m) →ₗ[B] wedgeGraded ι k n :=
  TensorProduct.lift
    { toFun := gradedLeftMulAux ι h
      map_add' := fun a a' => by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        simp only [LinearMap.comp_apply, LinearMap.add_apply, Submodule.mkQ_apply,
          gradedLeftMulAux_mk, ← Submodule.Quotient.mk_add]
        congr 1
        apply Subtype.ext
        apply Subtype.ext
        simp [add_mul]
      map_smul' := fun c a => by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.mkQ_apply,
          gradedLeftMulAux_mk, RingHom.id_apply, ← Submodule.Quotient.mk_smul]
        congr 1
        apply Subtype.ext
        apply Subtype.ext
        simp [Algebra.smul_mul_assoc] }

/-- `gradedLeftMul ι h` sends `a ⊗ [y]` to the class of `(⋀ ι) a ∧ y`. -/
@[simp]
theorem gradedLeftMul_tmul_mk {k m n : ℕ} (h : k + m = n) (a : ⋀[B]^k E) (y : ⋀[B]^m H) :
    gradedLeftMul ι h (a ⊗ₜ Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ⟨wedgeLeftMul ι h a y, wedgeLeftMul_mem_wedgeStep ι h le_rfl a y⟩ :=
  rfl

/-! ### The split case -/

section Split

variable {G : Type*} [AddCommGroup G] [Module B G]

/-- The second projection `⋀ᵐ (E × G) ⟶ ⋀ᵐ G` is a left inverse of `⋀ᵐ` of the second
inclusion `G ⟶ E × G`. -/
theorem sndPower_map_inr (m : ℕ) (b : ⋀[B]^m G) :
    sndPower B E G m (map m (LinearMap.inr B E G) b) = b := by
  rw [← LinearMap.comp_apply, ← map_comp, LinearMap.snd_comp_inr, map_id, LinearMap.id_apply]

/-- The second projection `⋀ᵐ (E × G) ⟶ ⋀ᵐ G` is surjective. -/
theorem sndPower_surjective (m : ℕ) : Function.Surjective (sndPower B E G m) :=
  fun b => ⟨_, sndPower_map_inr m b⟩

variable (B E G) in
/-- **The zeroth graded piece of `⋀ᵐ (E × G)` is `⋀ᵐ G`**, through the second projection. -/
noncomputable def zeroGradedProdEquiv (m : ℕ) :
    wedgeZeroGraded (LinearMap.inl B E G) m ≃ₗ[B] ⋀[B]^m G :=
  (Submodule.quotEquivOfEq _ _ (ker_sndPower m).symm).trans
    ((sndPower B E G m).quotKerEquivOfSurjective (sndPower_surjective m))

/-- `zeroGradedProdEquiv` sends the class of `y` to its image under the second projection. -/
@[simp]
theorem zeroGradedProdEquiv_mk (m : ℕ) (y : ⋀[B]^m (E × G)) :
    zeroGradedProdEquiv B E G m (Submodule.Quotient.mk y) = sndPower B E G m y :=
  rfl

/-- For the first inclusion `E ⟶ E × G`, the graded left multiplication is `prodGradedMap`
composed with `zeroGradedProdEquiv` on the second factor. -/
theorem gradedLeftMul_inl_eq {k m n : ℕ} (h : k + m = n) :
    gradedLeftMul (LinearMap.inl B E G) h =
      prodGradedMap B E G h ∘ₗ
        TensorProduct.map LinearMap.id (zeroGradedProdEquiv B E G m).toLinearMap := by
  refine TensorProduct.ext' fun a q => ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
  rw [Submodule.mkQ_apply, gradedLeftMul_tmul_mk, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearEquiv.coe_coe, zeroGradedProdEquiv_mk]
  refine (Submodule.Quotient.eq _).2 ?_
  rw [Submodule.mem_comap, map_sub]
  change wedgeLeftMul (LinearMap.inl B E G) h a y - prodBlock h (a ⊗ₜ sndPower B E G m y) ∈ _
  rw [prodBlock_tmul, ← map_sub]
  refine wedgeLeftMul_mem_wedgeStep_succ _ h a ?_
  rw [← ker_sndPower, LinearMap.mem_ker, map_sub, sndPower_map_inr, sub_self]

/-- **The graded left multiplication for the first inclusion `E ⟶ E × G` is bijective.** -/
theorem gradedLeftMul_inl_bijective {k m n : ℕ} (h : k + m = n) :
    Function.Bijective (gradedLeftMul (LinearMap.inl B E G) h) := by
  rw [gradedLeftMul_inl_eq]
  exact (prodGradedMap_bijective h).comp
    (TensorProduct.congr (LinearEquiv.refl B _) (zeroGradedProdEquiv B E G m)).bijective

end Split

/-! ### Transport along an isomorphism -/

section Transport

variable {H' : Type*} [AddCommGroup H'] [Module B H'] (ι' : E →ₗ[B] H') (e : H ≃ₗ[B] H')
  (he : e.toLinearMap ∘ₗ ι = ι')

/-- `⋀ⁿ e` for a linear isomorphism `e`, as a linear isomorphism. -/
noncomputable def powerEquiv (e : H ≃ₗ[B] H') (n : ℕ) : ⋀[B]^n H ≃ₗ[B] ⋀[B]^n H' :=
  LinearEquiv.ofLinearMap (map n e.toLinearMap) (map n e.symm.toLinearMap)
    (by rw [← map_comp]; simp [map_id]) (by rw [← map_comp]; simp [map_id])

/-- `powerEquiv e n` acts as `⋀ⁿ e`. -/
@[simp]
theorem powerEquiv_apply (n : ℕ) (y : ⋀[B]^n H) : powerEquiv e n y = map n e.toLinearMap y :=
  rfl

include he in
/-- If `e ∘ ι = ι'`, then `⋀ⁿ e` carries the `k`-th step for `ι` onto the `k`-th step for `ι'`. -/
theorem map_wedgeStep_powerEquiv (k n : ℕ) :
    (wedgeStep ι k n).map (powerEquiv e n).toLinearMap = wedgeStep ι' k n := by
  rw [wedgeStep_comap_map_of_comp_eq ι ι' e he k n]
  exact Submodule.map_comap_eq_of_surjective (powerEquiv e n).surjective _

/-- The isomorphism of zeroth graded pieces induced by `e`. -/
noncomputable def zeroGradedEquiv (m : ℕ) : wedgeZeroGraded ι m ≃ₗ[B] wedgeZeroGraded ι' m :=
  Submodule.Quotient.equiv _ _ (powerEquiv e m) (map_wedgeStep_powerEquiv ι ι' e he 1 m)

/-- The isomorphism of steps induced by `e`. -/
noncomputable def stepEquiv (k n : ℕ) : wedgeStep ι k n ≃ₗ[B] wedgeStep ι' k n :=
  ((powerEquiv e n).submoduleMap (wedgeStep ι k n)).trans
    (LinearEquiv.ofEq _ _ (map_wedgeStep_powerEquiv ι ι' e he k n))

/-- `stepEquiv` acts as `⋀ⁿ e` on the underlying elements of `⋀ⁿ H`. -/
@[simp]
theorem coe_stepEquiv_apply (k n : ℕ) (z : wedgeStep ι k n) :
    (stepEquiv ι ι' e he k n z : ⋀[B]^n H') = map n e.toLinearMap z :=
  rfl

/-- `stepEquiv` carries `F^{k+1}`, viewed inside `F^k`, for `ι` onto the same submodule for
`ι'`. -/
theorem map_stepEquiv_comap (k n : ℕ) :
    ((wedgeStep ι (k + 1) n).comap (wedgeStep ι k n).subtype).map
        (stepEquiv ι ι' e he k n).toLinearMap =
      (wedgeStep ι' (k + 1) n).comap (wedgeStep ι' k n).subtype := by
  ext z
  rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap,
    Submodule.subtype_apply, Submodule.subtype_apply,
    wedgeStep_comap_map_of_comp_eq ι ι' e he (k + 1) n, Submodule.mem_comap,
    ← coe_stepEquiv_apply ι ι' e he, LinearEquiv.apply_symm_apply]

/-- The isomorphism of `k`-th graded pieces induced by `e`. -/
noncomputable def gradedEquiv (k n : ℕ) : wedgeGraded ι k n ≃ₗ[B] wedgeGraded ι' k n :=
  Submodule.Quotient.equiv _ _ (stepEquiv ι ι' e he k n) (map_stepEquiv_comap ι ι' e he k n)

/-- The graded left multiplications for `ι` and `ι'` commute with the isomorphisms
`gradedEquiv` and `zeroGradedEquiv` induced by `e`. -/
theorem gradedEquiv_comp_gradedLeftMul {k m n : ℕ} (h : k + m = n) :
    (gradedEquiv ι ι' e he k n).toLinearMap ∘ₗ gradedLeftMul ι h =
      gradedLeftMul ι' h ∘ₗ
        TensorProduct.map LinearMap.id (zeroGradedEquiv ι ι' e he m).toLinearMap := by
  refine TensorProduct.ext' fun a q => ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
  rw [Submodule.mkQ_apply, LinearMap.comp_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
    gradedLeftMul_tmul_mk, LinearMap.id_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe]
  change Submodule.Quotient.mk (stepEquiv ι ι' e he k n _) =
    gradedLeftMul ι' h (a ⊗ₜ Submodule.Quotient.mk (powerEquiv e m y))
  rw [gradedLeftMul_tmul_mk]
  congr 1
  refine Subtype.ext ?_
  rw [coe_stepEquiv_apply, map_wedgeLeftMul, he]
  rfl

include e he in
/-- **Bijectivity of the graded left multiplication is carried along a linear isomorphism
compatible with the two maps.** -/
theorem gradedLeftMul_bijective_of_equiv {k m n : ℕ} (h : k + m = n)
    (h' : Function.Bijective (gradedLeftMul ι' h)) : Function.Bijective (gradedLeftMul ι h) := by
  have : Function.Bijective ((gradedEquiv ι ι' e he k n).toLinearMap ∘ₗ gradedLeftMul ι h) := by
    rw [gradedEquiv_comp_gradedLeftMul ι ι' e he h]
    exact h'.comp
      (TensorProduct.congr (LinearEquiv.refl B _) (zeroGradedEquiv ι ι' e he m)).bijective
  exact (Function.Bijective.of_comp_iff' (gradedEquiv ι ι' e he k n).bijective _).1 this

end Transport

end exteriorPower

namespace KaehlerDifferential

variable (R A B : Type*) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
  [Algebra R B] [IsScalarTower R A B] [Algebra.FormallySmooth A B]

/-- A `B`-linear retraction of `B ⊗_A Ω_{A/R} ⟶ Ω_{B/R}`, which exists since `A → B` is formally
smooth ([Stacks, Tag 031K]). -/
noncomputable def towerRetraction : Ω[B⁄R] →ₗ[B] B ⊗[A] Ω[A⁄R] :=
  Classical.choose (exists_retraction_mapBaseChange R A B)

/-- `towerRetraction` is a left inverse of `B ⊗_A Ω_{A/R} ⟶ Ω_{B/R}`. -/
theorem towerRetraction_comp_mapBaseChange :
    towerRetraction R A B ∘ₗ mapBaseChange R A B = LinearMap.id :=
  Classical.choose_spec (exists_retraction_mapBaseChange R A B)

/-- `towerRetraction` sends the image of `y ∈ B ⊗_A Ω_{A/R}` in `Ω_{B/R}` back to `y`. -/
theorem towerRetraction_mapBaseChange (y : B ⊗[A] Ω[A⁄R]) :
    towerRetraction R A B (mapBaseChange R A B y) = y :=
  LinearMap.congr_fun (towerRetraction_comp_mapBaseChange R A B) y

/-- **The splitting `Ω_{B/R} ≅ (B ⊗_A Ω_{A/R}) × Ω_{B/A}`** of the sequence of a tower with
`A → B` formally smooth: a retraction of the first map and the second map. -/
@[ega "0 20.7.2" "special case"]
noncomputable def towerSplitEquiv : Ω[B⁄R] ≃ₗ[B] (B ⊗[A] Ω[A⁄R]) × Ω[B⁄A] :=
  LinearEquiv.ofBijective ((towerRetraction R A B).prod (map R A B B)) <| by
    have hex := exact_mapBaseChange_map R A B
    constructor
    · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
      have h1 : towerRetraction R A B x = 0 := congrArg Prod.fst hx
      obtain ⟨y, rfl⟩ := (hex x).1 (congrArg Prod.snd hx)
      rw [towerRetraction_mapBaseChange] at h1
      rw [h1, map_zero]
    · rintro ⟨u, v⟩
      obtain ⟨x₀, hx₀⟩ := map_surjective R A B v
      refine ⟨x₀ + mapBaseChange R A B (u - towerRetraction R A B x₀), Prod.ext ?_ ?_⟩
      · simp [towerRetraction_mapBaseChange]
      · simp [hx₀, hex.apply_apply_eq_zero]

/-- Under `towerSplitEquiv`, the map `B ⊗_A Ω_{A/R} ⟶ Ω_{B/R}` becomes the first inclusion. -/
theorem towerSplitEquiv_comp_mapBaseChange :
    (towerSplitEquiv R A B).toLinearMap ∘ₗ mapBaseChange R A B = LinearMap.inl B _ _ :=
  LinearMap.ext fun y => Prod.ext (towerRetraction_mapBaseChange R A B y)
    ((exact_mapBaseChange_map R A B).apply_apply_eq_zero y)

/-- Under `towerSplitEquiv`, the map `Ω_{B/R} ⟶ Ω_{B/A}` becomes the second projection. -/
theorem snd_comp_towerSplitEquiv :
    LinearMap.snd B _ _ ∘ₗ (towerSplitEquiv R A B).toLinearMap = map R A B B :=
  rfl

/-- **The kernel of `⋀ⁿ Ω_{B/R} ⟶ ⋀ⁿ Ω_{B/A}` is the first step of the filtration by the forms
pulled back from `A`**, for `A → B` formally smooth. -/
theorem ker_map_exteriorPower_eq_wedgeStep_one (n : ℕ) :
    LinearMap.ker (exteriorPower.map n (map R A B B)) =
      exteriorPower.wedgeStep (mapBaseChange R A B) 1 n := by
  rw [← snd_comp_towerSplitEquiv, exteriorPower.map_comp, LinearMap.ker_comp,
    exteriorPower.ker_sndPower,
    exteriorPower.wedgeStep_comap_map_of_comp_eq _ _ _ (towerSplitEquiv_comp_mapBaseChange R A B)]

/-- **`⋀ⁿ Ω_{B/R} / F^1 ≅ ⋀ⁿ Ω_{B/A}`** for `A → B` formally smooth. -/
noncomputable def wedgeZeroGradedEquiv (n : ℕ) :
    exteriorPower.wedgeZeroGraded (mapBaseChange R A B) n ≃ₗ[B] ⋀[B]^n Ω[B⁄A] :=
  (Submodule.quotEquivOfEq _ _ (ker_map_exteriorPower_eq_wedgeStep_one R A B n).symm).trans
    ((exteriorPower.map n (map R A B B)).quotKerEquivOfSurjective
      (exteriorPower.map_surjective (map_surjective R A B)))

/-- `wedgeZeroGradedEquiv` sends the class of `y` to its image under
`⋀ⁿ Ω_{B/R} ⟶ ⋀ⁿ Ω_{B/A}`. -/
@[simp]
theorem wedgeZeroGradedEquiv_mk (n : ℕ) (y : ⋀[B]^n Ω[B⁄R]) :
    wedgeZeroGradedEquiv R A B n (Submodule.Quotient.mk y) = exteriorPower.map n (map R A B B) y :=
  rfl

/-- **The graded pieces of the filtration of `⋀^• Ω_{B/R}` by the forms pulled back from `A`**:
for `A → B` formally smooth and `k + m = n`, left multiplication induces an isomorphism
`⋀ᵏ(B ⊗_A Ω_{A/R}) ⊗_B (⋀ᵐ Ω_{B/R} / F^1) ≅ F^k ⋀ⁿ Ω_{B/R} / F^{k+1}`. -/
theorem gradedLeftMul_bijective {k m n : ℕ} (h : k + m = n) :
    Function.Bijective (exteriorPower.gradedLeftMul (mapBaseChange R A B) h) :=
  exteriorPower.gradedLeftMul_bijective_of_equiv (mapBaseChange R A B)
    (LinearMap.inl B (B ⊗[A] Ω[A⁄R]) Ω[B⁄A]) (towerSplitEquiv R A B)
    (towerSplitEquiv_comp_mapBaseChange R A B) h
    (exteriorPower.gradedLeftMul_inl_bijective (B := B) (E := B ⊗[A] Ω[A⁄R]) (G := Ω[B⁄A]) h)

end KaehlerDifferential

end
