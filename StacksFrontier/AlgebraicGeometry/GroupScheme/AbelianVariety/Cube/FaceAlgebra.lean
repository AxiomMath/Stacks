module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.ChainMap
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# The theorem of the cube: face cochains as a base change

Let `A` be a scheme over a field `k`, `U` a finite affine open cover of `A` whose finite
intersections are affine, and `V ⊆ A` an affine open with ring `R`. Functions on `U_j × V ⊆ A × A`
are the base change to `R` of functions on `U_j`, through pullback along the first projection
(`Stacks.Cube.isBaseChange_faceψ`). Consequently the face cochains are flat over `R`
(`Stacks.Cube.flat_faceCochain`), and the kernel of the face differential stays finite after any
base change, because the degree-zero cocycles of `A` are the constants
(`Stacks.Cube.finite_ker_targetD_baseChange`).

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.Cube

open Stacks.KunnethCech

/-! ### A finiteness lemma for kernels -/

section Algebra

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S]
  {M₀ M₁ N₀ N₁ : Type u} [AddCommGroup M₀] [AddCommGroup M₁] [Module k M₀] [Module k M₁]
  [AddCommGroup N₀] [AddCommGroup N₁] [Module k N₀] [Module k N₁] [Module S N₀] [Module S N₁]
  [IsScalarTower k S N₀] [IsScalarTower k S N₁]

/-- **The kernel of a base change of a map with finite-dimensional kernel is finite.** -/
theorem finite_ker_of_isBaseChange {α : M₀ →ₗ[k] N₀} {β : M₁ →ₗ[k] N₁}
    (hα : IsBaseChange S α) (hβ : IsBaseChange S β) (g : M₀ →ₗ[k] M₁) (H : N₀ →ₗ[S] N₁)
    (hH : (H.restrictScalars k) ∘ₗ α = β ∘ₗ g) [Module.Finite k (LinearMap.ker g)] :
    Module.Finite S (LinearMap.ker H) := by
  have hcomm : H ∘ₗ hα.equiv.toLinearMap = hβ.equiv.toLinearMap ∘ₗ g.baseChange S := by
    refine TensorProduct.AlgebraTensorModule.ext fun s m => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, map_smul]
    congr 1
    exact LinearMap.congr_fun hH m
  have hker : LinearMap.ker (g.baseChange S) =
      LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor S S
        (LinearMap.ker g).subtype) :=
    Module.Flat.ker_lTensor_eq (R := k) (S := S) (M := S) g
  have hfin : Module.Finite S (LinearMap.ker (g.baseChange S)) := by
    rw [hker]
    exact Module.Finite.range _
  have he : LinearMap.ker H =
      (LinearMap.ker (g.baseChange S)).map hα.equiv.toLinearMap := by
    rw [← LinearMap.ker_comp_of_ker_eq_bot (g.baseChange S) hβ.equiv.ker, ← hcomm,
      LinearMap.ker_comp, Submodule.map_comap_eq_of_surjective hα.equiv.surjective]
  rw [he]
  exact Module.Finite.map _ _

end Algebra

/-! ### Faces as a base change -/

section Face

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} {V : A.left.Opens}
  {ι : Type u} (U : ι → A.left.Opens)

attribute [local instance] faceModule

/-- The `k`-algebra structure on the ring of the chart. -/
@[instance_reducible]
noncomputable def chartAlgebra (V : A.left.Opens) : Algebra k (chartRing V) :=
  Stacks.AffineProduct.sectionsAlgebra A.hom V

attribute [local instance] chartAlgebra

/-- The `k`-module structure on functions on `A`. -/
@[instance_reducible]
noncomputable def secAlg (O : A.left.Opens) : Algebra k Γ(A.left, O) :=
  Stacks.AffineProduct.sectionsAlgebra A.hom O

/-- The `k`-module structure on functions on `A × A`. -/
@[instance_reducible]
noncomputable def secAlgB (O : (B A).Opens) : Algebra k Γ(B A, O) :=
  Stacks.AffineProduct.sectionsAlgebra (bx A ≫ A.hom) O

attribute [local instance] secAlg secAlgB

/-- The face action sends the image of `c : k` in the ring of the chart to the image of `c` in
functions on the face open. -/
theorem algebraMap_faceAct {n : ℕ} (j : Fin n → ι) (c : k) :
    faceAct V U j (algebraMap k (chartRing V) c) = algebraMap k Γ(B A, faceOpen V U j) c := by
  show ((bz A).appLE V _ _).hom ((Stacks.Cech.baseRingHom A.hom V).hom c) =
    (Stacks.Cech.baseRingHom (bx A ≫ A.hom) _).hom c
  have h := Stacks.AffineProduct.baseRingHom_comp_appLE A.hom (bz A) V (faceOpen V U j)
    (Stacks.AffineProduct.prodOpen_le_snd (bx A) (bz A) _ _)
  rw [← (isPullback_B A).w] at h
  exact congr($(h).hom c)

/-- Functions on a face open, as a module over the ring of the chart through `faceAct`, form a
scalar tower over `k`. -/
instance isScalarTower_face {n : ℕ} (j : Fin n → ι) :
    letI := Module.compHom Γ(B A, faceOpen V U j) (faceAct V U j)
    IsScalarTower k (chartRing V) Γ(B A, faceOpen V U j) :=
  letI := Module.compHom Γ(B A, faceOpen V U j) (faceAct V U j)
  IsScalarTower.of_algebraMap_smul fun c x => by
    change faceAct V U j (algebraMap k (chartRing V) c) * x = algebraMap k _ c * x
    rw [algebraMap_faceAct]

/-- Face cochains form a scalar tower over `k` and the ring of the chart. -/
instance isScalarTower_faceCochain (p : ℕ) : IsScalarTower k (chartRing V) (FaceCochain V U p) :=
  letI := fun (j : Fin (p + 1) → ι) => Module.compHom Γ(B A, faceOpen V U j) (faceAct V U j)
  inferInstanceAs (IsScalarTower k (chartRing V)
    (∀ j : Fin (p + 1) → ι, Γ(B A, faceOpen V U j)))

/-- Pulling functions back along the first projection. -/
noncomputable def faceψj {n : ℕ} (j : Fin n → ι) :
    Γ(A.left, CechCochains.inter U j) →ₗ[k] Γ(B A, faceOpen V U j) where
  toFun f := (bx A).appLE _ _ (Stacks.AffineProduct.prodOpen_le_fst (bx A) (bz A) _ _) f
  map_add' := map_add _
  map_smul' c f := by
    simp only [Algebra.smul_def, map_mul, RingHom.id_apply]
    congr 1
    exact appLE_algebraMap A.hom (bx A ≫ A.hom) (bx A) rfl _ c

variable (V) in
/-- Pulling cochains back along the first projection. -/
noncomputable def faceψ (p : ℕ) :
    letI := cochainModule U A.hom p
    RawCochain U p →ₗ[k] FaceCochain V U p :=
  letI := cochainModule U A.hom p
  LinearMap.pi fun j => (faceψj U j).comp (LinearMap.proj j)

/-- The component of `faceψ V U p f` at `j` is the pullback of `f j` along the first projection. -/
theorem faceψ_apply (p : ℕ) (f : RawCochain U p) (j : Fin (p + 1) → ι) :
    letI := cochainModule U A.hom p
    faceψ V U p f j = (bx A).appLE _ _ (Stacks.AffineProduct.prodOpen_le_fst (bx A) (bz A) _ _)
      (f j) := rfl

variable (hV : IsAffineOpen V)
  (hU : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (CechCochains.inter U i))
include hV hU

/-- Functions on `U_j × V` are the base change to the ring of the chart of functions on `U_j`,
through `faceψj`. -/
theorem isBaseChange_faceψj {n : ℕ} (j : Fin (n + 1) → ι) :
    letI := Module.compHom Γ(B A, faceOpen V U j) (faceAct V U j)
    IsBaseChange (chartRing V) (faceψj U j (V := V)) := by
  let := Stacks.AffineProduct.sectionsAlgebra A.hom (CechCochains.inter U j)
  let := Stacks.AffineProduct.sectionsAlgebra A.hom V
  let := Stacks.AffineProduct.sectionsAlgebra (bx A ≫ A.hom) (faceOpen V U j)
  let := Stacks.AffineProduct.fstAlgebra (bx A) (bz A) (CechCochains.inter U j) V
  let := Stacks.AffineProduct.sndAlgebra (bx A) (bz A) (CechCochains.inter U j) V
  have := Stacks.AffineProduct.isScalarTower_fst (f := A.hom) (bx A) (bz A)
    (CechCochains.inter U j) V
  have := Stacks.AffineProduct.isScalarTower_snd (bx A) (bz A) (isPullback_B A)
    (CechCochains.inter U j) V
  exact (Stacks.AffineProduct.algebraIsPushout (isPullback_B A) (hU n j) hV).symm.out

/-- Face cochains are the base change to the ring of the chart of the cochains of `U`, through
`faceψ`. -/
theorem isBaseChange_faceψ [Finite ι] (p : ℕ) :
    letI := cochainModule U A.hom p
    IsBaseChange (chartRing V) (faceψ V U p) := by
  let := cochainModule U A.hom p
  let := fun (j : Fin (p + 1) → ι) => Module.compHom Γ(B A, faceOpen V U j) (faceAct V U j)
  exact Stacks.Cech.isBaseChange_pi (A := k) (A' := chartRing V) (ι := Fin (p + 1) → ι)
    (fun j => Γ(A.left, CechCochains.inter U j)) (fun j => Γ(B A, faceOpen V U j))
    (fun j => faceψj U j) (fun j => isBaseChange_faceψj U hV hU j)

/-- **Face cochains are flat over the ring of the chart.** -/
theorem flat_faceCochain [Finite ι] (p : ℕ) : Module.Flat (chartRing V) (FaceCochain V U p) := by
  let := cochainModule U A.hom p
  exact Module.Flat.isBaseChange (R := k) (S := chartRing V) (M := RawCochain U p) _
    (isBaseChange_faceψ U hV hU p)

end Face

/-! ### The kernel of the face differential -/

section Kernel

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} {V : A.left.Opens}
  {ι : Type u} (U : ι → A.left.Opens)

attribute [local instance] faceModule chartAlgebra secAlg secAlgB

/-- Pulling back along the first projection commutes with the differentials: `faceD` after `faceψ`
equals `faceψ` after `rawD`. -/
theorem faceD_faceψ (p : ℕ) (f : RawCochain U p) :
    letI := cochainModule U A.hom p
    faceD V U p (faceψ V U p f) = faceψ V U (p + 1) (rawD U p f) := by
  funext j
  rw [faceD_apply, faceψ_apply, rawD, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_zsmul, faceψ_apply, res_appLE, appLE_res]

/-- The first component of `TensorProduct.prodRight` is the base change of `LinearMap.fst`. -/
theorem prodRight_fst {R S M₁ M₂ : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂] (z : S ⊗[R] (M₁ × M₂)) :
    (TensorProduct.prodRight R S S M₁ M₂ z).1 = (LinearMap.fst R M₁ M₂).baseChange S z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => simp
  | add x y hx hy => simp only [map_add, Prod.fst_add, hx, hy]

/-- The second component of `TensorProduct.prodRight` is the base change of `LinearMap.snd`. -/
theorem prodRight_snd {R S M₁ M₂ : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂] (z : S ⊗[R] (M₁ × M₂)) :
    (TensorProduct.prodRight R S S M₁ M₂ z).2 = (LinearMap.snd R M₁ M₂).baseChange S z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => simp
  | add x y hx hy => simp only [map_add, Prod.snd_add, hx, hy]

/-- Finiteness of the kernel of a base change of a map whose two first components factor through
a map with finite kernel. -/
theorem finite_ker_baseChange_of_comp {R S M N Q : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing S] [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q] [Module R M]
    [Module R N] [Module R Q] (T : M × M →ₗ[R] N × (N × Q)) (f : M →ₗ[R] N)
    (h1 : LinearMap.fst R N (N × Q) ∘ₗ T = f ∘ₗ LinearMap.fst R M M)
    (h2 : LinearMap.fst R N Q ∘ₗ LinearMap.snd R N (N × Q) ∘ₗ T = f ∘ₗ LinearMap.snd R M M)
    (hf : Module.Finite S (LinearMap.ker (f.baseChange S))) :
    Module.Finite S (LinearMap.ker (T.baseChange S)) := by
  let e := TensorProduct.prodRight R S S M M
  let K := LinearMap.ker (f.baseChange S)
  have key : ∀ (P : N × (N × Q) →ₗ[R] N) (π : M × M →ₗ[R] M), P ∘ₗ T = f ∘ₗ π →
      ∀ x : LinearMap.ker (T.baseChange S), f.baseChange S (π.baseChange S x) = 0 := by
    intro P π h x
    have hx : T.baseChange S x = 0 := x.2
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← h, LinearMap.baseChange_comp,
      LinearMap.comp_apply, hx, map_zero]
  have hmem : ∀ x : LinearMap.ker (T.baseChange S), (e x).1 ∈ K ∧ (e x).2 ∈ K := fun x => by
    refine ⟨?_, ?_⟩
    · rw [prodRight_fst]
      exact key _ _ h1 x
    · rw [prodRight_snd]
      exact key (LinearMap.fst R N Q ∘ₗ LinearMap.snd R N (N × Q)) _ h2 x
  let φ : LinearMap.ker (T.baseChange S) →ₗ[S] K × K :=
    { toFun := fun x => (⟨(e x).1, (hmem x).1⟩, ⟨(e x).2, (hmem x).2⟩)
      map_add' := fun x y => by ext <;> simp
      map_smul' := fun c x => by ext <;> simp }
  refine Module.Finite.of_injective φ fun x y hxy => ?_
  exact Subtype.ext (e.injective (Prod.ext (congrArg (fun z => (z.1 : S ⊗[R] M)) hxy)
    (congrArg (fun z => (z.2 : S ⊗[R] M)) hxy)))

variable [Finite ι] (hV : IsAffineOpen V)
  (hU : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (CechCochains.inter U i))
  (hUcov : (⊤ : A.left.Opens) = ⨆ a, U a)
  (hAc : Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop))
include hV hU hUcov hAc

/-- **The kernel of the face differential stays finite after base change.** -/
theorem finite_ker_faceD_baseChange (S : Type u) [CommRing S] [Algebra (chartRing V) S] :
    Module.Finite S (LinearMap.ker ((faceD V U 0).baseChange S)) := by
  let : Algebra k S := ((algebraMap (chartRing V) S).comp (algebraMap k (chartRing V))).toAlgebra
  have : IsScalarTower k (chartRing V) S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := cochainModule U A.hom 0
  let := cochainModule U A.hom 1
  have hα := (isBaseChange_faceψ U hV hU 0).comp (TensorProduct.isBaseChange (chartRing V)
    (FaceCochain V U 0) S)
  have hβ := (isBaseChange_faceψ U hV hU 1).comp (TensorProduct.isBaseChange (chartRing V)
    (FaceCochain V U 1) S)
  have : Module.Finite k (LinearMap.ker (rawDₗ U A.hom 0)) := by
    have hle : LinearMap.ker (rawDₗ U A.hom 0) ≤ Submodule.span k {one U} := by
      intro s hs
      obtain ⟨c, hc⟩ := exists_eq_smul_one_of_rawD_eq_zero A.hom U hUcov hAc s hs
      rw [hc]
      exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
    exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  refine finite_ker_of_isBaseChange hα hβ (rawDₗ U A.hom 0) ((faceD V U 0).baseChange S) ?_
  refine LinearMap.ext fun f => ?_
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    TensorProduct.mk_apply, LinearMap.baseChange_tmul]
  congr 1
  exact faceD_faceψ U 0 f

/-- **The kernel of the target differential stays finite after a Noetherian base change.** -/
theorem finite_ker_targetD_baseChange [GrpObj A] {a₀ : ι} (ha₀ : eA (A := A) ⁻¹ᵁ U a₀ = ⊤)
    (S : Type u) [CommRing S] [Algebra (chartRing V) S] [IsNoetherianRing S] :
    Module.Finite S (LinearMap.ker ((targetD V U ha₀).baseChange S)) :=
  finite_ker_baseChange_of_comp (targetD V U ha₀) (faceD V U 0) rfl rfl
    (finite_ker_faceD_baseChange U hV hU hUcov hAc S)

end Kernel

end Stacks.Cube

end
