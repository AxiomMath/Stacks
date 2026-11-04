module

public import StacksFrontier.RingTheory.Descent.AmitsurComplex
public import StacksFrontier.RingTheory.Descent.FaithfullyFlatModules

/-!
# One-cocycles of a descent situation presented by comparison maps

Let `A → B` be a faithfully flat ring map and let `K` be a `B`-module. In geometry the two
pullbacks of `K` to `Spec B ×_{Spec A} Spec B` and its three pullbacks to the triple fibre product
are rarely given as tensor products: they are modules `L` over a ring `C` and `P` over a ring `D`
standing for the rings of functions on those fibre products, together with the pullback maps
`α₁ α₂ : K → L` along the two projections, `γ₁₂ γ₁₃ γ₂₃ : L → P` along the three partial
projections and `Δ : L → K` along the diagonal. This file proves that the Čech complex
`K → L → P`, with differentials `α₁ - α₂` and `γ₁₂ - γ₁₃ + γ₂₃`, is exact in the middle, as soon
as the two comparison maps

* `B ⊗[A] K → L`, `b ⊗ k ↦ i₁ b • α₂ k`, is bijective, and
* `B ⊗[A] (B ⊗[A] K) → P`, `b ⊗ y ↦ f₁₂ (i₁ b) • γ₂₃ (θ y)`, is injective, `θ` being the first,

which is how flat base change and the tensor product description of the rings of a fibre product
of affine schemes enter in geometry. Such a complex is the Čech complex of a quasi-coherent module
on an affine scheme for a faithfully flat covering, and the statement is the vanishing of its
first Čech cohomology.

## Main definitions

* `Module.Descent.cmpLeft`: the comparison map `B ⊗[A] K → L`.
* `Module.Descent.cmpRight`: the comparison map `B ⊗[A] (B ⊗[A] K) → P`.

## Main results

* `Module.Descent.exists_sub_eq_of_cocycle`: every one-cocycle `ξ ∈ L`, that is every `ξ` with
  `γ₁₂ ξ - γ₁₃ ξ + γ₂₃ ξ = 0`, is a coboundary `α₁ k - α₂ k`.

## Implementation notes

The proof is descent followed by the Amitsur complex. The first comparison map transports `α₁`
to a coaction `K → B ⊗[A] K`; it is counital because of the diagonal, and coassociative because
after the injective second comparison map both sides of the coassociativity equation become the
pullback of `α₁` along `γ₁₂ = γ₁₃` on the image of `α₁`. So `K` carries a descent datum
`Module.Descent.Datum`, which is effective by `Module.Descent.Datum.equivBaseChange`: `K` is
`B ⊗[A] M` for the module `M` of invariants. Under these identifications the cocycle condition is
the vanishing of the degree-one Amitsur differential `Module.Descent.amitsurDiff₁`, and
`Module.Descent.exists_amitsurDiff₀_eq` produces the primitive.

Only three relations between the ring maps are used: `μ ∘ i₁ = id` for the diagonal, and
`f₁₂ ∘ i₁ = f₁₃ ∘ i₁`, `f₁₂ ∘ i₂ = f₂₃ ∘ i₁` for the three partial projections. The modules `L`
and `P` carry no `A`-module structure: the comparison maps are additive maps out of tensor
products, built with `TensorProduct.liftAddHom`.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
-/

@[expose] public section

open TensorProduct

namespace Module.Descent

variable {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D] [Algebra A B]
  {K L P : Type*} [AddCommGroup K] [Module A K] [Module B K] [IsScalarTower A B K]
  [AddCommGroup L] [Module C L] [AddCommGroup P] [Module D P]

section Comparison

/-- The comparison map `B ⊗[A] K → L`, `b ⊗ k ↦ i₁ b • α₂ k`. When `L` is the module of the
pullback of `K` to a fibre product `Spec C = Spec B ×_{Spec A} Spec B`, `α₂` being pullback along
the second projection, this is the base change map whose bijectivity is flat base change. -/
noncomputable def cmpLeft (i₁ i₂ : B →+* C)
    (hA : ∀ a : A, i₁ (algebraMap A B a) = i₂ (algebraMap A B a))
    (α₂ : K →+ L) (hα₂ : ∀ (b : B) (k : K), α₂ (b • k) = i₂ b • α₂ k) : B ⊗[A] K →+ L :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun k => i₁ b • α₂ k)
        (fun k k' => by rw [map_add, smul_add]))
      (fun b b' => by ext k; simp [add_smul]))
    (fun a b k => by
      simp only [AddMonoidHom.mk'_apply]
      rw [Algebra.smul_def, map_mul, hA, ← algebraMap_smul B a k, hα₂, smul_smul,
        mul_comm (i₁ b)])

variable (i₁ i₂ : B →+* C) (hA : ∀ a : A, i₁ (algebraMap A B a) = i₂ (algebraMap A B a))
  (α₂ : K →+ L) (hα₂ : ∀ (b : B) (k : K), α₂ (b • k) = i₂ b • α₂ k)

/-- The comparison map `Module.Descent.cmpLeft` sends `b ⊗ k` to `i₁ b • α₂ k`. -/
@[simp]
lemma cmpLeft_tmul (b : B) (k : K) : cmpLeft i₁ i₂ hA α₂ hα₂ (b ⊗ₜ k) = i₁ b • α₂ k := rfl

/-- The comparison map `Module.Descent.cmpLeft` is semilinear along `i₁`. -/
lemma cmpLeft_smul (b : B) (x : B ⊗[A] K) :
    cmpLeft i₁ i₂ hA α₂ hα₂ (b • x) = i₁ b • cmpLeft i₁ i₂ hA α₂ hα₂ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c k =>
    rw [TensorProduct.smul_tmul', cmpLeft_tmul, cmpLeft_tmul, smul_eq_mul, map_mul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The comparison map `B ⊗[A] (B ⊗[A] K) → P`, `b ⊗ y ↦ f₁₂ (i₁ b) • γ₂₃ (θ y)`, where `θ` is
`Module.Descent.cmpLeft`. On a pure tensor `b ⊗ (c ⊗ k)` it is the product of the pullbacks of
`b`, `c` along the first two projections of a triple fibre product with the pullback of `k` along
the third. -/
noncomputable def cmpRight (f₁₂ f₂₃ : C →+* D) (h₁₂₂₃ : ∀ b, f₁₂ (i₂ b) = f₂₃ (i₁ b))
    (γ₂₃ : L →+ P) (hγ₂₃ : ∀ (c : C) (l : L), γ₂₃ (c • l) = f₂₃ c • γ₂₃ l) :
    B ⊗[A] (B ⊗[A] K) →+ P :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk'
        (fun y => f₁₂ (i₁ b) • γ₂₃ (cmpLeft i₁ i₂ hA α₂ hα₂ y))
        (fun y y' => by rw [map_add, map_add, smul_add]))
      (fun b b' => by ext y; simp [add_smul]))
    (fun a b y => by
      simp only [AddMonoidHom.mk'_apply]
      rw [← algebraMap_smul B a y, cmpLeft_smul, hγ₂₃, Algebra.smul_def, map_mul, map_mul,
        smul_smul, ← h₁₂₂₃, hA, mul_comm (f₁₂ (i₁ b))])

/-- The comparison map `Module.Descent.cmpRight` sends `b ⊗ y` to
`f₁₂ (i₁ b) • γ₂₃ (cmpLeft i₁ i₂ hA α₂ hα₂ y)`. -/
@[simp]
lemma cmpRight_tmul (f₁₂ f₂₃ : C →+* D) (h₁₂₂₃ : ∀ b, f₁₂ (i₂ b) = f₂₃ (i₁ b))
    (γ₂₃ : L →+ P) (hγ₂₃ : ∀ (c : C) (l : L), γ₂₃ (c • l) = f₂₃ c • γ₂₃ l) (b : B) (y : B ⊗[A] K) :
    cmpRight i₁ i₂ hA α₂ hα₂ f₁₂ f₂₃ h₁₂₂₃ γ₂₃ hγ₂₃ (b ⊗ₜ y) =
      f₁₂ (i₁ b) • γ₂₃ (cmpLeft i₁ i₂ hA α₂ hα₂ y) := rfl

end Comparison

/-- **Vanishing of the first Čech cohomology of a descent situation presented by comparison
maps.** Let `A → B` be faithfully flat, `K` a `B`-module, and let `L`, `P` be modules over rings
`C`, `D` receiving the pullbacks of `K` along the two projections `i₁ i₂ : B → C` and along the
three partial projections `f₁₂ f₁₃ f₂₃ : C → D`, with a diagonal `μ : C → B`. If the comparison
map `B ⊗[A] K → L` is bijective and the comparison map `B ⊗[A] (B ⊗[A] K) → P` is injective, then
every `ξ ∈ L` with `γ₁₂ ξ - γ₁₃ ξ + γ₂₃ ξ = 0` is of the form `α₁ k - α₂ k`. -/
theorem exists_sub_eq_of_cocycle [Module.FaithfullyFlat A B]
    (i₁ i₂ : B →+* C) (μ : C →+* B) (f₁₂ f₁₃ f₂₃ : C →+* D)
    (hA : ∀ a : A, i₁ (algebraMap A B a) = i₂ (algebraMap A B a))
    (hμ : ∀ b, μ (i₁ b) = b)
    (h₁₂₁₃ : ∀ b, f₁₂ (i₁ b) = f₁₃ (i₁ b)) (h₁₂₂₃ : ∀ b, f₁₂ (i₂ b) = f₂₃ (i₁ b))
    (α₁ α₂ : K →+ L) (hα₁ : ∀ (b : B) (k : K), α₁ (b • k) = i₁ b • α₁ k)
    (hα₂ : ∀ (b : B) (k : K), α₂ (b • k) = i₂ b • α₂ k)
    (Δ : L →+ K) (hΔ : ∀ (c : C) (l : L), Δ (c • l) = μ c • Δ l)
    (hΔ₁ : ∀ k, Δ (α₁ k) = k) (hΔ₂ : ∀ k, Δ (α₂ k) = k)
    (γ₁₂ γ₁₃ γ₂₃ : L →+ P) (hγ₁₂ : ∀ (c : C) (l : L), γ₁₂ (c • l) = f₁₂ c • γ₁₂ l)
    (hγ₁₃ : ∀ (c : C) (l : L), γ₁₃ (c • l) = f₁₃ c • γ₁₃ l)
    (hγ₂₃ : ∀ (c : C) (l : L), γ₂₃ (c • l) = f₂₃ c • γ₂₃ l)
    (hγα₁ : ∀ k, γ₁₂ (α₁ k) = γ₁₃ (α₁ k)) (hγα₂ : ∀ k, γ₁₂ (α₂ k) = γ₂₃ (α₁ k))
    (hγα₃ : ∀ k, γ₁₃ (α₂ k) = γ₂₃ (α₂ k))
    (hL : Function.Bijective (cmpLeft i₁ i₂ hA α₂ hα₂))
    (hP : Function.Injective (cmpRight i₁ i₂ hA α₂ hα₂ f₁₂ f₂₃ h₁₂₂₃ γ₂₃ hγ₂₃))
    (ξ : L) (hξ : γ₁₂ ξ - γ₁₃ ξ + γ₂₃ ξ = 0) :
    ∃ k : K, α₁ k - α₂ k = ξ := by
  classical
  set θ := cmpLeft i₁ i₂ hA α₂ hα₂
  set ρ := cmpRight i₁ i₂ hA α₂ hα₂ f₁₂ f₂₃ h₁₂₂₃ γ₂₃ hγ₂₃
  let eθ : B ⊗[A] K ≃ L := Equiv.ofBijective θ hL
  have heθ : ∀ l, θ (eθ.symm l) = l := fun l => Equiv.ofBijective_apply_symm_apply θ hL l
  -- The coaction transported from `α₁`.
  let co : K →ₗ[B] B ⊗[A] K :=
    { toFun := fun k => eθ.symm (α₁ k)
      map_add' := fun k k' => hL.1 (by simp only [map_add, heθ])
      map_smul' := fun b k => hL.1 (by
        rw [RingHom.id_apply, heθ, cmpLeft_smul, heθ, hα₁]) }
  have hco : ∀ k, θ (co k) = α₁ k := fun k => heθ (α₁ k)
  have hcounit : ∀ x : B ⊗[A] K, counit A B K x = Δ (θ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b k => rw [counit_tmul, cmpLeft_tmul, hΔ, hμ, hΔ₂]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have hρco : ∀ x : B ⊗[A] K,
      ρ (AlgebraTensorModule.lTensor B B (co.restrictScalars A) x) = γ₁₂ (θ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b k =>
      rw [AlgebraTensorModule.lTensor_tmul, LinearMap.restrictScalars_apply, cmpRight_tmul, hco,
        cmpLeft_tmul, hγ₁₂, hγα₂]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hρmk : ∀ x : B ⊗[A] K,
      ρ (AlgebraTensorModule.lTensor B B (TensorProduct.mk A B K 1) x) = γ₁₃ (θ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b k =>
      rw [AlgebraTensorModule.lTensor_tmul, TensorProduct.mk_apply, cmpRight_tmul, cmpLeft_tmul,
        map_one, one_smul, cmpLeft_tmul, hγ₁₃, h₁₂₁₃, hγα₃]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hρone : ∀ x : B ⊗[A] K, ρ ((1 : B) ⊗ₜ x) = γ₂₃ (θ x) := by
    intro x
    rw [cmpRight_tmul, map_one, map_one, one_smul]
  let d : Datum A B K :=
    { coaction := co
      counit_coaction := fun k => by rw [hcounit, hco, hΔ₁]
      coassoc := fun k => hP (by rw [hρco, hρmk, hco, hγα₁]) }
  have hdes : ∀ m : d.descended, co (m : K) = (1 : B) ⊗ₜ (m : K) :=
    fun m => (d.mem_descended_iff).1 m.2
  -- Effectivity: `K = B ⊗[A] M` for the invariants `M`.
  let e : B ⊗[A] d.descended ≃ₗ[B] K := d.equivBaseChange
  have he : ∀ (b : B) (m : d.descended), e (b ⊗ₜ m) = b • (m : K) :=
    fun b m => d.equivBaseChange_tmul b m
  let E₁ : B ⊗[A] (B ⊗[A] d.descended) ≃ₗ[A] B ⊗[A] K := (e.restrictScalars A).lTensor B
  let E₂ : B ⊗[A] (B ⊗[A] (B ⊗[A] d.descended)) ≃ₗ[A] B ⊗[A] (B ⊗[A] K) := E₁.lTensor B
  have hE₁ : ∀ (s : B) (z : B ⊗[A] d.descended), E₁ (s ⊗ₜ z) = s ⊗ₜ e z := fun _ _ => rfl
  have hE₂ : ∀ (s : B) (z : B ⊗[A] (B ⊗[A] d.descended)), E₂ (s ⊗ₜ z) = s ⊗ₜ E₁ z :=
    fun _ _ => rfl
  -- The cocycle condition, read in `B ⊗[A] (B ⊗[A] K)`.
  set x := eθ.symm ξ
  have hx : θ x = ξ := heθ ξ
  have hcoc : AlgebraTensorModule.lTensor B B (co.restrictScalars A) x -
      AlgebraTensorModule.lTensor B B (TensorProduct.mk A B K 1) x + (1 : B) ⊗ₜ x = 0 := by
    apply hP
    rwa [map_add, map_sub, hρco, hρmk, hρone, hx, map_zero]
  -- The Amitsur differentials, transported.
  have hdiff₁ : ∀ x' : B ⊗[A] (B ⊗[A] d.descended),
      E₂ (amitsurDiff₁ A B d.descended x') =
        AlgebraTensorModule.lTensor B B (co.restrictScalars A) (E₁ x') -
          AlgebraTensorModule.lTensor B B (TensorProduct.mk A B K 1) (E₁ x') +
            (1 : B) ⊗ₜ E₁ x' := by
    intro x'
    induction x' using TensorProduct.induction_on with
    | zero => simp
    | tmul s z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul t m =>
        simp only [amitsurDiff₁_tmul, map_add, map_sub, hE₂, hE₁, he, one_smul,
          AlgebraTensorModule.lTensor_tmul, LinearMap.restrictScalars_apply,
          TensorProduct.mk_apply, LinearMap.map_smul_of_tower, hdes, TensorProduct.smul_tmul',
          smul_eq_mul, mul_one]
        abel
      | add z z' hz hz' =>
        rw [TensorProduct.tmul_add, map_add, map_add, hz, hz', map_add, map_add, map_add,
          TensorProduct.tmul_add]
        abel
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add, map_add, map_add, TensorProduct.tmul_add]
      abel
  have hdiff₀ : ∀ y : B ⊗[A] d.descended,
      E₁ (amitsurDiff₀ A B d.descended y) = co (e y) - (1 : B) ⊗ₜ e y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      simp only [amitsurDiff₀_tmul, map_sub, hE₁, he, one_smul, LinearMap.map_smul, hdes,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add y y' hy hy' =>
      rw [map_add, map_add, hy, hy', map_add, map_add, TensorProduct.tmul_add]
      abel
  obtain ⟨y, hy⟩ := exists_amitsurDiff₀_eq A B d.descended (x := E₁.symm x) (by
    apply E₂.injective
    rwa [hdiff₁, map_zero, LinearEquiv.apply_symm_apply])
  refine ⟨e y, ?_⟩
  calc α₁ (e y) - α₂ (e y) = θ (co (e y) - (1 : B) ⊗ₜ e y) := by
        rw [map_sub, hco, cmpLeft_tmul, map_one, one_smul]
    _ = θ (E₁ (amitsurDiff₀ A B d.descended y)) := by rw [hdiff₀]
    _ = ξ := by rw [hy, LinearEquiv.apply_symm_apply, hx]

end Module.Descent

end
