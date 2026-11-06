module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.RingTheory.Flat.Basic

/-!
# Descent of a comparison with a flat coefficient module

Let `A` be a commutative ring and `W` a flat `A`-module. This file proves the local-to-global
step that turns a bijection over the members of a finite cover into a bijection over the union,
for a comparison

`W ⊗[A] M U ⟶ N U`

between an `A`-module-valued sheaf `M` on a frame of opens and a sheaf `N` of abelian groups
indexed by the same frame.

This is the coefficient-module analogue of `Stacks.FlatSectionsDescent`, where the left tensor
factor is a flat algebra `B` and the comparison is the base change of an `A`-linear map. Here the
left factor is only a module, so the comparison is given directly, and the target is asked to be
no more than a sheaf of abelian groups: nothing in the argument uses the scalars of the target.

## Main definitions

* `Stacks.FlatCoefficientDescent.Comparison`: the data of a comparison — restriction maps on both
  sides, the comparison maps, the two sheaf axioms needed, and their compatibilities.

## Main results

* `Stacks.FlatCoefficientDescent.injective_of_pi` and
  `Stacks.FlatCoefficientDescent.bijective_of_pair`: the two purely algebraic steps. The first
  says that injectivity of a comparison can be checked on a finite family of quotients whose
  joint kernel is zero; the second is the Mayer–Vietoris step, deducing bijectivity over a union
  from bijectivity over the two pieces and injectivity over the intersection.
* `Stacks.FlatCoefficientDescent.Comparison.injective_of_iSup` and
  `Stacks.FlatCoefficientDescent.Comparison.bijective_of_iSup`: **the induction.** The comparison
  is injective over a finite union of opens on which it is injective, and bijective over a finite
  union of opens on which it is bijective provided it is injective over the pairwise
  intersections.

## Implementation notes

Flatness is used three times and only through Mathlib: `Module.Flat.lTensor_exact` and
`Module.Flat.lTensor_preserves_injective_linearMap` for the two algebraic steps, and the
distributivity of `⊗` over finite products (`TensorProduct.piRight`, `TensorProduct.prodRight`)
to read off the components. The algebraic steps are stated for abstract modules so that the
tensor-product manipulations never run at a sheaf-section type; the induction then only applies
them.

The lattice of opens is taken abstractly, as an `Order.Frame`, and the target sheaf is indexed by
that same lattice: in the application `N U` is the sections of a module upstairs over the preimage
of `U`, and that the preimage preserves suprema and infima is checked at the application site
rather than assumed here.

Only separation is asked of the target `N`; gluing is needed for the source `M` alone, and only
for a pair of opens.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 058S](https://stacks.math.columbia.edu/tag/058S)
-/

@[expose] public noncomputable section

universe u

open TensorProduct

namespace Stacks.FlatCoefficientDescent

variable {A W : Type*} [CommRing A] [AddCommGroup W] [Module A W]

/-! ### Injectivity from a finite family -/

section Pi

variable {ι : Type*} [Finite ι]
  {M : Type*} [AddCommGroup M] [Module A M]
  {Mi : ι → Type*} [∀ i, AddCommGroup (Mi i)] [∀ i, Module A (Mi i)]
  {N : Type*} [AddCommGroup N] {Ni : ι → Type*} [∀ i, AddCommGroup (Ni i)]

omit [Finite ι] in
/-- The components of a tensored map into a finite product. -/
theorem piRightHom_lTensor_pi (r : ∀ i, M →ₗ[A] Mi i) (i : ι) (x : W ⊗[A] M) :
    TensorProduct.piRightHom A A W Mi (LinearMap.lTensor W (LinearMap.pi r) x) i =
      LinearMap.lTensor W (r i) x := by
  induction x with
  | add u v hu hv => simp [hu, hv]
  | tmul w m => simp

/-- **Injectivity from a finite cover.** A comparison is injective as soon as it is injective
after passing to a finite family of quotients of the source whose joint kernel is zero. -/
theorem injective_of_pi [Module.Flat A W]
    (c : W ⊗[A] M →+ N) (ci : ∀ i, W ⊗[A] Mi i →+ Ni i)
    (r : ∀ i, M →ₗ[A] Mi i) (s : ∀ i, N →+ Ni i)
    (hsq : ∀ (i : ι) (x : W ⊗[A] M), ci i (LinearMap.lTensor W (r i) x) = s i (c x))
    (hsep : ∀ m : M, (∀ i, r i m = 0) → m = 0)
    (hi : ∀ i, Function.Injective (ci i)) :
    Function.Injective c := by
  classical
  cases nonempty_fintype ι
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  have hL : Function.Injective (LinearMap.lTensor W (LinearMap.pi r)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _
      ((injective_iff_map_eq_zero _).mpr fun m hm => hsep m fun i => congrFun hm i)
  have h0 : ∀ i, LinearMap.lTensor W (r i) x = 0 :=
    fun i => hi i (by rw [hsq i x, hx, map_zero, map_zero])
  refine (injective_iff_map_eq_zero _).mp hL x ?_
  refine (TensorProduct.piRight A A W Mi).injective ?_
  rw [map_zero]
  refine funext fun i => ?_
  rw [TensorProduct.piRight_apply, piRightHom_lTensor_pi r i x, h0 i]
  rfl

end Pi

/-! ### The Mayer–Vietoris step -/

section Pair

variable {M M₁ M₂ M₀ : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M₁] [Module A M₁]
  [AddCommGroup M₂] [Module A M₂] [AddCommGroup M₀] [Module A M₀]
  {N N₁ N₂ N₀ : Type*} [AddCommGroup N] [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₀]

/-- The components of a tensored map into a binary product. -/
theorem prodRight_lTensor_prod (r₁ : M →ₗ[A] M₁) (r₂ : M →ₗ[A] M₂) (x : W ⊗[A] M) :
    TensorProduct.prodRight A A W M₁ M₂ (LinearMap.lTensor W (LinearMap.prod r₁ r₂) x) =
      (LinearMap.lTensor W r₁ x, LinearMap.lTensor W r₂ x) := by
  induction x with
  | add u v hu hv => simp [hu, hv]
  | tmul w m => simp

/-- The tensored difference of two restrictions, read through the binary product. -/
theorem lTensor_diff (s₁ : M₁ →ₗ[A] M₀) (s₂ : M₂ →ₗ[A] M₀) (w : W ⊗[A] (M₁ × M₂)) :
    LinearMap.lTensor W (s₁ ∘ₗ LinearMap.fst A M₁ M₂ - s₂ ∘ₗ LinearMap.snd A M₁ M₂) w =
      LinearMap.lTensor W s₁ (TensorProduct.prodRight A A W M₁ M₂ w).1 -
        LinearMap.lTensor W s₂ (TensorProduct.prodRight A A W M₁ M₂ w).2 := by
  induction w with
  | add u v hu hv =>
      simp only [map_add, hu, hv, Prod.fst_add, Prod.snd_add]
      abel
  | tmul b m => simp

/-- A tensored element whose two restrictions vanish is zero, when the pair of restrictions
is jointly injective. -/
private theorem eq_zero_of_lTensor_prod [Module.Flat A W] (r₁ : M →ₗ[A] M₁) (r₂ : M →ₗ[A] M₂)
    (hMsep : ∀ m : M, r₁ m = 0 → r₂ m = 0 → m = 0) (x : W ⊗[A] M)
    (h₁ : LinearMap.lTensor W r₁ x = 0) (h₂ : LinearMap.lTensor W r₂ x = 0) : x = 0 := by
  have hRinj : Function.Injective (LinearMap.prod r₁ r₂) :=
    (injective_iff_map_eq_zero _).mpr fun m hm =>
      hMsep m (congrArg Prod.fst hm) (congrArg Prod.snd hm)
  refine (injective_iff_map_eq_zero _).mp
    (Module.Flat.lTensor_preserves_injective_linearMap (M := W) _ hRinj) x ?_
  refine (TensorProduct.prodRight A A W M₁ M₂).injective ?_
  rw [prodRight_lTensor_prod r₁ r₂ x, h₁, h₂, map_zero]
  rfl

/-- Gluing for a pair makes the joint restriction exact against the difference of the two
restrictions to the overlap. -/
private theorem exact_prod_sub_of_glue (r₁ : M →ₗ[A] M₁) (r₂ : M →ₗ[A] M₂) (s₁ : M₁ →ₗ[A] M₀)
    (s₂ : M₂ →ₗ[A] M₀) (hMcomm : ∀ m, s₁ (r₁ m) = s₂ (r₂ m))
    (hMglue : ∀ (x₁ : M₁) (x₂ : M₂), s₁ x₁ = s₂ x₂ → ∃ m, r₁ m = x₁ ∧ r₂ m = x₂) :
    Function.Exact (LinearMap.prod r₁ r₂)
      (s₁ ∘ₗ LinearMap.fst A M₁ M₂ - s₂ ∘ₗ LinearMap.snd A M₁ M₂) := by
  refine fun z => ⟨fun hz => ?_, ?_⟩
  · obtain ⟨m, hm1, hm2⟩ := hMglue z.1 z.2 (by
      simpa only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.fst_apply, LinearMap.snd_apply, sub_eq_zero] using hz)
    exact ⟨m, by simp [LinearMap.prod_apply, hm1, hm2]⟩
  · rintro ⟨m, rfl⟩
    simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.prod_apply, sub_eq_zero]
    exact hMcomm m

/-- Gluing for a pair survives tensoring with a flat module. -/
private theorem exists_lTensor_of_glue [Module.Flat A W] (r₁ : M →ₗ[A] M₁) (r₂ : M →ₗ[A] M₂)
    (s₁ : M₁ →ₗ[A] M₀) (s₂ : M₂ →ₗ[A] M₀) (hMcomm : ∀ m, s₁ (r₁ m) = s₂ (r₂ m))
    (hMglue : ∀ (x₁ : M₁) (x₂ : M₂), s₁ x₁ = s₂ x₂ → ∃ m, r₁ m = x₁ ∧ r₂ m = x₂)
    (y₁ : W ⊗[A] M₁) (y₂ : W ⊗[A] M₂)
    (hy : LinearMap.lTensor W s₁ y₁ = LinearMap.lTensor W s₂ y₂) :
    ∃ x : W ⊗[A] M, LinearMap.lTensor W r₁ x = y₁ ∧ LinearMap.lTensor W r₂ x = y₂ := by
  obtain ⟨z, hpz⟩ := (TensorProduct.prodRight A A W M₁ M₂).surjective (y₁, y₂)
  have hz : LinearMap.lTensor W
      (s₁ ∘ₗ LinearMap.fst A M₁ M₂ - s₂ ∘ₗ LinearMap.snd A M₁ M₂) z = 0 := by
    rw [lTensor_diff s₁ s₂ z, hpz, hy, sub_self]
  obtain ⟨x, hx⟩ := (Module.Flat.lTensor_exact (M := W)
    (exact_prod_sub_of_glue r₁ r₂ s₁ s₂ hMcomm hMglue) z).mp hz
  have hcomp := prodRight_lTensor_prod r₁ r₂ x
  rw [hx, hpz] at hcomp
  exact ⟨x, (congrArg Prod.fst hcomp).symm, (congrArg Prod.snd hcomp).symm⟩

/-- **Mayer–Vietoris.** A comparison bijective over two opens and injective over their
intersection is bijective over their union. -/
theorem bijective_of_pair [Module.Flat A W]
    (c : W ⊗[A] M →+ N) (c₁ : W ⊗[A] M₁ →+ N₁) (c₂ : W ⊗[A] M₂ →+ N₂)
    (c₀ : W ⊗[A] M₀ →+ N₀)
    (r₁ : M →ₗ[A] M₁) (r₂ : M →ₗ[A] M₂) (s₁ : M₁ →ₗ[A] M₀) (s₂ : M₂ →ₗ[A] M₀)
    (ρ₁ : N →+ N₁) (ρ₂ : N →+ N₂) (σ₁ : N₁ →+ N₀) (σ₂ : N₂ →+ N₀)
    (hsq₁ : ∀ x, c₁ (LinearMap.lTensor W r₁ x) = ρ₁ (c x))
    (hsq₂ : ∀ x, c₂ (LinearMap.lTensor W r₂ x) = ρ₂ (c x))
    (hsq₁' : ∀ x, c₀ (LinearMap.lTensor W s₁ x) = σ₁ (c₁ x))
    (hsq₂' : ∀ x, c₀ (LinearMap.lTensor W s₂ x) = σ₂ (c₂ x))
    (hMcomm : ∀ m, s₁ (r₁ m) = s₂ (r₂ m))
    (hMsep : ∀ m : M, r₁ m = 0 → r₂ m = 0 → m = 0)
    (hMglue : ∀ (x₁ : M₁) (x₂ : M₂), s₁ x₁ = s₂ x₂ → ∃ m, r₁ m = x₁ ∧ r₂ m = x₂)
    (hNcomm : ∀ n, σ₁ (ρ₁ n) = σ₂ (ρ₂ n))
    (hNsep : ∀ n : N, ρ₁ n = 0 → ρ₂ n = 0 → n = 0)
    (h₁ : Function.Bijective c₁) (h₂ : Function.Bijective c₂)
    (h₀ : Function.Injective c₀) :
    Function.Bijective c := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_, fun n => ?_⟩
  · refine eq_zero_of_lTensor_prod r₁ r₂ hMsep x (h₁.injective ?_) (h₂.injective ?_)
    · rw [hsq₁ x, hx, map_zero, map_zero]
    · rw [hsq₂ x, hx, map_zero, map_zero]
  · obtain ⟨y₁, hy₁⟩ := h₁.surjective (ρ₁ n)
    obtain ⟨y₂, hy₂⟩ := h₂.surjective (ρ₂ n)
    have key : LinearMap.lTensor W s₁ y₁ = LinearMap.lTensor W s₂ y₂ := by
      refine h₀ ?_
      rw [hsq₁' y₁, hsq₂' y₂, hy₁, hy₂, hNcomm n]
    obtain ⟨x, hx₁, hx₂⟩ := exists_lTensor_of_glue r₁ r₂ s₁ s₂ hMcomm hMglue y₁ y₂ key
    refine ⟨x, sub_eq_zero.mp (hNsep (c x - n) ?_ ?_)⟩
    · rw [map_sub, ← hsq₁ x, hx₁, hy₁, sub_self]
    · rw [map_sub, ← hsq₂ x, hx₂, hy₂, sub_self]

end Pair

/-! ### The local-to-global induction -/

section Lattice

/-- The data of a comparison, with coefficients in an `A`-module `W`, between a sheaf of
`A`-modules and a sheaf of abelian groups indexed by a frame of opens. -/
structure Comparison (A W : Type u) [CommRing A] [AddCommGroup W] [Module A W]
    (L : Type u) [Order.Frame L]
    (M : L → Type u) [∀ U, AddCommGroup (M U)] [∀ U, Module A (M U)]
    (N : L → Type u) [∀ U, AddCommGroup (N U)] where
  /-- Restriction in the source. -/
  resM : ∀ {U V : L}, V ≤ U → M U →ₗ[A] M V
  /-- Restriction in the target. -/
  resN : ∀ {U V : L}, V ≤ U → N U →+ N V
  /-- The comparison map. -/
  cmp : ∀ U, W ⊗[A] M U →+ N U
  resM_resM : ∀ {U V W' : L} (h₁ : V ≤ U) (h₂ : W' ≤ V) (x : M U),
    resM h₂ (resM h₁ x) = resM (h₂.trans h₁) x
  resN_resN : ∀ {U V W' : L} (h₁ : V ≤ U) (h₂ : W' ≤ V) (y : N U),
    resN h₂ (resN h₁ y) = resN (h₂.trans h₁) y
  cmp_res : ∀ {U V : L} (h : V ≤ U) (x : W ⊗[A] M U),
    cmp V (LinearMap.lTensor W (resM h) x) = resN h (cmp U x)
  sepM : ∀ (U : L) (cov : Set L) (hcov : ∀ V ∈ cov, V ≤ U) (_hU : U ≤ sSup cov)
    (x : M U), (∀ V (hV : V ∈ cov), resM (hcov V hV) x = 0) → x = 0
  sepN : ∀ (U : L) (cov : Set L) (hcov : ∀ V ∈ cov, V ≤ U) (_hU : U ≤ sSup cov)
    (y : N U), (∀ V (hV : V ∈ cov), resN (hcov V hV) y = 0) → y = 0
  glueM : ∀ (U₁ U₂ : L) (x₁ : M U₁) (x₂ : M U₂),
    resM (inf_le_left : U₁ ⊓ U₂ ≤ U₁) x₁ = resM (inf_le_right : U₁ ⊓ U₂ ≤ U₂) x₂ →
    ∃ y : M (U₁ ⊔ U₂), resM (le_sup_left : U₁ ≤ U₁ ⊔ U₂) y = x₁ ∧
      resM (le_sup_right : U₂ ≤ U₁ ⊔ U₂) y = x₂

namespace Comparison

variable {A W : Type u} [CommRing A] [AddCommGroup W] [Module A W] [Module.Flat A W]
  {L : Type u} [Order.Frame L]
  {M : L → Type u} [∀ U, AddCommGroup (M U)] [∀ U, Module A (M U)]
  {N : L → Type u} [∀ U, AddCommGroup (N U)]

omit [Module.Flat A W] in
/-- The source of a comparison has only the zero section over `⊥`. -/
theorem subsingleton_M_bot (c : Comparison A W L M N) (x : M ⊥) : x = 0 :=
  c.sepM ⊥ ∅ (by simp) (by simp) x (by simp)

omit [Module.Flat A W] in
/-- The target of a comparison has only the zero section over `⊥`. -/
theorem subsingleton_N_bot (c : Comparison A W L M N) (y : N ⊥) : y = 0 :=
  c.sepN ⊥ ∅ (by simp) (by simp) y (by simp)

omit [Module.Flat A W] in
/-- The comparison map over `⊥` is bijective. -/
theorem bijective_cmp_bot (c : Comparison A W L M N) : Function.Bijective (c.cmp ⊥) := by
  refine ⟨fun x y _ => ?_, fun n => ⟨0, by rw [map_zero, c.subsingleton_N_bot n]⟩⟩
  have h : ∀ z : W ⊗[A] M (⊥ : L), z = 0 := by
    intro z
    induction z with
    | add u v hu hv => rw [hu, hv, add_zero]
    | tmul w m => rw [c.subsingleton_M_bot m, TensorProduct.tmul_zero]
  rw [h x, h y]

omit [Module.Flat A W] in
/-- A source section over `U₁ ⊔ U₂` whose restrictions to `U₁` and `U₂` vanish is zero. -/
private theorem eq_zero_of_resM_sup (c : Comparison A W L M N) {U₁ U₂ : L} (x : M (U₁ ⊔ U₂))
    (h₁ : c.resM le_sup_left x = 0) (h₂ : c.resM le_sup_right x = 0) : x = 0 := by
  refine c.sepM (U₁ ⊔ U₂) {U₁, U₂} ?_ (by simp) x ?_
  · rintro Y (rfl | rfl)
    exacts [le_sup_left, le_sup_right]
  · rintro Y (rfl | rfl)
    exacts [h₁, h₂]

omit [Module.Flat A W] in
/-- A target section over `U₁ ⊔ U₂` whose restrictions to `U₁` and `U₂` vanish is zero. -/
private theorem eq_zero_of_resN_sup (c : Comparison A W L M N) {U₁ U₂ : L} (y : N (U₁ ⊔ U₂))
    (h₁ : c.resN le_sup_left y = 0) (h₂ : c.resN le_sup_right y = 0) : y = 0 := by
  refine c.sepN (U₁ ⊔ U₂) {U₁, U₂} ?_ (by simp) y ?_
  · rintro Y (rfl | rfl)
    exacts [le_sup_left, le_sup_right]
  · rintro Y (rfl | rfl)
    exacts [h₁, h₂]

/-- **Injectivity is local on a finite cover.** -/
theorem injective_of_iSup (c : Comparison A W L M N) {ι : Type*} [Finite ι]
    (U : L) (V : ι → L) (hV : ∀ i, V i ≤ U) (hU : U ≤ ⨆ i, V i)
    (h : ∀ i, Function.Injective (c.cmp (V i))) :
    Function.Injective (c.cmp U) :=
  injective_of_pi (c.cmp U) (fun i => c.cmp (V i))
    (fun i => c.resM (hV i)) (fun i => c.resN (hV i)) (fun i x => c.cmp_res (hV i) x)
    (fun x hx => c.sepM U (Set.range V) (Set.forall_mem_range.2 hV)
      (by rwa [sSup_range]) x (by rintro Z ⟨i, rfl⟩; exact hx i)) h

/-- **Bijectivity is local on a finite cover, given injectivity on the pairwise
intersections.** -/
theorem bijective_of_iSup (c : Comparison A W L M N) {ι : Type*} [Finite ι]
    (U : L) (V : ι → L) (hV : ∀ i, V i ≤ U) (hU : U ≤ ⨆ i, V i)
    (hb : ∀ i, Function.Bijective (c.cmp (V i)))
    (hinj : ∀ i j, Function.Injective (c.cmp (V i ⊓ V j))) :
    Function.Bijective (c.cmp U) := by
  classical
  cases nonempty_fintype ι
  obtain rfl : U = ⨆ i, V i := le_antisymm hU (iSup_le hV)
  have step : ∀ s : Finset ι, Function.Bijective (c.cmp (⨆ i ∈ s, V i)) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        rw [show (⨆ i ∈ (∅ : Finset ι), V i) = (⊥ : L) by simp]
        exact c.bijective_cmp_bot
    | @insert a s ha ih =>
        rw [Finset.iSup_insert]
        set Z := ⨆ i ∈ s, V i with hZ
        have hdist : V a ⊓ Z = ⨆ i : {x // x ∈ s}, (V a ⊓ V i) := by
          rw [hZ, iSup_subtype', inf_iSup_eq]
        have h0 : Function.Injective (c.cmp (V a ⊓ Z)) := by
          refine c.injective_of_iSup (V a ⊓ Z) (fun i : {x // x ∈ s} => V a ⊓ V i)
            (fun i => by
              rw [hdist]
              exact le_iSup (fun j : {x // x ∈ s} => V a ⊓ V j) i)
            (le_of_eq hdist) (fun i => hinj a i)
        exact bijective_of_pair (c.cmp (V a ⊔ Z)) (c.cmp (V a)) (c.cmp Z) (c.cmp (V a ⊓ Z))
          (c.resM le_sup_left) (c.resM le_sup_right) (c.resM inf_le_left) (c.resM inf_le_right)
          (c.resN le_sup_left) (c.resN le_sup_right) (c.resN inf_le_left) (c.resN inf_le_right)
          (fun x => c.cmp_res _ x) (fun x => c.cmp_res _ x)
          (fun x => c.cmp_res _ x) (fun x => c.cmp_res _ x)
          (fun m => by rw [c.resM_resM, c.resM_resM]) (fun m => c.eq_zero_of_resM_sup m)
          (c.glueM (V a) Z) (fun n => by rw [c.resN_resN, c.resN_resN])
          (fun n => c.eq_zero_of_resN_sup n) (hb a) ih h0
  rw [← show (⨆ i ∈ (Finset.univ : Finset ι), V i) = ⨆ i, V i by simp]
  exact step Finset.univ

end Comparison

end Lattice

end Stacks.FlatCoefficientDescent

end
