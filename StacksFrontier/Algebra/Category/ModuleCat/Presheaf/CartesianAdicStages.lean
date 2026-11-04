module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianChangeOfRings
public import StacksFrontier.Examples.Completion.AdicTowerEquivalence

/-!
# Cartesian presheaves of modules over a cofinal tower of adic stages

Let `O` be a presheaf of commutative rings on a category `C`, let `A` be a commutative ring and
let `I ⊆ A` be an ideal. An *adic stage system* for `(O, A, I)` is a tower
`x₀ ⟶ x₁ ⟶ x₂ ⟶ ⋯` of objects of `C` with surjections `αₙ : A ⟶ O(xₙ)` of kernel `Iⁿ`,
compatible with the restriction maps, such that every object of `C` maps to some stage and maps
to each stage in at most one way.

This is the shape of the affine part of the category fibred in groupoids of a formal completion
`Spf(A) = colim Spec(A ⧸ Iⁿ)`: an affine scheme over it factors through a stage, and through
each stage at most once, the stages being monomorphisms into the colimit.

This file proves that for such a system the cartesian presheaves of `O`-modules are the same as
the adic towers over `(A, I)`, hence, for `I` finitely generated, the same as the `I`-adically
complete `A`-modules (Stacks 09B8): the module attached to a cartesian presheaf `𝓕` is
`lim 𝓕(xₙ)`, and the presheaf attached to a complete module `M` is `x ↦ O(x) ⊗_A M`.

## Main definitions

* `Stacks.PresheafOfModules.AdicStages`: an adic stage system.
* `Stacks.PresheafOfModules.AdicStages.tower`: the adic tower `n ↦ 𝓕(xₙ)` of a cartesian
  presheaf of modules, as a functor.
* `Stacks.PresheafOfModules.AdicStages.baseChange`: the cartesian presheaf `x ↦ O(x) ⊗_A M` of
  an `A`-module `M`, as a functor.
* `Stacks.PresheafOfModules.AdicStages.cartesianEquivalence`: the equivalence between cartesian
  presheaves of modules and adic towers.
* `Stacks.PresheafOfModules.AdicStages.cartesianEquivalenceComplete`: the equivalence between
  cartesian presheaves of modules and `I`-adically complete `A`-modules.

## Implementation notes

The ring map `A ⟶ O(x)` at an arbitrary object is read off any map `x ⟶ xₙ` to a stage, and does
not depend on the choice because maps to the stages are unique and compatible with the tower.
This makes `O` a presheaf of `A`-algebras, and `M ↦ O ⊗_A M` is the change of rings
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRings` along `A ⟶ O` applied to the constant
presheaf of modules with value `M`.

The comparison `O ⊗_A lim 𝓕(xₙ) ⟶ 𝓕` is the adjoint transpose of the maps
`lim 𝓕(xₙ) ⟶ 𝓕(x)`, `m ↦ 𝓕(g)(mₙ)` for any `g : x ⟶ xₙ`; at `x` it factors as
`O(x) ⊗_A M ≅ O(x) ⊗_{O(xₙ)} (O(xₙ) ⊗_A M) ≅ O(x) ⊗_{O(xₙ)} 𝓕(xₙ) ≅ 𝓕(x)`, the middle step
being `O(xₙ) ⊗_A M = M ⧸ Iⁿ M = 𝓕(xₙ)` and the last the cartesian condition.

## References

* [Stacks Project, Tag 09B8](https://stacks.math.columbia.edu/tag/09B8)
* [Stacks Project, Tag 0ALF](https://stacks.math.columbia.edu/tag/0ALF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u v₁ u₁

namespace Stacks.PresheafOfModules

/-! ### Base change along a surjection of rings -/

section BaseChange

variable {S T : Type*} [CommRing S] [CommRing T] (q : S →+* T) (hq : Function.Surjective q)
  {N : Type*} [AddCommGroup N] [Module S N]

include hq in
/-- Along a surjective ring map `q : S ⟶ T`, every element of `T ⊗_S N` is of the form
`1 ⊗ y`. -/
theorem exists_one_tmul_eq (z : letI := q.toAlgebra; T ⊗[S] N) :
    letI := q.toAlgebra
    ∃ y : N, (1 : T) ⊗ₜ[S] y = z := by
  let := q.toAlgebra
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, tmul_zero _ _⟩
  | tmul t y =>
    obtain ⟨s, rfl⟩ := hq t
    refine ⟨s • y, ?_⟩
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  | add z z' hz hz' =>
    obtain ⟨y, rfl⟩ := hz
    obtain ⟨y', rfl⟩ := hz'
    exact ⟨y + y', tmul_add _ _ _⟩

include hq in
/-- Along a surjective ring map `q : S ⟶ T`, an element `y` of an `S`-module `N` becomes zero
in `T ⊗_S N` exactly when it lies in `(ker q) N`: `T ⊗_S N = N ⧸ (ker q) N`. -/
theorem one_tmul_eq_zero_iff (y : N) :
    letI := q.toAlgebra
    (1 : T) ⊗ₜ[S] y = 0 ↔ y ∈ RingHom.ker q • (⊤ : Submodule S N) := by
  let := q.toAlgebra
  let f : S →ₐ[S] T := Algebra.ofId S T
  have hf : Function.Surjective f := hq
  let e : (S ⧸ RingHom.ker q) ≃ₗ[S] T :=
    (Ideal.quotientKerAlgEquivOfSurjective hf).toLinearEquiv
  let Φ : T ⊗[S] N ≃ₗ[S] N ⧸ (RingHom.ker q • (⊤ : Submodule S N)) :=
    (TensorProduct.congr e.symm (LinearEquiv.refl S N)).trans
      (TensorProduct.quotTensorEquivQuotSMul N (RingHom.ker q))
  have hΦ : Φ ((1 : T) ⊗ₜ[S] y) = Submodule.Quotient.mk y := by
    have h1 : e.symm (1 : T) = Ideal.Quotient.mk (RingHom.ker q) 1 := by
      rw [LinearEquiv.symm_apply_eq]
      exact (map_one (Ideal.quotientKerAlgEquivOfSurjective hf)).symm
    show TensorProduct.quotTensorEquivQuotSMul N (RingHom.ker q)
      (e.symm (1 : T) ⊗ₜ[S] y) = _
    rw [h1, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  rw [← Φ.map_eq_zero_iff, hΦ, Submodule.Quotient.mk_eq_zero]

include hq in
/-- **Base change along a surjection, read off a semilinear map.** Let `q : S ⟶ T` be a
surjective ring map, `g : N ⟶ P` a `q`-semilinear map from an `S`-module to a `T`-module, and
suppose that its adjoint `T ⊗_S N ⟶ P`, `t ⊗ y ↦ t • g y`, is bijective. Then `g` is surjective
and its kernel is `(ker q) N`. -/
theorem surjective_and_ker_of_bijective {P : Type*} [AddCommGroup P] [Module T P]
    (g : N →+ P)
    (Λ : (letI := q.toAlgebra; T ⊗[S] N) →+ P)
    (hΛ : ∀ (t : T) (y : N), Λ (letI := q.toAlgebra; t ⊗ₜ[S] y) = t • g y)
    (hbij : Function.Bijective Λ) :
    Function.Surjective g ∧ ∀ y, g y = 0 ↔ y ∈ RingHom.ker q • (⊤ : Submodule S N) := by
  let := q.toAlgebra
  have h1 (y : N) : Λ ((1 : T) ⊗ₜ[S] y) = g y := by rw [hΛ, one_smul]
  refine ⟨fun p => ?_, fun y => ?_⟩
  · obtain ⟨z, rfl⟩ := hbij.2 p
    obtain ⟨y, rfl⟩ := exists_one_tmul_eq q hq z
    exact ⟨y, (h1 y).symm⟩
  · rw [← one_tmul_eq_zero_iff q hq, ← h1, ← map_zero Λ]
    exact hbij.1.eq_iff

include hq in
/-- **Base change of a module along a surjection onto its reduction.** Let `α : S ⟶ T` be a
surjective ring map with kernel `J`, and let `p : N ⟶ P` be an `α`-semilinear surjection from an
`S`-module onto a `T`-module whose kernel is `J N`. Then the adjoint `T ⊗_S N ⟶ P`,
`t ⊗ y ↦ t • p y`, is bijective: `P = N ⧸ J N = T ⊗_S N`. -/
theorem bijective_of_surjective_of_ker {P : Type*} [AddCommGroup P] [Module T P]
    (p : N →+ P)
    (hsurj : Function.Surjective p)
    (hker : ∀ y, p y = 0 ↔ y ∈ RingHom.ker q • (⊤ : Submodule S N))
    (Λ : (letI := q.toAlgebra; T ⊗[S] N) →+ P)
    (hΛ : ∀ (t : T) (y : N), Λ (letI := q.toAlgebra; t ⊗ₜ[S] y) = t • p y) :
    Function.Bijective Λ := by
  let := q.toAlgebra
  have h1 (y : N) : Λ ((1 : T) ⊗ₜ[S] y) = p y := by rw [hΛ, one_smul]
  refine ⟨(injective_iff_map_eq_zero Λ).2 fun z hz => ?_, fun x => ?_⟩
  · obtain ⟨y, rfl⟩ := exists_one_tmul_eq q hq z
    rw [h1, hker] at hz
    exact (one_tmul_eq_zero_iff q hq y).2 hz
  · obtain ⟨y, rfl⟩ := hsurj x
    exact ⟨_, h1 y⟩

/-- Restriction of scalars along a surjective ring map `α : A ⟶ S` identifies the submodule
`J N` of the `A`-module `N` with the submodule `α(J) N` of the `S`-module `N`. -/
theorem mem_smul_top_compHom_iff {A S : Type*} [CommRing A] [CommRing S] (α : A →+* S)
    (hα : Function.Surjective α) (J : Ideal A) {N : Type*} [AddCommGroup N] [Module S N]
    (y : N) :
    letI := Module.compHom N α
    y ∈ J • (⊤ : Submodule A N) ↔ y ∈ J.map α • (⊤ : Submodule S N) := by
  let := Module.compHom N α
  constructor
  · intro hy
    refine Submodule.smul_induction_on hy (fun a ha z _ => ?_) (fun _ _ => Submodule.add_mem _)
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem α ha) Submodule.mem_top
  · intro hy
    refine Submodule.smul_induction_on hy (fun s hs z _ => ?_) (fun _ _ => Submodule.add_mem _)
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective α hα).1 hs
    exact Submodule.smul_mem_smul (M := N) (N := ⊤) ha Submodule.mem_top

/-- **Base change through a stage.** Let `α : A ⟶ T` be a surjective ring map with kernel `J`
and `σ : T ⟶ U` a ring map. Let `p : M ⟶ P` be an `α`-semilinear surjection from an `A`-module
onto a `T`-module with kernel `J M`, and `g : P ⟶ Q` a `σ`-semilinear map to a `U`-module whose
adjoint `U ⊗_T P ⟶ Q` is bijective. Then the adjoint `U ⊗_A M ⟶ Q`, `u ⊗ m ↦ u • g (p m)`, of
the composite is bijective: it is `U ⊗_A M = U ⊗_T (T ⊗_A M) = U ⊗_T P = Q`. -/
theorem bijective_tensor_of_stage {A T U M P Q : Type*} [CommRing A] [CommRing T] [CommRing U]
    (α : A →+* T) (hα : Function.Surjective α) (σ : T →+* U)
    [AddCommGroup M] [Module A M] [AddCommGroup P] [Module T P] [AddCommGroup Q] [Module U Q]
    (p : M →+ P) (hp : ∀ (a : A) (m : M), p (a • m) = α a • p m)
    (hpsurj : Function.Surjective p)
    (hpker : ∀ m, p m = 0 ↔ m ∈ RingHom.ker α • (⊤ : Submodule A M))
    (g : P →+ Q)
    (Γ : (letI := σ.toAlgebra; U ⊗[T] P) →+ Q)
    (hΓ : ∀ (u : U) (y : P), Γ (letI := σ.toAlgebra; u ⊗ₜ[T] y) = u • g y)
    (hΓbij : Function.Bijective Γ)
    (Λ : (letI := (σ.comp α).toAlgebra; U ⊗[A] M) →+ Q)
    (hΛ : ∀ (u : U) (m : M), Λ (letI := (σ.comp α).toAlgebra; u ⊗ₜ[A] m) = u • g (p m)) :
    Function.Bijective Λ := by
  let : Algebra A T := α.toAlgebra
  let : Algebra T U := σ.toAlgebra
  let : Algebra A U := (σ.comp α).toAlgebra
  have : IsScalarTower A T U := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Module A P := Module.compHom P α
  have : IsScalarTower A T P := ⟨fun a t y => mul_smul (α a) t y⟩
  let p' : M →ₗ[A] P := { p with map_smul' := hp }
  have hbij₁ : Function.Bijective (p'.liftBaseChange T) :=
    bijective_of_surjective_of_ker α hα p hpsurj hpker (p'.liftBaseChange T).toAddMonoidHom
      fun t m => LinearMap.liftBaseChange_tmul T p' t m
  let e₁ : T ⊗[A] M ≃ₗ[T] P := LinearEquiv.ofBijective (p'.liftBaseChange T) hbij₁
  let e₂ : U ⊗[T] (T ⊗[A] M) ≃ₗ[U] U ⊗[T] P := e₁.baseChange T U _ _
  let e₃ : U ⊗[T] (T ⊗[A] M) ≃ₗ[U] U ⊗[A] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A T U U M
  have key (z) : Λ z = Γ (e₂ (e₃.symm z)) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul u m =>
      rw [hΛ, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
        LinearEquiv.baseChange_tmul, hΓ]
      congr 2
      show p m = (p'.liftBaseChange T) ((1 : T) ⊗ₜ[A] m)
      rw [LinearMap.liftBaseChange_tmul, one_smul]
      rfl
    | add z z' hz hz' => rw [map_add, hz, hz', map_add, map_add, map_add]
  rw [show (Λ : _ → Q) = Γ ∘ e₂ ∘ e₃.symm from funext key]
  exact hΓbij.comp (e₂.bijective.comp e₃.symm.bijective)

end BaseChange

/-! ### Adic stage systems -/

variable {C : Type u₁} [Category.{v₁} C] (O : Cᵒᵖ ⥤ CommRingCat.{u}) {A : Type u} [CommRing A]
  (I : Ideal A)

/-- An **adic stage system** for a presheaf of commutative rings `O` on `C` and an ideal `I` of
a commutative ring `A`: a tower `x₀ ⟶ x₁ ⟶ ⋯` of objects of `C` with surjective ring maps
`αₙ : A ⟶ O(xₙ)` of kernel `Iⁿ`, compatible with the restriction maps, such that every object of
`C` maps to some stage, and to each stage in at most one way. -/
structure AdicStages where
  /-- The tower of stages. -/
  x : ℕ ⥤ C
  /-- The ring map `A ⟶ O(xₙ)`. -/
  α : ∀ n, A →+* O.obj (op (x.obj n))
  /-- The ring map `A ⟶ O(xₙ)` is surjective. -/
  surjective_α : ∀ n, Function.Surjective (α n)
  /-- The kernel of `A ⟶ O(xₙ)` is `Iⁿ`. -/
  ker_α : ∀ n, RingHom.ker (α n) = I ^ n
  /-- The ring maps are compatible with the restriction along `xₙ ⟶ xₙ₊₁`. -/
  map_comp_α : ∀ n,
    (O.map (x.map (homOfLE (Nat.le_succ n))).op).hom.comp (α (n + 1)) = α n
  /-- Every object maps to some stage. -/
  exists_hom : ∀ c : C, ∃ n, Nonempty (c ⟶ x.obj n)
  /-- An object maps to a stage in at most one way. -/
  subsingleton_hom : ∀ (c : C) (n : ℕ), Subsingleton (c ⟶ x.obj n)

namespace AdicStages

variable {O I} (D : AdicStages O I)

/-- The ring maps `A ⟶ O(xₙ)` are compatible with the restriction along `xₙ ⟶ xₘ` for every
`n ≤ m`. -/
theorem map_comp_α_of_le {n m : ℕ} (h : n ≤ m) :
    (O.map (D.x.map (homOfLE h)).op).hom.comp (D.α m) = D.α n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    rw [show homOfLE (hnm.trans (Nat.le_succ m)) = homOfLE hnm ≫ homOfLE (Nat.le_succ m) from rfl,
      D.x.map_comp, op_comp, O.map_comp, CommRingCat.hom_comp, RingHom.comp_assoc,
      D.map_comp_α, ih]

/-- A function of a map `c ⟶ xₙ` to a stage that is compatible with the transition maps does not
depend on the stage or on the map. -/
private theorem eq_of_stage_maps {β : Sort*} {c : C} (φ : ∀ n, (c ⟶ D.x.obj n) → β)
    (h : ∀ {n N : ℕ} (hle : n ≤ N) (g : c ⟶ D.x.obj n),
      φ n g = φ N (g ≫ D.x.map (homOfLE hle)))
    {n m : ℕ} (g : c ⟶ D.x.obj n) (g' : c ⟶ D.x.obj m) : φ n g = φ m g' := by
  have key {n N : ℕ} (hle : n ≤ N) (g : c ⟶ D.x.obj n) (g' : c ⟶ D.x.obj N) :
      φ n g = φ N g' := by
    have := D.subsingleton_hom c N
    obtain rfl : g' = g ≫ D.x.map (homOfLE hle) := Subsingleton.elim _ _
    exact h hle g
  exact (key (le_max_left n m) g (g ≫ D.x.map (homOfLE (le_max_left n m)))).trans
    (key (le_max_right n m) g' (g ≫ D.x.map (homOfLE (le_max_left n m)))).symm

/-- The ring map `A ⟶ O(x)` read off a map `x ⟶ xₙ` to a stage does not depend on the stage or
on the map. -/
theorem comp_α_eq {c : C} {n m : ℕ} (g : c ⟶ D.x.obj n) (g' : c ⟶ D.x.obj m) :
    (O.map g.op).hom.comp (D.α n) = (O.map g'.op).hom.comp (D.α m) :=
  D.eq_of_stage_maps (fun n g => (O.map g.op).hom.comp (D.α n)) (fun hle g => by
    rw [op_comp, O.map_comp, CommRingCat.hom_comp, RingHom.comp_assoc, D.map_comp_α_of_le]) g g'

/-- A chosen stage that an object maps to. -/
def stage (c : C) : ℕ := (D.exists_hom c).choose

/-- A chosen map from an object to a stage. -/
def toStage (c : C) : c ⟶ D.x.obj (D.stage c) := (D.exists_hom c).choose_spec.some

/-- The ring map `A ⟶ O(x)`, read off the chosen map to a stage. -/
def lam (c : C) : A →+* O.obj (op c) := (O.map (D.toStage c).op).hom.comp (D.α (D.stage c))

/-- The ring map `A ⟶ O(x)` is the one read off any map to a stage. -/
theorem lam_eq {c : C} {n : ℕ} (g : c ⟶ D.x.obj n) : D.lam c = (O.map g.op).hom.comp (D.α n) :=
  D.comp_α_eq _ _

/-- The ring maps `A ⟶ O(x)` are compatible with the restriction maps of `O`. -/
theorem map_comp_lam {c c' : C} (f : c' ⟶ c) :
    (O.map f.op).hom.comp (D.lam c) = D.lam c' := by
  rw [D.lam_eq (f ≫ D.toStage c), op_comp, O.map_comp, CommRingCat.hom_comp, RingHom.comp_assoc]
  rfl

/-- At a stage, the ring map `A ⟶ O(xₙ)` is `αₙ`. -/
theorem lam_stage (n : ℕ) : D.lam (D.x.obj n) = D.α n := by
  rw [D.lam_eq (𝟙 _)]
  simp

/-- The structure of presheaf of `A`-algebras on `O`: the morphism from the constant presheaf of
rings `A` to `O` whose components are the ring maps `A ⟶ O(x)`. -/
def ringHom : (Functor.const Cᵒᵖ).obj (CommRingCat.of A) ⟶ O where
  app c := CommRingCat.ofHom (D.lam c.unop)
  naturality _ _ f := CommRingCat.hom_ext (D.map_comp_lam f.unop).symm

end AdicStages

/-! ### The constant presheaf of modules -/

/-- The constant presheaf of modules with value an `A`-module `M`, over the constant presheaf of
rings `A`. -/
def constModule (C : Type u₁) [Category.{v₁} C] (M : ModuleCat.{u} A) :
    PresheafOfModules.{u} (ringPresheaf ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))) where
  obj _ := M
  map _ := ModuleCat.ofHom
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The constant presheaf of modules, as a functor. -/
def constModuleFunctor (C : Type u₁) [Category.{v₁} C] :
    ModuleCat.{u} A ⥤
      PresheafOfModules.{u} (ringPresheaf ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))) where
  obj M := constModule C M
  map g := { app _ := g }

namespace AdicStages

variable {O I} (D : AdicStages O I)

/-! ### The adic tower of a cartesian presheaf of modules -/

/-- The transition `xₙ ⟶ xₙ₊₁` of the tower of stages. -/
abbrev t (n : ℕ) : D.x.obj n ⟶ D.x.obj (n + 1) := D.x.map (homOfLE (Nat.le_succ n))

/-- The restriction `O(xₙ₊₁) ⟶ O(xₙ)` is surjective. -/
theorem surjective_map_t (n : ℕ) : Function.Surjective (O.map (D.t n).op).hom := by
  intro b
  obtain ⟨a, rfl⟩ := D.surjective_α n b
  refine ⟨D.α (n + 1) a, ?_⟩
  rw [← D.map_comp_α n]
  rfl

/-- The kernel of the restriction `O(xₙ₊₁) ⟶ O(xₙ)` is the image of `Iⁿ`. -/
theorem ker_map_t (n : ℕ) : RingHom.ker (O.map (D.t n).op).hom = (I ^ n).map (D.α (n + 1)) := by
  have h : (RingHom.ker (O.map (D.t n).op).hom).comap (D.α (n + 1)) = I ^ n := by
    rw [← D.ker_α n, ← D.map_comp_α n, RingHom.comap_ker]
  rw [← h, Ideal.map_comap_of_surjective _ (D.surjective_α (n + 1))]

/-- If a presheaf of modules is cartesian along `f`, the adjoint `O(Y) ⊗_{O(X)} 𝓕(X) ⟶ 𝓕(Y)`,
`c ⊗ y ↦ c • 𝓕(f) y`, is an additive bijection. -/
private theorem exists_bijective_adjoint (F : PresheafOfModules.{u} (ringPresheaf O)) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) [IsIso (restrictionBaseChange F f)] :
    ∃ Λ : (letI := (O.map f).hom.toAlgebra; O.obj Y ⊗[O.obj X] F.obj X) →+ F.obj Y,
      (∀ (c : O.obj Y) (y : F.obj X),
        Λ (letI := (O.map f).hom.toAlgebra; c ⊗ₜ[O.obj X] y) = c • (F.map f).hom y) ∧
      Function.Bijective Λ :=
  ⟨{ toFun := restrictionTensorEquiv F f (O.map f) rfl
     map_zero' := restrictionTensorEquiv_zero F f _ rfl
     map_add' := restrictionTensorEquiv_add F f _ rfl },
    fun c y => restrictionTensorEquiv_tmul F f _ rfl c y,
    (restrictionTensorEquiv F f (O.map f) rfl).bijective⟩

variable (F : PresheafOfModules.{u} (ringPresheaf O))

/-- The `A`-module `𝓕(xₙ)`, the `A`-action being through `αₙ`. -/
abbrev towerModule (n : ℕ) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (D.α n)).obj (F.obj (op (D.x.obj n)))

/-- The restriction `𝓕(xₙ₊₁) ⟶ 𝓕(xₙ)`, as a map of `A`-modules. -/
def towerTransition (n : ℕ) : D.towerModule F (n + 1) ⟶ D.towerModule F n :=
  (ModuleCat.restrictScalars (D.α (n + 1))).map (F.map (D.t n).op) ≫
    (ModuleCat.restrictScalarsComp'App (D.α (n + 1)) (O.map (D.t n).op).hom (D.α n)
      (D.map_comp_α n).symm (F.obj (op (D.x.obj n)))).inv

/-- The transition `𝓕(xₙ₊₁) ⟶ 𝓕(xₙ)` acts on elements as the restriction of `𝓕`. -/
theorem towerTransition_apply (n : ℕ) (y : F.obj (op (D.x.obj (n + 1)))) :
    (D.towerTransition F n).hom y = (F.map (D.t n).op).hom y :=
  rfl

variable {F} in
/-- For a presheaf of modules which is cartesian along `xₙ ⟶ xₙ₊₁`, the restriction
`𝓕(xₙ₊₁) ⟶ 𝓕(xₙ)` is surjective with kernel `Iⁿ 𝓕(xₙ₊₁)`. -/
theorem surjective_and_ker_towerTransition (n : ℕ)
    [IsIso (restrictionBaseChange F (D.t n).op)] :
    Function.Surjective (D.towerTransition F n).hom ∧
      ∀ y, (D.towerTransition F n).hom y = 0 ↔
        y ∈ I ^ n • (⊤ : Submodule A (D.towerModule F (n + 1))) := by
  obtain ⟨Λ, hΛ, hbij⟩ := exists_bijective_adjoint F (D.t n).op
  have h := surjective_and_ker_of_bijective (O.map (D.t n).op).hom (D.surjective_map_t n)
    (N := F.obj (op (D.x.obj (n + 1)))) (P := F.obj (op (D.x.obj n)))
    (F.map (D.t n).op).hom.toAddMonoidHom Λ hΛ hbij
  refine ⟨h.1, fun y => (h.2 y).trans ?_⟩
  rw [D.ker_map_t n]
  exact (mem_smul_top_compHom_iff (D.α (n + 1)) (D.surjective_α (n + 1)) (I ^ n) y).symm

/-- **The adic tower `n ↦ 𝓕(xₙ)` of a cartesian presheaf of modules.** -/
def towerObj (hF : cartesianModules O F) : Stacks.Examples.AdicTower.{u, u} A I where
  M n := D.towerModule F n
  π n := D.towerTransition F n
  surjective n :=
    have := hF (D.t n).op
    (D.surjective_and_ker_towerTransition n).1
  ker_π n := by
    have := hF (D.t n).op
    ext y
    exact (D.surjective_and_ker_towerTransition n).2 y

/-- **The adic tower of a cartesian presheaf of modules, as a functor.** -/
def tower :
    (cartesianModules.{u₁, v₁, u, u} O).FullSubcategory ⥤ Stacks.Examples.AdicTower.{u, u} A I where
  obj F := D.towerObj F.obj F.property
  map {F G} φ :=
    { f := fun n => (ModuleCat.restrictScalars (D.α n)).map (φ.hom.app (op (D.x.obj n)))
      comm := fun n => by
        ext y
        exact PresheafOfModules.naturality_apply φ.hom (D.t n).op y }
  map_id _ := rfl
  map_comp _ _ := rfl

end AdicStages

/-- **The constant presheaf of modules is cartesian**: its restriction maps are identities over
identities of rings. -/
theorem cartesianModules_constModule (M : ModuleCat.{u} A) :
    cartesianModules.{u₁, v₁, u, u} ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
      (constModule C M) := by
  intro X Y f
  rw [ConcreteCategory.isIso_iff_bijective]
  refine bijective_of_surjective_of_ker
    (((Functor.const Cᵒᵖ).obj (CommRingCat.of A)).map f).hom (fun a => ⟨a, rfl⟩)
    (N := (constModule C M).obj X) (P := (constModule C M).obj Y) (AddMonoidHom.id M)
    Function.surjective_id
    (fun y => ?_) (restrictionBaseChange.{u₁, v₁, u, u} (constModule C M) f).hom.toAddMonoidHom
    (fun a y => restrictionBaseChange_tmul.{u₁, v₁, u, u} (constModule C M) f a y)
  have hker : RingHom.ker (((Functor.const Cᵒᵖ).obj (CommRingCat.of A)).map f).hom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).1 fun _ _ h => h
  rw [hker, Submodule.bot_smul, Submodule.mem_bot]
  rfl

namespace AdicStages

variable {O I} (D : AdicStages O I)

/-! ### The cartesian presheaf `O ⊗_A M` of an `A`-module -/

/-- **The presheaf `x ↦ O(x) ⊗_A M` of an `A`-module `M`**, as a functor to the cartesian
presheaves of modules: the change of rings along `A ⟶ O` of the constant presheaf with value
`M`. -/
def baseChange : ModuleCat.{u} A ⥤ (cartesianModules.{u₁, v₁, u, u} O).FullSubcategory :=
  ObjectProperty.lift _ (constModuleFunctor C ⋙ ChangeOfRings.changeOfRings D.ringHom)
    (fun M => ChangeOfRings.cartesianModules_changeOfRings D.ringHom _
      (cartesianModules_constModule M))

/-- The map `M ⟶ O(xₙ) ⊗_A M`, `m ↦ 1 ⊗ m`, as a map of `A`-modules. -/
def oneTmul (M : ModuleCat.{u} A) (n : ℕ) :
    M →ₗ[A] D.towerModule (D.baseChange.obj M).obj n where
  toFun m := letI := (D.lam (D.x.obj n)).toAlgebra; (1 : O.obj (op (D.x.obj n))) ⊗ₜ[A] m
  map_add' m m' := by
    let := (D.lam (D.x.obj n)).toAlgebra
    exact tmul_add _ _ _
  map_smul' a m := by
    let := (D.lam (D.x.obj n)).toAlgebra
    have h : (1 : O.obj (op (D.x.obj n))) ⊗ₜ[A] (a • (m : M)) =
        (D.lam (D.x.obj n) a) • ((1 : O.obj (op (D.x.obj n))) ⊗ₜ[A] (m : M)) := by
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one]
      rfl
    have h2 : D.lam (D.x.obj n) a = D.α n a := by rw [D.lam_stage n]
    exact h.trans (congrArg (fun r => r • ((1 : O.obj (op (D.x.obj n))) ⊗ₜ[A] (m : M))) h2)

/-- The map `M ⟶ O(xₙ) ⊗_A M`, `m ↦ 1 ⊗ m`, is surjective. -/
theorem oneTmul_surjective (M : ModuleCat.{u} A) (n : ℕ) : Function.Surjective (D.oneTmul M n) :=
  fun z => by
    have hs : Function.Surjective (D.lam (D.x.obj n)) := by
      rw [D.lam_stage n]; exact D.surjective_α n
    exact exists_one_tmul_eq (D.lam (D.x.obj n)) hs (N := M) z

/-- The kernel of `M ⟶ O(xₙ) ⊗_A M`, `m ↦ 1 ⊗ m`, is `Iⁿ M`. -/
theorem ker_oneTmul (M : ModuleCat.{u} A) (n : ℕ) :
    LinearMap.ker (D.oneTmul M n) = I ^ n • (⊤ : Submodule A M) := by
  have hs : Function.Surjective (D.lam (D.x.obj n)) := by
    rw [D.lam_stage n]; exact D.surjective_α n
  ext m
  rw [LinearMap.mem_ker]
  refine (one_tmul_eq_zero_iff (D.lam (D.x.obj n)) hs (N := M) m).trans ?_
  rw [D.lam_stage n, D.ker_α n]

/-- `O(xₙ) ⊗_A M = M ⧸ Iⁿ M`, as `A`-modules. -/
def quotientEquivTower (M : ModuleCat.{u} A) (n : ℕ) :
    (M ⧸ (I ^ n • (⊤ : Submodule A M))) ≃ₗ[A] D.towerModule (D.baseChange.obj M).obj n :=
  (Submodule.quotEquivOfEq _ _ (D.ker_oneTmul M n).symm).trans
    ((D.oneTmul M n).quotKerEquivOfSurjective (D.oneTmul_surjective M n))

/-- The isomorphism `M ⧸ Iⁿ M ≅ O(xₙ) ⊗_A M` sends the class of `m` to `1 ⊗ m`. -/
theorem quotientEquivTower_mk (M : ModuleCat.{u} A) (n : ℕ) (m : M) :
    D.quotientEquivTower M n (Submodule.Quotient.mk m) = D.oneTmul M n m :=
  rfl

/-! ### The adic tower of `O ⊗_A lim Mₙ` is `(Mₙ)` -/

open Stacks.Examples

/-- An isomorphism of adic towers from isomorphisms of the levels commuting with the
transitions. -/
def towerIsoMk {S T : AdicTower.{u, u} A I} (e : ∀ n, S.M n ≅ T.M n)
    (comm : ∀ n, S.π n ≫ (e n).hom = (e (n + 1)).hom ≫ T.π n) : S ≅ T where
  hom := ⟨fun n => (e n).hom, comm⟩
  inv := ⟨fun n => (e n).inv, fun n => by
    rw [Iso.comp_inv_eq, Category.assoc, comm, Iso.inv_hom_id_assoc]⟩
  hom_inv_id := AdicTower.Hom.ext (funext fun n => (e n).hom_inv_id)
  inv_hom_id := AdicTower.Hom.ext (funext fun n => (e n).inv_hom_id)

variable (hI : I.FG)

/-- The level `n` of the adic tower of `O ⊗_A lim Sₙ` is `Sₙ`: both are `(lim Sₙ) ⧸ Iⁿ`, by
Stacks 09B8 and by `O(xₙ) = A ⧸ Iⁿ`. -/
def towerBaseChangeLimitIso (S : AdicTower.{u, u} A I) (n : ℕ) :
    S.M n ≅ D.towerModule (D.baseChange.obj S.limitModule).obj n :=
  ((S.toInverseSystem.quotientEquiv hI n).symm.trans
    (D.quotientEquivTower S.limitModule n)).toModuleIso

/-- The isomorphism `Sₙ ≅ O(xₙ) ⊗_A lim Sₙ` sends the `n`-th projection of `m` to `1 ⊗ m`. -/
theorem towerBaseChangeLimitIso_limitProj (S : AdicTower.{u, u} A I) (n : ℕ)
    (m : S.limitSubmodule) :
    (D.towerBaseChangeLimitIso hI S n).hom (S.limitProj n m) =
      D.oneTmul S.limitModule n m := by
  have hsymm : (S.toInverseSystem.quotientEquiv hI n).symm (S.limitProj n m)
      = (Submodule.Quotient.mk m :
          S.limitSubmodule ⧸ (I ^ n • (⊤ : Submodule A S.limitSubmodule))) :=
    (LinearEquiv.symm_apply_eq _).2 rfl
  show D.quotientEquivTower S.limitModule n ((S.toInverseSystem.quotientEquiv hI n).symm
    (S.limitProj n m)) = _
  rw [hsymm]
  rfl

/-- The tower of `O ⊗_A lim Sₙ` is isomorphic to the adic tower `(Sₙ)`. -/
def towerBaseChangeLimit (S : AdicTower.{u, u} A I) :
    S ≅ D.tower.obj (D.baseChange.obj S.limitModule) :=
  towerIsoMk (D.towerBaseChangeLimitIso hI S) fun n => by
    ext y
    obtain ⟨m, rfl⟩ := S.limitProj_surjective (n + 1) y
    change (D.towerBaseChangeLimitIso hI S n).hom ((S.π n).hom (S.limitProj (n + 1) m)) =
      (D.towerTransition _ n).hom ((D.towerBaseChangeLimitIso hI S (n + 1)).hom
        (S.limitProj (n + 1) m))
    rw [S.π_limitProj, towerBaseChangeLimitIso_limitProj, towerBaseChangeLimitIso_limitProj]
    let := (D.lam (D.x.obj n)).toAlgebra
    let := (D.lam (D.x.obj (n + 1))).toAlgebra
    have h := ChangeOfRings.cofMap_tmul D.ringHom (constModule C S.limitModule) (D.t n).op 1 m
    refine Eq.trans ?_ h.symm
    exact congrArg (fun r => r ⊗ₜ[A] (m : S.limitModule)) (map_one (O.map (D.t n).op).hom).symm

/-- The isomorphism between `(Sₙ)` and the tower of `O ⊗_A lim Sₙ` is natural in `S`. -/
theorem towerBaseChangeLimit_naturality {S S' : AdicTower.{u, u} A I} (φ : S ⟶ S') :
    (D.towerBaseChangeLimit hI S).hom ≫
        D.tower.map (D.baseChange.map (ModuleCat.ofHom (AdicTower.limitMap φ))) =
      φ ≫ (D.towerBaseChangeLimit hI S').hom := by
  refine AdicTower.Hom.ext (funext fun n => ?_)
  ext y
  obtain ⟨m, rfl⟩ := S.limitProj_surjective n y
  have h1 := D.towerBaseChangeLimitIso_limitProj hI S n m
  have h2 := D.towerBaseChangeLimitIso_limitProj hI S' n (AdicTower.limitMap φ m)
  let := (D.lam (D.x.obj n)).toAlgebra
  have h3 := ChangeOfRings.cofHom_app_tmul D.ringHom (G := constModule C S.limitModule)
    (H := constModule C S'.limitModule)
    ((constModuleFunctor C).map (ModuleCat.ofHom (AdicTower.limitMap φ))) (op (D.x.obj n)) 1 m
  refine Eq.trans (congrArg (fun z => ((ChangeOfRings.cofHom D.ringHom ((constModuleFunctor C).map
    (ModuleCat.ofHom (AdicTower.limitMap φ)))).app (op (D.x.obj n))).hom z) h1) ?_
  exact h3.trans h2.symm

/-! ### The comparison `O ⊗_A lim 𝓕(xₙ) ⟶ 𝓕` -/

/-- The restriction of a presheaf of modules along an identity is the identity on elements. -/
theorem map_id_apply (F : PresheafOfModules.{u} (ringPresheaf O)) (X : Cᵒᵖ) (y : F.obj X) :
    (F.map (𝟙 X)).hom y = y := by
  rw [F.map_id]
  rfl

variable (F : (cartesianModules.{u₁, v₁, u, u} O).FullSubcategory)

/-- The `n`-th component of an element of `lim 𝓕(xₙ)`, as a section of `𝓕` over `xₙ`. -/
def component (m : (D.tower.obj F).limitSubmodule) (n : ℕ) : F.obj.obj (op (D.x.obj n)) :=
  (D.tower.obj F).limitProj n m

/-- The restriction along `xₙ ⟶ xₙ₊₁` of the `(n + 1)`-th component of an element of `lim 𝓕(xₙ)`
is its `n`-th component. -/
theorem component_succ (m : (D.tower.obj F).limitSubmodule) (n : ℕ) :
    (F.obj.map (D.t n).op).hom (D.component F m (n + 1)) = D.component F m n :=
  (D.tower.obj F).π_limitProj n m

/-- The restriction along `xₙ ⟶ x_N` of the `N`-th component of an element of `lim 𝓕(xₙ)` is its
`n`-th component. -/
theorem map_component_of_le (m : (D.tower.obj F).limitSubmodule) {n N : ℕ} (h : n ≤ N) :
    (F.obj.map (D.x.map (homOfLE h)).op).hom (D.component F m N) = D.component F m n := by
  induction N, h using Nat.le_induction with
  | base =>
    rw [show homOfLE (le_refl n) = 𝟙 n from rfl, D.x.map_id, op_id, map_id_apply]
  | succ N hnN ih =>
    have hc : (D.x.map (homOfLE (hnN.trans (Nat.le_succ N)))).op =
        (D.t N).op ≫ (D.x.map (homOfLE hnN)).op := by
      rw [← op_comp, ← D.x.map_comp]
      rfl
    rw [hc, ChangeOfRings.G_map_comp_apply, component_succ, ih]

/-- **The components of an element of `lim 𝓕(xₙ)` restrict compatibly**: for any two maps
`x ⟶ xₙ`, `x ⟶ xₙ'` from an object to stages, the restrictions of the `n`-th and the `n'`-th
components to `x` agree. -/
theorem map_component_eq (m : (D.tower.obj F).limitSubmodule) {c : C} {n n' : ℕ}
    (g : c ⟶ D.x.obj n) (g' : c ⟶ D.x.obj n') :
    (F.obj.map g.op).hom (D.component F m n) = (F.obj.map g'.op).hom (D.component F m n') := by
  refine D.eq_of_stage_maps (fun n g => (F.obj.map g.op).hom (D.component F m n))
    (fun hle g => ?_) g g'
  beta_reduce
  rw [op_comp, ChangeOfRings.G_map_comp_apply, D.map_component_of_le F m hle]

/-- The map `lim 𝓕(xₙ) ⟶ 𝓕(x)`, `m ↦ 𝓕(g)(mₙ)` for the chosen `g : x ⟶ xₙ`. -/
def sectionAt (X : Cᵒᵖ) (m : (D.tower.obj F).limitSubmodule) : F.obj.obj X :=
  (F.obj.map (D.toStage X.unop).op).hom (D.component F m (D.stage X.unop))

/-- The map `lim 𝓕(xₙ) ⟶ 𝓕(x)` is additive. -/
theorem sectionAt_add (X : Cᵒᵖ) (m m' : (D.tower.obj F).limitSubmodule) :
    D.sectionAt F X (m + m') = D.sectionAt F X m + D.sectionAt F X m' :=
  (congrArg (F.obj.map (D.toStage X.unop).op).hom
    (((D.tower.obj F).limitProj (D.stage X.unop)).map_add m m')).trans (map_add _ _ _)

/-- The map `lim 𝓕(xₙ) ⟶ 𝓕(x)` is `A`-linear, `A` acting on `𝓕(x)` through `A ⟶ O(x)`. -/
theorem sectionAt_smul (X : Cᵒᵖ) (a : A) (m : (D.tower.obj F).limitSubmodule) :
    D.sectionAt F X (a • m) = D.lam X.unop a • D.sectionAt F X m :=
  (congrArg (F.obj.map (D.toStage X.unop).op).hom
    (((D.tower.obj F).limitProj (D.stage X.unop)).map_smul a m)).trans
    ((F.obj.map (D.toStage X.unop).op).hom.map_smul (D.α (D.stage X.unop) a) _)

/-- The maps `lim 𝓕(xₙ) ⟶ 𝓕(x)` commute with the restrictions of `𝓕`. -/
theorem map_sectionAt {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : (D.tower.obj F).limitSubmodule) :
    (F.obj.map f).hom (D.sectionAt F X m) = D.sectionAt F Y m := by
  unfold sectionAt
  rw [← ChangeOfRings.G_map_comp_apply]
  exact D.map_component_eq F m (f.unop ≫ D.toStage X.unop) (D.toStage Y.unop)

/-- The maps `lim 𝓕(xₙ) ⟶ 𝓕(x)`, as a morphism from the constant presheaf of `A`-modules to `𝓕`
regarded as a presheaf of `A`-modules. -/
def limitToSections :
    constModule C (D.tower.obj F).limitModule ⟶
      (ChangeOfRings.restrictScalars D.ringHom).obj F.obj where
  app X := ModuleCat.ofHom (X := (D.tower.obj F).limitSubmodule)
    (Y := ((ChangeOfRings.restrictScalars D.ringHom).obj F.obj).obj X)
    { toFun := D.sectionAt F X
      map_add' := D.sectionAt_add F X
      map_smul' := D.sectionAt_smul F X }
  naturality {_ _} f :=
    ModuleCat.hom_ext (LinearMap.ext fun m => (D.map_sectionAt F f m).symm)

/-- **The comparison `O ⊗_A lim 𝓕(xₙ) ⟶ 𝓕`**, `u ⊗ m ↦ u • 𝓕(g)(mₙ)` at an object `x` with a map
`g : x ⟶ xₙ` to a stage. -/
def comparison : D.baseChange.obj (D.tower.obj F).limitModule ⟶ F :=
  ObjectProperty.homMk (ChangeOfRings.counitHom D.ringHom (D.limitToSections F))

/-- **The comparison is an isomorphism at every object**: at `x` with `g : x ⟶ xₙ` it is
`O(x) ⊗_A M = O(x) ⊗_{O(xₙ)} (M ⧸ Iⁿ M) = O(x) ⊗_{O(xₙ)} 𝓕(xₙ) = 𝓕(x)`, by Stacks 09B8 and
the cartesian condition. -/
theorem bijective_comparison_app (hI : I.FG) (X : Cᵒᵖ) :
    Function.Bijective ((D.comparison F).hom.app X).hom := by
  have := F.property (D.toStage X.unop).op
  let S := D.tower.obj F
  let k := D.stage X.unop
  let g := D.toStage X.unop
  obtain ⟨Γ, hΓ, hΓbij⟩ := exists_bijective_adjoint F.obj g.op
  refine bijective_tensor_of_stage (D.α k) (D.surjective_α k) (O.map g.op).hom
    (M := S.limitSubmodule) (P := F.obj.obj (op (D.x.obj k))) (Q := F.obj.obj X)
    { toFun := fun m => D.component F m k
      map_zero' := (S.limitProj k).map_zero
      map_add' := (S.limitProj k).map_add } (fun a m => (S.limitProj k).map_smul a m)
    (S.limitProj_surjective k) (fun m => ?_) (F.obj.map g.op).hom.toAddMonoidHom Γ hΓ hΓbij
    (ChangeOfRings.counitApp D.ringHom (D.limitToSections F) X).hom.toAddMonoidHom
    (fun a m => ChangeOfRings.counitApp_tmul D.ringHom (D.limitToSections F) X a m)
  rw [D.ker_α k]
  exact (Submodule.ext_iff.1 (S.toInverseSystem.ker_proj hI k) m)

/-- The comparison `O ⊗_A lim 𝓕(xₙ) ≅ 𝓕`, as an isomorphism of cartesian presheaves. -/
def comparisonIso (hI : I.FG) : D.baseChange.obj (D.tower.obj F).limitModule ≅ F :=
  ObjectProperty.isoMk _
    (PresheafOfModules.isoMk
      (fun X => (LinearEquiv.ofBijective ((D.comparison F).hom.app X).hom
        (D.bijective_comparison_app F hI X)).toModuleIso)
      (fun _ _ f => (D.comparison F).hom.naturality f))

/-- The forward morphism of `comparisonIso` is `comparison`. -/
theorem comparisonIso_hom (hI : I.FG) : (D.comparisonIso F hI).hom = D.comparison F :=
  rfl

variable {F} in
/-- The maps `lim 𝓕(xₙ) ⟶ 𝓕(x)` are natural in the cartesian presheaf `𝓕`. -/
theorem sectionAt_limitMap {G : (cartesianModules.{u₁, v₁, u, u} O).FullSubcategory} (h : F ⟶ G)
    (X : Cᵒᵖ) (m : (D.tower.obj F).limitSubmodule) :
    D.sectionAt G X (AdicTower.limitMap (D.tower.map h) m) =
      (h.hom.app X).hom (D.sectionAt F X m) :=
  (PresheafOfModules.naturality_apply h.hom (D.toStage X.unop).op
    (D.component F m (D.stage X.unop))).symm

variable {F} in
/-- The comparison is natural in the cartesian presheaf. -/
theorem comparison_naturality {G : (cartesianModules.{u₁, v₁, u, u} O).FullSubcategory}
    (h : F ⟶ G) :
    D.baseChange.map (ModuleCat.ofHom (AdicTower.limitMap (D.tower.map h))) ≫ D.comparison G =
      D.comparison F ≫ h := by
  refine ObjectProperty.hom_ext _ (PresheafOfModules.hom_ext fun X =>
    ModuleCat.hom_ext (LinearMap.ext fun z => ?_))
  let := (D.lam X.unop).toAlgebra
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add z z' hz hz' => exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hz hz').trans
      (map_add _ _ _).symm)
  | tmul a m =>
    have e1 := ChangeOfRings.cofHom_app_tmul D.ringHom
      (G := constModule C (D.tower.obj F).limitModule)
      (H := constModule C (D.tower.obj G).limitModule)
      ((constModuleFunctor C).map (ModuleCat.ofHom (AdicTower.limitMap (D.tower.map h)))) X a m
    have e2 := ChangeOfRings.counitApp_tmul D.ringHom (D.limitToSections G) X a
      (AdicTower.limitMap (D.tower.map h) m)
    have e3 := ChangeOfRings.counitApp_tmul D.ringHom (D.limitToSections F) X a m
    refine (congrArg (ChangeOfRings.counitApp D.ringHom (D.limitToSections G) X).hom e1).trans ?_
    refine e2.trans ?_
    refine (congrArg (fun y => a • y) (D.sectionAt_limitMap h X m)).trans ?_
    refine ((h.hom.app X).hom.map_smul a (D.sectionAt F X m)).symm.trans ?_
    exact congrArg (h.hom.app X).hom e3.symm

/-! ### The equivalence -/

/-- **Cartesian presheaves of modules over an adic stage system are adic towers.** The functor
is `𝓕 ↦ (𝓕(xₙ))ₙ`; its inverse is `(Mₙ) ↦ O ⊗_A lim Mₙ`. -/
def cartesianEquivalence (hI : I.FG) :
    (cartesianModules.{u₁, v₁, u, u} O).FullSubcategory ≌ AdicTower.{u, u} A I :=
  CategoryTheory.Equivalence.mk D.tower
    (AdicTower.limitFunctor hI ⋙ ObjectProperty.ι _ ⋙ D.baseChange)
    (NatIso.ofComponents (fun F => (D.comparisonIso F hI).symm) fun {F G} h => by
      change h ≫ (D.comparisonIso G hI).inv =
        (D.comparisonIso F hI).inv ≫
          D.baseChange.map (ModuleCat.ofHom (AdicTower.limitMap (D.tower.map h)))
      rw [Iso.comp_inv_eq, Category.assoc, comparisonIso_hom, comparison_naturality,
        ← comparisonIso_hom D F hI, Iso.inv_hom_id_assoc])
    (NatIso.ofComponents (fun S => (D.towerBaseChangeLimit hI S).symm) fun {S S'} φ => by
      change D.tower.map (D.baseChange.map (ModuleCat.ofHom (AdicTower.limitMap φ))) ≫
          (D.towerBaseChangeLimit hI S').inv = (D.towerBaseChangeLimit hI S).inv ≫ φ
      rw [Iso.comp_inv_eq, Category.assoc, ← D.towerBaseChangeLimit_naturality hI φ,
        Iso.inv_hom_id_assoc])

/-- **Cartesian presheaves of modules over an adic stage system are the `I`-adically complete
`A`-modules**, for `I` finitely generated: the composite of `cartesianEquivalence` with the
equivalence `lim : AdicTower ≌ complete modules` of Stacks 09B8. -/
def cartesianEquivalenceComplete (hI : I.FG) :
    (cartesianModules.{u₁, v₁, u, u} O).FullSubcategory ≌ IAdicallyCompleteModuleCat.{u} A I :=
  (D.cartesianEquivalence hI).trans (AdicTower.limitEquivalence hI)

end AdicStages

end Stacks.PresheafOfModules

end
