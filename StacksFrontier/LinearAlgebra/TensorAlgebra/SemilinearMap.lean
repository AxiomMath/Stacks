module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorAlgebra.Grading

/-!
# Base change of the tensor and exterior algebras along a ring homomorphism

Let `φ : R →+* S` be a homomorphism of commutative rings and let `u : M →ₛₗ[φ] N` be a
`φ`-semilinear map from an `R`-module to an `S`-module. We construct the induced ring
homomorphisms `TensorAlgebra R M →+* TensorAlgebra S N` and
`ExteriorAlgebra R M →+* ExteriorAlgebra S N`, and show that each carries the degree-`n`
homogeneous piece of the source into the degree-`n` homogeneous piece of the target.

## Main definitions

* `TensorAlgebra.algebraOfRingHom` and `ExteriorAlgebra.algebraOfRingHom`: `TensorAlgebra S N`
  respectively `ExteriorAlgebra S N` viewed as an `R`-algebra along `φ : R →+* S`.
* `TensorAlgebra.ιCompₛₗ` and `ExteriorAlgebra.ιCompₛₗ`: the degree-one generator of the target
  algebra, read along `u` as an `R`-linear map on `M`.
* `TensorAlgebra.mapₛₗ` and `ExteriorAlgebra.mapₛₗ`: the base change maps, as ring
  homomorphisms.
* `TensorAlgebra.gradedPiece`: the degree-`n` homogeneous piece of the tensor algebra.
* `TensorAlgebra.powMapₛₗ` and `ExteriorAlgebra.powMapₛₗ`: the restrictions of the base change
  maps to the degree-`n` pieces, as semilinear maps.
* `TensorAlgebra.liftRing` and `ExteriorAlgebra.liftRing`: the extension of a linear map
  `γ : M →ₗ[R] T` into a semiring carrying a compatible `R`-module structure (with square-zero
  values in the exterior case) to a ring homomorphism out of the algebra.

## Main results

* `TensorAlgebra.mapₛₗ_ι`, `TensorAlgebra.mapₛₗ_algebraMap` and their exterior analogues: the
  values of the base change map on generators and scalars.
* `ExteriorAlgebra.mapₛₗ_ιMulti` and `ExteriorAlgebra.powMapₛₗ_ιMulti`: base change carries the
  wedge of a family of vectors to the wedge of their images.
* `ExteriorAlgebra.powMapₛₗ_ext`: two semilinear maps out of `⋀[R]^n M` agreeing on wedges are
  equal.
* `TensorAlgebra.mapₛₗ_eq_comp`, `TensorAlgebra.mapₛₗ_eq_self` and their exterior analogues:
  functoriality of base change.
* `TensorAlgebra.mapₛₗ_mem_pow_range_ι` and `ExteriorAlgebra.mapₛₗ_mem_exteriorPower`: base
  change respects the `ℕ`-grading.
* `TensorAlgebra.pow_range_ι_eq_span_prod_ι`: the degree-`n` piece of the tensor algebra is
  spanned by the ordered products of `n` degree-one generators.
* `TensorAlgebra.liftRing_ι`, `TensorAlgebra.liftRing_smul`, `TensorAlgebra.liftRing_prod_ι`
  and their exterior analogues: the equations characterizing `liftRing`.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public section

/-- A ring homomorphism carrying the `i`-th factors of an ordered product to those of another
carries the product to the product. -/
private theorem map_ofFn_prod {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B) {n : ℕ}
    (a : Fin n → A) (b : Fin n → B) (h : ∀ i, f (a i) = b i) :
    f (List.ofFn a).prod = (List.ofFn b).prod := by
  rw [map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, h]

/-- A ring homomorphism compatible with scalars and generators carries the `n`-th power of the
range of one generator map into that of the other. -/
private theorem map_mem_pow_range {R S M N A B : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra S B] (ιA : M →ₗ[R] A) (ιB : N →ₗ[S] B) (f : A →+* B) (φ : R →+* S)
    (u : M →ₛₗ[φ] N) (h₀ : ∀ r, f (algebraMap R A r) = algebraMap S B (φ r))
    (h₁ : ∀ m, f (ιA m) = ιB (u m)) (n : ℕ) {x : A} (hx : x ∈ LinearMap.range ιA ^ n) :
    f x ∈ LinearMap.range ιB ^ n := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => rw [h₀, pow_zero]; exact Submodule.algebraMap_mem _
  | add x y i _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | mem_mul m hm i x _ ih =>
      obtain ⟨m₀, rfl⟩ := hm
      rw [map_mul, h₁, pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ (u m₀)) ih

namespace TensorAlgebra

/-! ### Base change of the tensor algebra -/

section BaseChange

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]
  {M : Type*} [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module S N]

/-- `TensorAlgebra S N` viewed as an `R`-algebra by restricting scalars along a ring
homomorphism `φ : R →+* S`. -/
@[instance_reducible]
noncomputable def algebraOfRingHom (φ : R →+* S) : Algebra R (TensorAlgebra S N) :=
  ((algebraMap S (TensorAlgebra S N)).comp φ).toAlgebra' fun c x => Algebra.commutes (φ c) x

/-- The degree-one generator of `TensorAlgebra S N`, read along a semilinear map
`u : M →ₛₗ[φ] N` as an `R`-linear map on `M`, where `R` acts through `φ`. -/
noncomputable def ιCompₛₗ (φ : R →+* S) (u : M →ₛₗ[φ] N) :
    letI := algebraOfRingHom (N := N) φ
    M →ₗ[R] TensorAlgebra S N :=
  letI := algebraOfRingHom (N := N) φ
  { toFun := fun m => TensorAlgebra.ι S (u m)
    map_add' := fun m m' => by rw [map_add, map_add]
    map_smul' := fun r m => by
      change TensorAlgebra.ι S (u (r • m)) = r • TensorAlgebra.ι S (u m)
      rw [map_smulₛₗ, map_smul, Algebra.smul_def, Algebra.smul_def]
      rfl }

/-- A ring homomorphism `φ : R →+* S` together with a
`φ`-semilinear map `u : M →ₛₗ[φ] N` induces a ring homomorphism
`TensorAlgebra R M →+* TensorAlgebra S N` carrying `ι R m` to `ι S (u m)`. -/
noncomputable def mapₛₗ (φ : R →+* S) (u : M →ₛₗ[φ] N) :
    TensorAlgebra R M →+* TensorAlgebra S N :=
  letI := algebraOfRingHom (N := N) φ
  (TensorAlgebra.lift R (ιCompₛₗ φ u)).toRingHom

/-- Base change carries the generator `ι R m` to `ι S (u m)`. -/
@[simp]
theorem mapₛₗ_ι (φ : R →+* S) (u : M →ₛₗ[φ] N) (m : M) :
    mapₛₗ φ u (TensorAlgebra.ι R m) = TensorAlgebra.ι S (u m) :=
  let := algebraOfRingHom (N := N) φ
  TensorAlgebra.lift_ι_apply (ιCompₛₗ φ u) m

/-- Base change carries the scalar `r` to the scalar `φ r`. -/
@[simp]
theorem mapₛₗ_algebraMap (φ : R →+* S) (u : M →ₛₗ[φ] N) (r : R) :
    mapₛₗ φ u (algebraMap R (TensorAlgebra R M) r) =
      algebraMap S (TensorAlgebra S N) (φ r) :=
  let := algebraOfRingHom (N := N) φ
  (TensorAlgebra.lift R (ιCompₛₗ φ u)).commutes r

/-- Two ring homomorphisms out of a tensor algebra agree as soon as they agree on the image of
the base ring and on the degree-one generators. -/
theorem ringHom_ext {T : Type*} [Semiring T] {f g : TensorAlgebra R M →+* T}
    (h₁ : ∀ r : R, f (algebraMap R (TensorAlgebra R M) r) =
      g (algebraMap R (TensorAlgebra R M) r))
    (h₂ : ∀ m : M, f (TensorAlgebra.ι R m) = g (TensorAlgebra.ι R m)) : f = g := by
  refine RingHom.ext fun x => ?_
  induction x using TensorAlgebra.induction with
  | algebraMap r => exact h₁ r
  | ι m => exact h₂ m
  | mul x y hx hy => rw [map_mul, map_mul, hx, hy]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Base change is semilinear along `φ`. -/
theorem mapₛₗ_smul (φ : R →+* S) (u : M →ₛₗ[φ] N) (r : R) (x : TensorAlgebra R M) :
    mapₛₗ φ u (r • x) = φ r • mapₛₗ φ u x := by
  rw [Algebra.smul_def, map_mul, mapₛₗ_algebraMap, Algebra.smul_def]

/-- Base change along `χ = ψ ∘ φ` and `v = w ∘ u` is the composite of the base changes along
`φ, u` and `ψ, w`. -/
theorem mapₛₗ_eq_comp {T : Type*} [CommSemiring T] {P : Type*} [AddCommMonoid P] [Module T P]
    {φ : R →+* S} {ψ : S →+* T} {χ : R →+* T} (u : M →ₛₗ[φ] N) (w : N →ₛₗ[ψ] P)
    (v : M →ₛₗ[χ] P) (hχ : ∀ r, χ r = ψ (φ r)) (hv : ∀ m, v m = w (u m))
    (x : TensorAlgebra R M) : mapₛₗ χ v x = mapₛₗ ψ w (mapₛₗ φ u x) :=
  RingHom.congr_fun (ringHom_ext (f := mapₛₗ χ v) (g := (mapₛₗ ψ w).comp (mapₛₗ φ u))
    (fun r => by simp [hχ]) fun m => by simp [hv]) x

/-- Base change along maps that are pointwise the identity is the identity. -/
theorem mapₛₗ_eq_self {φ : R →+* R} (u : M →ₛₗ[φ] M) (hφ : ∀ r, φ r = r) (hu : ∀ m, u m = m)
    (x : TensorAlgebra R M) : mapₛₗ φ u x = x :=
  RingHom.congr_fun (ringHom_ext (f := mapₛₗ φ u) (g := RingHom.id (TensorAlgebra R M))
    (fun r => by simp [hφ]) fun m => by simp [hu]) x

/-- Base change carries the `n`-th power of the range of `TensorAlgebra.ι R` into the `n`-th power
of the range of `TensorAlgebra.ι S`. -/
theorem mapₛₗ_mem_pow_range_ι (φ : R →+* S) (u : M →ₛₗ[φ] N) (n : ℕ)
    {x : TensorAlgebra R M}
    (hx : x ∈ LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ n) :
    mapₛₗ φ u x ∈
      LinearMap.range (TensorAlgebra.ι S : N →ₗ[S] TensorAlgebra S N) ^ n := by
  exact map_mem_pow_range _ _ (mapₛₗ φ u) φ u (mapₛₗ_algebraMap φ u) (mapₛₗ_ι φ u) n hx

/-- The degree-`n` homogeneous piece of the tensor algebra: the `n`-th power of the range of
`TensorAlgebra.ι`, the `n`-th tensor power of `M` realized inside `TensorAlgebra R M`. -/
abbrev gradedPiece (R : Type*) [CommSemiring R] (n : ℕ) (M : Type*) [AddCommMonoid M]
    [Module R M] : Submodule R (TensorAlgebra R M) :=
  LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ n

/-- `1` lies in the degree-zero piece of the tensor algebra. -/
theorem one_mem_gradedPiece : (1 : TensorAlgebra R M) ∈ gradedPiece R 0 M := by
  rw [gradedPiece, pow_zero]
  exact Submodule.mem_one.2 ⟨1, map_one _⟩

/-- The generators lie in the degree-one piece of the tensor algebra. -/
theorem ι_mem_gradedPiece (m : M) : TensorAlgebra.ι R m ∈ gradedPiece R 1 M := by
  rw [gradedPiece, pow_one]
  exact LinearMap.mem_range_self _ m

/-- The degree-`i` and degree-`j` pieces multiply into the degree-`i + j` piece. -/
theorem mul_mem_gradedPiece {i j : ℕ} {x y : TensorAlgebra R M} (hx : x ∈ gradedPiece R i M)
    (hy : y ∈ gradedPiece R j M) : x * y ∈ gradedPiece R (i + j) M := by
  rw [gradedPiece, pow_add]
  exact Submodule.mul_mem_mul hx hy

/-- The restriction of
`TensorAlgebra.mapₛₗ φ u` to the degree-`n` pieces, as a `φ`-semilinear map. -/
noncomputable def powMapₛₗ (n : ℕ) (φ : R →+* S) (u : M →ₛₗ[φ] N) :
    gradedPiece R n M →ₛₗ[φ] gradedPiece S n N where
  toFun x := ⟨mapₛₗ φ u x, mapₛₗ_mem_pow_range_ι φ u n x.2⟩
  map_add' x y := Subtype.ext (map_add (mapₛₗ φ u) x.1 y.1)
  map_smul' r x := Subtype.ext (mapₛₗ_smul φ u r x)

/-- The underlying element of `powMapₛₗ n φ u x` is `mapₛₗ φ u x`. -/
@[simp]
theorem powMapₛₗ_coe (n : ℕ) (φ : R →+* S) (u : M →ₛₗ[φ] N) (x : gradedPiece R n M) :
    (powMapₛₗ n φ u x : TensorAlgebra S N) = mapₛₗ φ u x := rfl

/-- An ordered product of `n` degree-one generators lies in the degree-`n` homogeneous piece. -/
theorem prod_ι_mem_pow_range_ι {n : ℕ} (s : Fin n → M) :
    (List.ofFn fun i => TensorAlgebra.ι R (s i)).prod ∈
      LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ n := by
  induction n with
  | zero => simpa only [List.ofFn_zero, List.prod_nil, pow_zero] using Submodule.one_le.mp le_rfl
  | succ n ih =>
      rw [List.ofFn_succ, List.prod_cons, pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ (s 0)) (ih _)

/-- The degree-`n` piece of the tensor algebra is spanned by the ordered products of `n`
degree-one generators. -/
theorem pow_range_ι_eq_span_prod_ι (n : ℕ) :
    LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ n =
      Submodule.span R
        (Set.range fun s : Fin n → M => (List.ofFn fun i => TensorAlgebra.ι R (s i)).prod) := by
  refine le_antisymm ?_ (Submodule.span_le.mpr ?_)
  · induction n with
    | zero =>
        rw [pow_zero, Submodule.one_eq_span]
        exact Submodule.span_le.mpr fun x hx => by
          rw [Set.mem_singleton_iff] at hx
          exact Submodule.subset_span ⟨fun i => (i.elim0 : M), by simp [hx]⟩
    | succ n ih =>
        rw [pow_succ']
        refine Submodule.mul_le.mpr fun a ha b hb => ?_
        obtain ⟨m, rfl⟩ := ha
        have key : ∀ y ∈ Submodule.span R
            (Set.range fun s : Fin n → M => (List.ofFn fun i => TensorAlgebra.ι R (s i)).prod),
            TensorAlgebra.ι R m * y ∈ Submodule.span R
              (Set.range fun s : Fin (n + 1) → M =>
                (List.ofFn fun i => TensorAlgebra.ι R (s i)).prod) := by
          intro y hy
          induction hy using Submodule.span_induction with
          | mem z hz =>
              obtain ⟨s, rfl⟩ := hz
              exact Submodule.subset_span ⟨Fin.cons m s, by simp [List.ofFn_succ]⟩
          | zero => simpa only [mul_zero] using Submodule.zero_mem _
          | add y z _ _ hy hz => simpa only [mul_add] using Submodule.add_mem _ hy hz
          | smul r y _ hy => simpa only [Algebra.mul_smul_comm] using Submodule.smul_mem _ r hy
        exact key b (ih hb)
  · rintro _ ⟨s, rfl⟩
    exact prod_ι_mem_pow_range_ι s

end BaseChange

/-! ### Lifting into a ring with a compatible module structure -/

section LiftRing

variable {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  {T : Type*} [Semiring T] [Module R T]
  {h₁ : ∀ (r : R) (x y : T), r • x * y = r • (x * y)}
  {h₂ : ∀ (r : R) (x y : T), x * r • y = r • (x * y)}
  {γ : M →ₗ[R] T}

/-- A linear map `γ : M →ₗ[R] T` into a semiring `T` carrying an `R`-module structure compatible
with its multiplication extends to an `R`-linear ring homomorphism `TensorAlgebra R M →+* T`
carrying `ι R m` to `γ m`. -/
theorem exists_liftRing
    (h₁ : ∀ (r : R) (x y : T), r • x * y = r • (x * y))
    (h₂ : ∀ (r : R) (x y : T), x * r • y = r • (x * y))
    (γ : M →ₗ[R] T) :
    ∃ Φ : TensorAlgebra R M →+* T,
      (∀ m : M, Φ (TensorAlgebra.ι R m) = γ m) ∧
        ∀ (r : R) (x : TensorAlgebra R M), Φ (r • x) = r • Φ x := by
  let _ : Algebra R T := Algebra.ofModule h₁ h₂
  refine ⟨(TensorAlgebra.lift R γ).toRingHom, TensorAlgebra.lift_ι_apply γ, fun r x => ?_⟩
  change (TensorAlgebra.lift R γ) (r • x) = r • (TensorAlgebra.lift R γ) x
  rw [Algebra.smul_def, map_mul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, h₁, one_mul]

/-- The ring homomorphism `TensorAlgebra R M →+* T` extending a linear map into a semiring with a
compatible module structure; see `TensorAlgebra.exists_liftRing`. -/
noncomputable def liftRing
    (h₁ : ∀ (r : R) (x y : T), r • x * y = r • (x * y))
    (h₂ : ∀ (r : R) (x y : T), x * r • y = r • (x * y))
    (γ : M →ₗ[R] T) : TensorAlgebra R M →+* T :=
  (exists_liftRing h₁ h₂ γ).choose

/-- `liftRing` carries the generator `ι R m` to `γ m`. -/
@[simp]
theorem liftRing_ι (m : M) : liftRing h₁ h₂ γ (TensorAlgebra.ι R m) = γ m :=
  (exists_liftRing h₁ h₂ γ).choose_spec.1 m

/-- `liftRing` is `R`-linear. -/
theorem liftRing_smul (r : R) (x : TensorAlgebra R M) :
    liftRing h₁ h₂ γ (r • x) = r • liftRing h₁ h₂ γ x :=
  (exists_liftRing h₁ h₂ γ).choose_spec.2 r x

/-- The value of `liftRing` on an ordered product of degree-one generators is the corresponding
ordered product in the target. -/
theorem liftRing_prod_ι {n : ℕ} (s : Fin n → M) :
    liftRing h₁ h₂ γ (List.ofFn fun i => TensorAlgebra.ι R (s i)).prod =
      (List.ofFn fun i => γ (s i)).prod := by
  exact map_ofFn_prod _ _ _ fun i => liftRing_ι _

end LiftRing

end TensorAlgebra

namespace ExteriorAlgebra

/-! ### Base change of the exterior algebra -/

section BaseChange

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S]
  {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module S N]

/-- `ExteriorAlgebra S N` viewed as an `R`-algebra by restricting scalars along a ring
homomorphism `φ : R →+* S`. -/
@[instance_reducible]
noncomputable def algebraOfRingHom (φ : R →+* S) : Algebra R (ExteriorAlgebra S N) :=
  ((algebraMap S (ExteriorAlgebra S N)).comp φ).toAlgebra' fun c x => Algebra.commutes (φ c) x

/-- The degree-one generator of `ExteriorAlgebra S N`, read along a semilinear map
`u : M →ₛₗ[φ] N` as an `R`-linear map on `M`, where `R` acts through `φ`. -/
noncomputable def ιCompₛₗ (φ : R →+* S) (u : M →ₛₗ[φ] N) :
    letI := algebraOfRingHom (N := N) φ
    M →ₗ[R] ExteriorAlgebra S N :=
  letI := algebraOfRingHom (N := N) φ
  { toFun := fun m => ExteriorAlgebra.ι S (u m)
    map_add' := fun m m' => by rw [map_add, map_add]
    map_smul' := fun r m => by
      change ExteriorAlgebra.ι S (u (r • m)) = r • ExteriorAlgebra.ι S (u m)
      rw [map_smulₛₗ, map_smul, Algebra.smul_def, Algebra.smul_def]
      rfl }

/-- Every value of `ιCompₛₗ` squares to zero. -/
theorem ιCompₛₗ_sq_zero (φ : R →+* S) (u : M →ₛₗ[φ] N) (m : M) :
    letI := algebraOfRingHom (N := N) φ
    ιCompₛₗ φ u m * ιCompₛₗ φ u m = 0 :=
  ExteriorAlgebra.ι_sq_zero (u m)

/-- A ring homomorphism `φ : R →+* S` together with a
`φ`-semilinear map `u : M →ₛₗ[φ] N` induces a ring homomorphism
`ExteriorAlgebra R M →+* ExteriorAlgebra S N` carrying `ι R m` to `ι S (u m)`. -/
noncomputable def mapₛₗ (φ : R →+* S) (u : M →ₛₗ[φ] N) :
    ExteriorAlgebra R M →+* ExteriorAlgebra S N :=
  letI := algebraOfRingHom (N := N) φ
  (ExteriorAlgebra.lift R
    ⟨ιCompₛₗ φ u, fun m => ExteriorAlgebra.ι_sq_zero (u m)⟩).toRingHom

/-- Base change carries the generator `ι R m` to `ι S (u m)`. -/
@[simp]
theorem mapₛₗ_ι (φ : R →+* S) (u : M →ₛₗ[φ] N) (m : M) :
    mapₛₗ φ u (ExteriorAlgebra.ι R m) = ExteriorAlgebra.ι S (u m) :=
  let := algebraOfRingHom (N := N) φ
  ExteriorAlgebra.lift_ι_apply R (ιCompₛₗ φ u) (fun m => ExteriorAlgebra.ι_sq_zero (u m)) m

/-- Base change carries the wedge `ιMulti R n v` of a family of vectors to the wedge of their
images. -/
theorem mapₛₗ_ιMulti (φ : R →+* S) (u : M →ₛₗ[φ] N) (n : ℕ) (v : Fin n → M) :
    mapₛₗ φ u (ιMulti R n v) = ιMulti S n fun i => u (v i) := by
  rw [ιMulti_apply, ιMulti_apply]
  exact map_ofFn_prod _ _ _ fun i => mapₛₗ_ι φ u _

/-- Base change carries the scalar `r` to the scalar `φ r`. -/
@[simp]
theorem mapₛₗ_algebraMap (φ : R →+* S) (u : M →ₛₗ[φ] N) (r : R) :
    mapₛₗ φ u (algebraMap R (ExteriorAlgebra R M) r) =
      algebraMap S (ExteriorAlgebra S N) (φ r) :=
  let := algebraOfRingHom (N := N) φ
  (ExteriorAlgebra.lift R
    ⟨ιCompₛₗ φ u, fun m => ExteriorAlgebra.ι_sq_zero (u m)⟩).commutes r

/-- Two ring homomorphisms out of an exterior algebra agree as soon as they agree on the image
of the base ring and on the degree-one generators. -/
theorem ringHom_ext {T : Type*} [Semiring T] {f g : ExteriorAlgebra R M →+* T}
    (h₁ : ∀ r : R, f (algebraMap R (ExteriorAlgebra R M) r) =
      g (algebraMap R (ExteriorAlgebra R M) r))
    (h₂ : ∀ m : M, f (ExteriorAlgebra.ι R m) = g (ExteriorAlgebra.ι R m)) : f = g := by
  refine RingHom.ext fun x => ?_
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => exact h₁ r
  | ι m => exact h₂ m
  | mul x y hx hy => rw [map_mul, map_mul, hx, hy]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Base change is semilinear along `φ`. -/
theorem mapₛₗ_smul (φ : R →+* S) (u : M →ₛₗ[φ] N) (r : R) (x : ExteriorAlgebra R M) :
    mapₛₗ φ u (r • x) = φ r • mapₛₗ φ u x := by
  rw [Algebra.smul_def, map_mul, mapₛₗ_algebraMap, Algebra.smul_def]

/-- Base change along `χ = ψ ∘ φ` and `v = w ∘ u` is the composite of the base changes along
`φ, u` and `ψ, w`. -/
theorem mapₛₗ_eq_comp {T : Type*} [CommRing T] {P : Type*} [AddCommGroup P] [Module T P]
    {φ : R →+* S} {ψ : S →+* T} {χ : R →+* T} (u : M →ₛₗ[φ] N) (w : N →ₛₗ[ψ] P)
    (v : M →ₛₗ[χ] P) (hχ : ∀ r, χ r = ψ (φ r)) (hv : ∀ m, v m = w (u m))
    (x : ExteriorAlgebra R M) : mapₛₗ χ v x = mapₛₗ ψ w (mapₛₗ φ u x) :=
  RingHom.congr_fun (ringHom_ext (f := mapₛₗ χ v) (g := (mapₛₗ ψ w).comp (mapₛₗ φ u))
    (fun r => by simp [hχ]) fun m => by simp [hv]) x

/-- Base change along maps that are pointwise the identity is the identity. -/
theorem mapₛₗ_eq_self {φ : R →+* R} (u : M →ₛₗ[φ] M) (hφ : ∀ r, φ r = r) (hu : ∀ m, u m = m)
    (x : ExteriorAlgebra R M) : mapₛₗ φ u x = x :=
  RingHom.congr_fun (ringHom_ext (f := mapₛₗ φ u) (g := RingHom.id (ExteriorAlgebra R M))
    (fun r => by simp [hφ]) fun m => by simp [hu]) x

/-- Base change carries `⋀[R]^n M` into `⋀[S]^n N`. -/
theorem mapₛₗ_mem_exteriorPower (φ : R →+* S) (u : M →ₛₗ[φ] N) (n : ℕ)
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M) : mapₛₗ φ u x ∈ ⋀[S]^n N := by
  exact map_mem_pow_range _ _ (mapₛₗ φ u) φ u (mapₛₗ_algebraMap φ u) (mapₛₗ_ι φ u) n hx

/-- `1` lies in `⋀[R]^0 M`. -/
theorem one_mem_exteriorPower : (1 : ExteriorAlgebra R M) ∈ ⋀[R]^0 M := by
  rw [show (⋀[R]^0 M) = 1 from pow_zero _]
  exact Submodule.mem_one.2 ⟨1, map_one _⟩

/-- The generators lie in `⋀[R]^1 M`. -/
theorem ι_mem_exteriorPower (m : M) : ExteriorAlgebra.ι R m ∈ ⋀[R]^1 M := by
  rw [show (⋀[R]^1 M) = LinearMap.range (ExteriorAlgebra.ι R) from pow_one _]
  exact LinearMap.mem_range_self _ m

/-- `⋀[R]^i M` and `⋀[R]^j M` multiply into `⋀[R]^(i + j) M`. -/
theorem mul_mem_exteriorPower {i j : ℕ} {x y : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^i M)
    (hy : y ∈ ⋀[R]^j M) : x * y ∈ ⋀[R]^(i + j) M := by
  rw [show (⋀[R]^(i + j) M) = (⋀[R]^i M) * (⋀[R]^j M) from pow_add _ i j]
  exact Submodule.mul_mem_mul hx hy

/-- The restriction of
`ExteriorAlgebra.mapₛₗ φ u` to the degree-`n` pieces, as a `φ`-semilinear map
`⋀[R]^n M →ₛₗ[φ] ⋀[S]^n N`. -/
noncomputable def powMapₛₗ (n : ℕ) (φ : R →+* S) (u : M →ₛₗ[φ] N) :
    ⋀[R]^n M →ₛₗ[φ] ⋀[S]^n N where
  toFun x := ⟨mapₛₗ φ u x, mapₛₗ_mem_exteriorPower φ u n x.2⟩
  map_add' x y := Subtype.ext (map_add (mapₛₗ φ u) x.1 y.1)
  map_smul' r x := Subtype.ext (mapₛₗ_smul φ u r x)

/-- The underlying element of `powMapₛₗ n φ u x` is `mapₛₗ φ u x`. -/
@[simp]
theorem powMapₛₗ_coe (n : ℕ) (φ : R →+* S) (u : M →ₛₗ[φ] N) (x : ⋀[R]^n M) :
    (powMapₛₗ n φ u x : ExteriorAlgebra S N) = mapₛₗ φ u x := rfl

/-- Base change of the `n`-th exterior power carries a wedge to the wedge of the images,
`u (v 0) ∧ ⋯ ∧ u (v (n-1))`. -/
@[simp]
theorem powMapₛₗ_ιMulti (n : ℕ) (φ : R →+* S) (u : M →ₛₗ[φ] N) (v : Fin n → M) :
    powMapₛₗ n φ u (_root_.exteriorPower.ιMulti R n v) =
      _root_.exteriorPower.ιMulti S n fun i => u (v i) := by
  refine Subtype.ext ?_
  rw [powMapₛₗ_coe, _root_.exteriorPower.ιMulti_apply_coe, _root_.exteriorPower.ιMulti_apply_coe,
    mapₛₗ_ιMulti]

/-- Two semilinear maps out of `⋀[R]^n M` agreeing on the wedges of families of vectors are
equal. -/
theorem powMapₛₗ_ext {P : Type*} [AddCommGroup P] [Module S P] {n : ℕ} {φ : R →+* S}
    {f g : (⋀[R]^n M) →ₛₗ[φ] P}
    (h : ∀ v : Fin n → M,
      f (_root_.exteriorPower.ιMulti R n v) = g (_root_.exteriorPower.ιMulti R n v)) :
    f = g := by
  refine LinearMap.ext fun x => ?_
  have hx : x ∈ (⊤ : Submodule R (⋀[R]^n M)) := Submodule.mem_top
  rw [← _root_.exteriorPower.ιMulti_span R n M] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨v, rfl⟩ := hy; exact h v
  | zero => rw [map_zero, map_zero]
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul r y _ hy => rw [map_smulₛₗ, map_smulₛₗ, hy]

/-- Base change of the `n`-th exterior power along `χ = ψ ∘ φ` and `v = w ∘ u` is the composite
of the base changes along `φ, u` and `ψ, w`. -/
theorem powMapₛₗ_eq_comp {T : Type*} [CommRing T] {P : Type*} [AddCommGroup P] [Module T P]
    {φ : R →+* S} {ψ : S →+* T} {χ : R →+* T} (n : ℕ) (u : M →ₛₗ[φ] N) (w : N →ₛₗ[ψ] P)
    (v : M →ₛₗ[χ] P) (hχ : ∀ r, χ r = ψ (φ r)) (hv : ∀ m, v m = w (u m)) (x : ⋀[R]^n M) :
    powMapₛₗ n χ v x = powMapₛₗ n ψ w (powMapₛₗ n φ u x) :=
  Subtype.ext (mapₛₗ_eq_comp u w v hχ hv x)

/-- Base change of the `n`-th exterior power along maps that are pointwise the identity is the
identity. -/
theorem powMapₛₗ_eq_self {φ : R →+* R} (n : ℕ) (u : M →ₛₗ[φ] M) (hφ : ∀ r, φ r = r)
    (hu : ∀ m, u m = m) (x : ⋀[R]^n M) : powMapₛₗ n φ u x = x :=
  Subtype.ext (mapₛₗ_eq_self u hφ hu x)

end BaseChange

/-! ### Lifting into a ring with a compatible module structure -/

section LiftRing

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {T : Type*} [Semiring T] [Module R T]
  {h₁ : ∀ (r : R) (x y : T), r • x * y = r • (x * y)}
  {h₂ : ∀ (r : R) (x y : T), x * r • y = r • (x * y)}
  {γ : M →ₗ[R] T} {hγ : ∀ m : M, γ m * γ m = 0}

/-- A linear map `γ : M →ₗ[R] T` with square-zero values, into a semiring `T` carrying an
`R`-module structure compatible with its multiplication, extends to an `R`-linear ring
homomorphism `ExteriorAlgebra R M →+* T` carrying `ι R m` to `γ m`. -/
theorem exists_liftRing
    (h₁ : ∀ (r : R) (x y : T), r • x * y = r • (x * y))
    (h₂ : ∀ (r : R) (x y : T), x * r • y = r • (x * y))
    (γ : M →ₗ[R] T) (hγ : ∀ m : M, γ m * γ m = 0) :
    ∃ Φ : ExteriorAlgebra R M →+* T,
      (∀ m : M, Φ (ExteriorAlgebra.ι R m) = γ m) ∧
        ∀ (r : R) (x : ExteriorAlgebra R M), Φ (r • x) = r • Φ x := by
  let _ : Algebra R T := Algebra.ofModule h₁ h₂
  refine ⟨(ExteriorAlgebra.lift R ⟨γ, hγ⟩).toRingHom,
    ExteriorAlgebra.lift_ι_apply R γ hγ, fun r x => ?_⟩
  change (ExteriorAlgebra.lift R ⟨γ, hγ⟩) (r • x) = r • (ExteriorAlgebra.lift R ⟨γ, hγ⟩) x
  rw [Algebra.smul_def, map_mul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, h₁, one_mul]

/-- The ring homomorphism `ExteriorAlgebra R M →+* T` extending a linear map with square-zero
values into a semiring with a compatible module structure; see
`ExteriorAlgebra.exists_liftRing`. -/
noncomputable def liftRing
    (h₁ : ∀ (r : R) (x y : T), r • x * y = r • (x * y))
    (h₂ : ∀ (r : R) (x y : T), x * r • y = r • (x * y))
    (γ : M →ₗ[R] T) (hγ : ∀ m : M, γ m * γ m = 0) : ExteriorAlgebra R M →+* T :=
  (exists_liftRing h₁ h₂ γ hγ).choose

/-- `liftRing` carries the generator `ι R m` to `γ m`. -/
@[simp]
theorem liftRing_ι (m : M) : liftRing h₁ h₂ γ hγ (ExteriorAlgebra.ι R m) = γ m :=
  (exists_liftRing h₁ h₂ γ hγ).choose_spec.1 m

/-- `liftRing` is `R`-linear. -/
theorem liftRing_smul (r : R) (x : ExteriorAlgebra R M) :
    liftRing h₁ h₂ γ hγ (r • x) = r • liftRing h₁ h₂ γ hγ x :=
  (exists_liftRing h₁ h₂ γ hγ).choose_spec.2 r x

/-- The value of `liftRing` on an ordered product of degree-one generators is the corresponding
ordered product in the target. -/
theorem liftRing_prod_ι {n : ℕ} (s : Fin n → M) :
    liftRing h₁ h₂ γ hγ (List.ofFn fun i => ExteriorAlgebra.ι R (s i)).prod =
      (List.ofFn fun i => γ (s i)).prod := by
  exact map_ofFn_prod _ _ _ fun i => liftRing_ι _

end LiftRing

end ExteriorAlgebra
