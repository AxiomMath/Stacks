module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Flat
import StacksFrontier.RingTheory.Etale.Basic
import StacksFrontier.RingTheory.Etale.SquareZeroFaithfullyFlat
import StacksFrontier.RingTheory.Etale.SquareZeroIdealBaseChange
import StacksFrontier.RingTheory.Etale.SquareZeroPushout

/-!
# The equalizer of a first-order thickening of an étale Čech nerve

Let `F` be an algebraic space whose reduction `G = Spec A₀` is affine and a first-order
thickening of `F`. Choose an étale affine chart `U = Spec B → F`. Write `C` and `D` for the rings
of `U ×_F U` and `U ×_F U ×_F U`, with `d₀, d₁ : B → C` and `e₀, e₁, e₂ : C → D` the pullbacks
along the projections. Write `B₀ → C₀ ⇉ D₀` for the same rings over `G`, so that
`C₀ = B₀ ⊗[A₀] B₀` and `D₀ = C₀ ⊗[B₀] C₀`. This file proves that the equalizer
`A = {b | d₀ b = d₁ b}` is a ring over which `B` is étale and faithfully flat, with
`B ⊗[A] B = C`. That is the algebraic core of the direct proof of Stacks 05ZR for first-order
thickenings.

## Main results

* `Module.FaithfullyFlat.exists_sub_one_tmul_eq_of_cocycle`: for `R → S` faithfully flat and
  any `σ : N → S ⊗[R] N`, a `1`-cocycle `x`, i.e. `(S ⊗ σ) x - (S ⊗ (1 ⊗ ·)) x + 1 ⊗ x = 0`, is a
  coboundary `σ n - 1 ⊗ n`.
* `Module.FaithfullyFlat.bijective_liftBaseChange_coinvariants`: faithfully flat descent for a
  coassociative coaction `σ : N → S ⊗[R] N` whose translates span: `S ⊗[R] Nᵒ ≅ N` for the
  invariants `Nᵒ = {n | σ n = 1 ⊗ n}`. This is Stacks 023N, stated so that it can be fed from
  geometric data.
* `RingHom.bijective_liftBaseChange_kerLinearMap`: the kernel of a flat thickening `E → E₀` over
  `B → B₀` with `ker (E → E₀) = ker (B → B₀) E` is the base change of `ker (B → B₀)`.
* `SquareZeroEqualizerDescent.exists_sub_mem_eqLocus`: vanishing of `H¹`. An element of `B`
  whose reduction comes from `A₀` can be corrected by `ker (B → B₀)` into the equalizer.
* `RingHom.eqLocus_etale_faithfullyFlat_isPushout`: **the main theorem**.

## Implementation notes

`J = ker (B → B₀)`, `K = ker (C → C₀)` and `L = ker (D → D₀)` are modules over the reduced rings
because they have square zero (`RingHom.moduleOfKerSMul`). Flatness of `d₁` and the pushout `C₀`
identify `B₀ ⊗[A₀] J` with `K` by `s ⊗ j ↦ d₀' s • d₁ j` (`SquareZeroEqualizerDescent.β`).
Flatness of `e₂` and the pasted pushout `D₀ = B₀ ⊗[A₀] C₀` embed `B₀ ⊗[A₀] K` into `L`
(`SquareZeroEqualizerDescent.Γ`). The coaction `σ = β⁻¹ ∘ d₀` on `J` is checked coassociative
after this embedding, where it becomes `e₀ ∘ d₀ = e₁ ∘ d₀`; the same embedding turns the cocycle
condition on `d₀ b - d₁ b` into the cosimplicial identities. The counit of `σ` is not needed as
input: it follows from coassociativity because the translates of `σ` span, which is
`ker qC = (ker qB) C` for `d₀`. So no diagonal `C → B` is used.

The three remaining steps live in their own files.
`IsBaseChange.of_bijective_liftBaseChange_reduction` passes from `B₀ ⊗[A₀] (A ∩ J) ≅ J` to the
base change over `A` that Stacks 05YT asks for.
`RingHom.FaithfullyFlat.of_surjective_of_isNilpotent_ker` gives faithful flatness, and
`CommRingCat.isPushout_of_isPushout_reduction` gives the pushout `B ⊗[A] B = C`.

## References

* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 05YT](https://stacks.math.columbia.edu/tag/05YT)
* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

noncomputable section

universe u

open TensorProduct

namespace RingHom

variable {B B₀ : Type*} [CommRing B] [CommRing B₀] {q : B →+* B₀} (hq : Function.Surjective q)

/-- A `B`-module annihilated by the kernel of a surjection `q : B → B₀` is a `B₀`-module, with
`q b • x = b • x`. -/
@[instance_reducible]
def moduleOfKerSMul (Q : Type*) [AddCommGroup Q] [Module B Q]
    (hQ : ∀ j ∈ RingHom.ker q, ∀ x : Q, j • x = 0) : Module B₀ Q :=
  letI : Module (B ⧸ RingHom.ker q) Q :=
    Module.IsTorsionBySet.module (I := RingHom.ker q) fun x j => hQ j j.2 x
  Module.compHom Q (RingHom.quotientKerEquivOfSurjective hq).symm.toRingHom

/-- In the module structure `moduleOfKerSMul`, `q b • x = b • x`. -/
lemma moduleOfKerSMul_smul (Q : Type*) [AddCommGroup Q] [Module B Q]
    (hQ : ∀ j ∈ RingHom.ker q, ∀ x : Q, j • x = 0) (b : B) (x : Q) :
    letI := moduleOfKerSMul hq Q hQ
    q b • x = b • x := by
  let : Module (B ⧸ RingHom.ker q) Q :=
    Module.IsTorsionBySet.module (I := RingHom.ker q) fun x j => hQ j j.2 x
  change ((RingHom.quotientKerEquivOfSurjective hq).symm (q b)) • x = b • x
  have : (RingHom.quotientKerEquivOfSurjective hq).symm (q b) = Ideal.Quotient.mk _ b :=
    (RingHom.quotientKerEquivOfSurjective hq).symm_apply_eq.mpr rfl
  rw [this]
  rfl

end RingHom

namespace Module.FaithfullyFlat

variable {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup N]

section Cocycle

variable [Module R N] [Module.FaithfullyFlat R S]

/-- **Vanishing of the first cohomology of the Amitsur complex, with a twisted coboundary.** Let
`R → S` be faithfully flat, `N` an `R`-module and `σ : N → S ⊗[R] N` any `R`-linear map. If
`x ∈ S ⊗[R] N` satisfies `(S ⊗ σ) x - (S ⊗ (1 ⊗ ·)) x + 1 ⊗ x = 0`, then `x = σ n - 1 ⊗ n` for some
`n`. After base change along `R → S` the element `1 ⊗ x` is the image of `-x` under `S ⊗ D` for
`D = σ - (1 ⊗ ·)`, so `x` dies in the cokernel of `D` after a faithfully flat base change. -/
theorem exists_sub_one_tmul_eq_of_cocycle (σ : N →ₗ[R] S ⊗[R] N) (x : S ⊗[R] N)
    (hx : σ.lTensor S x - (TensorProduct.mk R S N 1).lTensor S x + (1 : S) ⊗ₜ[R] x = 0) :
    ∃ n, σ n - (1 : S) ⊗ₜ[R] n = x := by
  set D : N →ₗ[R] S ⊗[R] N := σ - TensorProduct.mk R S N 1 with hD
  have h1 : (1 : S) ⊗ₜ[R] x = -(D.lTensor S x) := by
    rw [hD, LinearMap.lTensor_sub, LinearMap.sub_apply, eq_neg_iff_add_eq_zero, add_comm]
    exact hx
  have hq : (LinearMap.range D).mkQ x = 0 := by
    refine (Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := R) (A := S)
      (m := (LinearMap.range D).mkQ x)).mp ?_
    have : (1 : S) ⊗ₜ[R] (LinearMap.range D).mkQ x =
        ((LinearMap.range D).mkQ.lTensor S) ((1 : S) ⊗ₜ[R] x) := rfl
    rw [this, h1, map_neg, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      LinearMap.range_mkQ_comp, LinearMap.lTensor_zero, LinearMap.zero_apply, neg_zero]
  obtain ⟨n, hn⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
  exact ⟨n, hn⟩

end Cocycle

section Descent

variable [Module S N] [Module R N] [IsScalarTower R S N] [Module.FaithfullyFlat R S]

omit [Module.FaithfullyFlat R S] in
/-- The multiplication map `S ⊗[R] N → N`. -/
abbrev mulMap : S ⊗[R] N →ₗ[S] N := (LinearMap.id : N →ₗ[R] N).liftBaseChange S

/-- **Counit from coassociativity.** If an `S`-linear coaction `σ : N → S ⊗[R] N` is
coassociative and its translates by the second factor span `S ⊗[R] N`, then `σ` is counital:
`μ (σ n) = n` for the multiplication `μ : S ⊗[R] N → N`. -/
theorem mulMap_coaction (σ : N →ₗ[S] S ⊗[R] N)
    (hcoassoc : ∀ n, (σ.restrictScalars R).lTensor S (σ n) =
      (TensorProduct.mk R S N 1).lTensor S (σ n))
    (hgen : Submodule.span S (Set.range fun p : S × N =>
      ((LinearMap.lsmul S N p.1).restrictScalars R).lTensor S (σ p.2)) = ⊤) (n : N) :
    mulMap (R := R) (σ n) = n := by
  set e : N →ₗ[R] N := (mulMap (R := R)).restrictScalars R ∘ₗ σ.restrictScalars R -
    LinearMap.id with he
  have hμmk : (mulMap (R := R) (S := S) (N := N)).restrictScalars R ∘ₗ
      TensorProduct.mk R S N 1 = LinearMap.id := by
    ext m; simp
  have h1 : ∀ m, e.lTensor S (σ m) = 0 := by
    intro m
    have := congrArg ((mulMap (R := R) (S := S) (N := N)).restrictScalars R |>.lTensor S)
      (hcoassoc m)
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      ← LinearMap.lTensor_comp, hμmk, LinearMap.lTensor_id, LinearMap.id_apply] at this
    rw [he, LinearMap.lTensor_sub, LinearMap.sub_apply, LinearMap.lTensor_id, LinearMap.id_apply,
      sub_eq_zero]
    exact this
  have h2 : e.baseChange S = 0 := by
    refine LinearMap.ext_on_range hgen ?_
    rintro ⟨s, m⟩
    rw [LinearMap.zero_apply, LinearMap.baseChange_eq_lTensor, ← LinearMap.comp_apply,
      ← LinearMap.lTensor_comp]
    have hc : e ∘ₗ (LinearMap.lsmul S N s).restrictScalars R =
        ((LinearMap.lsmul S N s).restrictScalars R) ∘ₗ e := by
      ext x
      simp only [he, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.restrictScalars_apply,
        LinearMap.id_apply, LinearMap.lsmul_apply, map_smul, smul_sub]
    rw [hc, LinearMap.lTensor_comp, LinearMap.comp_apply, h1, map_zero]
  have h3 : e.restrictScalars R = 0 := by
    refine (Module.FaithfullyFlat.zero_iff_lTensor_zero R S _).mpr (LinearMap.ext fun y => ?_)
    have := LinearMap.congr_fun h2 y
    rwa [LinearMap.baseChange_eq_lTensor] at this
  have := LinearMap.congr_fun h3 n
  simpa [he, sub_eq_zero] using this

omit [Module.FaithfullyFlat R S] in
/-- The invariants of a coaction `σ : N → S ⊗[R] N`: the `n` with `σ n = 1 ⊗ n`. -/
def coinvariants (σ : N →ₗ[S] S ⊗[R] N) : Submodule R N :=
  LinearMap.ker (σ.restrictScalars R - TensorProduct.mk R S N 1)

omit [Module.FaithfullyFlat R S] in
/-- `n` is an invariant of `σ` if and only if `σ n = 1 ⊗ n`. -/
lemma mem_coinvariants {σ : N →ₗ[S] S ⊗[R] N} {n : N} :
    n ∈ coinvariants σ ↔ σ n = (1 : S) ⊗ₜ[R] n := by
  simp [coinvariants, sub_eq_zero]

omit [Module.FaithfullyFlat R S] in
/-- Multiplying out the first two factors of `S ⊗[R] (S ⊗[R] N)`. -/
abbrev mulLeftMap : S ⊗[R] (S ⊗[R] N) →ₗ[S] S ⊗[R] N :=
  (LinearMap.id : S ⊗[R] N →ₗ[R] S ⊗[R] N).liftBaseChange S

omit [Module.FaithfullyFlat R S] in
/-- `σ ∘ μ` is `μ₁₂ ∘ (S ⊗ σ)`, by `S`-linearity of `σ`. -/
lemma coaction_mulMap (σ : N →ₗ[S] S ⊗[R] N) (y : S ⊗[R] N) :
    σ (mulMap (R := R) y) = mulLeftMap ((σ.restrictScalars R).lTensor S y) := by
  induction y with
  | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]
  | tmul s n => simp

omit [Module S N] [IsScalarTower R S N] [Module.FaithfullyFlat R S] in
/-- `mulLeftMap` is a left inverse of `S ⊗ (1 ⊗ ·) : S ⊗[R] N → S ⊗[R] (S ⊗[R] N)`. -/
lemma mulLeftMap_lTensor_mk (y : S ⊗[R] N) :
    mulLeftMap ((TensorProduct.mk R S N 1).lTensor S y) = y := by
  induction y with
  | add y z hy hz => rw [map_add, map_add, hy, hz]
  | tmul s n => simp [TensorProduct.smul_tmul']

/-- **Faithfully flat descent for a coaction.** Let `R → S` be faithfully flat and let `N` be an
`S`-module with an `S`-linear coaction `σ : N → S ⊗[R] N` (the unit `n ↦ φ (n ⊗ 1)` of a descent
datum `φ : N ⊗[R] S ≅ S ⊗[R] N`). If `σ` is coassociative and the elements `(1 ⊗ s) • σ n` span
`S ⊗[R] N` (which holds when `φ` is surjective), then `N` is the base change of its module of
invariants: `S ⊗[R] Nᵒ → N`, `s ⊗ n ↦ s • n`, is bijective. -/
theorem bijective_liftBaseChange_coinvariants (σ : N →ₗ[S] S ⊗[R] N)
    (hcoassoc : ∀ n, (σ.restrictScalars R).lTensor S (σ n) =
      (TensorProduct.mk R S N 1).lTensor S (σ n))
    (hgen : Submodule.span S (Set.range fun p : S × N =>
      ((LinearMap.lsmul S N p.1).restrictScalars R).lTensor S (σ p.2)) = ⊤) :
    Function.Bijective ((coinvariants σ).subtype.liftBaseChange S) := by
  set D : N →ₗ[R] S ⊗[R] N := σ.restrictScalars R - TensorProduct.mk R S N 1 with hD
  have hex : Function.Exact ((coinvariants σ).subtype.lTensor S) (D.lTensor S) :=
    Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map D)
  have hinj : Function.Injective ((coinvariants σ).subtype.lTensor S) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have hfac : ∀ x, (coinvariants σ).subtype.liftBaseChange S x =
      mulMap (R := R) ((coinvariants σ).subtype.lTensor S x) := by
    intro x
    induction x with
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
    | tmul s n => simp
  have hcounit := mulMap_coaction σ hcoassoc hgen
  have hker : ∀ y, D.lTensor S y = 0 → σ (mulMap (R := R) y) = y := by
    intro y hy
    rw [hD, LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero] at hy
    rw [coaction_mulMap, hy, mulLeftMap_lTensor_mk]
  refine ⟨fun x x' hxx' => hinj ?_, fun n => ?_⟩
  · rw [hfac, hfac] at hxx'
    rw [← hker _ ((hex _).mpr ⟨x, rfl⟩), ← hker _ ((hex _).mpr ⟨x', rfl⟩), hxx']
  · obtain ⟨x, hx⟩ := (hex (σ n)).mp (by
      rw [hD, LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero]
      exact hcoassoc n)
    exact ⟨x, by rw [hfac, hx, hcounit]⟩

end Descent

end Module.FaithfullyFlat

namespace RingHom

section FlatKernel

variable {B B₀ E E₀ : Type*} [CommRing B] [CommRing B₀] [CommRing E] [CommRing E₀]
  {qB : B →+* B₀} {qE : E →+* E₀} {g : B →+* E}

/-- The restriction `ker qB → ker qE` of a ring map `g` carrying `ker qB` into `ker qE`. -/
def kerHom (hmap : ∀ j ∈ RingHom.ker qB, g j ∈ RingHom.ker qE) :
    RingHom.ker qB →+ RingHom.ker qE where
  toFun j := ⟨g (j : B), hmap j j.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

/-- The underlying element of `kerHom hmap j` is `g j`. -/
@[simp]
lemma coe_kerHom (hmap : ∀ j ∈ RingHom.ker qB, g j ∈ RingHom.ker qE) (j : RingHom.ker qB) :
    (kerHom hmap j : E) = g j := rfl

/-- If `qE ∘ g = g₀ ∘ qB`, then `g` carries `ker qB` into `ker qE`. -/
lemma map_mem_ker_of_comp_eq {g₀ : B₀ →+* E₀} (hg : qE.comp g = g₀.comp qB) :
    ∀ j ∈ RingHom.ker qB, g j ∈ RingHom.ker qE := fun j hj => by
  rw [RingHom.mem_ker, ← RingHom.comp_apply, hg, RingHom.comp_apply, RingHom.mem_ker.mp hj,
    map_zero]

/-- If `ker qE = (ker qB) E`, then `g` carries `ker qB` into `ker qE`. -/
lemma map_mem_ker_of_ker_eq (hK : RingHom.ker qE = Ideal.map g (RingHom.ker qB)) :
    ∀ j ∈ RingHom.ker qB, g j ∈ RingHom.ker qE := fun _ hj => hK ▸ Ideal.mem_map_of_mem g hj

/-- `kerHom` is semilinear over the reduction `g₀` of `g`. -/
lemma kerHom_smul {g₀ : B₀ →+* E₀} (hg : qE.comp g = g₀.comp qB) (hqB : Function.Surjective qB)
    [Module B₀ (RingHom.ker qB)] (hJs : ∀ (b : B) (j : RingHom.ker qB), qB b • j = b • j)
    [Module E₀ (RingHom.ker qE)] (hKs : ∀ (e : E) (k : RingHom.ker qE), qE e • k = e • k)
    (hmap : ∀ j ∈ RingHom.ker qB, g j ∈ RingHom.ker qE) (s : B₀) (j : RingHom.ker qB) :
    kerHom hmap (s • j) = g₀ s • kerHom hmap j := by
  obtain ⟨b, rfl⟩ := hqB s
  have h : g₀ (qB b) = qE (g b) := (RingHom.congr_fun hg b).symm
  rw [hJs, h, hKs]
  exact Subtype.ext (map_mul g b j)

variable (hqE : Function.Surjective qE) (hK : RingHom.ker qE = Ideal.map g (RingHom.ker qB))
  [Algebra B₀ E₀] (hg : qE.comp g = (algebraMap B₀ E₀).comp qB)
  [Module B₀ (RingHom.ker qB)] (hJs : ∀ (b : B) (j : RingHom.ker qB), qB b • j = b • j)
  [Module E₀ (RingHom.ker qE)] (hKs : ∀ (e : E) (k : RingHom.ker qE), qE e • k = e • k)
  [Module B₀ (RingHom.ker qE)] [IsScalarTower B₀ E₀ (RingHom.ker qE)]

include hK hg hJs hKs

/-- `kerHom` as a `B₀`-linear map. -/
def kerLinearMap (hqB : Function.Surjective qB) : RingHom.ker qB →ₗ[B₀] RingHom.ker qE where
  toFun := kerHom (map_mem_ker_of_ker_eq hK)
  map_add' := map_add _
  map_smul' s j := by
    rw [RingHom.id_apply, kerHom_smul hg hqB hJs hKs, algebraMap_smul]

/-- The underlying element of `kerLinearMap hK hg hJs hKs hqB j` is `g j`. -/
@[simp]
lemma coe_kerLinearMap (hqB : Function.Surjective qB) (j : RingHom.ker qB) :
    (kerLinearMap hK hg hJs hKs hqB j : E) = g j := rfl

include hqE in
/-- **The kernel of a flat thickening is a base change.** Let `g : B → E` be flat and lie over
`B₀ → E₀` along the surjections `qB`, `qE`, with `ker qE = (ker qB) E`, and suppose both kernels
are modules over the reductions. Then `E₀ ⊗[B₀] ker qB → ker qE` is bijective. -/
theorem bijective_liftBaseChange_kerLinearMap (hqB : Function.Surjective qB) (hflat : g.Flat) :
    Function.Bijective ((kerLinearMap hK hg hJs hKs hqB).liftBaseChange E₀) := by
  let : Algebra B E := g.toAlgebra
  have : Module.Flat B E := hflat
  let gB : RingHom.ker qB →ₗ[B] RingHom.ker qE :=
    { kerHom (map_mem_ker_of_ker_eq hK) with
      map_smul' := fun b j => Subtype.ext (map_mul g b (j : B)) }
  -- the comparison over `B` is injective by flatness
  have hrid : ∀ x : E ⊗[B] RingHom.ker qB, ((gB.liftBaseChange E x : RingHom.ker qE) : E) =
      TensorProduct.rid B E ((RingHom.ker qB).subtype.lTensor E x) := by
    intro x
    induction x with
    | add x y hx hy => rw [map_add, Submodule.coe_add, hx, hy, map_add, map_add]
    | tmul e j =>
      rw [LinearMap.liftBaseChange_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
        Submodule.coe_smul, smul_eq_mul, Algebra.smul_def, mul_comm]
      rfl
  have hinjB : Function.Injective (gB.liftBaseChange E) := by
    intro x y hxy
    have h := congrArg (fun z : RingHom.ker qE => (z : E)) hxy
    simp only [hrid] at h
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
      ((TensorProduct.rid B E).injective h)
  -- the comparison over `B` is surjective since `ker qE = (ker qB) E`
  have hsurjB : Function.Surjective (gB.liftBaseChange E) := by
    have key : ∀ y ∈ Ideal.map g (RingHom.ker qB), ∃ x,
        ((gB.liftBaseChange E x : RingHom.ker qE) : E) = y := by
      intro y hy
      refine Submodule.span_induction (fun y hy => ?_) ⟨0, by simp⟩
        (fun y z _ _ ⟨x, hx⟩ ⟨x', hx'⟩ => ⟨x + x', by rw [map_add, Submodule.coe_add, hx, hx']⟩)
        (fun a y _ ⟨x, hx⟩ => ⟨a • x, by rw [map_smul, Submodule.coe_smul, hx, smul_eq_mul]⟩) hy
      obtain ⟨j, hj, rfl⟩ := hy
      exact ⟨1 ⊗ₜ ⟨j, hj⟩, by simp [gB]⟩
    intro k
    obtain ⟨x, hx⟩ := key k (hK ▸ k.2)
    exact ⟨x, Subtype.ext hx⟩
  -- the reduction map `E ⊗[B] ker qB → E₀ ⊗[B₀] ker qB`
  let π : E ⊗[B] RingHom.ker qB →+ E₀ ⊗[B₀] RingHom.ker qB :=
    TensorProduct.liftAddHom
      { toFun := fun e => (TensorProduct.mk B₀ E₀ _ (qE e)).toAddMonoidHom
        map_zero' := by ext; simp
        map_add' := fun _ _ => by ext; simp }
      (fun b e j => by
        change qE (b • e) ⊗ₜ[B₀] j = qE e ⊗ₜ[B₀] (b • j)
        rw [← hJs, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, ← RingHom.comp_apply,
          hg, RingHom.comp_apply, ← Algebra.smul_def, TensorProduct.smul_tmul])
  have hπ : ∀ x, (kerLinearMap hK hg hJs hKs hqB).liftBaseChange E₀ (π x) =
      gB.liftBaseChange E x := by
    intro x
    induction x with
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
    | tmul e j =>
      change (kerLinearMap hK hg hJs hKs hqB).liftBaseChange E₀ (qE e ⊗ₜ j) = _
      rw [LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, hKs]
      rfl
  have hπs : Function.Surjective π := by
    intro y
    induction y with
    | add y z hy hz =>
      obtain ⟨x, rfl⟩ := hy
      obtain ⟨x', rfl⟩ := hz
      exact ⟨x + x', map_add π x x'⟩
    | tmul e₀ j =>
      obtain ⟨e, rfl⟩ := hqE e₀
      exact ⟨e ⊗ₜ j, rfl⟩
  refine ⟨fun y y' h => ?_, fun k => ?_⟩
  · obtain ⟨x, rfl⟩ := hπs y
    obtain ⟨x', rfl⟩ := hπs y'
    rw [hπ, hπ] at h
    rw [hinjB h]
  · obtain ⟨x, rfl⟩ := hsurjB k
    exact ⟨π x, hπ x⟩

end FlatKernel

end RingHom

section PushoutBaseChange

open CategoryTheory

variable {R S X₀ Y₀ : Type u} [CommRing R] [CommRing S] [CommRing X₀] [CommRing Y₀]
  [Algebra R S] [Algebra R X₀] [Algebra X₀ Y₀]
  {N Q : Type*} [AddCommGroup N] [Module X₀ N] [Module R N] [IsScalarTower R X₀ N]
  [AddCommGroup Q] [Module Y₀ Q] [Module X₀ Q] [IsScalarTower X₀ Y₀ Q]

/-- **Base change along a pushout square.** Let `Y₀ = S ⊗[R] X₀` be a pushout of rings, with legs
`h : S → Y₀` and `X₀ → Y₀`, and let `ν : N → Q` exhibit the `Y₀`-module `Q` as the base change of
the `X₀`-module `N`. Then every additive map `S ⊗[R] N → Q` sending `s ⊗ n` to `h s • ν n` is
bijective: `Q = Y₀ ⊗[X₀] N = S ⊗[R] N`. -/
theorem bijective_of_isPushout_of_bijective_liftBaseChange (h : S →+* Y₀)
    (hP : IsPushout (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R X₀))
      (CommRingCat.ofHom h) (CommRingCat.ofHom (algebraMap X₀ Y₀)))
    (ν : N →ₗ[X₀] Q) (hν : Function.Bijective (ν.liftBaseChange Y₀))
    (F : S ⊗[R] N →+ Q) (hF : ∀ s n, F (s ⊗ₜ n) = h s • ν n) : Function.Bijective F := by
  let : Algebra S Y₀ := h.toAlgebra
  let : Algebra R Y₀ := ((algebraMap X₀ Y₀).comp (algebraMap R X₀)).toAlgebra
  have : IsScalarTower R X₀ Y₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R S Y₀ := IsScalarTower.of_algebraMap_eq fun r =>
    (congrArg (fun f => (CommRingCat.Hom.hom f) r) hP.w).symm
  have : Algebra.IsPushout R S X₀ Y₀ := CommRingCat.isPushout_iff_isPushout.mp hP
  have hcomp : ∀ x, F x = ν.liftBaseChange Y₀
      ((Algebra.IsPushout.cancelBaseChange R S X₀ Y₀ N).symm x) := by
    intro x
    induction x with
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
    | tmul s n =>
      rw [hF, Algebra.IsPushout.cancelBaseChange_symm_tmul, LinearMap.liftBaseChange_tmul]
      rfl
  have : (F : S ⊗[R] N → Q) =
      ν.liftBaseChange Y₀ ∘ (Algebra.IsPushout.cancelBaseChange R S X₀ Y₀ N).symm :=
    funext hcomp
  rw [this]
  exact hν.comp (LinearEquiv.bijective _)

end PushoutBaseChange

/-! ### Reduction of a subring of a square-zero thickening -/

/-- In an ideal of square zero, the product of any two elements vanishes. -/
theorem Ideal.mul_eq_zero_of_sq_eq_bot {R : Type*} [CommSemiring R] {I : Ideal R}
    (hI : I ^ 2 = ⊥) {x y : R} (hx : x ∈ I) (hy : y ∈ I) : x * y = 0 := by
  have := Ideal.mul_mem_mul hx hy
  rwa [← pow_two, hI, Ideal.mem_bot] at this

/-- A ring map with values in the range of an injective ring map `φ` factors through `φ`. -/
theorem RingHom.exists_comp_eq_of_forall_mem_range {A A₀ B₀ : Type*} [Ring A] [Ring A₀]
    [Ring B₀] {φ : A₀ →+* B₀} (hφ : Function.Injective φ) (f : A →+* B₀)
    (hf : ∀ a, f a ∈ φ.range) : ∃ ψ : A →+* A₀, φ.comp ψ = f := by
  let e := RingEquiv.ofBijective φ.rangeRestrict
    ⟨fun x y h => hφ (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩
  exact ⟨e.symm.toRingHom.comp (f.codRestrict φ.range hf), RingHom.ext fun a =>
    congrArg Subtype.val (e.apply_symm_apply (f.codRestrict φ.range hf a))⟩

namespace SquareZeroEqualizerDescent

variable {A₀ B B₀ : Type*} [CommRing A₀] [CommRing B] [CommRing B₀] [Algebra A₀ B₀]
  {qB : B →+* B₀} {A : Subring B} {ψ : A →+* A₀} (hφ : Function.Injective (algebraMap A₀ B₀))
  (hφψ : (algebraMap A₀ B₀).comp ψ = qB.comp A.subtype)

include hφ hφψ in
/-- If `A₀ → B₀` is injective, the kernel of the reduction `ψ : A → A₀` of a subring `A` of `B`
is the part of `A` in `ker qB`. -/
theorem mem_ker_iff_of_comp_eq (a : A) : a ∈ RingHom.ker ψ ↔ qB a = 0 := by
  rw [RingHom.mem_ker, ← hφ.eq_iff, map_zero]
  exact iff_of_eq (congrArg (· = 0) (RingHom.congr_fun hφψ a))

include hφ hφψ in
/-- The reduction `A → A₀` of a subring of a square-zero thickening `B → B₀` has square-zero
kernel. -/
theorem ker_sq_eq_bot_of_comp_eq (hJ : RingHom.ker qB ^ 2 = ⊥) : RingHom.ker ψ ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff]
  refine Ideal.mul_le.mpr fun x hx y hy => ?_
  rw [Ideal.mem_bot]
  exact Subtype.ext (Ideal.mul_eq_zero_of_sq_eq_bot hJ ((mem_ker_iff_of_comp_eq hφ hφψ x).mp hx)
    ((mem_ker_iff_of_comp_eq hφ hφψ y).mp hy))

variable [Module B₀ (RingHom.ker qB)] [Module A₀ (RingHom.ker qB)]
  [IsScalarTower A₀ B₀ (RingHom.ker qB)] (hJs : ∀ (b : B) (j : RingHom.ker qB), qB b • j = b • j)
  (N : Submodule A₀ (RingHom.ker qB)) (hN : ∀ j, j ∈ N ↔ (j : B) ∈ A)
  (hdesc : Function.Bijective (N.subtype.liftBaseChange B₀))

include hφ hφψ hJs hN hdesc in
/-- If `ker qB` descends to its part `N` in `A`, then `ker qB` is generated by the kernel of the
reduction `A → A₀`. -/
theorem ker_eq_map_of_comp_eq (hqB : Function.Surjective qB) :
    RingHom.ker qB = Ideal.map A.subtype (RingHom.ker ψ) := by
  refine le_antisymm (fun j hj => ?_) (Ideal.map_le_iff_le_comap.mpr fun x hx =>
    RingHom.mem_ker.mpr ((mem_ker_iff_of_comp_eq hφ hφψ x).mp hx))
  obtain ⟨t, ht⟩ := hdesc.2 ⟨j, hj⟩
  have key : ∀ t, (N.subtype.liftBaseChange B₀ t : B) ∈ Ideal.map A.subtype (RingHom.ker ψ) := by
    intro t
    induction t with
    | add x y hx hy =>
      rw [map_add, Submodule.coe_add]
      exact Ideal.add_mem _ hx hy
    | tmul s m =>
      obtain ⟨b, rfl⟩ := hqB s
      rw [LinearMap.liftBaseChange_tmul, Submodule.subtype_apply, hJs, Submodule.coe_smul,
        smul_eq_mul]
      refine Ideal.mul_mem_left _ b (Ideal.mem_map_of_mem A.subtype (x :=
        ⟨((m : RingHom.ker qB) : B), (hN m).mp m.2⟩) ?_)
      exact (mem_ker_iff_of_comp_eq hφ hφψ _).mpr (RingHom.mem_ker.mp (m : RingHom.ker qB).2)
  simpa [ht] using key t

include hφ hφψ hJs hN hdesc in
/-- **Stacks 05YT for a subring.** If `ker qB` of a square-zero thickening `B → B₀` of an étale
`A₀`-algebra descends to its part in a subring `A` of `B` reducing onto `A₀`, then `A → B` is
étale. -/
theorem etale_subtype_of_comp_eq [Algebra.Etale A₀ B₀] (hqB : Function.Surjective qB)
    (hψ : Function.Surjective ψ) (hJ : RingHom.ker qB ^ 2 = ⊥) : A.subtype.Etale := by
  let : Algebra A A₀ := ψ.toAlgebra
  let : Algebra A B := A.subtype.toAlgebra
  let : Algebra B B₀ := qB.toAlgebra
  let : Algebra A B₀ := (qB.comp A.subtype).toAlgebra
  have : IsScalarTower A A₀ B₀ := IsScalarTower.of_algebraMap_eq fun a =>
    (RingHom.congr_fun hφψ a).symm
  have : IsScalarTower A B B₀ := IsScalarTower.of_algebraMap_eq fun a => rfl
  have hker (x : RingHom.ker (algebraMap A A₀)) := (mem_ker_iff_of_comp_eq hφ hφψ x).mp x.2
  let f : RingHom.ker (algebraMap A A₀) →ₗ[A] RingHom.ker (algebraMap B B₀) :=
    { toFun := fun x => ⟨((x : A) : B), RingHom.mem_ker.mpr (hker x)⟩
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl }
  have hbc : IsBaseChange B f :=
    IsBaseChange.of_bijective_liftBaseChange_reduction hψ hqB hJs f (fun x => rfl)
      (fun x y h => Subtype.ext (Subtype.ext
        (congrArg (fun z : RingHom.ker (algebraMap B B₀) => (z : B)) h))) N
      (fun j => by
        rw [hN]
        refine ⟨fun h => ⟨⟨⟨(j : B), h⟩, (mem_ker_iff_of_comp_eq hφ hφψ _).mpr
          (RingHom.mem_ker.mp j.2)⟩, rfl⟩, ?_⟩
        rintro ⟨x, rfl⟩
        exact x.1.2)
      hdesc
  exact Algebra.Etale.of_ker_sq_eq_bot_of_isBaseChange hψ hqB
    (ker_sq_eq_bot_of_comp_eq hφ hφψ hJ) f (fun x => rfl) hbc

end SquareZeroEqualizerDescent

/-! ### The kernel of a first-order thickening of a Čech nerve -/

namespace SquareZeroEqualizerDescent

open CategoryTheory

variable {A₀ B B₀ C C₀ D D₀ : Type u} [CommRing A₀] [CommRing B] [CommRing B₀] [CommRing C]
  [CommRing C₀] [CommRing D] [CommRing D₀] [Algebra A₀ B₀] [Algebra A₀ C₀]
  {qB : B →+* B₀} {qC : C →+* C₀} {qD : D →+* D₀}
  {d₀ d₁ : B →+* C} {e₀ e₁ e₂ : C →+* D} {d₀' d₁' : B₀ →+* C₀} {e₀' e₁' e₂' : C₀ →+* D₀}
  [Module B₀ (RingHom.ker qB)] [Module A₀ (RingHom.ker qB)] [IsScalarTower A₀ B₀ (RingHom.ker qB)]
  [Module C₀ (RingHom.ker qC)] [Module A₀ (RingHom.ker qC)] [IsScalarTower A₀ C₀ (RingHom.ker qC)]
  [Module D₀ (RingHom.ker qD)]
  (hqB : Function.Surjective qB) (hqC : Function.Surjective qC) (hqD : Function.Surjective qD)
  (hJs : ∀ (b : B) (j : RingHom.ker qB), qB b • j = b • j)
  (hKs : ∀ (c : C) (k : RingHom.ker qC), qC c • k = c • k)
  (hLs : ∀ (x : D) (l : RingHom.ker qD), qD x • l = x • l)
  (hAC : algebraMap A₀ C₀ = d₀'.comp (algebraMap A₀ B₀))
  (hd₀ : qC.comp d₀ = d₀'.comp qB) (hd₁ : qC.comp d₁ = d₁'.comp qB)
  (he₀ : qD.comp e₀ = e₀'.comp qC) (he₁ : qD.comp e₁ = e₁'.comp qC)
  (he₂ : qD.comp e₂ = e₂'.comp qC)
  (h01 : e₀.comp d₀ = e₁.comp d₀) (h02 : e₀.comp d₁ = e₂.comp d₀)
  (h12 : e₁.comp d₁ = e₂.comp d₁)
  (hC : IsPushout (CommRingCat.ofHom (algebraMap A₀ B₀)) (CommRingCat.ofHom (algebraMap A₀ B₀))
    (CommRingCat.ofHom d₀') (CommRingCat.ofHom d₁'))
  (hD : IsPushout (CommRingCat.ofHom d₁') (CommRingCat.ofHom d₀') (CommRingCat.ofHom e₀')
    (CommRingCat.ofHom e₂'))

/-- The restriction `ker qB → ker qC` of `d₀`. -/
abbrev δ₀ (hd₀ : qC.comp d₀ = d₀'.comp qB) : RingHom.ker qB →+ RingHom.ker qC :=
  RingHom.kerHom (RingHom.map_mem_ker_of_comp_eq hd₀)

/-- The restriction `ker qC → ker qD` of `e`. -/
abbrev ε (he : qD.comp e₀ = e₀'.comp qC) : RingHom.ker qC →+ RingHom.ker qD :=
  RingHom.kerHom (RingHom.map_mem_ker_of_comp_eq he)

omit [Algebra A₀ C₀] in
include hC in
/-- The two maps `B₀ → C₀` agree on `A₀`. -/
lemma comp_algebraMap_eq : d₀'.comp (algebraMap A₀ B₀) = d₁'.comp (algebraMap A₀ B₀) := by
  ext r
  exact congrArg (fun f => (CommRingCat.Hom.hom f) r) hC.w

omit [Module B₀ (RingHom.ker qB)] [Module C₀ (RingHom.ker qC)] [Module D₀ (RingHom.ker qD)] in
include hqB in
/-- If `f₀ ∘ d = f₁ ∘ d`, then the reductions satisfy `f₀' ∘ d' = f₁' ∘ d'`. -/
lemma comp_eq_of_comp_eq {f₀ f₁ : C →+* D} {d : B →+* C} {d' : B₀ →+* C₀} {f₀' f₁' : C₀ →+* D₀}
    (h : f₀.comp d = f₁.comp d) (hd : qC.comp d = d'.comp qB) (hf₀ : qD.comp f₀ = f₀'.comp qC)
    (hf₁ : qD.comp f₁ = f₁'.comp qC) : f₀'.comp d' = f₁'.comp d' := by
  ext s
  obtain ⟨b, rfl⟩ := hqB s
  have h1 := RingHom.congr_fun (congrArg (qD.comp) h) b
  simp only [RingHom.comp_apply] at h1
  have e0 := RingHom.congr_fun hf₀ (d b)
  have e1 := RingHom.congr_fun hf₁ (d b)
  have ed := RingHom.congr_fun hd b
  simp only [RingHom.comp_apply] at e0 e1 ed
  simp only [RingHom.comp_apply, ← ed, ← e0, ← e1, h1]

include hqB hJs hKs in
/-- `δ₀` is semilinear over `d₀'`. -/
lemma δ₀_smul (s : B₀) (j : RingHom.ker qB) : δ₀ hd₀ (s • j) = d₀' s • δ₀ hd₀ j :=
  RingHom.kerHom_smul hd₀ hqB hJs hKs _ s j

include hqC hKs hLs in
/-- `ε` is semilinear over `e₀'`. -/
lemma ε_smul (c : C₀) (k : RingHom.ker qC) : ε he₀ (c • k) = e₀' c • ε he₀ k :=
  RingHom.kerHom_smul he₀ hqC hKs hLs _ c k

/-- The map `B₀ ⊗[A₀] ker qB → ker qC`, `s ⊗ j ↦ d₀' s • d₁ j`. -/
def β : B₀ ⊗[A₀] RingHom.ker qB →ₗ[A₀] RingHom.ker qC :=
  TensorProduct.lift <| LinearMap.mk₂ A₀ (fun s j => d₀' s • δ₀ hd₁ j)
    (fun s s' j => by rw [map_add, add_smul])
    (fun r s j => by
      rw [Algebra.smul_def, map_mul, mul_smul, ← RingHom.comp_apply, ← hAC, algebraMap_smul])
    (fun s j j' => by rw [map_add, smul_add])
    (fun r s j => by
      rw [← algebraMap_smul B₀ r j, δ₀_smul hqB hJs hKs hd₁, smul_comm, ← RingHom.comp_apply,
        ← comp_algebraMap_eq hC, ← hAC, algebraMap_smul])

/-- `β (s ⊗ j) = d₀' s • d₁ j`. -/
lemma β_tmul (s : B₀) (j : RingHom.ker qB) :
    β hqB hJs hKs hAC hd₁ hC (s ⊗ₜ j) = d₀' s • δ₀ hd₁ j := rfl

/-- `β` is semilinear over `d₀'` for the scalar action on the left factor. -/
lemma β_smul (s : B₀) (x : B₀ ⊗[A₀] RingHom.ker qB) :
    β hqB hJs hKs hAC hd₁ hC (s • x) = d₀' s • β hqB hJs hKs hAC hd₁ hC x := by
  induction x with
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  | tmul t j => rw [TensorProduct.smul_tmul', β_tmul, β_tmul, smul_eq_mul, map_mul, mul_smul]

/-- `β` is semilinear over `d₁'` for the scalar action on `ker qB`. -/
lemma β_lTensor_smul (s : B₀) (x : B₀ ⊗[A₀] RingHom.ker qB) :
    β hqB hJs hKs hAC hd₁ hC (((LinearMap.lsmul B₀ (RingHom.ker qB) s).restrictScalars A₀).lTensor
      B₀ x) = d₁' s • β hqB hJs hKs hAC hd₁ hC x := by
  induction x with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]
  | tmul t j =>
    rw [LinearMap.lTensor_tmul, β_tmul, β_tmul, LinearMap.restrictScalars_apply,
      LinearMap.lsmul_apply, δ₀_smul hqB hJs hKs hd₁, smul_comm]

include hqC in
/-- `β` is bijective, by flatness of `d₁` and the pushout `C₀ = B₀ ⊗[A₀] B₀`. -/
theorem bijective_β (hK₁ : RingHom.ker qC = Ideal.map d₁ (RingHom.ker qB)) (hfd₁ : d₁.Flat) :
    Function.Bijective (β hqB hJs hKs hAC hd₁ hC) := by
  let : Algebra B₀ C₀ := d₁'.toAlgebra
  let : Module B₀ (RingHom.ker qC) := Module.compHom _ d₁'
  have : IsScalarTower B₀ C₀ (RingHom.ker qC) := ⟨fun s c k => mul_smul (d₁' s) c k⟩
  exact bijective_of_isPushout_of_bijective_liftBaseChange d₀' hC
    (RingHom.kerLinearMap hK₁ hd₁ hJs hKs hqB)
    (RingHom.bijective_liftBaseChange_kerLinearMap hqC hK₁ hd₁ hJs hKs hqB hfd₁)
    (β hqB hJs hKs hAC hd₁ hC).toAddMonoidHom fun s j => rfl

/-- The map `B₀ ⊗[A₀] ker qC → ker qD`, `s ⊗ k ↦ e₀' (d₀' s) • e₂ k`. -/
def Γ : B₀ ⊗[A₀] RingHom.ker qC →+ RingHom.ker qD :=
  TensorProduct.liftAddHom
    { toFun := fun s =>
        { toFun := fun k => e₀' (d₀' s) • ε he₂ k
          map_zero' := by rw [map_zero, smul_zero]
          map_add' := fun k k' => by rw [map_add, smul_add] }
      map_zero' := by ext k; simp
      map_add' := fun s s' => by ext k; simp [add_smul] }
    fun r s k => by
      change e₀' (d₀' (r • s)) • ε he₂ k = e₀' (d₀' s) • ε he₂ (r • k)
      have hw : e₂' (d₀' (algebraMap A₀ B₀ r)) = e₀' (d₀' (algebraMap A₀ B₀ r)) := by
        have h1 := congrArg (fun f => (CommRingCat.Hom.hom f) (algebraMap A₀ B₀ r)) hD.w
        have h2 := RingHom.congr_fun (comp_algebraMap_eq hC) r
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
          Function.comp_apply] at h1 h2
        rw [← h1, h2]
      rw [← algebraMap_smul C₀ r k, ε_smul hqC hKs hLs he₂, hAC, RingHom.comp_apply, hw,
        Algebra.smul_def, map_mul, map_mul, mul_smul, smul_comm]

/-- `Γ (s ⊗ k) = e₀' (d₀' s) • e₂ k`. -/
lemma Γ_tmul (s : B₀) (k : RingHom.ker qC) :
    Γ hqC hKs hLs hAC he₂ hC hD (s ⊗ₜ k) = e₀' (d₀' s) • ε he₂ k := rfl

include hqD in
/-- `Γ` is injective (indeed bijective), by flatness of `e₂` and the pushout
`D₀ = B₀ ⊗[A₀] C₀` obtained by pasting the two given squares. -/
theorem injective_Γ (hL₂ : RingHom.ker qD = Ideal.map e₂ (RingHom.ker qC)) (hfe₂ : e₂.Flat) :
    Function.Injective (Γ hqC hKs hLs hAC he₂ hC hD) := by
  let : Algebra C₀ D₀ := e₂'.toAlgebra
  let : Module C₀ (RingHom.ker qD) := Module.compHom _ e₂'
  have : IsScalarTower C₀ D₀ (RingHom.ker qD) := ⟨fun s c k => mul_smul (e₂' s) c k⟩
  have hP := hC.paste_vert hD
  rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← hAC] at hP
  exact (bijective_of_isPushout_of_bijective_liftBaseChange (e₀'.comp d₀') hP
    (RingHom.kerLinearMap hL₂ he₂ hKs hLs hqC)
    (RingHom.bijective_liftBaseChange_kerLinearMap hqD hL₂ he₂ hKs hLs hqC hfe₂)
    (Γ hqC hKs hLs hAC he₂ hC hD) fun s j => rfl).1

variable (hβ : Function.Bijective (β hqB hJs hKs hAC hd₁ hC))

/-- The coaction `ker qB → B₀ ⊗[A₀] ker qB`, `j ↦ β⁻¹ (d₀ j)`: the unit of the descent datum
on `ker qB`. -/
def σ : RingHom.ker qB →ₗ[B₀] B₀ ⊗[A₀] RingHom.ker qB where
  toFun j := (LinearEquiv.ofBijective _ hβ).symm (δ₀ hd₀ j)
  map_add' j j' := by rw [map_add, map_add]
  map_smul' s j := by
    have hx : ∀ x, β hqB hJs hKs hAC hd₁ hC ((LinearEquiv.ofBijective _ hβ).symm x) = x :=
      (LinearEquiv.ofBijective _ hβ).apply_symm_apply
    apply hβ.1
    rw [RingHom.id_apply, hx, β_smul hqB hJs hKs hAC hd₁ hC, hx, δ₀_smul hqB hJs hKs hd₀]

/-- `β (σ j) = d₀ j`. -/
lemma β_σ (j : RingHom.ker qB) :
    β hqB hJs hKs hAC hd₁ hC (σ hqB hJs hKs hAC hd₀ hd₁ hC hβ j) = δ₀ hd₀ j :=
  (LinearEquiv.ofBijective _ hβ).apply_symm_apply _

/-- `β (1 ⊗ j) = d₁ j`. -/
lemma β_one_tmul (j : RingHom.ker qB) :
    β hqB hJs hKs hAC hd₁ hC ((1 : B₀) ⊗ₜ j) = δ₀ hd₁ j := by
  rw [β_tmul, map_one, one_smul]

/-- The comparison `B₀ ⊗[A₀] (B₀ ⊗[A₀] ker qB) → ker qD` through which the cocycle condition is
checked: `s ⊗ (s' ⊗ j) ↦ e₀' (d₀' s) • e₂ (d₀' s' • d₁ j)`. -/
def γ : B₀ ⊗[A₀] (B₀ ⊗[A₀] RingHom.ker qB) →+ RingHom.ker qD :=
  (Γ hqC hKs hLs hAC he₂ hC hD).comp
    ((β hqB hJs hKs hAC hd₁ hC).lTensor B₀).toAddMonoidHom

variable [Module.Flat A₀ B₀]

include hqD hβ in
/-- `γ` is injective when `A₀ → B₀` is flat, `e₂` is flat and `ker qD = (ker qC) D`. -/
lemma injective_γ (hL₂ : RingHom.ker qD = Ideal.map e₂ (RingHom.ker qC)) (hfe₂ : e₂.Flat) :
    Function.Injective (γ hqB hqC hJs hKs hLs hAC hd₁ he₂ hC hD) :=
  (injective_Γ hqC hqD hKs hLs hAC he₂ hC hD hL₂ hfe₂).comp
    (Module.Flat.lTensor_preserves_injective_linearMap _ hβ.1)

omit [Module.Flat A₀ B₀]

include h02 in
/-- `γ ∘ (B₀ ⊗ σ) = e₀ ∘ β`. -/
lemma γ_lTensor_σ (x : B₀ ⊗[A₀] RingHom.ker qB) :
    γ hqB hqC hJs hKs hLs hAC hd₁ he₂ hC hD
      ((σ hqB hJs hKs hAC hd₀ hd₁ hC hβ).restrictScalars A₀ |>.lTensor B₀ x) =
      ε he₀ (β hqB hJs hKs hAC hd₁ hC x) := by
  induction x with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul s j =>
    simp only [γ, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, β_σ, Γ_tmul, β_tmul,
      ε_smul hqC hKs hLs he₀]
    congr 1
    exact Subtype.ext (RingHom.congr_fun h02 j).symm

include hqB h01 h12 hd₀ he₀ in
/-- `γ ∘ (B₀ ⊗ (1 ⊗ ·)) = e₁ ∘ β`. -/
lemma γ_lTensor_mk (x : B₀ ⊗[A₀] RingHom.ker qB) :
    γ hqB hqC hJs hKs hLs hAC hd₁ he₂ hC hD ((TensorProduct.mk A₀ B₀ _ 1).lTensor B₀ x) =
      ε he₁ (β hqB hJs hKs hAC hd₁ hC x) := by
  have h : e₀'.comp d₀' = e₁'.comp d₀' := comp_eq_of_comp_eq hqB h01 hd₀ he₀ he₁
  induction x with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul s j =>
    simp only [γ, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      LinearMap.lTensor_tmul, TensorProduct.mk_apply, Γ_tmul, β_tmul,
      ε_smul hqC hKs hLs he₁, map_one, one_smul]
    rw [← RingHom.comp_apply e₀', h, RingHom.comp_apply]
    congr 1
    exact Subtype.ext (RingHom.congr_fun h12 j).symm

/-- `γ (1 ⊗ x) = e₂ (β x)`. -/
lemma γ_one_tmul (x : B₀ ⊗[A₀] RingHom.ker qB) :
    γ hqB hqC hJs hKs hLs hAC hd₁ he₂ hC hD ((1 : B₀) ⊗ₜ x) =
      ε he₂ (β hqB hJs hKs hAC hd₁ hC x) := by
  simp only [γ, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
    LinearMap.lTensor_tmul, Γ_tmul, map_one, one_smul]

include hqC hLs he₀ he₁ he₂ h01 h02 h12 hD hqD hβ in
/-- **The cocycle condition**: the coaction `σ` is coassociative. -/
theorem σ_coassoc (hL₂ : RingHom.ker qD = Ideal.map e₂ (RingHom.ker qC)) (hfe₂ : e₂.Flat)
    [Module.Flat A₀ B₀] (j : RingHom.ker qB) :
    ((σ hqB hJs hKs hAC hd₀ hd₁ hC hβ).restrictScalars A₀).lTensor B₀
        (σ hqB hJs hKs hAC hd₀ hd₁ hC hβ j) =
      (TensorProduct.mk A₀ B₀ _ 1).lTensor B₀ (σ hqB hJs hKs hAC hd₀ hd₁ hC hβ j) := by
  apply injective_γ hqB hqC hqD hJs hKs hLs hAC hd₁ he₂ hC hD hβ hL₂ hfe₂
  rw [γ_lTensor_σ hqB hqC hJs hKs hLs hAC hd₀ hd₁ he₀ he₂ h02 hC hD hβ,
    γ_lTensor_mk hqB hqC hJs hKs hLs hAC hd₀ hd₁ he₀ he₁ he₂ h01 h12 hC hD, β_σ]
  exact Subtype.ext (RingHom.congr_fun h01 j)

/-- The invariants of `σ` are the `j ∈ ker qB` with `d₀ j = d₁ j`. -/
lemma mem_coinvariants_σ (j : RingHom.ker qB) :
    j ∈ Module.FaithfullyFlat.coinvariants (σ hqB hJs hKs hAC hd₀ hd₁ hC hβ) ↔
      d₀ (j : B) = d₁ (j : B) := by
  rw [Module.FaithfullyFlat.mem_coinvariants, ← hβ.1.eq_iff, β_σ, β_one_tmul, Subtype.ext_iff]
  rfl

/-- The map `B₀ ⊗[A₀] ker qB → ker qC`, `s ⊗ j ↦ d₁' s • d₀ j`. -/
def α : B₀ ⊗[A₀] RingHom.ker qB →+ RingHom.ker qC :=
  TensorProduct.liftAddHom
    { toFun := fun s =>
        { toFun := fun j => d₁' s • δ₀ hd₀ j
          map_zero' := by rw [map_zero, smul_zero]
          map_add' := fun k k' => by rw [map_add, smul_add] }
      map_zero' := by ext k; simp
      map_add' := fun s s' => by ext k; simp [add_smul] }
    fun r s j => by
      change d₁' (r • s) • δ₀ hd₀ j = d₁' s • δ₀ hd₀ (r • j)
      rw [← algebraMap_smul B₀ r j, δ₀_smul hqB hJs hKs hd₀, Algebra.smul_def, map_mul, mul_smul,
        smul_comm, ← RingHom.comp_apply d₁', ← comp_algebraMap_eq hC, RingHom.comp_apply]

omit [Algebra A₀ C₀] [Module A₀ (RingHom.ker qC)] [IsScalarTower A₀ C₀ (RingHom.ker qC)] in
include hqC in
/-- `α` is bijective, by flatness of `d₀` and the pushout `C₀ = B₀ ⊗[A₀] B₀`. -/
theorem bijective_α (hK₀ : RingHom.ker qC = Ideal.map d₀ (RingHom.ker qB)) (hfd₀ : d₀.Flat) :
    Function.Bijective (α hqB hJs hKs hd₀ hC) := by
  let : Algebra B₀ C₀ := d₀'.toAlgebra
  let : Module B₀ (RingHom.ker qC) := Module.compHom _ d₀'
  have : IsScalarTower B₀ C₀ (RingHom.ker qC) := ⟨fun s c k => mul_smul (d₀' s) c k⟩
  exact bijective_of_isPushout_of_bijective_liftBaseChange d₁' hC.flip
    (RingHom.kerLinearMap hK₀ hd₀ hJs hKs hqB)
    (RingHom.bijective_liftBaseChange_kerLinearMap hqC hK₀ hd₀ hJs hKs hqB hfd₀)
    (α hqB hJs hKs hd₀ hC) fun s j => rfl

include hqC in
/-- The translates `(1 ⊗ s) • σ j` span `B₀ ⊗[A₀] ker qB`: the descent datum is surjective. -/
theorem span_σ_eq_top (hK₀ : RingHom.ker qC = Ideal.map d₀ (RingHom.ker qB)) (hfd₀ : d₀.Flat) :
    Submodule.span B₀ (Set.range fun p : B₀ × RingHom.ker qB =>
      ((LinearMap.lsmul B₀ (RingHom.ker qB) p.1).restrictScalars A₀).lTensor B₀
        (σ hqB hJs hKs hAC hd₀ hd₁ hC hβ p.2)) = ⊤ := by
  set G := Submodule.span B₀ (Set.range fun p : B₀ × RingHom.ker qB =>
      ((LinearMap.lsmul B₀ (RingHom.ker qB) p.1).restrictScalars A₀).lTensor B₀
        (σ hqB hJs hKs hAC hd₀ hd₁ hC hβ p.2))
  have key : ∀ x, ∃ y ∈ G, β hqB hJs hKs hAC hd₁ hC y = α hqB hJs hKs hd₀ hC x := by
    intro x
    induction x with
    | add x x' hx hx' =>
      obtain ⟨y, hy, h⟩ := hx
      obtain ⟨y', hy', h'⟩ := hx'
      exact ⟨y + y', G.add_mem hy hy', by rw [map_add, map_add, h, h']⟩
    | tmul s j =>
      refine ⟨_, Submodule.subset_span ⟨(s, j), rfl⟩, ?_⟩
      rw [β_lTensor_smul, β_σ]
      rfl
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨x, hx⟩ := (bijective_α hqB hqC hJs hKs hd₀ hC hK₀ hfd₀).2
    (β hqB hJs hKs hAC hd₁ hC z)
  obtain ⟨y, hy, h⟩ := key x
  rwa [← hβ.1 (h.trans hx)]

include hqB hqC hqD hJs hKs hLs hAC hd₀ hd₁ he₀ he₁ he₂ h01 h02 h12 hC hD hβ in
/-- **Vanishing of `H¹`.** Every element of `B` whose reduction comes from `A₀` can be corrected
by an element of `ker qB` to an element of the equalizer of `d₀` and `d₁`. The defect
`d₀ b - d₁ b` is a `1`-cocycle in `ker qC`, which is a coboundary by faithfully flat descent. -/
theorem exists_sub_mem_eqLocus (hL₂ : RingHom.ker qD = Ideal.map e₂ (RingHom.ker qC))
    (hfe₂ : e₂.Flat) [Module.FaithfullyFlat A₀ B₀] (b : B)
    (hb : qB b ∈ Set.range (algebraMap A₀ B₀)) :
    ∃ j : RingHom.ker qB, d₀ (b - j) = d₁ (b - j) := by
  obtain ⟨a, ha⟩ := hb
  have hmem : d₀ b - d₁ b ∈ RingHom.ker qC := by
    have h0 := RingHom.congr_fun hd₀ b
    have h1 := RingHom.congr_fun hd₁ b
    have hw := RingHom.congr_fun (comp_algebraMap_eq hC) a
    simp only [RingHom.comp_apply] at h0 h1 hw
    rw [RingHom.mem_ker, map_sub, h0, h1, ← ha, hw, sub_self]
  set δ : RingHom.ker qC := ⟨d₀ b - d₁ b, hmem⟩
  set τ := (LinearEquiv.ofBijective _ hβ).symm δ
  have hτ : β hqB hJs hKs hAC hd₁ hC τ = δ := (LinearEquiv.ofBijective _ hβ).apply_symm_apply δ
  have hcoc : ((σ hqB hJs hKs hAC hd₀ hd₁ hC hβ).restrictScalars A₀).lTensor B₀ τ -
      (TensorProduct.mk A₀ B₀ _ 1).lTensor B₀ τ + (1 : B₀) ⊗ₜ[A₀] τ = 0 := by
    apply injective_γ hqB hqC hqD hJs hKs hLs hAC hd₁ he₂ hC hD hβ hL₂ hfe₂
    rw [map_add, map_sub, map_zero,
      γ_lTensor_σ hqB hqC hJs hKs hLs hAC hd₀ hd₁ he₀ he₂ h02 hC hD hβ,
      γ_lTensor_mk hqB hqC hJs hKs hLs hAC hd₀ hd₁ he₀ he₁ he₂ h01 h12 hC hD, γ_one_tmul, hτ]
    apply Subtype.ext
    have h01b := RingHom.congr_fun h01 b
    have h02b := RingHom.congr_fun h02 b
    have h12b := RingHom.congr_fun h12 b
    simp only [RingHom.comp_apply] at h01b h02b h12b
    simp only [Submodule.coe_add, Submodule.coe_sub, RingHom.coe_kerHom, δ, map_sub,
      ZeroMemClass.coe_zero, h01b, h02b, h12b]
    ring
  obtain ⟨n, hn⟩ := Module.FaithfullyFlat.exists_sub_one_tmul_eq_of_cocycle _ τ hcoc
  refine ⟨n, ?_⟩
  have h := congrArg (fun x => ((β hqB hJs hKs hAC hd₁ hC x : RingHom.ker qC) : C)) hn
  simp only [map_sub, LinearMap.restrictScalars_apply, β_σ, β_one_tmul, hτ, Submodule.coe_sub,
    RingHom.coe_kerHom, δ] at h
  rw [map_sub, map_sub, ← sub_eq_zero]
  linear_combination -h

include hqC hqD hLs he₀ he₁ he₂ h01 h02 h12 hD in
/-- **Descent of `ker qB`.** `ker qB` is the base change of the invariants of `σ`. -/
theorem bijective_liftBaseChange_coinvariants_σ
    (hL₂ : RingHom.ker qD = Ideal.map e₂ (RingHom.ker qC)) (hfe₂ : e₂.Flat)
    (hK₀ : RingHom.ker qC = Ideal.map d₀ (RingHom.ker qB)) (hfd₀ : d₀.Flat)
    [Module.FaithfullyFlat A₀ B₀] :
    Function.Bijective ((Module.FaithfullyFlat.coinvariants
      (σ hqB hJs hKs hAC hd₀ hd₁ hC hβ)).subtype.liftBaseChange B₀) :=
  Module.FaithfullyFlat.bijective_liftBaseChange_coinvariants _
    (σ_coassoc hqB hqC hqD hJs hKs hLs hAC hd₀ hd₁ he₀ he₁ he₂ h01 h02 h12 hC hD hβ hL₂ hfe₂)
    (span_σ_eq_top hqB hqC hJs hKs hAC hd₀ hd₁ hC hβ hK₀ hfd₀)

include hqB hqC hqD hJs hKs hLs hAC hd₀ hd₁ he₀ he₁ he₂ h01 h02 h12 hC hD hβ in
/-- The reduction `ψ` of the equalizer of `d₀` and `d₁` is surjective onto `A₀`. -/
theorem surjective_of_comp_eq (hL₂ : RingHom.ker qD = Ideal.map e₂ (RingHom.ker qC))
    (hfe₂ : e₂.Flat) [Module.FaithfullyFlat A₀ B₀] (hφ : Function.Injective (algebraMap A₀ B₀))
    {ψ : RingHom.eqLocus d₀ d₁ →+* A₀}
    (hφψ : (algebraMap A₀ B₀).comp ψ = qB.comp (RingHom.eqLocus d₀ d₁).subtype) :
    Function.Surjective ψ := by
  intro a₀
  obtain ⟨b, hb⟩ := hqB (algebraMap A₀ B₀ a₀)
  obtain ⟨j, hj⟩ := exists_sub_mem_eqLocus hqB hqC hqD hJs hKs hLs hAC hd₀ hd₁ he₀ he₁ he₂ h01
    h02 h12 hC hD hβ hL₂ hfe₂ b ⟨a₀, hb.symm⟩
  refine ⟨⟨b - j, hj⟩, hφ ((RingHom.congr_fun hφψ _).trans ?_)⟩
  change qB (b - j) = _
  rw [map_sub, RingHom.mem_ker.mp j.2, sub_zero, hb]

end SquareZeroEqualizerDescent

/-! ### The equalizer of a first-order thickening of an étale Čech nerve -/

open CategoryTheory in
/-- **The algebraic core of Stacks 05ZR, first-order case.** Let `B → C ⇉ D` be the rings of
functions of `U ⇇ U ×_F U ⇇ U ×_F U ×_F U` for an étale affine chart `U` of an algebraic space
`F`, with `d₀, d₁ : B → C` and `e₀, e₁, e₂ : C → D` the pullbacks along the projections, and let
`B₀ → C₀ ⇉ D₀` be the same rings for the reduction `G = Spec A₀` of `F`, a first-order thickening:
`ker (B → B₀)` has square zero, `B₀` is étale and faithfully flat over `A₀`, `C₀ = B₀ ⊗[A₀] B₀`
and `D₀ = C₀ ⊗[B₀] C₀`, all the maps of the thickened nerve are flat, and every kernel is the
extension of the previous one. Then the equalizer `A = {b | d₀ b = d₁ b}` of `d₀` and `d₁` is a
ring over which `B` is étale and faithfully flat, with `B ⊗[A] B = C`.

The proof descends the `B₀`-module `J = ker (B → B₀)` along `A₀ → B₀`: flatness of `d₁` and
`e₂` and the two pushout squares give a coassociative coaction `J → B₀ ⊗[A₀] J`, so `J` is the
base change of `A ∩ J`; vanishing of the first Amitsur cohomology makes `A → A₀` surjective, and
Stacks 05YT (`Algebra.Etale.of_ker_sq_eq_bot_of_isBaseChange`) makes `A → B` étale. -/
theorem RingHom.eqLocus_etale_faithfullyFlat_isPushout {A₀ B B₀ C C₀ D D₀ : Type u}
    [CommRing A₀] [CommRing B] [CommRing B₀] [CommRing C] [CommRing C₀] [CommRing D] [CommRing D₀]
    (qB : B →+* B₀) (qC : C →+* C₀) (qD : D →+* D₀)
    (hqB : Function.Surjective qB) (hqC : Function.Surjective qC) (hqD : Function.Surjective qD)
    (hJ : RingHom.ker qB ^ 2 = ⊥)
    (d₀ d₁ : B →+* C) (e₀ e₁ e₂ : C →+* D)
    (h01 : e₀.comp d₀ = e₁.comp d₀) (h02 : e₀.comp d₁ = e₂.comp d₀)
    (h12 : e₁.comp d₁ = e₂.comp d₁)
    (d₀' d₁' : B₀ →+* C₀) (e₀' e₁' e₂' : C₀ →+* D₀)
    (hd₀ : qC.comp d₀ = d₀'.comp qB) (hd₁ : qC.comp d₁ = d₁'.comp qB)
    (he₀ : qD.comp e₀ = e₀'.comp qC) (he₁ : qD.comp e₁ = e₁'.comp qC)
    (he₂ : qD.comp e₂ = e₂'.comp qC)
    (φ : A₀ →+* B₀) (hφe : φ.Etale) (hφff : φ.FaithfullyFlat)
    (hC : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom φ) (CommRingCat.ofHom d₀')
      (CommRingCat.ofHom d₁'))
    (hD : IsPushout (CommRingCat.ofHom d₁') (CommRingCat.ofHom d₀') (CommRingCat.ofHom e₀')
      (CommRingCat.ofHom e₂'))
    (hfd₀ : d₀.Flat) (hfd₁ : d₁.Flat) (hfe₂ : e₂.Flat)
    (hK₀ : RingHom.ker qC = Ideal.map d₀ (RingHom.ker qB))
    (hK₁ : RingHom.ker qC = Ideal.map d₁ (RingHom.ker qB))
    (hL₂ : RingHom.ker qD = Ideal.map e₂ (RingHom.ker qC)) :
    (RingHom.eqLocus d₀ d₁).subtype.Etale ∧ (RingHom.eqLocus d₀ d₁).subtype.FaithfullyFlat ∧
      IsPushout (CommRingCat.ofHom (RingHom.eqLocus d₀ d₁).subtype)
        (CommRingCat.ofHom (RingHom.eqLocus d₀ d₁).subtype) (CommRingCat.ofHom d₀)
        (CommRingCat.ofHom d₁) := by
  set A := RingHom.eqLocus d₀ d₁
  have hK : RingHom.ker qC ^ 2 = ⊥ := by rw [hK₀, ← Ideal.map_pow, hJ, Ideal.map_bot]
  have hL : RingHom.ker qD ^ 2 = ⊥ := by rw [hL₂, ← Ideal.map_pow, hK, Ideal.map_bot]
  let : Algebra A₀ B₀ := φ.toAlgebra
  let : Algebra A₀ C₀ := (d₀'.comp φ).toAlgebra
  have : Module.FaithfullyFlat A₀ B₀ := hφff
  have : Algebra.Etale A₀ B₀ := hφe
  let : Module B₀ (RingHom.ker qB) := RingHom.moduleOfKerSMul hqB _
    fun j hj x => Subtype.ext (Ideal.mul_eq_zero_of_sq_eq_bot hJ hj x.2)
  let : Module A₀ (RingHom.ker qB) := Module.compHom _ φ
  have : IsScalarTower A₀ B₀ (RingHom.ker qB) := ⟨fun r s j => mul_smul (φ r) s j⟩
  let : Module C₀ (RingHom.ker qC) := RingHom.moduleOfKerSMul hqC _
    fun j hj x => Subtype.ext (Ideal.mul_eq_zero_of_sq_eq_bot hK hj x.2)
  let : Module A₀ (RingHom.ker qC) := Module.compHom _ (d₀'.comp φ)
  have : IsScalarTower A₀ C₀ (RingHom.ker qC) := ⟨fun r s j => mul_smul (d₀' (φ r)) s j⟩
  let : Module D₀ (RingHom.ker qD) := RingHom.moduleOfKerSMul hqD _
    fun j hj x => Subtype.ext (Ideal.mul_eq_zero_of_sq_eq_bot hL hj x.2)
  have hJs : ∀ (b : B) (j : RingHom.ker qB), qB b • j = b • j :=
    RingHom.moduleOfKerSMul_smul hqB _ _
  have hKs : ∀ (c : C) (k : RingHom.ker qC), qC c • k = c • k :=
    RingHom.moduleOfKerSMul_smul hqC _ _
  have hLs : ∀ (x : D) (l : RingHom.ker qD), qD x • l = x • l :=
    RingHom.moduleOfKerSMul_smul hqD _ _
  have hAC : algebraMap A₀ C₀ = d₀'.comp (algebraMap A₀ B₀) := rfl
  have hβ := SquareZeroEqualizerDescent.bijective_β hqB hqC hJs hKs hAC hd₁ hC hK₁ hfd₁
  have hdesc := SquareZeroEqualizerDescent.bijective_liftBaseChange_coinvariants_σ hqB hqC hqD
    hJs hKs hLs hAC hd₀ hd₁ he₀ he₁ he₂ h01 h02 h12 hC hD hβ hL₂ hfe₂ hK₀ hfd₀
  have hN := SquareZeroEqualizerDescent.mem_coinvariants_σ hqB hJs hKs hAC hd₀ hd₁ hC hβ
  have hrange : ∀ a : A, qB.comp A.subtype a ∈ φ.range := fun a => by
    refine RingHom.mem_range_of_isPushout_of_faithfullyFlat φ hφff d₀' d₁' hC ?_
    change d₀' (qB a) = d₁' (qB a)
    rw [← RingHom.comp_apply, ← hd₀, ← RingHom.comp_apply, ← hd₁]
    exact congrArg qC a.2
  obtain ⟨ψ, hφψ⟩ := RingHom.exists_comp_eq_of_forall_mem_range hφff.injective _ hrange
  have hψ := SquareZeroEqualizerDescent.surjective_of_comp_eq hqB hqC hqD hJs hKs hLs hAC hd₀ hd₁
    he₀ he₁ he₂ h01 h02 h12 hC hD hβ hL₂ hfe₂ hφff.injective hφψ
  have hιe : A.subtype.Etale := SquareZeroEqualizerDescent.etale_subtype_of_comp_eq
    hφff.injective hφψ hJs _ hN hdesc hqB hψ hJ
  have hιf : A.subtype.Flat := (RingHom.Etale.iff_flat_and_formallyUnramified.mp hιe).1
  have hsq := SquareZeroEqualizerDescent.ker_sq_eq_bot_of_comp_eq hφff.injective hφψ hJ
  refine ⟨hιe, ?_, ?_⟩
  · refine RingHom.FaithfullyFlat.of_surjective_of_isNilpotent_ker A.subtype hιf ψ hψ qB φ hφψ
      hφff fun x hx => ⟨2, ?_⟩
    simpa [hsq] using Ideal.pow_mem_pow hx 2
  · exact CommRingCat.isPushout_of_isPushout_reduction A.subtype hιf d₀ d₁
      (RingHom.ext fun a => a.2) hfd₀ qB qC hqB ψ hψ φ hφψ hsq
      (SquareZeroEqualizerDescent.ker_eq_map_of_comp_eq hφff.injective hφψ hJs _ hN hdesc hqB)
      d₀' d₁' hd₀ hd₁ hC hK₀
