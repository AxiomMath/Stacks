module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.FrameDifferentials

/-!
# The module of differentials of a chart along a frame

Let `R` be an algebra over `A'` and let `B` be an `R`-algebra; write `ū : R → B` for the
structure map. The `B`-module `B ⊗[R] Ω[R⁄A']` represents, on modules over `B`-algebras, the
derivations along the composites of `ū`: for an algebra map `q : B → C` and a `C`-module `E`,
the derivations of `R` along `q ∘ ū` with values in `E` are the `q`-semilinear maps
`B ⊗[R] Ω[R⁄A'] → E`, through the universal derivation `r ↦ 1 ⊗ dr`.

## Main definitions

* `Stacks.ChartGlue.frameDiff`: the universal derivation `r ↦ 1 ⊗ dr` into `B ⊗[R] Ω[R⁄A']`.
* `Stacks.ChartGlue.frameLift`: the `q`-semilinear map attached to a derivation along `q ∘ ū`.

## Main results

* `Stacks.ChartGlue.frameLift_frameDiff`: its value on the universal derivation.
* `Stacks.ChartGlue.frame_semilinear_ext`: a `q`-semilinear map out of `B ⊗[R] Ω[R⁄A']` is
  determined by its values on the universal derivation.
-/

@[expose] public noncomputable section

open TensorProduct

universe u v w

namespace Stacks.ChartGlue

variable {A' : Type w} [CommRing A'] (R : Type u) [CommRing R] [Algebra A' R]
  (B : Type u) [CommRing B] [Algebra A' B] [Algebra R B] [IsScalarTower A' R B]

/-- The `B`-module of differentials of `R` read along the structure map `R → B`. -/
abbrev FrameModule := B ⊗[R] Ω[R⁄A']

/-- The universal derivation `r ↦ 1 ⊗ dr`. -/
def frameDiff : DerAlong (IsScalarTower.toAlgHom A' R B) (FrameModule (A' := A') R B) :=
  DerAlong.ofSemilinear
    { toFun := fun ω ↦ (1 : B) ⊗ₜ ω
      map_add' := fun ω ω' ↦ tmul_add _ _ _
      map_smul' := fun r ω ↦ by
        change (1 : B) ⊗ₜ[R] (r • ω) = (algebraMap R B r) • ((1 : B) ⊗ₜ[R] ω)
        rw [← smul_tmul, smul_tmul']
        congr 1
        rw [Algebra.smul_def, smul_eq_mul] }

/-- The universal derivation sends `r` to `1 ⊗ dr`. -/
@[simp] lemma frameDiff_apply (r : R) :
    frameDiff (A' := A') R B r = (1 : B) ⊗ₜ KaehlerDifferential.D A' R r := rfl

variable {R B}

/-- The image of the universal derivation spans the module over `B`. -/
lemma frame_span : Submodule.span B (Set.range (frameDiff (A' := A') R B)) = ⊤ := by
  have key (b : B) (ω : Ω[R⁄A']) : b ⊗ₜ[R] ω = b • ((1 : B) ⊗ₜ[R] ω) := by
    rw [smul_tmul', smul_eq_mul, mul_one]
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul b ω =>
    have hω : ω ∈ Submodule.span R (Set.range (KaehlerDifferential.D A' R)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    rw [key b ω]
    refine Submodule.smul_mem _ b ?_
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, rfl⟩ := hx
      exact Submodule.subset_span ⟨r, rfl⟩
    | zero => rw [tmul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [tmul_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      rw [← smul_tmul, key]
      exact Submodule.smul_mem _ _ hx

variable {C : Type u} [CommRing C] {E : Type v} [AddCommGroup E] [Module C E]

/-- **A `q`-semilinear map out of the frame module is determined by its values on the universal
derivation.** -/
lemma frame_semilinear_ext {q : B →+* C}
    {l l' : FrameModule (A' := A') R B →ₛₗ[q] E}
    (h : ∀ r, l (frameDiff (A' := A') R B r) = l' (frameDiff (A' := A') R B r)) : l = l' := by
  ext x
  have hx : x ∈ Submodule.span B (Set.range (frameDiff (A' := A') R B)) := by
    rw [frame_span]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨r, rfl⟩ := hx; exact h r
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul a x _ hx => rw [l.map_smulₛₗ, l'.map_smulₛₗ, hx]

variable [Algebra A' C]

/-- **The `q`-semilinear map attached to a derivation along `q ∘ ū`.** -/
def frameLift (q : B →ₐ[A'] C) (δ : DerAlong (q.comp (IsScalarTower.toAlgHom A' R B)) E) :
    FrameModule (A' := A') R B →ₛₗ[(q : B →+* C)] E := by
  let σ : R →+* C := ((q.comp (IsScalarTower.toAlgHom A' R B) : R →ₐ[A'] C) : R →+* C)
  let L := δ.toSemilinear
  let f : B →ₛₗ[σ] Ω[R⁄A'] →ₛₗ[σ] E :=
    { toFun := fun b ↦ (q b) • L
      map_add' := fun b b' ↦ by rw [map_add, add_smul]
      map_smul' := fun r b ↦ by
        ext ω
        change q (r • b) • L ω = σ r • (q b • L ω)
        rw [smul_smul, Algebra.smul_def, map_mul]
        rfl }
  exact
    { toFun := TensorProduct.lift f
      map_add' := map_add _
      map_smul' := fun c x ↦ by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
        | tmul b ω =>
          rw [smul_tmul', TensorProduct.lift.tmul, TensorProduct.lift.tmul]
          change q (c • b) • L ω = q c • (q b • L ω)
          rw [smul_eq_mul, map_mul, mul_smul] }

/-- The map `frameLift q δ` sends `b ⊗ ω` to `q b • δ̄ ω`, where `δ̄` is the semilinear map of `δ`
on `Ω[R⁄A']`. -/
@[simp] lemma frameLift_tmul (q : B →ₐ[A'] C)
    (δ : DerAlong (q.comp (IsScalarTower.toAlgHom A' R B)) E) (b : B) (ω : Ω[R⁄A']) :
    frameLift q δ (b ⊗ₜ ω) = q b • δ.toSemilinear ω := rfl

/-- The map `frameLift q δ` sends the universal derivation of `r` to `δ r`. -/
@[simp] lemma frameLift_frameDiff (q : B →ₐ[A'] C)
    (δ : DerAlong (q.comp (IsScalarTower.toAlgHom A' R B)) E) (r : R) :
    frameLift q δ (frameDiff (A' := A') R B r) = δ r := by
  rw [frameDiff_apply, frameLift_tmul, map_one, one_smul, DerAlong.toSemilinear_D]

/-- Every derivation along `q ∘ ū` is the pushforward of the universal one along its
semilinear map. -/
lemma map_frameLift_frameDiff (q : B →ₐ[A'] C)
    (δ : DerAlong (q.comp (IsScalarTower.toAlgHom A' R B)) E) :
    (frameDiff (A' := A') R B).map q (frameLift q δ) = δ :=
  DerAlong.ext (funext fun r ↦ frameLift_frameDiff q δ r)

end Stacks.ChartGlue

end
