module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningDeRham

/-!
# The order of the thickening `T → T''`, and its square-zero presentation over `T'`

Let `(T, J, δ)` be a divided power scheme over a scheme `Y`.
`StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickening` builds the structure sheaf
`𝒪_{T''} = 𝒪_T ⊕ Ω_{T/Y,δ} ⊕ Ω_{T/Y,δ} ⊕ Ω²_{T/Y,δ}` of the second-order universal thickening,
its ideal `J''` and its divided powers `δ''`.  This module measures the *order* of the thickening
`T → T''` and presents `T''` as a square-zero extension of the first-order universal thickening
`T'`, which is the shape a realization as a scheme needs.

Two facts about the ideal `I = ker(𝒪_{T''} → 𝒪_T) = 0 ⊕ Ω ⊕ Ω ⊕ Ω²`:

* `I³ = 0`, so `T → T''` is a thickening of order two — the "second order thickening" of
  [Stacks, Tag 07J3];
* `I² = 0` **if and only if** every exterior product `ω₁ ∧ ω₂` of divided power differentials
  vanishes, because `(0, ω₁, 0, 0) · (0, 0, ω₂, 0) = (0, 0, 0, ω₁ ∧ ω₂)`.  So `I` is *not* an
  ideal of square zero.

And one fact about the projection `𝒪_{T''} → 𝒪_{T'}`, `(f, ω₁, ω₂, η) ↦ (f, ω₁)`: its kernel
`0 ⊕ 0 ⊕ Ω ⊕ Ω²` *is* an ideal of square zero, the map is split by `q₀₁`, and it is compatible
with the divided power structures `δ''` and `δ'`.

## Main definitions

* `Crystalline.secondOrderThickeningProj` — the projection `𝒪_{T''} → 𝒪_{T'}`.
* `Crystalline.secondOrderThickeningFstProj` — the projection `𝒪_{T''} → 𝒪_T`, the composite of
  the previous one with the projection of the first-order thickening.
* `Crystalline.secondOrderThickeningTopIdeal` — the top summand `Ω²_{T/Y,δ}` as an ideal of
  `𝒪_{T''}`.

## Main results

* `Crystalline.secondOrderThickening_ker_cube` — **`T → T''` is a second-order thickening**:
  the ideal of `𝒪_{T''} → 𝒪_T` has vanishing cube.
* `Crystalline.secondOrderThickening_ker_sq_eq_bot_iff` — that ideal has vanishing square exactly
  when the exterior product is identically zero; with
  `Crystalline.secondOrderExt_mul_mk`, the explicit product that exhibits a wedge inside `I²`,
  this is the precise obstruction discussed below.
* `Crystalline.secondOrderThickening_ker_proj_sq` — **the ideal of `T' → T''` is of square
  zero**.
* `Crystalline.secondOrderThickeningQ₀₁_comp_proj` — `q₀₁` splits the projection onto `𝒪_{T'}`.
* `Crystalline.secondOrderThickeningProj_isDPMorphism` — the projection `𝒪_{T''} → 𝒪_{T'}` is
  compatible with `δ''` and `δ'`.

## What is and is not proved

**This module works with sheaves of rings on the space of `T`; the object `(U, T'', δ'')` of
`CRIS(X/S)` is built elsewhere, in
`StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningScheme`, as
`Crystalline.GlobalCrystallineSituation.secondOrderThickeningObject`.**  For the first-order
thickening the corresponding statement is
`Crystalline.GlobalCrystallineSituation.firstOrderThickeningObject`, proved in
`StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickeningScheme` by realizing `𝒪_{T'}` as a
scheme with `Stacks.Thickenings.squareZeroExtension_realization` in one step over `T`.  That
particular route is not the one `T''` admits, for a reason that is a theorem rather than a guess:

1. `Stacks.Thickenings.SquareZeroExtension` carries the field
   `square_zero : ι U x * ι U y = 0`, a *literal* vanishing of the square of the kernel, and
   `Crystalline.secondOrderThickening_ker_sq_eq_bot_iff` says the ideal of `T → T''` has that
   property only when every exterior product of divided power differentials vanishes.  So
   `squareZeroExtension_realization` does not apply to `𝒪_{T''} → 𝒪_T`.  This is not a defect of
   the construction: the source calls `T''` a *second order* thickening, and
   `Crystalline.secondOrderThickening_ker_cube` is that statement.
2. The library has no realization theorem for a nilpotent, finite-order or `n`-th order
   extension of a structure sheaf — `Stacks.Thickenings.IsNthOrderThickening` occurs only as a
   *hypothesis* or as a property of an already-constructed scheme, never as the output of a
   realization.  The general machinery that would support one (the "affine charts are `Spec` of
   their sections" step) is private to
   `StacksFrontier/AlgebraicGeometry/Thickenings/SquareZeroExtension.lean` and is stated for a
   `SquareZeroExtension`.

The way through, which this module sets up, is to realize `T''` in *two* square-zero steps
rather than one, using the scheme `T'` that
`StacksFrontier.AlgebraicGeometry.Crystalline.UniversalThickeningScheme` already provides and whose
structure sheaf is literally `𝒪_{T'}`:

`Crystalline.secondOrderThickening_ker_proj_sq` says `𝒪_{T''}` is a square-zero extension of
`𝒪_{T'}`, with kernel `K = 0 ⊕ 0 ⊕ Ω_{T/Y,δ} ⊕ Ω²_{T/Y,δ}` — additively `Ω ⊕ Ω²`, and an
`𝒪_{T'}`-module by `(f, ω₁) · (ω₂, η) = (f ω₂, f η + ω₁ ∧ ω₂)`.  Feeding that to
`squareZeroExtension_realization` over `T'` would give `T''` as a scheme, first-order over `T'`
and so second-order over `T` by `Crystalline.secondOrderThickening_ker_cube`.  **That route has
since been carried out**, and the three inputs this module listed as missing are all supplied:

* `Ω²_{T/Y,δ}` is quasi-coherent — `Crystalline.dpSecondExteriorPower_isQuasicoherent`
  (`StacksFrontier/AlgebraicGeometry/Crystalline/SecondExteriorPowerQuasicoherent.lean`), via the
  identification of the sheafified `PresheafOfModules.extPow 2` with the bundled exterior power.
* `K` is a quasi-coherent `𝒪_{T'}`-module — `Crystalline.secondOrderKerSheaf_isQuasicoherent`
  (`StacksFrontier/AlgebraicGeometry/Crystalline/SecondOrderThickeningKernel.lean`), from the short
  exact sequence `0 → i_*Ω² → K → i_*Ω → 0` and closure of quasi-coherent modules under
  extensions.  The extension is genuinely non-split.
* The order of `T ⟶ T''` at scheme level is
  `Crystalline.secondOrderThickeningιT_isNthOrderThickening`
  (`StacksFrontier/AlgebraicGeometry/Crystalline/SecondOrderThickeningScheme.lean`) — but **not** by
  the general principle this module conjectured.  "A composite of two first-order thickenings is
  second-order" is *false*: for `Z = Spec k[x]/(x⁴)` with `I = (x²)` and `K = (x)`, both steps are
  first-order yet `K³ = (x³) ≠ 0`, so the general statement gives order three.  The order-2 fact
  is transported from `Crystalline.secondOrderThickening_ker_cube` instead, which is what makes
  this particular composite second-order.

Nothing weaker than the real statement is recorded under Tag 07J3.  The six site morphisms
`q₀, q₁, q₂, q₀₁, q₁₂, q₀₂` of `CRIS(X/S)` and the transported composition relations do not live
in this module; they are in
`StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningScheme`, over the object
`Crystalline.GlobalCrystallineSituation.secondOrderThickeningObject` that the two-step
realization above yields.  Their sheaf-level counterparts are in
`StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickening` and
`StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningDeRham`.

## References

* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open scoped AlgebraicGeometry

universe u

namespace Crystalline

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)

/-! ### The projection onto the first-order thickening -/

/-- **The projection `𝒪_{T''} → 𝒪_{T'}`**, `(f, ω₁, ω₂, η) ↦ (f, ω₁)`.  It is a homomorphism
because the first two coordinates of a second-order product are the square-zero product of the
first two coordinates. -/
public def secondOrderThickeningProj :
    secondOrderThickeningPresheaf T Y f ⟶ firstOrderThickeningPresheaf T Y f where
  app W := sqZeroExtLift (dpDifferentialsModules T Y f)
    (CommRingCat.ofHom (secondOrderExtFstHom (dpWedge T Y f) W))
    (AddMonoidHom.mk' secondOrderExtLeft (fun x y => secondOrderExtLeft_add x y))
    (fun x y => secondOrderExtLeft_mul x y)
  naturality _ _ _ := CommRingCat.hom_ext (RingHom.ext fun _ => sqZeroExt_ext rfl rfl)

/-- **The projection `𝒪_{T''} → 𝒪_T`**, `(f, ω₁, ω₂, η) ↦ f`; the structure map of the
thickening `T → T''`, taken as the composite of the projection onto `𝒪_{T'}` with the projection
of the first-order thickening so that it inherits their spelling of the structure sheaf. -/
public def secondOrderThickeningFstProj :=
  secondOrderThickeningProj T Y f ≫ firstOrderThickeningProj T Y f

section Computations

variable {T Y f} (W : (Opens ↑T.scheme)ᵒᵖ)

/-- The first coordinate of the image of `x` under `secondOrderThickeningProj` is the first
coordinate of `x`. -/
@[simp] public theorem secondOrderThickeningProj_fst (x : SecondOrderExt (dpWedge T Y f) W) :
    sqZeroExtFst (((secondOrderThickeningProj T Y f).app W).hom x) = secondOrderExtFst x := rfl

/-- The second coordinate of the image of `x` under `secondOrderThickeningProj` is the first
middle coordinate of `x`. -/
@[simp] public theorem secondOrderThickeningProj_snd (x : SecondOrderExt (dpWedge T Y f) W) :
    sqZeroExtSnd (((secondOrderThickeningProj T Y f).app W).hom x) = secondOrderExtLeft x := rfl

/-- The projection `secondOrderThickeningFstProj` sends a section `x` to its first coordinate. -/
@[simp] public theorem secondOrderThickeningFstProj_apply
    (x : SecondOrderExt (dpWedge T Y f) W) :
    ((secondOrderThickeningFstProj T Y f).app W).hom x = secondOrderExtFst x := rfl

/-- The product of two sections whose first and first middle coordinates vanish is zero: this is
the square-zero property of the ideal of `T' → T''`, read on sections. -/
public theorem secondOrderExt_mul_eq_zero_of_fst_left
    {x y : SecondOrderExt (dpWedge T Y f) W}
    (hx0 : secondOrderExtFst x = 0) (hx1 : secondOrderExtLeft x = 0)
    (hy0 : secondOrderExtFst y = 0) (hy1 : secondOrderExtLeft y = 0) : x * y = 0 := by
  refine secondOrderExt_ext ?_ ?_ ?_ ?_
  · rw [secondOrderExtFst_mul, hx0, zero_mul, secondOrderExtFst_zero]
  · rw [secondOrderExtLeft_mul, hx1, hy1, smul_zero, smul_zero, add_zero,
      secondOrderExtLeft_zero]
  · rw [secondOrderExtRight_mul, hx0, hy0, zero_smul, zero_smul, add_zero,
      secondOrderExtRight_zero]
  · rw [secondOrderExtTop_mul, hx0, hy0, zero_smul, zero_smul, add_zero, hx1, hy1,
      bilinearApp_zero_left, bilinearApp_zero_left, add_zero, add_zero,
      secondOrderExtTop_zero]

/-- **The product of two sections of the ideal of `T → T''` has only a top coordinate.** -/
public theorem secondOrderExt_mul_coords_of_fst {x y : SecondOrderExt (dpWedge T Y f) W}
    (hx0 : secondOrderExtFst x = 0) (hy0 : secondOrderExtFst y = 0) :
    secondOrderExtFst (x * y) = 0 ∧ secondOrderExtLeft (x * y) = 0 ∧
      secondOrderExtRight (x * y) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [secondOrderExtFst_mul, hx0, zero_mul]
  · rw [secondOrderExtLeft_mul, hx0, hy0, zero_smul, zero_smul, add_zero]
  · rw [secondOrderExtRight_mul, hx0, hy0, zero_smul, zero_smul, add_zero]

/-- **A section with only a top coordinate annihilates the ideal of `T → T''`**, which is what
makes the cube of that ideal vanish. -/
public theorem secondOrderExt_mul_eq_zero_of_top {x y : SecondOrderExt (dpWedge T Y f) W}
    (hx0 : secondOrderExtFst x = 0) (hx1 : secondOrderExtLeft x = 0)
    (hx2 : secondOrderExtRight x = 0) (hy0 : secondOrderExtFst y = 0) : x * y = 0 := by
  refine secondOrderExt_ext ?_ ?_ ?_ ?_
  · rw [secondOrderExtFst_mul, hx0, zero_mul, secondOrderExtFst_zero]
  · rw [secondOrderExtLeft_mul, hx0, hx1, zero_smul, smul_zero, add_zero,
      secondOrderExtLeft_zero]
  · rw [secondOrderExtRight_mul, hx0, hx2, zero_smul, smul_zero, add_zero,
      secondOrderExtRight_zero]
  · simp only [secondOrderExtTop_mul, hx0, hx1, hx2, hy0, zero_smul,
      bilinearApp_zero_left, bilinearApp_zero_right, add_zero, secondOrderExtTop_zero]

/-- The product of two sections of the ideal of `T → T''` vanishes as soon as every exterior
product does. -/
public theorem secondOrderExt_mul_eq_zero_of_wedge {x y : SecondOrderExt (dpWedge T Y f) W}
    (hx0 : secondOrderExtFst x = 0) (hy0 : secondOrderExtFst y = 0)
    (h : ∀ ω₁ ω₂ : ↑((dpDifferentialsModules T Y f).obj W),
      (dpWedge T Y f).app W ω₁ ω₂ = 0) : x * y = 0 := by
  refine secondOrderExt_ext ?_ ?_ ?_ ?_
  · rw [secondOrderExtFst_mul, hx0, zero_mul, secondOrderExtFst_zero]
  · rw [secondOrderExtLeft_mul, hx0, hy0, zero_smul, zero_smul, add_zero,
      secondOrderExtLeft_zero]
  · rw [secondOrderExtRight_mul, hx0, hy0, zero_smul, zero_smul, add_zero,
      secondOrderExtRight_zero]
  · rw [secondOrderExtTop_mul, hx0, hy0, zero_smul, zero_smul, add_zero,
      bilinearApp_apply, bilinearApp_apply, h, h, add_zero, add_zero,
      secondOrderExtTop_zero]

/-- **The exterior product sits inside the square of the ideal of `T → T''`**:
`(0, ω₁, 0, 0) · (0, 0, ω₂, 0) = (0, 0, 0, ω₁ ∧ ω₂)`, both factors lying in the ideal. -/
public theorem secondOrderExt_mul_mk (ω₁ ω₂ : ↑((dpDifferentialsModules T Y f).obj W)) :
    secondOrderExtMk (q := dpWedge T Y f) 0 ω₁ 0 0 *
        secondOrderExtMk (q := dpWedge T Y f) 0 0 ω₂ 0 =
      secondOrderExtMk 0 0 0 ((dpWedge T Y f).app W ω₁ ω₂) := by
  refine secondOrderExt_ext ?_ ?_ ?_ ?_ <;>
    simp only [secondOrderExtFst_mul, secondOrderExtLeft_mul, secondOrderExtRight_mul,
      secondOrderExtTop_mul, secondOrderExtFst_mk, secondOrderExtLeft_mk,
      secondOrderExtRight_mk, secondOrderExtTop_mk, mul_zero, smul_zero, zero_smul,
      add_zero, zero_add, bilinearApp_apply, dpWedge_self]

end Computations

/-- The product of two ideals is zero as soon as every product of an element of each is. -/
private theorem ideal_mul_eq_bot_of_forall_mul_eq_zero {R : Type*} [CommSemiring R]
    {I J : Ideal R} (h : ∀ x ∈ I, ∀ y ∈ J, x * y = 0) : I * J = ⊥ :=
  le_antisymm (Ideal.mul_le.mpr fun x hx y hy => Ideal.mem_bot.mpr (h x hx y hy)) bot_le

/-- **`q₀₁` splits the projection onto `𝒪_{T'}`.** -/
public theorem secondOrderThickeningQ₀₁_comp_proj :
    secondOrderThickeningQ₀₁ T Y f ≫ secondOrderThickeningProj T Y f = 𝟙 _ :=
  NatTrans.ext (funext fun _ => CommRingCat.hom_ext (RingHom.ext fun _ =>
    sqZeroExt_ext rfl rfl))

/-- A section of `𝒪_{T''}` is killed by the projection onto `𝒪_{T'}` exactly when its first two
coordinates vanish. -/
public theorem mem_ker_secondOrderThickeningProj_iff (W : (Opens ↑T.scheme)ᵒᵖ)
    (x : SecondOrderExt (dpWedge T Y f) W) :
    x ∈ RingHom.ker (((secondOrderThickeningProj T Y f).app W).hom) ↔
      secondOrderExtFst x = 0 ∧ secondOrderExtLeft x = 0 :=
  RingHom.mem_ker.trans ⟨fun h => ⟨congrArg sqZeroExtFst h, congrArg sqZeroExtSnd h⟩,
    fun h => sqZeroExt_ext h.1 h.2⟩

/-- A section of `𝒪_{T''}` is killed by the projection onto `𝒪_T` exactly when its first
coordinate vanishes. -/
public theorem mem_ker_secondOrderExtFstHom_iff (W : (Opens ↑T.scheme)ᵒᵖ)
    (x : SecondOrderExt (dpWedge T Y f) W) :
    x ∈ RingHom.ker (secondOrderExtFstHom (dpWedge T Y f) W) ↔
      secondOrderExtFst x = 0 := RingHom.mem_ker

/-- **`T' → T''` is a first-order thickening**: the ideal of the projection `𝒪_{T''} → 𝒪_{T'}`
has square zero on every open.  This is the square-zero presentation of `𝒪_{T''}` over the
structure sheaf of the first-order universal thickening. -/
public theorem secondOrderThickening_ker_proj_sq (W : (Opens ↑T.scheme)ᵒᵖ) :
    RingHom.ker (((secondOrderThickeningProj T Y f).app W).hom) ^ 2 = ⊥ := by
  rw [pow_two]
  refine ideal_mul_eq_bot_of_forall_mul_eq_zero fun x hx y hy => ?_
  obtain ⟨hx0, hx1⟩ := (mem_ker_secondOrderThickeningProj_iff T Y f W x).mp hx
  obtain ⟨hy0, hy1⟩ := (mem_ker_secondOrderThickeningProj_iff T Y f W y).mp hy
  exact secondOrderExt_mul_eq_zero_of_fst_left W hx0 hx1 hy0 hy1

/-- **The top summand `Ω²_{T/Y,δ}` as an ideal of `𝒪_{T''}`**: the sections whose three lower
coordinates vanish. -/
public def secondOrderThickeningTopIdeal (W : (Opens ↑T.scheme)ᵒᵖ) :
    Ideal (SecondOrderExt (dpWedge T Y f) W) where
  carrier := {x | secondOrderExtFst x = 0 ∧ secondOrderExtLeft x = 0 ∧
    secondOrderExtRight x = 0}
  add_mem' {x y} hx hy :=
    ⟨by rw [secondOrderExtFst_add, hx.1, hy.1, add_zero],
      by rw [secondOrderExtLeft_add, hx.2.1, hy.2.1, add_zero],
      by rw [secondOrderExtRight_add, hx.2.2, hy.2.2, add_zero]⟩
  zero_mem' := ⟨rfl, rfl, rfl⟩
  smul_mem' c {x} hx :=
    ⟨by rw [show c • x = c * x from rfl, secondOrderExtFst_mul, hx.1, mul_zero],
      by rw [show c • x = c * x from rfl, secondOrderExtLeft_mul, hx.1, hx.2.1, smul_zero,
        zero_smul, add_zero],
      by rw [show c • x = c * x from rfl, secondOrderExtRight_mul, hx.1, hx.2.2, smul_zero,
        zero_smul, add_zero]⟩

/-- **`T → T''` is a second-order thickening**: the ideal of the projection `𝒪_{T''} → 𝒪_T` has
vanishing cube on every open.  Its square lies in the top summand, and the top summand
annihilates it. -/
@[stacks 07J3 "T → T'' is a second-order thickening of sheaves of rings"]
public theorem secondOrderThickening_ker_cube (W : (Opens ↑T.scheme)ᵒᵖ) :
    RingHom.ker (secondOrderExtFstHom (dpWedge T Y f) W) ^ 3 = ⊥ := by
  have hsq : RingHom.ker (secondOrderExtFstHom (dpWedge T Y f) W) ^ 2 ≤
      secondOrderThickeningTopIdeal T Y f W := by
    rw [pow_two]
    exact Ideal.mul_le.mpr fun x hx y hy => secondOrderExt_mul_coords_of_fst W hx hy
  rw [pow_succ]
  refine ideal_mul_eq_bot_of_forall_mul_eq_zero fun x hx y hy => ?_
  obtain ⟨hx0, hx1, hx2⟩ := hsq hx
  exact secondOrderExt_mul_eq_zero_of_top W hx0 hx1 hx2 hy

/-- **The exterior product is exactly the obstruction to `T → T''` being a first-order
thickening**: the ideal of `𝒪_{T''} → 𝒪_T` has vanishing square if and only if every exterior
product of divided power differentials vanishes.  This is why
`Stacks.Thickenings.squareZeroExtension_realization`, whose hypothesis
`Stacks.Thickenings.SquareZeroExtension.square_zero` is a literal vanishing of the square of the
kernel, cannot be applied to `𝒪_{T''} → 𝒪_T`. -/
public theorem secondOrderThickening_ker_sq_eq_bot_iff (W : (Opens ↑T.scheme)ᵒᵖ) :
    RingHom.ker (secondOrderExtFstHom (dpWedge T Y f) W) ^ 2 = ⊥ ↔
      ∀ ω₁ ω₂ : ↑((dpDifferentialsModules T Y f).obj W),
        (dpWedge T Y f).app W ω₁ ω₂ = 0 := by
  refine ⟨fun h ω₁ ω₂ => ?_, fun h => ?_⟩
  · have hmul : secondOrderExtMk (q := dpWedge T Y f) 0 ω₁ 0 0 *
        secondOrderExtMk (q := dpWedge T Y f) 0 0 ω₂ 0 = 0 := by
      refine Ideal.mem_bot.mp ?_
      rw [← h, pow_two]
      exact Ideal.mul_mem_mul (RingHom.mem_ker.mpr rfl) (RingHom.mem_ker.mpr rfl)
    have h2 := congrArg secondOrderExtTop ((secondOrderExt_mul_mk W ω₁ ω₂).symm.trans hmul)
    rwa [secondOrderExtTop_mk, secondOrderExtTop_zero] at h2
  · rw [pow_two]
    exact ideal_mul_eq_bot_of_forall_mul_eq_zero fun x hx y hy =>
      secondOrderExt_mul_eq_zero_of_wedge W hx hy h

/-- **The projection `𝒪_{T''} → 𝒪_{T'}` is compatible with the divided power structures `δ''`
and `δ'`**: in degree `k + 2` both formulas read off the same two coordinates, and in degrees
zero and one the two structures agree with the identity and the unit. -/
public theorem secondOrderThickeningProj_isDPMorphism (W : (Opens ↑T.scheme)ᵒᵖ) :
    DividedPowers.IsDPMorphism (secondOrderThickeningDividedPowers T Y f W)
      (firstOrderThickeningDividedPowers T Y f W)
      (((secondOrderThickeningProj T Y f).app W).hom) := by
  have hmem : ∀ x : SecondOrderExt (dpWedge T Y f) W,
      x ∈ secondOrderThickeningIdeal T Y f W →
      ((secondOrderThickeningProj T Y f).app W).hom x ∈ firstOrderThickeningIdeal T Y f W :=
    fun x hx => hx
  refine ⟨Ideal.map_le_iff_le_comap.mpr hmem, ?_⟩
  intro n x hx
  match n with
  | 0 =>
      exact (firstOrderThickeningDividedPowers_dpow_zero T Y f W (hmem x hx)).trans
        ((map_one ((secondOrderThickeningProj T Y f).app W).hom).symm.trans
          (congrArg (fun z => ((secondOrderThickeningProj T Y f).app W).hom z)
            (secondOrderExtDpow_zero (dpWedge T Y f) W
              (T.dividedPowers.dividedPowers W) hx).symm))
  | 1 =>
      refine (firstOrderThickeningDividedPowers_dpow_succ T Y f W 0 (hmem x hx)).trans ?_
      refine Eq.trans ?_ (congrArg (fun z => ((secondOrderThickeningProj T Y f).app W).hom z)
        (secondOrderExtDpow_one (dpWedge T Y f) W (T.dividedPowers.dividedPowers W) hx).symm)
      refine sqZeroExt_ext ?_ ?_
      · exact (T.dividedPowers.dividedPowers W).dpow_one hx
      · exact (congrArg (fun c : ↑(T.scheme.sheaf.obj.obj W) => c • secondOrderExtLeft x)
          ((T.dividedPowers.dividedPowers W).dpow_zero hx)).trans
            (one_smul _ (secondOrderExtLeft x))
  | k + 2 =>
      refine (firstOrderThickeningDividedPowers_dpow_succ T Y f W (k + 1) (hmem x hx)).trans ?_
      refine Eq.trans ?_ (congrArg (fun z => ((secondOrderThickeningProj T Y f).app W).hom z)
        (secondOrderThickeningDividedPowers_dpow_add_two T Y f W k hx).symm)
      exact sqZeroExt_ext rfl rfl

end Crystalline

end
