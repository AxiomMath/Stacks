module

public import StacksFrontier.AlgebraicGeometry.TwistedThickeningLift.LaurentChart
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushPullUnital
public import StacksFrontier.AlgebraicGeometry.AmpleThickeningDevissage.GradedUnitUngraded
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.QuasiAffineAscent
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackUnitSection

/-!
# Sections of tensor powers dying on a closed subscheme

Let `i : Z ⟶ X` be a closed immersion and `L` an invertible module on `X`. A homogeneous local
section `y` of `L^{⊗ k}` over an open `W` of `X` **dies on `Z`** when its image under the unit
`L^{⊗ k} ⟶ i_* i^* L^{⊗ k}` vanishes. Such sections satisfy the following.

* They are stable under differences and restriction, and under multiplication by any homogeneous
  section, the unit being a homomorphism of sheaves of graded algebras.
* In degree zero, a function dying on `Z` vanishes on `Z`.

The file also proves the ring identity `corrected_pow_eq`: in a ring with a square-zero ideal,
suitably corrected powers of two elements congruent modulo the ideal agree.

## Main definitions

* `Stacks.TwistedThickeningLift.Dies`: a homogeneous local section dies on `Z`.

## Main results

* `Stacks.TwistedThickeningLift.app_eq_zero_of_dies`: in degree zero, dying on `Z` is vanishing
  on `Z`.
* `Stacks.TwistedThickeningLift.corrected_pow_eq`: the corrected powers of two lifts agree.

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Ample (IsInvertibleModule)

universe u

namespace Stacks.TwistedThickeningLift

/-! ### A ring identity -/

/-- **The corrected powers of two lifts agree.** In a commutative ring with a square-zero ideal
`I`, let `x` and `y` be congruent modulo `I` and let `gy ∈ I`. If `x ^ K` kills
`x ^ m (x - y) - (gx - gy)`, then `x ^ N - N x ^ K gx = y ^ N - N y ^ K gy` for `N = K + m + 1`. -/
theorem corrected_pow_eq {R : Type*} [CommRing R] {I : Ideal R}
    (hI : ∀ x ∈ I, ∀ y ∈ I, x * y = 0) {x y gx gy : R} (K m : ℕ) (hxy : x - y ∈ I)
    (hgy : gy ∈ I) (hkill : x ^ K * (x ^ m * (x - y) - (gx - gy)) = 0) :
    x ^ (K + m + 1) - ((K + m + 1 : ℕ) : R) * (x ^ K * gx)
      = y ^ (K + m + 1) - ((K + m + 1 : ℕ) : R) * (y ^ K * gy) := by
  have h1 : x ^ (K + m + 1) - y ^ (K + m + 1)
      = (((K + m : ℕ) : R) + 1) * x ^ (K + m) * (x - y) :=
    Stacks.Thickenings.pow_sub_pow_of_sub_mem hI hxy (K + m)
  have h2 : y ^ K * gy = x ^ K * gy :=
    (Stacks.Thickenings.pow_mul_left_eq_of_sub_mem hI hxy K hgy).symm
  have h3 : x ^ (K + m) * (x - y) = x ^ K * (gx - gy) := by
    have h := hkill
    rw [mul_sub, sub_eq_zero] at h
    rw [pow_add, mul_assoc]
    exact h
  rw [← sub_eq_zero]
  have expand : (x ^ (K + m + 1) - ((K + m + 1 : ℕ) : R) * (x ^ K * gx))
        - (y ^ (K + m + 1) - ((K + m + 1 : ℕ) : R) * (y ^ K * gy))
      = (x ^ (K + m + 1) - y ^ (K + m + 1))
        - ((K + m + 1 : ℕ) : R) * (x ^ K * gx - y ^ K * gy) := by ring
  rw [expand, h1, h2]
  push_cast
  linear_combination ((K : R) + (m : R) + 1) * h3

/-! ### Sections dying on the closed subscheme -/

variable {X Z : Scheme.{u}} {L : X.Modules} [IsInvertibleModule X L] (i : Z ⟶ X)

variable (L) in
/-- The unit `A ⟶ i_* i^* A` of the Laurent algebra `A` of `L`, as a unital homomorphism of
sheaves of graded algebras. -/
abbrev unitHom :=
  Stacks.PushforwardGradedAlgebra.gradedUnitUnitalHom i.toLRSHom.toShHom
    (situation L).laurentAlgebra

variable (L) in
/-- The Laurent algebra of `L` pushed forward from its pullback to `Z`: `i_* i^* A`. -/
abbrev pushPull : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf :=
  Stacks.AmpleThickeningDevissage.pushforwardPullbackGradedAlgebra i (situation L).laurentAlgebra

variable (L) in
/-- The degree-`k` piece `i_* i^* L^{⊗ k}` of `i_* i^* A`, as an `𝒪_X`-module. -/
def ppiece (k : ℤ) : X.Modules := (pushPull L i).piece k

variable (L) in
/-- The degree-`k` component of the unit, `L^{⊗ k} ⟶ i_* i^* L^{⊗ k}`. -/
def unitApp (k : ℤ) : pow L k ⟶ ppiece L i k := (unitHom L i).app k

/-- The image of a homogeneous local section of `L^{⊗ k}` over `W` in `i_* i^* L^{⊗ k}`, i.e. its
pullback to `i^{-1} W`. -/
def up {W : X.Opens} {k : ℤ} (y : Γ(pow L k, W)) : Γ(ppiece L i k, W) :=
  (Scheme.Modules.Hom.app (unitApp L i k) W).hom y

/-- `up i y` is the value at `W` of the degree-`k` component of the unit `unitHom L i`. -/
theorem up_def {W : X.Opens} {k : ℤ} (y : Γ(pow L k, W)) :
    up i y = PresheafOfModules.Hom.app ((unitHom L i).app k).val (op W) y := rfl

/-- The image in `i_* i^* L^{⊗ k}` of a difference is the difference of the images. -/
theorem up_sub {W : X.Opens} {k : ℤ} (x y : Γ(pow L k, W)) : up i (x - y) = up i x - up i y :=
  map_sub _ x y

/-- Taking the image in `i_* i^* L^{⊗ k}` commutes with multiplication by functions on `W`. -/
theorem up_smul {W : X.Opens} {k : ℤ} (f : Γ(X, W)) (y : Γ(pow L k, W)) :
    up i (f • y) = f • up i y :=
  Scheme.Modules.Hom.app_smul _ f y

/-- The image in `i_* i^* L^{⊗ k}` is the pullback of the section along the unit of
`i^* ⊣ i_*`. -/
theorem up_eq {W : X.Opens} {k : ℤ} (y : Γ(pow L k, W)) :
    (up i y : Γ(ppiece L i k, W)) =
      Stacks.RingedSpace.pullbackUnit i.toLRSHom.toShHom (pow L k) (op W) y := by
  have h := Stacks.PushforwardGradedAlgebra.pullbackPushforwardGradedAlgebraAdjunction_unit_app_app
    i.toLRSHom.toShHom (situation L).laurentAlgebra k
  exact congrArg (fun φ => PresheafOfModules.Hom.app (SheafOfModules.Hom.val φ) (op W) y) h

variable (L) in
/-- **A homogeneous local section dies on `Z`** when its image in `i_* i^* L^{⊗ k}` is zero. -/
def Dies {W : X.Opens} {k : ℤ} (y : Γ(pow L k, W)) : Prop := up i y = 0

variable {i}

/-- The image in `i_* i^* L^{⊗ k}` of a product is the product of the images. -/
private theorem up_mul {W : X.Opens} {a b : ℤ} (x : Γ(pow L a, W)) (y : Γ(pow L b, W)) :
    up i (((situation L).laurentAlgebra.mul a b).app (op W) x y : Γ(pow L (a + b), W)) =
      ((pushPull L i).mul a b).app (op W) (up i x) (up i y) :=
  (up_def i _).trans ((unitHom L i).map_mul a b (op W) x y)

/-- The product of a section dying on `Z` with any homogeneous section dies on `Z`. -/
theorem Dies.mul_right {W : X.Opens} {a b : ℤ} {x : Γ(pow L a, W)} (hx : Dies L i x)
    (y : Γ(pow L b, W)) :
    Dies L i (((situation L).laurentAlgebra.mul a b).app (op W) x y : Γ(pow L (a + b), W)) := by
  unfold Dies at hx ⊢
  rw [up_mul, hx]
  exact AddMonoidHom.map_one₂ (((pushPull L i).mul a b).app (op W)) (up i y)

/-- The product of any homogeneous section with a section dying on `Z` dies on `Z`. -/
theorem Dies.mul_left {W : X.Opens} {a b : ℤ} (x : Γ(pow L a, W)) {y : Γ(pow L b, W)}
    (hy : Dies L i y) :
    Dies L i (((situation L).laurentAlgebra.mul a b).app (op W) x y : Γ(pow L (a + b), W)) := by
  unfold Dies at hy ⊢
  rw [up_mul, hy]
  exact map_zero _

/-- The difference of two sections dying on `Z` dies on `Z`. -/
theorem Dies.sub {W : X.Opens} {k : ℤ} {x y : Γ(pow L k, W)} (hx : Dies L i x)
    (hy : Dies L i y) : Dies L i (x - y) := by
  unfold Dies at hx hy ⊢
  rw [up_sub, hx, hy, sub_zero]

/-- A function multiple of a section dying on `Z` dies on `Z`. -/
theorem Dies.smul {W : X.Opens} {k : ℤ} {y : Γ(pow L k, W)} (hy : Dies L i y)
    (f : Γ(X, W)) : Dies L i (f • y) := by
  unfold Dies at hy ⊢
  rw [up_smul, hy, smul_zero]

/-- Two sections with the same image in `i_* i^* L^{⊗ k}` differ by a section dying on `Z`. -/
theorem dies_sub_of_up_eq {W : X.Opens} {k : ℤ} {x y : Γ(pow L k, W)} (h : up i x = up i y) :
    Dies L i (x - y) := by
  unfold Dies
  rw [up_sub, h, sub_self]

/-- Taking the image in `i_* i^* L^{⊗ k}` commutes with restriction to a smaller open. -/
theorem up_pres {W W' : X.Opens} (h : W' ≤ W) {k : ℤ} (y : Γ(pow L k, W)) :
    up i (pres h y) =
      ((Scheme.Modules.presheaf (ppiece L i k)).map (homOfLE h).op).hom (up i y) :=
  PresheafOfModules.naturality_apply ((unitHom L i).app k).val (homOfLE h).op y

/-- The restriction to a smaller open of a section dying on `Z` dies on `Z`. -/
theorem Dies.pres {W W' : X.Opens} (h : W' ≤ W) {k : ℤ} {y : Γ(pow L k, W)}
    (hy : Dies L i y) : Dies L i (pres h y) := by
  unfold Dies at hy ⊢
  rw [up_pres, hy]
  exact map_zero _

/-- Dying on `Z` transports along an equality of the images in the Laurent ring. -/
theorem dies_of_incl_eq {W : X.Opens} {k k' : ℤ} (hk : k = k') {y : Γ(pow L k, W)}
    {z : Γ(pow L k', W)} (he : incl k y = incl k' z) (hz : Dies L i z) : Dies L i y := by
  subst hk
  rw [incl_injective k he]
  exact hz

/-! ### Degree zero -/

/-- **In degree zero, a function dying on `Z` vanishes on `Z`.** The identification
`i^* 𝒪_X ⟶ 𝒪_Z` carries the pullback of a function to its image under `i^♯`
(`RingedSpaceModuleAdjunction.pullbackObjUnitToUnit_val_app_unit`). -/
theorem app_eq_zero_of_dies {W : X.Opens} (f : Γ(X, W))
    (hf : Dies L i (show Γ(pow L 0, W) from f)) : (i.app W).hom f = 0 := by
  have h := RingedSpaceModuleAdjunction.pullbackObjUnitToUnit_val_app_unit i.toLRSHom.toShHom W f
  have hup : ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
      i.toLRSHom.toShHom).unit.app
        (SheafOfModules.unit (structureSheafRing X.toRingedSpace))).val.app (op W) f = 0 :=
    (up_eq i (show Γ(pow L 0, W) from f)).symm.trans hf
  revert h hup
  generalize ((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
      i.toLRSHom.toShHom).unit.app
        (SheafOfModules.unit (structureSheafRing X.toRingedSpace))).val.app (op W) f = g
  intro h hg
  subst hg
  exact h.symm.trans (map_zero _)

end Stacks.TwistedThickeningLift

end
