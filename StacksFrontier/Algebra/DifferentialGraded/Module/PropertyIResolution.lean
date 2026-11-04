module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DualCover
public import StacksFrontier.Algebra.DifferentialGraded.Module.Product
public import StacksFrontier.Algebra.DifferentialGraded.Module.Subquotient

/-! # The totalization of a tower, and the resolution tower of Stacks 09KU

Let `(A, d)` be a differential graded algebra and let

`J₀ --g₀--> J₁ --g₁--> J₂ --g₂--> ⋯`

be a tower of right differential graded `A`-modules with `g_{i+1} ∘ gᵢ = 0`. Fix an *offset*
`o : ℤ`. The *totalization of `J` at offset `o`* is the differential graded `A`-module with
graded parts

`Iⁿ = ∏_{i ≥ 0} Jᵢ^{n - o - i}`

and differential `d(x) = gᵢ(x) + (-1)^{o + i} d_{Jᵢ}(x)` for `x ∈ Jᵢ^{n - o - i}`.

At offset `0` this is the module denoted `I` in the proof of Stacks 09KU, built there out of the
resolution `0 → M → I₀ → I₁ → ⋯` whose steps come from Stacks 09KT. The offset is carried along
because the stages of the filtration exhibiting property (I) are the totalizations of the
*tail* towers `Jᵢ, J_{i+1}, …` at offset `i` — see the implementation notes.

This file constructs the totalization, the resolution tower, and the augmentation
`M ⟶ I`; the property-(I) filtration of `I` and the quasi-isomorphy of the augmentation are
not done here.

## Main definitions

* `DifferentialGradedModule.twist`: the differential graded module obtained from `P` by adding
  to its differential a square-zero, degree-`+1`, `A`-linear operator anticommuting with `d_P`.
* `DifferentialGradedModule.towerFactor`: the `i`-th factor `Jᵢ[-o-i]` of the totalization.
* `DifferentialGradedModule.towerProduct`: the underlying graded module `∏ᵢ Jᵢ[-o-i]` of the
  totalization, with its componentwise differential.
* `DifferentialGradedModule.towerTwist`: the operator `x ↦ gᵢ(x)` which twists that
  differential.
* `DifferentialGradedModule.towerTotal`: the totalization itself.
* `DifferentialGradedModule.towerTotal.lift`: a homomorphism into the totalization, from its
  components.
* `DifferentialGradedModule.DualResolutionStep`: the data Stacks 09KT produces for a module.
* `DifferentialGradedModule.resolutionI`, `DifferentialGradedModule.resolutionMap`: the tower
  `I₀ → I₁ → ⋯` of the proof of Stacks 09KU.
* `DifferentialGradedModule.resolutionTotal`: its totalization, the module `I` of Stacks 09KU.
* `DifferentialGradedModule.resolutionAug`: the augmentation `M ⟶ I`.

## Main results

* `DifferentialGradedModule.towerTotal.mem_grading_iff`: a point of the totalization is
  homogeneous of degree `n` exactly when its `i`-th component lies in `Jᵢ^{n - o - i}`.
* `DifferentialGradedModule.towerTotal.exists_mem_grading`: every family of components of
  matching degrees is realized.
* `DifferentialGradedModule.towerTotal.π_d_zero` and
  `DifferentialGradedModule.towerTotal.π_d_succ`: the components of the twisted differential.
* `DifferentialGradedModule.nonempty_dualResolutionStep`: Stacks 09KT, packaged as a step.
* `DifferentialGradedModule.resolutionAug_injective`: the augmentation is injective.

## Implementation notes

*The shift carries the sign.* The `i`-th factor is `Jᵢ[-o-i]`, whose degree-`n` part is
`Jᵢ^{n - o - i}` as required and whose differential is `(-1)^{-o-i} d_{Jᵢ} = (-1)^{o+i} d_{Jᵢ}` —
exactly the sign appearing in the Stacks formula. So the twisted differential of the totalization
is the *componentwise* differential of the product `∏ᵢ Jᵢ[-o-i]` plus the unsigned shift-up
operator `x ↦ gᵢ(x)`, and the anticommutation of the two is precisely the cancellation
`(-1)^{o+i} + (-1)^{o+i+1} = 0`. Taking the shifts into the factors is what keeps the
construction a `twist` of a product rather than a differential built from scratch.

*Why the offset.* Stacks 09KU filters `I` by `F_{2i}I = ∏_{j ≥ i} Iⱼ^{n - j}`. Reindexing
`j = i + m`, that is the totalization of the tail tower `m ↦ I_{i + m}` *at offset `i`* — the
degrees are `I_{i+m}^{n - i - m}` and the sign on the `m`-th differential is `(-1)^{i+m}`. The
same object is **not** a shift of the offset-`0` totalization of the tail tower: shifting
multiplies the whole differential by `(-1)^i`, which fixes the signs on the `d_{Iⱼ}` but wrongly
introduces a factor `(-1)^i` on the transition maps `fⱼ`. Carrying `o` is therefore cheaper than
correcting the transitions by a sign afterwards, and it makes the inclusions `F_{p+1} → F_p`
plain component-matching maps.

*The product is `uliftProduct`.* The tower is indexed by `ℕ`, which is not a `Type u`, while
`DifferentialGradedModule A` only has `Type u`-indexed products — see the implementation notes
of `Module/Product.lean`. `DifferentialGradedModule.uliftProduct` is the product over
`ULift.{u} ℕ` with projections indexed by `ℕ` itself, which is what is used here.

*The projections are not homomorphisms of the totalization.* They are compatible with the
grading and the action but not with the twisted differential, so they appear as elements of
`DifferentialGradedModule.GradedHom` and, more often, as bare linear maps
`DifferentialGradedModule.towerTotal.π`. Their interaction with the differential is the content
of `towerTotal.π_d_zero` and `towerTotal.π_d_succ`.

*The resolution tower is built by choice.* `DifferentialGradedModule.exists_dual_injection`
(Stacks 09KT) is an existence statement, so the tower `M = M₀, M₁, …` is defined by recursion on
a choice function `dualResolutionStep`, obtained from `nonempty_dualResolutionStep` by
`Nonempty.some`. The data chosen is genuine — an injection together with the admissible short
exact sequence around its target — not a `Nonempty` placeholder; what choice supplies is only
*which* of the many such injections is used at each stage.

## References

* [Stacks Project, Tag 09KU](https://stacks.math.columbia.edu/tag/09KU), whose proof this
  construction is the first half of, and
  [Tag 09KT](https://stacks.math.columbia.edu/tag/09KT), which supplies its steps.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

/-! ### Twisting a differential -/

section Twist

variable (P : DifferentialGradedModule A) (T : P.M →ₗ[R] P.M)

/-- **Twisting the differential of a differential graded module.** If `T` is an `R`-linear
operator on `P` which commutes with the right `A`-action, raises degrees by one, squares to zero
and anticommutes with `d_P`, then `d_P + T` is again a differential making the same graded right
`A`-module a differential graded `A`-module.

Only the Leibniz rule uses more than linearity: the correction term `(-1)^n x · d_A a` comes
from `d_P` alone, and `T` contributes nothing to it because it is `A`-linear. -/
@[implicit_reducible]
def twist
    (hsmul : ∀ (x : P.M) (a : A.A), T (MulOpposite.op a • x) = MulOpposite.op a • T x)
    (hgrading : ∀ (n : ℤ) (x : P.M), x ∈ P.grading n → T x ∈ P.grading (n + 1))
    (hTT : ∀ x : P.M, T (T x) = 0)
    (hanti : ∀ x : P.M, T (P.d x) + P.d (T x) = 0) : DifferentialGradedModule A where
  M := P.M
  grading := P.grading
  smul_mem := P.smul_mem
  d := P.d + T
  d_comp_d := by
    refine LinearMap.ext fun x => ?_
    have hdd := LinearMap.congr_fun P.d_comp_d x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hdd
    simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add, hdd, hTT, zero_add, add_zero,
      LinearMap.zero_apply]
    exact hanti x
  d_mem := fun n x hx => Submodule.add_mem _ (P.d_mem n x hx) (hgrading n x hx)
  leibniz := by
    intro n m x a hx ha
    simp only [LinearMap.add_apply]
    rw [P.leibniz n m x a hx ha, hsmul x a, smul_add]
    abel

/-- A twist has the same grading as the module it twists. -/
@[simp] theorem twist_grading (hsmul hgrading hTT hanti) :
    (twist P T hsmul hgrading hTT hanti).grading = P.grading := rfl

/-- The differential of a twist is the sum of the original differential and the twisting
operator. -/
theorem twist_d_apply (hsmul hgrading hTT hanti) (x : P.M) :
    (twist P T hsmul hgrading hTT hanti).d x = P.d x + T x := rfl

end Twist

/-! ### The factors of the totalization -/

variable (J : ℕ → DifferentialGradedModule A) (o : ℤ)

/-- The `i`-th factor `Jᵢ[-o-i]` of the totalization of a tower `J` at offset `o`: the shift of
`Jᵢ` whose degree-`n` part is `Jᵢ^{n - o - i}` and whose differential is
`(-1)^{o + i} d_{Jᵢ}`. -/
@[implicit_reducible]
def towerFactor (i : ℕ) : DifferentialGradedModule A := shift (J i) (-(o + i))

/-- The degree-`n` part of the `i`-th factor of the totalization is `Jᵢ^{n - o - i}`. -/
theorem towerFactor_grading (i : ℕ) (n : ℤ) :
    (towerFactor J o i).grading n = (J i).grading (n - (o + i)) := by
  show (J i).grading (n + -(o + i)) = (J i).grading (n - (o + i))
  rw [sub_eq_add_neg]

/-- The differential of the `i`-th factor of the totalization is `(-1)^{o + i} d_{Jᵢ}`. -/
theorem towerFactor_d (i : ℕ) : (towerFactor J o i).d = (o + i).negOnePow • (J i).d := by
  show (-(o + i)).negOnePow • (J i).d = (o + i).negOnePow • (J i).d
  rw [Int.negOnePow_neg]

/-- The underlying graded module `∏ᵢ Jᵢ[-o-i]` of the totalization, carrying the *componentwise*
differential. The totalization itself is the twist of this by `towerTwist`. -/
@[implicit_reducible]
def towerProduct : DifferentialGradedModule A := uliftProduct (towerFactor J o)

/-- The `i`-th projection of `∏ᵢ Jᵢ[-o-i]`, as a homomorphism of differential graded modules for
the componentwise differential. -/
def towerProduct.π (i : ℕ) : towerProduct J o ⟶ towerFactor J o i :=
  uliftProduct.π (towerFactor J o) i

/-- A point of `∏ᵢ Jᵢ[-o-i]` is homogeneous of degree `n` exactly when its `i`-th component lies
in `Jᵢ^{n - o - i}`. -/
theorem towerProduct.mem_grading_iff {n : ℤ} (x : (towerProduct J o).M) :
    x ∈ (towerProduct J o).grading n ↔
      ∀ i, (towerProduct.π J o i).toFun x ∈ (J i).grading (n - (o + i)) := by
  rw [show (towerProduct J o).grading n = (uliftProduct (towerFactor J o)).grading n from rfl,
    uliftProduct.mem_grading_iff]
  refine forall_congr' fun i => ?_
  rw [towerFactor_grading]
  exact Iff.rfl

/-- The `i`-th projection of `∏ᵢ Jᵢ[-o-i]` turns the componentwise differential into
`(-1)^{o + i} d_{Jᵢ}`. -/
theorem towerProduct.π_d (i : ℕ) (y : (towerProduct J o).M) :
    (towerProduct.π J o i).toFun ((towerProduct J o).d y)
      = (((o + i).negOnePow : ℤ)) • (J i).d ((towerProduct.π J o i).toFun y) := by
  have h := LinearMap.congr_fun (towerProduct.π J o i).map_d y
  simp only [LinearMap.comp_apply] at h
  rw [h, towerFactor_d, LinearMap.smul_apply, Units.smul_def]

/-- **The lift of a family of graded component maps** to a map of graded modules into
`∏ᵢ Jᵢ[-o-i]`: the components must be `R`-linear and carry `Tⁿ` into `Jᵢ^{n - o - i}`, and
nothing is required of the differentials. -/
def towerProduct.liftGraded {T : DifferentialGradedModule A} (c : ∀ i, T.M →ₗ[R] (J i).M)
    (hgrading : ∀ (i : ℕ) (n : ℤ) (x : T.M), x ∈ T.grading n →
      c i x ∈ (J i).grading (n - (o + i))) :
    T.M →ₗ[R] (towerProduct J o).M :=
  LinearMap.codRestrict
    ((productSubmodule fun j : ULift.{u} ℕ => towerFactor J o j.down).restrictScalars R)
    (LinearMap.pi fun j : ULift.{u} ℕ => c j.down)
    fun x => pi_mem_productSubmodule (fun j : ULift.{u} ℕ => towerFactor J o j.down)
      (fun j => (c j.down).toAddMonoidHom) id
      (fun j n y hy => by rw [towerFactor_grading]; exact hgrading j.down n y hy) x

/-- The `i`-th component of a lift is the `i`-th given component map. -/
@[simp] theorem towerProduct.π_liftGraded {T : DifferentialGradedModule A}
    (c : ∀ i, T.M →ₗ[R] (J i).M)
    (hgrading : ∀ (i : ℕ) (n : ℤ) (x : T.M), x ∈ T.grading n →
      c i x ∈ (J i).grading (n - (o + i)))
    (i : ℕ) (x : T.M) :
    (towerProduct.π J o i).toFun (towerProduct.liftGraded J o c hgrading x) = c i x := rfl

/-- A point of `∏ᵢ Jᵢ[-o-i]` is determined by its components. -/
theorem towerProduct.eq_of_π_eq {x y : (towerProduct J o).M}
    (h : ∀ i, (towerProduct.π J o i).toFun x = (towerProduct.π J o i).toFun y) : x = y :=
  uliftProduct.eq_of_π_eq (towerFactor J o) h

/-- Every family of components of matching degrees is the family of components of a point of
`∏ᵢ Jᵢ[-o-i]` of degree `n`. -/
theorem towerProduct.exists_mem_grading (n : ℤ) (q : ∀ i, (J i).M)
    (hq : ∀ i, q i ∈ (J i).grading (n - (o + i))) :
    ∃ y ∈ (towerProduct J o).grading n, ∀ i, (towerProduct.π J o i).toFun y = q i :=
  uliftProduct.exists_mem_grading (towerFactor J o) n q fun i => by
    rw [towerFactor_grading]; exact hq i

/-! ### The twisting operator -/

variable (g : ∀ i, J i ⟶ J (i + 1))

/-- The `i`-th component of the twisting operator: zero for `i = 0`, and `gᵢ` applied to the
`i`-th component for `i + 1`. -/
def towerTwistComp : ∀ i : ℕ, (towerProduct J o).M →ₗ[R] (J i).M
  | 0 => 0
  | (i + 1) => (g i).toFun ∘ₗ (towerProduct.π J o i).toFun

/-- The zeroth component of the twisting operator vanishes. -/
@[simp] theorem towerTwistComp_zero : towerTwistComp J o g 0 = 0 := rfl

/-- The `(i + 1)`-st component of the twisting operator is `gᵢ` on the `i`-th component. -/
@[simp] theorem towerTwistComp_succ (i : ℕ) (x : (towerProduct J o).M) :
    towerTwistComp J o g (i + 1) x = (g i).toFun ((towerProduct.π J o i).toFun x) := rfl

/-- The components of the twisting operator raise degrees by one. -/
theorem towerTwistComp_mem (i : ℕ) (n : ℤ) (x : (towerProduct J o).M)
    (hx : x ∈ (towerProduct J o).grading n) :
    towerTwistComp J o g i x ∈ (towerFactor J o i).grading (n + 1) := by
  rw [towerFactor_grading]
  cases i with
  | zero => simpa only [towerTwistComp_zero, LinearMap.zero_apply] using Submodule.zero_mem _
  | succ i =>
      rw [towerTwistComp_succ,
        show n + 1 - (o + ((i + 1 : ℕ) : ℤ)) = n - (o + (i : ℤ)) from by push_cast; ring]
      exact (g i).map_grading _ _ ((towerProduct.mem_grading_iff J o x).1 hx i)

/-- **The twisting operator of the totalization**, `x ↦ gᵢ(x)`: an `R`-linear endomorphism of
`∏ᵢ Jᵢ[-o-i]` sending the `i`-th factor into the `(i + 1)`-st by `gᵢ`. -/
def towerTwist : (towerProduct J o).M →ₗ[R] (towerProduct J o).M :=
  LinearMap.codRestrict
    ((productSubmodule fun j : ULift.{u} ℕ => towerFactor J o j.down).restrictScalars R)
    (LinearMap.pi fun j : ULift.{u} ℕ => towerTwistComp J o g j.down)
    fun x => pi_mem_productSubmodule (fun j : ULift.{u} ℕ => towerFactor J o j.down)
      (fun j => (towerTwistComp J o g j.down).toAddMonoidHom) (fun n => n + 1)
      (fun j n y hy => towerTwistComp_mem J o g j.down n y hy) x

/-- The `i`-th projection reads the `i`-th component of the twisting operator. -/
@[simp] theorem towerProduct.π_towerTwist (i : ℕ) (x : (towerProduct J o).M) :
    (towerProduct.π J o i).toFun (towerTwist J o g x) = towerTwistComp J o g i x := rfl

/-- The twisting operator commutes with the right `A`-action. -/
theorem towerTwist_smul (x : (towerProduct J o).M) (a : A.A) :
    towerTwist J o g (MulOpposite.op a • x) = MulOpposite.op a • towerTwist J o g x := by
  refine towerProduct.eq_of_π_eq J o fun i => ?_
  rw [towerProduct.π_towerTwist, (towerProduct.π J o i).map_smul, towerProduct.π_towerTwist]
  cases i with
  | zero => simp only [towerTwistComp_zero, LinearMap.zero_apply, smul_zero]
  | succ i =>
      rw [towerTwistComp_succ, towerTwistComp_succ, (towerProduct.π J o i).map_smul,
        (g i).map_smul]

/-- The twisting operator raises degrees by one. -/
theorem towerTwist_grading (n : ℤ) (x : (towerProduct J o).M)
    (hx : x ∈ (towerProduct J o).grading n) :
    towerTwist J o g x ∈ (towerProduct J o).grading (n + 1) :=
  (towerProduct.mem_grading_iff J o _).2 fun i => by
    rw [towerProduct.π_towerTwist]
    have h := towerTwistComp_mem J o g i n x hx
    rwa [towerFactor_grading] at h

/-- The twisting operator squares to zero, because `g_{i+1} ∘ gᵢ = 0`. -/
theorem towerTwist_towerTwist
    (hg : ∀ (i : ℕ) (x : (J i).M), (g (i + 1)).toFun ((g i).toFun x) = 0)
    (x : (towerProduct J o).M) : towerTwist J o g (towerTwist J o g x) = 0 := by
  refine towerProduct.eq_of_π_eq J o fun i => ?_
  rw [towerProduct.π_towerTwist, map_zero]
  cases i with
  | zero => simp only [towerTwistComp_zero, LinearMap.zero_apply]
  | succ i =>
      rw [towerTwistComp_succ, towerProduct.π_towerTwist]
      cases i with
      | zero => simp only [towerTwistComp_zero, LinearMap.zero_apply, map_zero]
      | succ i => rw [towerTwistComp_succ, hg i]

/-- The twisting operator anticommutes with the componentwise differential: the signs
`(-1)^{o + i}` and `(-1)^{o + i + 1}` of the two factors involved cancel. -/
theorem towerTwist_anticomm (x : (towerProduct J o).M) :
    towerTwist J o g ((towerProduct J o).d x) + (towerProduct J o).d (towerTwist J o g x) = 0 := by
  refine towerProduct.eq_of_π_eq J o fun i => ?_
  rw [map_add, map_zero, towerProduct.π_towerTwist, towerProduct.π_d]
  cases i with
  | zero =>
      simp only [towerTwistComp_zero, LinearMap.zero_apply, towerProduct.π_towerTwist, map_zero,
        smul_zero, add_zero]
  | succ i =>
      rw [towerTwistComp_succ, towerProduct.π_towerTwist, towerTwistComp_succ,
        towerProduct.π_d]
      have hgd : (g i).toFun ((J i).d ((towerProduct.π J o i).toFun x))
          = (J (i + 1)).d ((g i).toFun ((towerProduct.π J o i).toFun x)) :=
        LinearMap.congr_fun (g i).map_d _
      rw [map_zsmul, hgd,
        show (o + ((i + 1 : ℕ) : ℤ)).negOnePow = -(o + (i : ℤ)).negOnePow from by
          rw [show o + ((i + 1 : ℕ) : ℤ) = (o + (i : ℤ)) + 1 from by push_cast; ring,
            Int.negOnePow_succ]]
      simp only [Units.val_neg, neg_smul, add_neg_cancel]

/-! ### The totalization -/

variable (hg : ∀ (i : ℕ) (x : (J i).M), (g (i + 1)).toFun ((g i).toFun x) = 0)

/-- **The totalization of a tower** `J₀ → J₁ → ⋯` of differential graded `A`-modules with
`g_{i+1} ∘ gᵢ = 0`, at offset `o`: the differential graded `A`-module with

`Iⁿ = ∏_{i ≥ 0} Jᵢ^{n - o - i}`

and differential `d(x) = gᵢ(x) + (-1)^{o + i} d_{Jᵢ}(x)` for `x ∈ Jᵢ^{n - o - i}`. At offset `0`
this is the module denoted `I` in the proof of Stacks 09KU. -/
@[implicit_reducible]
def towerTotal : DifferentialGradedModule A :=
  twist (towerProduct J o) (towerTwist J o g) (towerTwist_smul J o g) (towerTwist_grading J o g)
    (towerTwist_towerTwist J o g hg) (towerTwist_anticomm J o g)

/-- The `i`-th component of a point of the totalization. This is *not* a homomorphism of
differential graded modules: it is compatible with the grading and the action but not with the
twisted differential, for which see `towerTotal.π_d_zero` and `towerTotal.π_d_succ`. -/
def towerTotal.π (i : ℕ) : (towerTotal J o g hg).M →ₗ[R] (J i).M :=
  (towerProduct.π J o i).toFun

/-- The `i`-th projection of the totalization, as a map of graded right `A`-modules. -/
def towerTotal.gradedπ (i : ℕ) : GradedHom (towerTotal J o g hg) (towerFactor J o i) where
  toFun := towerTotal.π J o g hg i
  map_smul := (towerProduct.π J o i).map_smul
  map_grading := (towerProduct.π J o i).map_grading

/-- The graded projection of the totalization computes the `i`-th component. -/
theorem towerTotal.gradedπ_apply (i : ℕ) (x : (towerTotal J o g hg).M) :
    (towerTotal.gradedπ J o g hg i).toFun x = towerTotal.π J o g hg i x := rfl

/-- A point of the totalization is homogeneous of degree `n` exactly when its `i`-th component
lies in `Jᵢ^{n - o - i}`. -/
theorem towerTotal.mem_grading_iff {n : ℤ} (x : (towerTotal J o g hg).M) :
    x ∈ (towerTotal J o g hg).grading n ↔
      ∀ i, towerTotal.π J o g hg i x ∈ (J i).grading (n - (o + i)) :=
  towerProduct.mem_grading_iff J o x

/-- A point of the totalization is determined by its components. -/
theorem towerTotal.eq_of_π_eq {x y : (towerTotal J o g hg).M}
    (h : ∀ i, towerTotal.π J o g hg i x = towerTotal.π J o g hg i y) : x = y :=
  towerProduct.eq_of_π_eq J o h

/-- Every family of components of matching degrees is the family of components of a point of the
totalization of degree `n`. -/
theorem towerTotal.exists_mem_grading (n : ℤ) (q : ∀ i, (J i).M)
    (hq : ∀ i, q i ∈ (J i).grading (n - (o + i))) :
    ∃ y ∈ (towerTotal J o g hg).grading n, ∀ i, towerTotal.π J o g hg i y = q i :=
  towerProduct.exists_mem_grading J o n q hq

/-- **The components of the twisted differential of the totalization**: the `i`-th component of
`d(x)` is `(-1)^{o + i} d_{Jᵢ}(xᵢ)` corrected by the `i`-th component of the twisting
operator. -/
theorem towerTotal.π_d (i : ℕ) (x : (towerTotal J o g hg).M) :
    towerTotal.π J o g hg i ((towerTotal J o g hg).d x)
      = (((o + i).negOnePow : ℤ)) • (J i).d (towerTotal.π J o g hg i x)
        + towerTwistComp J o g i x := by
  have key : towerTotal.π J o g hg i ((towerTotal J o g hg).d x)
      = (towerProduct.π J o i).toFun ((towerProduct J o).d x)
        + (towerProduct.π J o i).toFun (towerTwist J o g x) :=
    map_add (towerProduct.π J o i).toFun _ _
  rw [key, towerProduct.π_d, towerProduct.π_towerTwist]
  rfl

/-- **The zeroth component of the twisted differential**: `d(x)₀ = (-1)^o d_{J₀}(x₀)`. -/
theorem towerTotal.π_d_zero (x : (towerTotal J o g hg).M) :
    towerTotal.π J o g hg 0 ((towerTotal J o g hg).d x)
      = ((o.negOnePow : ℤ)) • (J 0).d (towerTotal.π J o g hg 0 x) := by
  rw [towerTotal.π_d]
  simp only [towerTwistComp_zero, LinearMap.zero_apply, add_zero, Nat.cast_zero, add_zero]

/-- **The `(i + 1)`-st component of the twisted differential**:
`d(x)_{i+1} = gᵢ(xᵢ) + (-1)^{o + i + 1} d_{J_{i+1}}(x_{i+1})`. -/
theorem towerTotal.π_d_succ (i : ℕ) (x : (towerTotal J o g hg).M) :
    towerTotal.π J o g hg (i + 1) ((towerTotal J o g hg).d x)
      = (g i).toFun (towerTotal.π J o g hg i x)
        + (((o + ((i + 1 : ℕ) : ℤ)).negOnePow : ℤ)
          • (J (i + 1)).d (towerTotal.π J o g hg (i + 1) x)) := by
  have h := towerTwistComp_succ J o g i x
  rw [towerTotal.π_d, h]
  exact add_comm _ _

/-- **The lift of a family of component maps to a homomorphism into the totalization.** A
homomorphism `T ⟶ I` into the totalization is a family of `R`-linear maps `cᵢ : T → Jᵢ`
compatible with the right `A`-action, carrying `Tⁿ` into `Jᵢ^{n - o - i}`, and compatible with
the twisted differential — which, read off component by component, is the pair of conditions
`hd0` and `hdsucc`. -/
def towerTotal.lift {T : DifferentialGradedModule A} (c : ∀ i, T.M →ₗ[R] (J i).M)
    (hsmul : ∀ (i : ℕ) (x : T.M) (a : A.A),
      c i (MulOpposite.op a • x) = MulOpposite.op a • c i x)
    (hgrading : ∀ (i : ℕ) (n : ℤ) (x : T.M), x ∈ T.grading n →
      c i x ∈ (J i).grading (n - (o + i)))
    (hd0 : ∀ x : T.M, c 0 (T.d x) = ((o.negOnePow : ℤ)) • (J 0).d (c 0 x))
    (hdsucc : ∀ (i : ℕ) (x : T.M), c (i + 1) (T.d x)
      = (((o + ((i + 1 : ℕ) : ℤ)).negOnePow : ℤ)) • (J (i + 1)).d (c (i + 1) x)
        + (g i).toFun (c i x)) :
    T ⟶ towerTotal J o g hg where
  toFun := towerProduct.liftGraded J o c hgrading
  map_smul := fun x a => towerTotal.eq_of_π_eq J o g hg fun i => by
    have h1 : towerTotal.π J o g hg i
        (towerProduct.liftGraded J o c hgrading (MulOpposite.op a • x))
        = c i (MulOpposite.op a • x) := rfl
    have h2 : towerTotal.π J o g hg i
        (MulOpposite.op a • towerProduct.liftGraded J o c hgrading x)
        = MulOpposite.op a • c i x := (towerProduct.π J o i).map_smul _ a
    rw [h1, h2, hsmul i x a]
  map_grading := fun n x hx => (towerTotal.mem_grading_iff J o g hg _).2 fun i => by
    have h : towerTotal.π J o g hg i (towerProduct.liftGraded J o c hgrading x) = c i x := rfl
    rw [h]
    exact hgrading i n x hx
  map_d := by
    refine LinearMap.ext fun x => towerTotal.eq_of_π_eq J o g hg fun i => ?_
    have hl : towerTotal.π J o g hg i
        ((towerProduct.liftGraded J o c hgrading ∘ₗ T.d) x) = c i (T.d x) := rfl
    have hr : towerTotal.π J o g hg i
        (((towerTotal J o g hg).d ∘ₗ towerProduct.liftGraded J o c hgrading) x)
        = towerTotal.π J o g hg i
          ((towerTotal J o g hg).d (towerProduct.liftGraded J o c hgrading x)) := rfl
    rw [hl, hr, towerTotal.π_d]
    have hc : towerTotal.π J o g hg i (towerProduct.liftGraded J o c hgrading x) = c i x := rfl
    rw [hc]
    cases i with
    | zero =>
        rw [hd0 x, towerTwistComp_zero]
        simp only [Nat.cast_zero, add_zero, LinearMap.zero_apply, add_zero]
    | succ i =>
        rw [hdsucc i x, towerTwistComp_succ, towerProduct.π_liftGraded]

/-- The `i`-th component of a homomorphism into the totalization is the given `cᵢ`. -/
@[simp] theorem towerTotal.π_lift {T : DifferentialGradedModule A} (c : ∀ i, T.M →ₗ[R] (J i).M)
    (hsmul hgrading hd0 hdsucc) (i : ℕ) (x : T.M) :
    towerTotal.π J o g hg i
      ((towerTotal.lift J o g hg c hsmul hgrading hd0 hdsucc).toFun x) = c i x := rfl

/-! ### The resolution tower of Stacks 09KT -/

/-- One step of the inductive construction of Stacks 09KU: the data produced by Stacks 09KT for
a differential graded `A`-module `M`. It is an injection `φ : M → I` into a module `I` sitting in
an admissible short exact sequence whose two ends are products of shifts of `A^∨`, and such that
`Coker(d_M) → Coker(d_I)` is injective — the last condition being recorded in the elementwise
form `exists_eq_d`, as in `DifferentialGradedModule.exists_dual_injection`. -/
structure DualResolutionStep (M : DifferentialGradedModule A) where
  /-- The module `M` is injected into. -/
  I : DifferentialGradedModule A
  /-- The injection. -/
  φ : M ⟶ I
  /-- Stacks 09KT(1): the injection is injective. -/
  injective : Function.Injective φ.toFun
  /-- Stacks 09KT(2): `Coker(d_M) → Coker(d_I)` is injective, stated elementwise. -/
  exists_eq_d : ∀ x : M.M, (∃ w : I.M, I.d w = φ.toFun x) → ∃ y : M.M, M.d y = x
  /-- The index set of the two products of shifts of `A^∨`. -/
  ι : Type u
  /-- Decidable equality of that index set, needed to form the products. -/
  decEq : DecidableEq ι
  /-- The shifts attached to the factors. -/
  k : ι → ℤ
  /-- Stacks 09KT(3): the sub-object `I' = ∏ᵢ A^∨[kᵢ]` of `I`. -/
  sub : @productDualShifts _ _ A _ decEq k ⟶ I
  /-- Stacks 09KT(3): the quotient `I'' = ∏ᵢ A^∨[kᵢ + 1]` of `I`. -/
  quot : I ⟶ @productDualShifts _ _ A _ decEq (fun c => k c + 1)
  /-- Stacks 09KT(3): the sequence `0 → I' → I → I'' → 0` is admissible short exact. -/
  ses : IsAdmissibleShortExact sub quot

/-- **Stacks 09KT, as a step of the inductive construction.** Every differential graded
`A`-module admits one. -/
theorem nonempty_dualResolutionStep (M : DifferentialGradedModule A) :
    Nonempty (DualResolutionStep M) := by
  obtain ⟨ι, dec, k, b, φ, hinj, hd, i, p, hses⟩ := exists_dual_injection A M
  exact ⟨⟨_, φ, hinj, hd, ι, dec, k, i, p, hses⟩⟩

/-- A choice of resolution step for each module, from `nonempty_dualResolutionStep`. -/
def dualResolutionStep (M : DifferentialGradedModule A) : DualResolutionStep M :=
  (nonempty_dualResolutionStep M).some

variable (M : DifferentialGradedModule A)

/-- The tower `M = M₀, M₁, M₂, …` of the proof of Stacks 09KU: `M_{i+1}` is the cokernel of the
injection `Mᵢ → Iᵢ` of Stacks 09KT. -/
def resolutionModule : ℕ → DifferentialGradedModule A
  | 0 => M
  | (i + 1) => Hom.cokernelObj (dualResolutionStep (resolutionModule i)).φ

/-- The tower `I₀, I₁, I₂, …` of the proof of Stacks 09KU: `Iᵢ` is the module Stacks 09KT
injects `Mᵢ` into. -/
def resolutionI (i : ℕ) : DifferentialGradedModule A :=
  (dualResolutionStep (resolutionModule M i)).I

/-- The injection `Mᵢ → Iᵢ` of the resolution tower. -/
def resolutionφ (i : ℕ) : resolutionModule M i ⟶ resolutionI M i :=
  (dualResolutionStep (resolutionModule M i)).φ

/-- The transition map `fᵢ : Iᵢ → I_{i+1}` of the resolution tower, the composition of the
projection `Iᵢ → M_{i+1}` onto the cokernel with the injection `M_{i+1} → I_{i+1}`. -/
def resolutionMap (i : ℕ) : resolutionI M i ⟶ resolutionI M (i + 1) :=
  Hom.cokernelπ (resolutionφ M i) ≫ resolutionφ M (i + 1)

/-- A cokernel projection kills the image of the map it is the cokernel of. -/
private theorem cokernelπ_toFun_toFun {M N : DifferentialGradedModule A} (f : M ⟶ N) (x : M.M) :
    (Hom.cokernelπ f).toFun (f.toFun x) = 0 := by
  rw [Hom.cokernelπ_toFun_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨x, rfl⟩

/-- The resolution tower is a complex: `f_{i+1} ∘ fᵢ = 0`, because the composition
`M_{i+1} → I_{i+1} → M_{i+2}` of an injection with the projection onto its cokernel is zero. -/
theorem resolutionMap_resolutionMap (i : ℕ) (x : (resolutionI M i).M) :
    (resolutionMap M (i + 1)).toFun ((resolutionMap M i).toFun x) = 0 :=
  (congrArg (resolutionφ M (i + 1 + 1)).toFun
    (cokernelπ_toFun_toFun (resolutionφ M (i + 1)) _)).trans (map_zero _)

/-! ### The augmentation

`resolutionModule M 0` is `M`, but only by unfolding at default transparency, and instance
search runs below that — so `(resolutionφ M 0).toFun` is a linear map out of
`(resolutionModule M 0).M` and the rewriting tactics will not see it as a linear map out of
`M.M`. Every fact about the zeroth injection is therefore restated at the honest type of `M` and
discharged by plain application, which checks definitional equality at default transparency.
This is the pattern of `DifferentialGradedModule.product` in `Module/Product.lean`; see its
implementation notes. -/

/-- The injection `M → I₀` of Stacks 09KT, stated at the honest type of `M`. -/
def resolutionφ₀ : M.M →ₗ[R] (resolutionI M 0).M := (resolutionφ M 0).toFun

/-- The zeroth injection commutes with the right `A`-action. -/
theorem resolutionφ₀_smul (x : M.M) (a : A.A) :
    resolutionφ₀ M (MulOpposite.op a • x) = MulOpposite.op a • resolutionφ₀ M x :=
  (resolutionφ M 0).map_smul x a

/-- The zeroth injection preserves degrees. -/
theorem resolutionφ₀_grading (n : ℤ) (x : M.M) (hx : x ∈ M.grading n) :
    resolutionφ₀ M x ∈ (resolutionI M 0).grading n :=
  (resolutionφ M 0).map_grading n x hx

/-- The zeroth injection commutes with the differentials. -/
theorem resolutionφ₀_d (x : M.M) :
    resolutionφ₀ M (M.d x) = (resolutionI M 0).d (resolutionφ₀ M x) :=
  LinearMap.congr_fun (resolutionφ M 0).map_d x

/-- The zeroth injection is injective, by Stacks 09KT(1). -/
theorem resolutionφ₀_injective : Function.Injective (resolutionφ₀ M) :=
  (dualResolutionStep (resolutionModule M 0)).injective

/-- The composition `M → I₀ → I₁` is zero: the image of `M` in `I₀` is exactly what the
projection onto `M₁ = Coker(M → I₀)` kills. -/
theorem resolutionMap_resolutionφ₀ (x : M.M) :
    (resolutionMap M 0).toFun (resolutionφ₀ M x) = 0 :=
  (congrArg (resolutionφ M 1).toFun (cokernelπ_toFun_toFun (resolutionφ M 0) x)).trans
    (map_zero _)

/-- **The module `I` of Stacks 09KU**: the totalization at offset `0` of the resolution tower
`I₀ → I₁ → ⋯`, with graded parts `Iⁿ = ∏_{i ≥ 0} Iᵢ^{n - i}`. -/
def resolutionTotal : DifferentialGradedModule A :=
  towerTotal (resolutionI M) 0 (resolutionMap M) (resolutionMap_resolutionMap M)

/-- The `i`-th component of a point of `I`. -/
def resolutionTotal.π (i : ℕ) : (resolutionTotal M).M →ₗ[R] (resolutionI M i).M :=
  towerTotal.π (resolutionI M) 0 (resolutionMap M) (resolutionMap_resolutionMap M) i

/-- The components of the augmentation `M ⟶ I`: the injection `M → I₀` of Stacks 09KT in degree
`0`, and zero in all higher degrees. -/
def resolutionAugComp : ∀ i : ℕ, M.M →ₗ[R] (resolutionI M i).M
  | 0 => resolutionφ₀ M
  | (_ + 1) => 0

/-- The zeroth component of the augmentation is the injection `M → I₀`. -/
@[simp] theorem resolutionAugComp_zero : resolutionAugComp M 0 = resolutionφ₀ M := rfl

/-- The higher components of the augmentation vanish. -/
@[simp] theorem resolutionAugComp_succ (i : ℕ) : resolutionAugComp M (i + 1) = 0 := rfl

/-- **The augmentation `M ⟶ I` of Stacks 09KU**: the map whose zeroth component is the injection
`M → I₀` and whose higher components vanish. It is a homomorphism of differential graded modules
because the composition `M → I₀ → I₁` is zero. -/
def resolutionAug : M ⟶ resolutionTotal M :=
  towerTotal.lift (resolutionI M) 0 (resolutionMap M) (resolutionMap_resolutionMap M)
    (resolutionAugComp M)
    (by
      intro i x a
      cases i with
      | zero => rw [resolutionAugComp_zero]; exact resolutionφ₀_smul M x a
      | succ i => simp only [resolutionAugComp_succ, LinearMap.zero_apply, smul_zero])
    (by
      intro i n x hx
      cases i with
      | zero =>
          rw [resolutionAugComp_zero,
            show n - (0 + ((0 : ℕ) : ℤ)) = n from by push_cast; ring]
          exact resolutionφ₀_grading M n x hx
      | succ i =>
          simp only [resolutionAugComp_succ, LinearMap.zero_apply]
          exact Submodule.zero_mem _)
    (by
      intro x
      rw [resolutionAugComp_zero, Int.negOnePow_zero, Units.val_one, one_smul]
      exact resolutionφ₀_d M x)
    (by
      intro i x
      cases i with
      | zero =>
          simp only [resolutionAugComp_succ, resolutionAugComp_zero, LinearMap.zero_apply,
            map_zero, smul_zero, zero_add]
          exact (resolutionMap_resolutionφ₀ M x).symm
      | succ i =>
          simp only [resolutionAugComp_succ, LinearMap.zero_apply, map_zero, smul_zero,
            zero_add])

/-- The zeroth component of the augmentation is the injection `M → I₀` of Stacks 09KT. -/
theorem resolutionTotal.π_resolutionAug_zero (x : M.M) :
    resolutionTotal.π M 0 ((resolutionAug M).toFun x) = resolutionφ₀ M x := rfl

/-- The higher components of the augmentation vanish. -/
theorem resolutionTotal.π_resolutionAug_succ (i : ℕ) (x : M.M) :
    resolutionTotal.π M (i + 1) ((resolutionAug M).toFun x) = 0 := rfl

/-- **The augmentation `M ⟶ I` is injective**, because its zeroth component is the injection
`M → I₀` of Stacks 09KT. -/
theorem resolutionAug_injective : Function.Injective (resolutionAug M).toFun := fun x y h =>
  resolutionφ₀_injective M (by
    rw [← resolutionTotal.π_resolutionAug_zero M x, ← resolutionTotal.π_resolutionAug_zero M y,
      h])

end DifferentialGradedModule

end
