module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DualShift
public import StacksFrontier.Algebra.DifferentialGraded.Module.GradedSubmodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyIResolution

/-! # The property-(I) filtration of the totalization of Stacks 09KU

Let `(A, d)` be a differential graded algebra and `M` a right differential graded `A`-module.
`StacksFrontier/Algebra/DifferentialGraded/Module/PropertyIResolution.lean` builds, out of the
resolution tower `I₀ → I₁ → ⋯` of Stacks 09KT, the module

`I = ∏_{j ≥ 0} Iⱼ[-j]`

of the proof of Stacks 09KU, together with the augmentation `M ⟶ I`. This file equips `I` with
a filtration exhibiting property (I), i.e. with a
`DifferentialGradedModule.PropertyIFiltration`. The stages are

`F_{2i} I = ∏_{j ≥ i} Iⱼ[-j]` and `F_{2i+1} I = I'ᵢ[-i] × ∏_{j ≥ i+1} Iⱼ[-j]`,

where `0 → I'ᵢ → Iᵢ → I''ᵢ → 0` is the admissible short exact sequence of Stacks 09KT(3) at the
`i`-th stage of the tower, so that the successive graded pieces are `I''ᵢ[-i]` and `I'ᵢ[-i]` —
products of shifts of `A^∨`, as property (I) demands.

This is **one of the two halves of Stacks 09KU**; the other is that
`DifferentialGradedModule.resolutionAug` is a quasi-isomorphism. That half is not proved here,
and so no `@[stacks 09KU]` attribute is placed in this file.

## Main definitions

* `DifferentialGradedModule.ResolutionFiltration.carrier` and
  `DifferentialGradedModule.ResolutionFiltration.stage`: the `p`-th stage of the filtration, as
  a submodule and as a differential graded submodule of `I`.
* `DifferentialGradedModule.ResolutionFiltration.incl`: the inclusion `F_{p+1} I ⟶ Fᵖ I`.
* `DifferentialGradedModule.ResolutionFiltration.single`: the point of `I` supported in a single
  factor.
* `DifferentialGradedModule.ResolutionFiltration.modify`: the modification of a single component
  of a point of `I`, out of which both graded retractions are built.
* `DifferentialGradedModule.ResolutionFiltration.stageπ` and
  `DifferentialGradedModule.ResolutionFiltration.stageRetract`: the two homomorphisms out of a
  stage that the graded pieces are computed from.
* `DifferentialGradedModule.ResolutionFiltration.Piece` and
  `DifferentialGradedModule.ResolutionFiltration.piece`: the graded piece of a stage, bundled.
* `DifferentialGradedModule.resolutionPropertyIFiltration`: the filtration itself.

## Main results

* `DifferentialGradedModule.ResolutionFiltration.stage_admissible`: property (I)(2), that every
  inclusion `F_{p+1} I ⟶ Fᵖ I` is an admissible monomorphism.
* `DifferentialGradedModule.ResolutionFiltration.stage_separated` and
  `DifferentialGradedModule.ResolutionFiltration.stage_complete`: property (I)(1), that
  `I = lim I / Fᵖ I`.
* `DifferentialGradedModule.ResolutionFiltration.pieceMapEven_surjective`,
  `DifferentialGradedModule.ResolutionFiltration.pieceMapEven_ker`,
  `DifferentialGradedModule.ResolutionFiltration.pieceMapOdd_surjective` and
  `DifferentialGradedModule.ResolutionFiltration.pieceMapOdd_ker`: property (I)(3), that the
  graded pieces are the asserted products of shifts of `A^∨`.

## Implementation notes

*The stages are cut out of `I` by conditions on components, not built as tail totalizations.*
`F_{2i} I` is the totalization of the tail tower at offset `i`, and
`DifferentialGradedModule.towerTotal` carries the offset precisely so that it can be written
that way. Presenting it instead as the submodule of `I` on which the components below `i`
vanish is much cheaper: the inclusions `F_{p+1} I ⟶ Fᵖ I` become inclusions of submodules of one
fixed module rather than maps between two differently-offset totalizations, which would have to
cross the index casts `0 + m = m` and `m + 1 + i = m + i + 1`. The general differential graded
submodule `DifferentialGradedModule.GradedSub` of
`StacksFrontier/Algebra/DifferentialGraded/Module/GradedSubmodule.lean` exists for this purpose and
is used field for field.

*The two parities are packed into one formula for the stages.* `carrier p` asks that the `j`-th
component vanish whenever `2j + 2 ≤ p` and lie in `I'ⱼ` when `2j + 1 = p`. At `p = 2i` the first
condition says `j < i` and the second is vacuous; at `p = 2i + 1` the first still says `j < i`
and the second pins the `i`-th component. So the stages, their inclusions, their monotonicity,
separatedness and completeness are all uniform in `p` and need no case distinction at all, and
only the three fields that mention the graded pieces do.

*Those three fields are bundled so that the parity never enters a type.*
`DifferentialGradedModule.PropertyIFiltration.quotientMap` has a type depending on
`quotientShift`, and the shifts genuinely differ between the two parities (`kᵢ + 1 - i` against
`kᵢ - i`). Defining `quotientShift` by a parity-dependent formula and then `quotientMap` by
cases would require transporting a homomorphism along an equality of shift functions, i.e. an
`eqToHom`, through the surjectivity and kernel statements as well.
`DifferentialGradedModule.ResolutionFiltration.Piece` carries the shifts, the map, its
surjectivity and its kernel together, so the `dif` on the parity of `p` is taken once, in
`DifferentialGradedModule.ResolutionFiltration.piece`, and is never unfolded again. The index
type and its decidable equality are the same in both parities — both graded pieces are products
over the index set of Stacks 09KT(3) at stage `p / 2` — so those two fields stay outside the
bundle.

*The projections of `I` are not homomorphisms, but their restrictions to the stages are.* The
twisted differential of the totalization sends the `(i-1)`-st factor into the `i`-th, so the
`i`-th projection fails to commute with it by the term `f_{i-1}(x_{i-1})`. On a stage where the
components below `i` vanish that term is zero, which is the content of
`DifferentialGradedModule.resolutionTotal.π_d_eq` and is what makes
`DifferentialGradedModule.ResolutionFiltration.stageπ` a homomorphism. The same mechanism makes
`DifferentialGradedModule.ResolutionFiltration.stageRetract` one: the graded retraction
`Iᵢ ⟶ I'ᵢ` does not commute with the differentials, but on the `(2i+1)`-st stage the `i`-th
component lies in `I'ᵢ`, where the differential is computed by the homomorphism `I'ᵢ ⟶ Iᵢ`.

*Facts about the totalization are restated at the spelling `resolutionTotal M`.*
`DifferentialGradedModule.resolutionTotal` is a `def`, so a lemma about
`DifferentialGradedModule.towerTotal` is invisible to `rw` at that spelling; the first section
below restates the handful that are needed and discharges each by plain application, which
checks definitional equality at default transparency. This is the pattern the augmentation of
`Module/PropertyIResolution.lean` already uses; see its implementation notes.

## References

* [Stacks Project, Tag 09KU](https://stacks.math.columbia.edu/tag/09KU), whose proof this is the
  first half of.
* [Stacks Project, Tag 09KQ](https://stacks.math.columbia.edu/tag/09KQ), property (I).
* [Stacks Project, Tag 09KT](https://stacks.math.columbia.edu/tag/09KT), which supplies the
  steps of the resolution tower.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}
variable (M : DifferentialGradedModule.{u, u, u} A)

/-! ### Isomorphisms act bijectively on points -/

/-- The inverse of an isomorphism of differential graded modules undoes it on points. -/
theorem iso_inv_hom_apply {X Y : DifferentialGradedModule.{u, u, u} A} (f : X ≅ Y) (x : X.M) :
    f.inv.toFun (f.hom.toFun x) = x :=
  LinearMap.congr_fun (congrArg Hom.toFun f.hom_inv_id) x

/-- An isomorphism of differential graded modules undoes its inverse on points. -/
theorem iso_hom_inv_apply {X Y : DifferentialGradedModule.{u, u, u} A} (f : X ≅ Y) (y : Y.M) :
    f.hom.toFun (f.inv.toFun y) = y :=
  LinearMap.congr_fun (congrArg Hom.toFun f.inv_hom_id) y

/-- The inverse of an isomorphism of differential graded modules is injective on points. -/
theorem iso_inv_injective {X Y : DifferentialGradedModule.{u, u, u} A} (f : X ≅ Y) :
    Function.Injective f.inv.toFun := fun a b hab => by
  rw [← iso_hom_inv_apply f a, ← iso_hom_inv_apply f b, hab]

/-! ### The totalization, read componentwise

`DifferentialGradedModule.resolutionTotal` is a `def`, not an abbreviation, so a fact about
`DifferentialGradedModule.towerTotal` is not visible to the rewriting tactics at the spelling
`resolutionTotal M`. The facts this file needs are therefore restated here at that spelling and
discharged by plain application, which checks definitional equality at default transparency —
the pattern of the augmentation in `Module/PropertyIResolution.lean`. -/

/-- The components of a point of `I` commute with the right `A`-action. -/
theorem resolutionTotal.π_smul (i : ℕ) (x : (resolutionTotal M).M) (a : A.A) :
    resolutionTotal.π M i (MulOpposite.op a • x)
      = MulOpposite.op a • resolutionTotal.π M i x :=
  (towerProduct.π.{u, u, u} (resolutionI M) 0 i).map_smul x a

/-- A point of `I` is homogeneous of degree `n` exactly when its `i`-th component lies in
`Iᵢ^{n - i}`. -/
theorem resolutionTotal.mem_grading_iff {n : ℤ} (x : (resolutionTotal M).M) :
    x ∈ (resolutionTotal M).grading n ↔
      ∀ i : ℕ, resolutionTotal.π M i x ∈ (resolutionI M i).grading (n - i) :=
  Iff.trans (towerTotal.mem_grading_iff.{u, u, u} (resolutionI M) 0 (resolutionMap M)
      (resolutionMap_resolutionMap M) x)
    (forall_congr' fun i => by
      rw [show n - (0 + (i : ℤ)) = n - i from by ring]
      exact Iff.rfl)

/-- A point of `I` is determined by its components. -/
theorem resolutionTotal.eq_of_π_eq {x y : (resolutionTotal M).M}
    (h : ∀ i, resolutionTotal.π M i x = resolutionTotal.π M i y) : x = y :=
  towerTotal.eq_of_π_eq.{u, u, u} (resolutionI M) 0 (resolutionMap M)
    (resolutionMap_resolutionMap M) h

/-- A point of `I` with vanishing components is zero. -/
theorem resolutionTotal.eq_zero_of_π_eq_zero {x : (resolutionTotal M).M}
    (h : ∀ i, resolutionTotal.π M i x = 0) : x = 0 :=
  resolutionTotal.eq_of_π_eq M fun i => (h i).trans (map_zero _).symm

/-- Every family of components of matching degrees is realized by a point of `I` of degree
`n`. -/
theorem resolutionTotal.exists_mem_grading (n : ℤ) (q : ∀ i : ℕ, (resolutionI M i).M)
    (hq : ∀ i, q i ∈ (resolutionI M i).grading (n - i)) :
    ∃ y ∈ (resolutionTotal M).grading n, ∀ i, resolutionTotal.π M i y = q i :=
  towerTotal.exists_mem_grading.{u, u, u} (resolutionI M) 0 (resolutionMap M)
    (resolutionMap_resolutionMap M) n q fun i => by
      rw [show n - (0 + (i : ℤ)) = n - i from by ring]; exact hq i

/-- The components of the twisted differential of `I`. -/
theorem resolutionTotal.π_d (i : ℕ) (x : (resolutionTotal M).M) :
    resolutionTotal.π M i ((resolutionTotal M).d x)
      = (((0 + (i : ℤ)).negOnePow : ℤ)) • (resolutionI M i).d (resolutionTotal.π M i x)
        + towerTwistComp.{u, u, u} (resolutionI M) 0 (resolutionMap M) i x :=
  towerTotal.π_d.{u, u, u} (resolutionI M) 0 (resolutionMap M) (resolutionMap_resolutionMap M) i x

/-- The `i`-th component of the twisting operator vanishes on a point whose components below
`i` vanish: it is `0` for `i = 0` and `f_{i-1}` of the `(i-1)`-st component otherwise. -/
theorem resolutionTotal.towerTwistComp_eq_zero (i : ℕ) (x : (resolutionTotal M).M)
    (h : ∀ j, j < i → resolutionTotal.π M j x = 0) :
    towerTwistComp.{u, u, u} (resolutionI M) 0 (resolutionMap M) i x = 0 := by
  cases i with
  | zero => rfl
  | succ i =>
      refine Eq.trans (towerTwistComp_succ.{u, u, u} (resolutionI M) 0 (resolutionMap M) i x) ?_
      rw [show (towerProduct.π.{u, u, u} (resolutionI M) 0 i).toFun x
            = resolutionTotal.π M i x from rfl,
        h i (by omega), map_zero]

/-- **On a point whose components below `i` vanish the twist contributes nothing**: the `i`-th
component of `d(x)` is the differential of the `i`-th factor `Iᵢ[-i]` applied to the `i`-th
component of `x`. -/
theorem resolutionTotal.π_d_eq (i : ℕ) (x : (resolutionTotal M).M)
    (h : ∀ j, j < i → resolutionTotal.π M j x = 0) :
    resolutionTotal.π M i ((resolutionTotal M).d x)
      = (towerFactor (resolutionI M) 0 i).d (resolutionTotal.π M i x) := by
  rw [resolutionTotal.π_d, resolutionTotal.towerTwistComp_eq_zero M i x h, add_zero,
    towerFactor_d, LinearMap.smul_apply, Units.smul_def]

/-! ### The data chosen at each stage of the resolution tower -/

/-- The Stacks 09KT step chosen at the `i`-th stage of the resolution tower of Stacks 09KU. -/
def resolutionStep (i : ℕ) : DualResolutionStep (resolutionModule M i) :=
  dualResolutionStep (resolutionModule M i)

/-- The inclusion `I'ᵢ = ∏ A^∨[kᵢ] ⟶ Iᵢ` of Stacks 09KT(3). -/
def resolutionSubHom (i : ℕ) :
    @productDualShifts _ _ A _ (resolutionStep M i).decEq (resolutionStep M i).k ⟶
      resolutionI M i :=
  (resolutionStep M i).sub

/-- The projection `Iᵢ ⟶ I''ᵢ = ∏ A^∨[kᵢ + 1]` of Stacks 09KT(3). -/
def resolutionQuotHom (i : ℕ) :
    resolutionI M i ⟶
      @productDualShifts _ _ A _ (resolutionStep M i).decEq
        (fun c => (resolutionStep M i).k c + 1) :=
  (resolutionStep M i).quot

/-- The sequence `0 → I'ᵢ → Iᵢ → I''ᵢ → 0` is admissible short exact. -/
theorem resolutionSes (i : ℕ) :
    IsAdmissibleShortExact (resolutionSubHom M i) (resolutionQuotHom M i) :=
  (resolutionStep M i).ses

/-- The graded retraction `Iᵢ ⟶ I'ᵢ` of `DifferentialGradedModule.resolutionSubHom`, supplied
by the graded splitting of the admissible short exact sequence of Stacks 09KT(3). -/
def resolutionRetraction (i : ℕ) :
    GradedHom (resolutionI M i)
      (@productDualShifts _ _ A _ (resolutionStep M i).decEq (resolutionStep M i).k) :=
  (resolutionSes M i).admissibleMono.choose

/-- The retraction retracts. -/
theorem resolutionRetraction_resolutionSubHom (i : ℕ)
    (y : (@productDualShifts _ _ A _ (resolutionStep M i).decEq (resolutionStep M i).k).M) :
    (resolutionRetraction M i).toFun ((resolutionSubHom M i).toFun y) = y :=
  (resolutionSes M i).admissibleMono.choose_spec y

/-- The `j`-th shifted inclusion `I'ⱼ[-j] ⟶ Iⱼ[-j]`, the `j`-th factor of the totalization
being `Iⱼ[-j]`. -/
def resolutionSubShift (j : ℕ) :
    shift (@productDualShifts _ _ A _ (resolutionStep M j).decEq (resolutionStep M j).k)
      (-(0 + (j : ℤ))) ⟶ towerFactor (resolutionI M) 0 j :=
  shiftMap (resolutionSubHom M j) (-(0 + (j : ℤ)))

/-- The shifted inclusion has the same underlying linear map as the inclusion. -/
theorem resolutionSubShift_toFun (j : ℕ) :
    (resolutionSubShift M j).toFun = (resolutionSubHom M j).toFun := rfl

/-- The `j`-th shifted projection `Iⱼ[-j] ⟶ I''ⱼ[-j]`. -/
def resolutionQuotShift (j : ℕ) :
    towerFactor (resolutionI M) 0 j ⟶
      shift (@productDualShifts _ _ A _ (resolutionStep M j).decEq
        (fun c => (resolutionStep M j).k c + 1)) (-(0 + (j : ℤ))) :=
  shiftMap (resolutionQuotHom M j) (-(0 + (j : ℤ)))

/-- The shifted projection has the same underlying linear map as the projection. -/
theorem resolutionQuotShift_toFun (j : ℕ) :
    (resolutionQuotShift M j).toFun = (resolutionQuotHom M j).toFun := rfl

/-! ### Points supported in a single factor -/

namespace ResolutionFiltration

/-- The components of `DifferentialGradedModule.ResolutionFiltration.single`: the identity in
slot `i` and zero elsewhere. -/
def singleComp (i : ℕ) : ∀ j : ℕ,
    (towerFactor (resolutionI M) 0 i).M →ₗ[R] (resolutionI M j).M :=
  Function.update (fun _ => 0) i LinearMap.id

/-- The `i`-th component of `singleComp i` is the identity. -/
theorem singleComp_self (i : ℕ) : singleComp M i i = LinearMap.id :=
  Function.update_self (β := fun j : ℕ =>
    (towerFactor (resolutionI M) 0 i).M →ₗ[R] (resolutionI M j).M) i _ _

/-- The other components of `singleComp i` vanish. -/
theorem singleComp_of_ne {i j : ℕ} (h : j ≠ i) : singleComp M i j = 0 :=
  Function.update_of_ne h _ _

/-- The components of `singleComp i` carry `Iᵢ[-i]^n` into `Iⱼ^{n - j}`. -/
theorem singleComp_grading (i : ℕ) :
    ∀ (j : ℕ) (n : ℤ) (y : (towerFactor (resolutionI M) 0 i).M),
      y ∈ (towerFactor (resolutionI M) 0 i).grading n →
        singleComp M i j y ∈ (resolutionI M j).grading (n - (0 + j)) := by
  intro j n y hy
  by_cases h : j = i
  · subst h
    rw [towerFactor_grading] at hy
    rw [singleComp_self]
    exact hy
  · rw [singleComp_of_ne M h]
    exact Submodule.zero_mem _

/-- **The point of `I` whose `i`-th component is `w` and whose other components vanish.** It is
only a map of graded modules, not of differential graded ones: the twisted differential sends
the `i`-th factor into the `(i + 1)`-st. -/
def single (i : ℕ) : (resolutionI M i).M →ₗ[R] (resolutionTotal M).M :=
  towerProduct.liftGraded.{u, u, u} (T := towerFactor (resolutionI M) 0 i) (resolutionI M) 0
    (singleComp M i) (singleComp_grading M i)

/-- The `j`-th component of `single i w` is `singleComp i j w`. -/
private theorem π_single_eq (i j : ℕ) (w : (resolutionI M i).M) :
    resolutionTotal.π M j (single M i w) = singleComp M i j w :=
  towerProduct.π_liftGraded.{u, u, u} _ _ _ _ _ _

/-- The `i`-th component of `single i w` is `w`. -/
theorem π_single_self (i : ℕ) (w : (resolutionI M i).M) :
    resolutionTotal.π M i (single M i w) = w := by
  rw [π_single_eq, singleComp_self]
  rfl

/-- The other components of `single i w` vanish. -/
theorem π_single_of_ne {i j : ℕ} (h : j ≠ i) (w : (resolutionI M i).M) :
    resolutionTotal.π M j (single M i w) = 0 := by
  rw [π_single_eq, singleComp_of_ne M h]
  rfl

/-- `single i` commutes with the right `A`-action. -/
theorem single_smul (i : ℕ) (w : (resolutionI M i).M) (a : A.A) :
    single M i (MulOpposite.op a • w) = MulOpposite.op a • single M i w := by
  refine resolutionTotal.eq_of_π_eq M fun j => ?_
  rw [resolutionTotal.π_smul]
  by_cases h : j = i
  · subst h; rw [π_single_self, π_single_self]
  · rw [π_single_of_ne M h, π_single_of_ne M h, smul_zero]

/-- `single i` carries `Iᵢ^{n - i}` into `Iⁿ`. -/
theorem single_mem_grading (i : ℕ) (n : ℤ) (w : (resolutionI M i).M)
    (hw : w ∈ (resolutionI M i).grading (n - i)) :
    single M i w ∈ (resolutionTotal M).grading n := by
  refine (resolutionTotal.mem_grading_iff M _).2 fun j => ?_
  by_cases h : j = i
  · subst h; rw [π_single_self]; exact hw
  · rw [π_single_of_ne M h]; exact Submodule.zero_mem _

/-! ### The stages of the filtration -/

/-- The `j`-th component of a graded component of a point of `I` is the graded component of its
`j`-th component. -/
theorem π_decompose (j : ℕ) (n : ℤ) (x : (resolutionTotal M).M) :
    resolutionTotal.π M j
        (DirectSum.decompose (resolutionTotal M).grading x n : (resolutionTotal M).M)
      = (DirectSum.decompose (towerFactor (resolutionI M) 0 j).grading
          (resolutionTotal.π M j x) n : (towerFactor (resolutionI M) 0 j).M) :=
  (DirectSum.coe_decompose_apply_map (resolutionTotal M).grading
    (towerFactor (resolutionI M) 0 j).grading (resolutionTotal.π M j)
    (fun m y hy => (towerProduct.π.{u, u, u} (resolutionI M) 0 j).map_grading m y hy) x n).symm

/-- If the `j`-th component of a point of `I` lies in the image of `I'ⱼ ⟶ Iⱼ`, so does the
`j`-th component of each of its graded components. -/
theorem π_decompose_mem_range (j : ℕ) (n : ℤ) (x : (resolutionTotal M).M)
    (hx : resolutionTotal.π M j x ∈ LinearMap.range (resolutionSubHom M j).toFun) :
    resolutionTotal.π M j
        (DirectSum.decompose (resolutionTotal M).grading x n : (resolutionTotal M).M)
      ∈ LinearMap.range (resolutionSubHom M j).toFun := by
  obtain ⟨y, hy⟩ := hx
  refine ⟨(DirectSum.decompose (shift (@productDualShifts _ _ A _ (resolutionStep M j).decEq
      (resolutionStep M j).k) (-(0 + (j : ℤ)))).grading y n :
    (shift (@productDualShifts _ _ A _ (resolutionStep M j).decEq
      (resolutionStep M j).k) (-(0 + (j : ℤ)))).M), ?_⟩
  rw [π_decompose, ← hy]
  exact (DirectSum.coe_decompose_apply_map
    (shift (@productDualShifts _ _ A _ (resolutionStep M j).decEq
      (resolutionStep M j).k) (-(0 + (j : ℤ)))).grading
    (towerFactor (resolutionI M) 0 j).grading (resolutionSubHom M j).toFun
    (fun m z hz => (resolutionSubShift M j).map_grading m z hz) y n).symm

/-- **The carrier of the `p`-th stage of the property-(I) filtration of `I`**: the points whose
`j`-th component vanishes whenever `2j + 2 ≤ p` and whose `j`-th component lies in `I'ⱼ` when
`2j + 1 = p`. For `p = 2i` this is `∏_{j ≥ i} Iⱼ[-j]`, and for `p = 2i + 1` it is
`I'ᵢ[-i] × ∏_{j ≥ i+1} Iⱼ[-j]`; the two parity cases are packed into one formula so that the
stages, their inclusions and the conditions stated in terms of them are uniform in `p`. -/
def carrier (p : ℕ) : Submodule (MulOpposite A.A) (resolutionTotal M).M where
  carrier := {x | (∀ j : ℕ, 2 * j + 2 ≤ p → resolutionTotal.π M j x = 0) ∧
    ∀ j : ℕ, 2 * j + 1 = p →
      resolutionTotal.π M j x ∈ LinearMap.range (resolutionSubHom M j).toFun}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at *
    exact ⟨fun j hj => by rw [map_add, hx.1 j hj, hy.1 j hj, add_zero],
      fun j hj => by rw [map_add]; exact Submodule.add_mem _ (hx.2 j hj) (hy.2 j hj)⟩
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun _ _ => map_zero _, fun _ _ => by rw [map_zero]; exact Submodule.zero_mem _⟩
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq] at *
    have hc : ∀ j : ℕ, resolutionTotal.π M j (c • x)
        = MulOpposite.op c.unop • resolutionTotal.π M j x := fun j => by
      rw [show c • x = MulOpposite.op c.unop • x from rfl, resolutionTotal.π_smul]
    refine ⟨fun j hj => by rw [hc j, hx.1 j hj, smul_zero], fun j hj => ?_⟩
    obtain ⟨y, hy⟩ := hx.2 j hj
    exact ⟨MulOpposite.op c.unop • y, by
      rw [hc j, ← hy, (resolutionSubHom M j).map_smul y c.unop]⟩

/-- Membership in the `p`-th stage, unfolded. -/
theorem mem_carrier {p : ℕ} {x : (resolutionTotal M).M} :
    x ∈ carrier M p ↔ (∀ j : ℕ, 2 * j + 2 ≤ p → resolutionTotal.π M j x = 0) ∧
      ∀ j : ℕ, 2 * j + 1 = p →
        resolutionTotal.π M j x ∈ LinearMap.range (resolutionSubHom M j).toFun := Iff.rfl

/-- The components of a point of the `p`-th stage below `⌈p/2⌉` vanish — in the two parity
cases, below `i` for `p = 2i` and for `p = 2i + 1`. -/
theorem π_eq_zero_of_mem_carrier {p j l : ℕ} {x : (resolutionTotal M).M}
    (hx : x ∈ carrier M p) (hj : 2 * j ≤ p) (hl : l < j) : resolutionTotal.π M l x = 0 :=
  hx.1 l (by omega)

/-- **The `p`-th stage is stable under the differential.** The `j`-th component of `d(x)` is the
shifted differential of the `j`-th component of `x`, because the twisting term reads the
`(j-1)`-st component, which vanishes at every `j` the two conditions mention. -/
theorem carrier_d_mem (p : ℕ) (x : (resolutionTotal M).M) (hx : x ∈ carrier M p) :
    (resolutionTotal M).d x ∈ carrier M p := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rw [resolutionTotal.π_d_eq M j x (fun l hl => hx.1 l (by omega)), hx.1 j hj, map_zero]
  · obtain ⟨y, hy⟩ := hx.2 j hj
    refine ⟨(shift (@productDualShifts _ _ A _ (resolutionStep M j).decEq
      (resolutionStep M j).k) (-(0 + (j : ℤ)))).d y, ?_⟩
    rw [resolutionTotal.π_d_eq M j x (fun l hl => hx.1 l (by omega)), ← hy]
    exact LinearMap.congr_fun (resolutionSubShift M j).map_d y

/-- **The `p`-th stage, as a differential graded submodule of `I`.** -/
def stage (p : ℕ) : GradedSub (resolutionTotal M) where
  carrier := carrier M p
  decompose_mem := by
    intro n x hx
    exact ⟨fun j hj => by rw [π_decompose, hx.1 j hj, DirectSum.decompose_zero,
        DirectSum.zero_apply, ZeroMemClass.coe_zero],
      fun j hj => π_decompose_mem_range M j n x (hx.2 j hj)⟩
  d_mem := fun x hx => carrier_d_mem M p x hx

/-- The carrier of the `p`-th stage is the submodule it was built from. -/
@[simp] theorem stage_carrier (p : ℕ) : (stage M p).carrier = carrier M p := rfl

/-- **The filtration is decreasing.** -/
theorem stage_carrier_le (p : ℕ) : (stage M (p + 1)).carrier ≤ (stage M p).carrier := by
  intro x hx
  exact ⟨fun j hj => hx.1 j (by omega), fun j hj => by
    rw [hx.1 j (by omega)]; exact Submodule.zero_mem _⟩

/-- **The inclusion of the `(p+1)`-st stage into the `p`-th.** -/
def incl (p : ℕ) : (stage M (p + 1)).obj ⟶ (stage M p).obj :=
  GradedSub.incl (stage_carrier_le M p)

/-- The inclusions of the filtration are compatible with the embeddings into `I`. -/
@[simp] theorem incl_ι (p : ℕ) (x : (stage M (p + 1)).obj.M) :
    ((stage M p).ι).toFun ((incl M p).toFun x) = ((stage M (p + 1)).ι).toFun x :=
  GradedSub.incl_ι (stage_carrier_le M p) x

/-- The range of an inclusion of the filtration, read in the `p`-th stage. -/
theorem mem_range_incl (p : ℕ) (x : (stage M p).obj.M) :
    x ∈ LinearMap.range (incl M p).toFun ↔
      ((stage M p).ι).toFun x ∈ carrier M (p + 1) := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [incl_ι]
    exact ((stage M (p + 1)).ι_mem y)
  · intro h
    exact ⟨⟨((stage M p).ι).toFun x, h⟩, rfl⟩

/-- The zeroth stage is the whole of `I`. -/
theorem carrier_zero : carrier M 0 = ⊤ :=
  Submodule.eq_top_iff'.2 fun _ => ⟨fun _ hj => by omega, fun _ hj => by omega⟩

/-! ### Modifying a single component, and the graded splittings -/

/-- **Replacing the `i`-th component of a point of `I` by `e` of it**, leaving the other
components alone. The two graded retractions witnessing condition (2) of property (I) are of
this form: the inclusion `F_{2i+1} → F_{2i}` is retracted by `e = sub ∘ r`, and
`F_{2i+2} → F_{2i+1}` by `e = 0`. -/
def modify (i : ℕ) (e : (resolutionI M i).M →ₗ[R] (resolutionI M i).M) :
    (resolutionTotal M).M →ₗ[R] (resolutionTotal M).M :=
  LinearMap.id - (single M i).comp (resolutionTotal.π M i)
    + (single M i).comp (e.comp (resolutionTotal.π M i))

/-- The modification, applied to a point. -/
theorem modify_apply (i : ℕ) (e : (resolutionI M i).M →ₗ[R] (resolutionI M i).M)
    (x : (resolutionTotal M).M) :
    modify M i e x = x - single M i (resolutionTotal.π M i x)
      + single M i (e (resolutionTotal.π M i x)) := rfl

/-- The modification replaces the `i`-th component by `e` of it. -/
theorem π_modify_self (i : ℕ) (e : (resolutionI M i).M →ₗ[R] (resolutionI M i).M)
    (x : (resolutionTotal M).M) :
    resolutionTotal.π M i (modify M i e x) = e (resolutionTotal.π M i x) := by
  rw [modify_apply, map_add, map_sub, π_single_self, π_single_self, sub_self, zero_add]

/-- The modification leaves the other components alone. -/
theorem π_modify_of_ne {i j : ℕ} (h : j ≠ i)
    (e : (resolutionI M i).M →ₗ[R] (resolutionI M i).M) (x : (resolutionTotal M).M) :
    resolutionTotal.π M j (modify M i e x) = resolutionTotal.π M j x := by
  rw [modify_apply, map_add, map_sub, π_single_of_ne M h, π_single_of_ne M h, sub_zero,
    add_zero]

/-- The modification commutes with the right `A`-action as soon as `e` does. -/
theorem modify_smul (i : ℕ) (e : (resolutionI M i).M →ₗ[R] (resolutionI M i).M)
    (he : ∀ (y : (resolutionI M i).M) (a : A.A),
      e (MulOpposite.op a • y) = MulOpposite.op a • e y)
    (x : (resolutionTotal M).M) (a : A.A) :
    modify M i e (MulOpposite.op a • x) = MulOpposite.op a • modify M i e x := by
  refine resolutionTotal.eq_of_π_eq M fun j => ?_
  rw [resolutionTotal.π_smul]
  by_cases h : j = i
  · subst h
    rw [π_modify_self, π_modify_self, resolutionTotal.π_smul, he]
  · rw [π_modify_of_ne M h, π_modify_of_ne M h, resolutionTotal.π_smul]

/-- The modification preserves degrees as soon as `e` does. -/
theorem modify_mem_grading (i : ℕ) (e : (resolutionI M i).M →ₗ[R] (resolutionI M i).M)
    (he : ∀ (m : ℤ) (y : (resolutionI M i).M),
      y ∈ (resolutionI M i).grading m → e y ∈ (resolutionI M i).grading m)
    (n : ℤ) (x : (resolutionTotal M).M) (hx : x ∈ (resolutionTotal M).grading n) :
    modify M i e x ∈ (resolutionTotal M).grading n := by
  refine (resolutionTotal.mem_grading_iff M _).2 fun j => ?_
  by_cases h : j = i
  · subst h
    rw [π_modify_self]
    exact he _ _ ((resolutionTotal.mem_grading_iff M x).1 hx j)
  · rw [π_modify_of_ne M h]
    exact (resolutionTotal.mem_grading_iff M x).1 hx j

/-- **The admissibility criterion for an inclusion of the filtration**: a modification of the
`i`-th component which carries the `p`-th stage into the `(p+1)`-st and fixes the `(p+1)`-st is
a graded retraction of the inclusion. -/
theorem isAdmissibleMono_incl_of_modify (p i : ℕ)
    (e : (resolutionI M i).M →ₗ[R] (resolutionI M i).M)
    (hesmul : ∀ (y : (resolutionI M i).M) (a : A.A),
      e (MulOpposite.op a • y) = MulOpposite.op a • e y)
    (hegrading : ∀ (m : ℤ) (y : (resolutionI M i).M),
      y ∈ (resolutionI M i).grading m → e y ∈ (resolutionI M i).grading m)
    (hmem : ∀ x : (resolutionTotal M).M, x ∈ carrier M p → modify M i e x ∈ carrier M (p + 1))
    (hfix : ∀ x : (resolutionTotal M).M, x ∈ carrier M (p + 1) → modify M i e x = x) :
    IsAdmissibleMono (incl M p) :=
  GradedSub.isAdmissibleMono_incl (stage_carrier_le M p) (modify M i e)
    (modify_smul M i e hesmul) (modify_mem_grading M i e hegrading) hmem hfix

/-- The endomorphism `sub ∘ r` of `Iᵢ`, the projection onto the graded direct summand `I'ᵢ`. -/
def subRetract (i : ℕ) : (resolutionI M i).M →ₗ[R] (resolutionI M i).M :=
  (resolutionSubHom M i).toFun.comp (resolutionRetraction M i).toFun

/-- `sub ∘ r` lands in the image of `I'ᵢ ⟶ Iᵢ`. -/
theorem subRetract_mem_range (i : ℕ) (z : (resolutionI M i).M) :
    subRetract M i z ∈ LinearMap.range (resolutionSubHom M i).toFun :=
  ⟨(resolutionRetraction M i).toFun z, rfl⟩

/-- `sub ∘ r` fixes the image of `I'ᵢ ⟶ Iᵢ` pointwise. -/
theorem subRetract_of_mem_range (i : ℕ) (z : (resolutionI M i).M)
    (hz : z ∈ LinearMap.range (resolutionSubHom M i).toFun) : subRetract M i z = z := by
  obtain ⟨y, rfl⟩ := hz
  rw [show subRetract M i ((resolutionSubHom M i).toFun y)
    = (resolutionSubHom M i).toFun
      ((resolutionRetraction M i).toFun ((resolutionSubHom M i).toFun y)) from rfl,
    resolutionRetraction_resolutionSubHom]

/-- `sub ∘ r` commutes with the right `A`-action. -/
theorem subRetract_smul (i : ℕ) (z : (resolutionI M i).M) (a : A.A) :
    subRetract M i (MulOpposite.op a • z) = MulOpposite.op a • subRetract M i z := by
  rw [show subRetract M i (MulOpposite.op a • z)
    = (resolutionSubHom M i).toFun
      ((resolutionRetraction M i).toFun (MulOpposite.op a • z)) from rfl,
    (resolutionRetraction M i).map_smul, (resolutionSubHom M i).map_smul]
  rfl

/-- `sub ∘ r` preserves degrees. -/
theorem subRetract_mem_grading (i : ℕ) (m : ℤ) (z : (resolutionI M i).M)
    (hz : z ∈ (resolutionI M i).grading m) : subRetract M i z ∈ (resolutionI M i).grading m :=
  (resolutionSubHom M i).map_grading m _ ((resolutionRetraction M i).map_grading m z hz)

/-- **Property (I)(2): every inclusion of the filtration is an admissible monomorphism.** For
`p = 2i` the graded retraction replaces the `i`-th component by its projection onto the graded
direct summand `I'ᵢ` of `Iᵢ`; for `p = 2i + 1` it deletes the `i`-th component. -/
theorem stage_admissible (p : ℕ) : IsAdmissibleMono (incl M p) := by
  rcases Nat.even_or_odd' p with ⟨i, hp | hp⟩
  · subst hp
    refine isAdmissibleMono_incl_of_modify M (2 * i) i (subRetract M i) (subRetract_smul M i)
      (subRetract_mem_grading M i) (fun x hx => ⟨fun j hj => ?_, fun j hj => ?_⟩)
      (fun x hx => resolutionTotal.eq_of_π_eq M fun j => ?_)
    · rw [π_modify_of_ne M (show j ≠ i by omega)]
      exact hx.1 j (by omega)
    · rw [show j = i by omega, π_modify_self]
      exact subRetract_mem_range M i _
    · by_cases h : j = i
      · subst h
        rw [π_modify_self]
        exact subRetract_of_mem_range M j _ (hx.2 j (by omega))
      · rw [π_modify_of_ne M h]
  · subst hp
    refine isAdmissibleMono_incl_of_modify M (2 * i + 1) i 0
      (fun y a => by simp only [LinearMap.zero_apply, smul_zero])
      (fun m y _ => by simpa only [LinearMap.zero_apply] using Submodule.zero_mem _)
      (fun x hx => ⟨fun j hj => ?_, fun j hj => by omega⟩)
      (fun x hx => resolutionTotal.eq_of_π_eq M fun j => ?_)
    · by_cases h : j = i
      · subst h
        rw [π_modify_self, LinearMap.zero_apply]
      · rw [π_modify_of_ne M h]
        exact hx.1 j (by omega)
    · by_cases h : j = i
      · subst h
        rw [π_modify_self, LinearMap.zero_apply, hx.1 j (by omega)]
      · rw [π_modify_of_ne M h]

/-! ### The graded pieces -/

/-- **The `i`-th component, as a homomorphism out of the `p`-th stage** into the `i`-th factor
`Iᵢ[-i]` of the totalization, for any `p` with `2i ≤ p`. The projections of the totalization are
not homomorphisms, because the twisted differential sends the `(i-1)`-st factor into the `i`-th;
on a stage where the `(i-1)`-st component vanishes they are. -/
def stageπ (p i : ℕ) (hp : 2 * i ≤ p) :
    (stage M p).obj ⟶ towerFactor (resolutionI M) 0 i where
  toFun := (resolutionTotal.π M i).comp ((stage M p).ι).toFun
  map_smul x a := by
    change resolutionTotal.π M i (((stage M p).ι).toFun (MulOpposite.op a • x))
      = MulOpposite.op a • resolutionTotal.π M i (((stage M p).ι).toFun x)
    rw [(stage M p).ι.map_smul, resolutionTotal.π_smul]
  map_grading n x hx :=
    (towerProduct.π.{u, u, u} (resolutionI M) 0 i).map_grading n _
      ((GradedSub.mem_obj_grading (stage M p)).1 hx)
  map_d := by
    refine LinearMap.ext fun x => ?_
    change resolutionTotal.π M i (((stage M p).ι).toFun ((stage M p).obj.d x))
      = (towerFactor (resolutionI M) 0 i).d
        (resolutionTotal.π M i (((stage M p).ι).toFun x))
    rw [show ((stage M p).ι).toFun ((stage M p).obj.d x)
      = (resolutionTotal M).d (((stage M p).ι).toFun x) from
        LinearMap.congr_fun (stage M p).ι.map_d x]
    exact resolutionTotal.π_d_eq M i _ fun l hl => ((stage M p).ι_mem x).1 l (by omega)

/-- The `i`-th component out of the `p`-th stage, applied to a point. -/
@[simp] theorem stageπ_toFun (p i : ℕ) (hp : 2 * i ≤ p) (x : (stage M p).obj.M) :
    (stageπ M p i hp).toFun x = resolutionTotal.π M i (((stage M p).ι).toFun x) := rfl

/-- **`I''ᵢ[-i] ≅ ∏ A^∨[kᵢ + 1 - i]`**, the identification that presents the `(2i)`-th graded
piece as a product of shifts of `A^∨`, which is the form the field
`DifferentialGradedModule.PropertyIFiltration.quotientMap` demands. -/
def evenShiftIso (i : ℕ) :
    @productDualShifts _ _ A _ (resolutionStep M i).decEq
        (fun c => ((resolutionStep M i).k c + 1) + -(0 + (i : ℤ))) ≅
      shift (@productDualShifts _ _ A _ (resolutionStep M i).decEq
        (fun c => (resolutionStep M i).k c + 1)) (-(0 + (i : ℤ))) :=
  @productDualShiftsShiftIso _ _ A _ (resolutionStep M i).decEq
    (fun c => (resolutionStep M i).k c + 1) (-(0 + (i : ℤ)))

/-- **`I'ᵢ[-i] ≅ ∏ A^∨[kᵢ - i]`**, the same identification for the `(2i+1)`-st graded piece. -/
def oddShiftIso (i : ℕ) :
    @productDualShifts _ _ A _ (resolutionStep M i).decEq
        (fun c => (resolutionStep M i).k c + -(0 + (i : ℤ))) ≅
      shift (@productDualShifts _ _ A _ (resolutionStep M i).decEq
        (resolutionStep M i).k) (-(0 + (i : ℤ))) :=
  @productDualShiftsShiftIso _ _ A _ (resolutionStep M i).decEq
    (resolutionStep M i).k (-(0 + (i : ℤ)))

/-- **The `(2i)`-th graded piece**: the `i`-th component followed by the projection
`Iᵢ ⟶ I''ᵢ`, read in `I''ᵢ[-i]` and transported back to a product of shifts of `A^∨` by
`DifferentialGradedModule.productDualShiftsShiftIso`. -/
def pieceMapEven (p i : ℕ) (hp : p = 2 * i) :
    (stage M p).obj ⟶ @productDualShifts _ _ A _ (resolutionStep M i).decEq
      (fun c => ((resolutionStep M i).k c + 1) + -(0 + (i : ℤ))) :=
  stageπ M p i (by omega) ≫ resolutionQuotShift M i ≫ (evenShiftIso M i).inv

/-- The `(2i)`-th graded piece map, applied to a point. -/
theorem pieceMapEven_toFun (p i : ℕ) (hp : p = 2 * i) (x : (stage M p).obj.M) :
    (pieceMapEven M p i hp).toFun x
      = (evenShiftIso M i).inv.toFun
        ((resolutionQuotHom M i).toFun
          (resolutionTotal.π M i (((stage M p).ι).toFun x))) := rfl

/-- A point of `Iᵢ` supported in the `i`-th factor lies in the `(2i)`-th stage. -/
theorem single_mem_carrier_even (i : ℕ) (z : (resolutionI M i).M) :
    single M i z ∈ carrier M (2 * i) :=
  ⟨fun j hj => π_single_of_ne M (show j ≠ i by omega) z, fun j hj => by omega⟩

/-- A point of `Iᵢ` lying in `I'ᵢ` and supported in the `i`-th factor lies in the `(2i+1)`-st
stage. -/
theorem single_mem_carrier_odd (i : ℕ)
    (w : (@productDualShifts _ _ A _ (resolutionStep M i).decEq (resolutionStep M i).k).M) :
    single M i ((resolutionSubHom M i).toFun w) ∈ carrier M (2 * i + 1) :=
  ⟨fun j hj => π_single_of_ne M (show j ≠ i by omega) _, fun j hj => by
    rw [show j = i by omega, π_single_self]
    exact ⟨w, rfl⟩⟩

/-- **The `(2i)`-th graded piece map is surjective**: the projection `Iᵢ ⟶ I''ᵢ` is surjective
by Stacks 09KT(3), and every point of `Iᵢ` is the `i`-th component of a point of the `(2i)`-th
stage. -/
theorem pieceMapEven_surjective (p i : ℕ) (hp : p = 2 * i) :
    Function.Surjective (pieceMapEven M p i hp).toFun := by
  intro v
  obtain ⟨z, hz⟩ := (resolutionSes M i).surjective ((evenShiftIso M i).hom.toFun v)
  refine ⟨⟨single M i z, by rw [stage_carrier, hp]; exact single_mem_carrier_even M i z⟩, ?_⟩
  rw [pieceMapEven_toFun]
  rw [show ((stage M p).ι).toFun ⟨single M i z, _⟩ = single M i z from rfl, π_single_self, hz]
  exact iso_inv_hom_apply _ v

/-- **The kernel of the `(2i)`-th graded piece map is the `(2i+1)`-st stage**, because the
kernel of `Iᵢ ⟶ I''ᵢ` is the image of `I'ᵢ ⟶ Iᵢ` by Stacks 09KT(3). -/
theorem pieceMapEven_ker (p i : ℕ) (hp : p = 2 * i) :
    LinearMap.ker (pieceMapEven M p i hp).toFun = LinearMap.range (incl M p).toFun := by
  refine Submodule.ext fun x => ?_
  rw [LinearMap.mem_ker, mem_range_incl]
  have hkey : (pieceMapEven M p i hp).toFun x = 0 ↔
      resolutionTotal.π M i (((stage M p).ι).toFun x)
        ∈ LinearMap.range (resolutionSubHom M i).toFun := by
    rw [pieceMapEven_toFun, (resolutionSes M i).exact, LinearMap.mem_ker]
    exact ⟨fun h => iso_inv_injective (evenShiftIso M i) (by rw [h, map_zero]),
      fun h => by rw [h, map_zero]⟩
  rw [hkey]
  refine ⟨fun h => ⟨fun j hj => ((stage M p).ι_mem x).1 j (by omega), fun j hj => by
    rw [show j = i by omega]; exact h⟩, fun h => h.2 i (by omega)⟩

/-- **The graded retraction of `I'ᵢ ⟶ Iᵢ` composed with the `i`-th component, as a homomorphism
out of the `(2i+1)`-st stage** into `I'ᵢ[-i]`. The retraction is only a map of graded modules,
but on the `(2i+1)`-st stage the composite *does* commute with the differentials: there the
`i`-th component lies in `I'ᵢ`, the twisting term vanishes, and `I'ᵢ ⟶ Iᵢ` is a homomorphism,
so the differential of the `i`-th component is again computed inside `I'ᵢ`. -/
def stageRetract (p i : ℕ) (hp : p = 2 * i + 1) :
    (stage M p).obj ⟶ shift (@productDualShifts _ _ A _ (resolutionStep M i).decEq
      (resolutionStep M i).k) (-(0 + (i : ℤ))) where
  toFun := (resolutionRetraction M i).toFun.comp
    ((resolutionTotal.π M i).comp ((stage M p).ι).toFun)
  map_smul x a := by
    change (resolutionRetraction M i).toFun
        (resolutionTotal.π M i (((stage M p).ι).toFun (MulOpposite.op a • x)))
      = MulOpposite.op a • (resolutionRetraction M i).toFun
        (resolutionTotal.π M i (((stage M p).ι).toFun x))
    rw [(stage M p).ι.map_smul, resolutionTotal.π_smul, (resolutionRetraction M i).map_smul]
  map_grading n x hx :=
    (resolutionRetraction M i).map_grading (n + -(0 + (i : ℤ))) _
      ((towerProduct.π.{u, u, u} (resolutionI M) 0 i).map_grading n _
        ((GradedSub.mem_obj_grading (stage M p)).1 hx))
  map_d := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨w, hw⟩ : ∃ w, (resolutionSubHom M i).toFun w
        = resolutionTotal.π M i (((stage M p).ι).toFun x) :=
      ((stage M p).ι_mem x).2 i (by omega)
    have hιd : ((stage M p).ι).toFun ((stage M p).obj.d x)
        = (resolutionTotal M).d (((stage M p).ι).toFun x) :=
      LinearMap.congr_fun (stage M p).ι.map_d x
    have hπd : resolutionTotal.π M i ((resolutionTotal M).d (((stage M p).ι).toFun x))
        = (towerFactor (resolutionI M) 0 i).d
          (resolutionTotal.π M i (((stage M p).ι).toFun x)) :=
      resolutionTotal.π_d_eq M i _ fun l hl => ((stage M p).ι_mem x).1 l (by omega)
    have hsd : (resolutionSubHom M i).toFun
          ((shift (@productDualShifts _ _ A _ (resolutionStep M i).decEq
            (resolutionStep M i).k) (-(0 + (i : ℤ)))).d w)
        = (towerFactor (resolutionI M) 0 i).d ((resolutionSubHom M i).toFun w) :=
      LinearMap.congr_fun (resolutionSubShift M i).map_d w
    change (resolutionRetraction M i).toFun
        (resolutionTotal.π M i (((stage M p).ι).toFun ((stage M p).obj.d x)))
      = (shift (@productDualShifts _ _ A _ (resolutionStep M i).decEq
          (resolutionStep M i).k) (-(0 + (i : ℤ)))).d
        ((resolutionRetraction M i).toFun
          (resolutionTotal.π M i (((stage M p).ι).toFun x)))
    rw [hιd, hπd, ← hw, ← hsd, resolutionRetraction_resolutionSubHom,
      resolutionRetraction_resolutionSubHom]

/-- The retraction out of the `(2i+1)`-st stage, applied to a point. -/
theorem stageRetract_toFun (p i : ℕ) (hp : p = 2 * i + 1) (x : (stage M p).obj.M) :
    (stageRetract M p i hp).toFun x
      = (resolutionRetraction M i).toFun
        (resolutionTotal.π M i (((stage M p).ι).toFun x)) := rfl

/-- **The `(2i+1)`-st graded piece**: the retraction onto `I'ᵢ[-i]`, transported back to a
product of shifts of `A^∨`. -/
def pieceMapOdd (p i : ℕ) (hp : p = 2 * i + 1) :
    (stage M p).obj ⟶ @productDualShifts _ _ A _ (resolutionStep M i).decEq
      (fun c => (resolutionStep M i).k c + -(0 + (i : ℤ))) :=
  stageRetract M p i hp ≫ (oddShiftIso M i).inv

/-- The `(2i+1)`-st graded piece map, applied to a point. -/
theorem pieceMapOdd_toFun (p i : ℕ) (hp : p = 2 * i + 1) (x : (stage M p).obj.M) :
    (pieceMapOdd M p i hp).toFun x
      = (oddShiftIso M i).inv.toFun ((resolutionRetraction M i).toFun
        (resolutionTotal.π M i (((stage M p).ι).toFun x))) := rfl

/-- **The `(2i+1)`-st graded piece map is surjective**: every point of `I'ᵢ` is the retraction
of the `i`-th component of a point of the `(2i+1)`-st stage, namely of its own image under
`I'ᵢ ⟶ Iᵢ` placed in the `i`-th factor. -/
theorem pieceMapOdd_surjective (p i : ℕ) (hp : p = 2 * i + 1) :
    Function.Surjective (pieceMapOdd M p i hp).toFun := by
  intro v
  refine ⟨⟨single M i ((resolutionSubHom M i).toFun ((oddShiftIso M i).hom.toFun v)),
    by rw [stage_carrier, hp]; exact single_mem_carrier_odd M i _⟩, ?_⟩
  rw [pieceMapOdd_toFun]
  rw [show ((stage M p).ι).toFun
      ⟨single M i ((resolutionSubHom M i).toFun ((oddShiftIso M i).hom.toFun v)), _⟩
    = single M i ((resolutionSubHom M i).toFun ((oddShiftIso M i).hom.toFun v)) from rfl,
    π_single_self, resolutionRetraction_resolutionSubHom]
  exact iso_inv_hom_apply _ v

/-- A point of the `(2i+1)`-st stage dies in the `(2i+1)`-st graded piece exactly when its
`i`-th component vanishes. -/
theorem pieceMapOdd_eq_zero_iff (p i : ℕ) (hp : p = 2 * i + 1) (x : (stage M p).obj.M) :
    (pieceMapOdd M p i hp).toFun x = 0 ↔
      resolutionTotal.π M i (((stage M p).ι).toFun x) = 0 := by
  obtain ⟨w, hw⟩ : ∃ w, (resolutionSubHom M i).toFun w
      = resolutionTotal.π M i (((stage M p).ι).toFun x) := ((stage M p).ι_mem x).2 i (by omega)
  rw [pieceMapOdd_toFun]
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero, map_zero]⟩
  have hr : (resolutionRetraction M i).toFun
      (resolutionTotal.π M i (((stage M p).ι).toFun x)) = 0 :=
    iso_inv_injective (oddShiftIso M i) (by rw [h, map_zero])
  rw [← hw, resolutionRetraction_resolutionSubHom] at hr
  rw [← hw, hr, map_zero]

/-- **The kernel of the `(2i+1)`-st graded piece map is the `(2i+2)`-nd stage**: deleting the
`i`-th component is exactly what the next stage asks for. -/
theorem pieceMapOdd_ker (p i : ℕ) (hp : p = 2 * i + 1) :
    LinearMap.ker (pieceMapOdd M p i hp).toFun = LinearMap.range (incl M p).toFun := by
  refine Submodule.ext fun x => ?_
  rw [LinearMap.mem_ker, mem_range_incl, pieceMapOdd_eq_zero_iff]
  refine ⟨fun h => ⟨fun j hj => ?_, fun j hj => by omega⟩, fun h => h.1 i (by omega)⟩
  by_cases hji : j = i
  · rw [hji]; exact h
  · exact ((stage M p).ι_mem x).1 j (by omega)

/-! ### The graded piece of a stage, with the parity hidden -/

/-- **The graded piece of the `p`-th stage of the filtration, bundled.** The index type of the
product of shifts of `A^∨` is the same for `p = 2i` and `p = 2i + 1` — both graded pieces are
products over the index set `ιᵢ` of Stacks 09KT(3) — but the *shifts* are not, and neither are
the maps. Bundling them means that the three fields of
`DifferentialGradedModule.PropertyIFiltration` whose types depend on the shifts can be read off
uniformly in `p`, with no transport along an equality of index functions. -/
structure Piece (p : ℕ) where
  /-- The shifts of the factors of the `p`-th graded piece. -/
  shifts : (resolutionStep M (p / 2)).ι → ℤ
  /-- The projection of the `p`-th stage onto its graded piece. -/
  map : (stage M p).obj ⟶ @productDualShifts _ _ A _ (resolutionStep M (p / 2)).decEq shifts
  /-- The projection onto the graded piece is surjective. -/
  surjective : Function.Surjective map.toFun
  /-- Its kernel is the next stage. -/
  ker : LinearMap.ker map.toFun = LinearMap.range (incl M p).toFun

/-- The graded piece of an even stage: `F_{2i} / F_{2i+1} = I''ᵢ[-i]`. -/
def pieceEven (p : ℕ) (h : p % 2 = 0) : Piece M p where
  shifts c := ((resolutionStep M (p / 2)).k c + 1) + -(0 + ((p / 2 : ℕ) : ℤ))
  map := pieceMapEven M p (p / 2) (by omega)
  surjective := pieceMapEven_surjective M p (p / 2) (by omega)
  ker := pieceMapEven_ker M p (p / 2) (by omega)

/-- The graded piece of an odd stage: `F_{2i+1} / F_{2i+2} = I'ᵢ[-i]`. -/
def pieceOdd (p : ℕ) (h : p % 2 = 1) : Piece M p where
  shifts c := (resolutionStep M (p / 2)).k c + -(0 + ((p / 2 : ℕ) : ℤ))
  map := pieceMapOdd M p (p / 2) (by omega)
  surjective := pieceMapOdd_surjective M p (p / 2) (by omega)
  ker := pieceMapOdd_ker M p (p / 2) (by omega)

/-- **The graded piece of the `p`-th stage.** -/
def piece (p : ℕ) : Piece M p :=
  if h : p % 2 = 0 then pieceEven M p h else pieceOdd M p (by omega)

/-! ### Separatedness and completeness -/

/-- **The filtration is decreasing**, in the form needed for the telescoping argument below. -/
theorem carrier_antitone {p q : ℕ} (h : p ≤ q) : carrier M q ≤ carrier M p :=
  antitone_nat_of_succ_le (fun p => stage_carrier_le M p) h

/-- **Telescoping**: if each consecutive difference of a sequence lies in the corresponding
stage, then `x q - x p` lies in the `p`-th stage for every `q ≥ p`. -/
theorem sub_mem_carrier_of_le {x : ℕ → (resolutionTotal M).M}
    (hstep : ∀ p, x (p + 1) - x p ∈ carrier M p) (p q : ℕ) (hpq : p ≤ q) :
    x q - x p ∈ carrier M p := by
  induction q, hpq using Nat.le_induction with
  | base => rw [sub_self]; exact Submodule.zero_mem _
  | succ q hq ih =>
      rw [show x (q + 1) - x p = (x (q + 1) - x q) + (x q - x p) from by abel]
      exact Submodule.add_mem _ (carrier_antitone M hq (hstep q)) ih

/-- **Property (I)(1), separatedness**: a point of `I` lying in every stage of the filtration is
zero, because its `j`-th component is killed by the stage `2j + 2`. -/
theorem stage_separated (x : (resolutionTotal M).M)
    (h : ∀ p, ∃ y, ((stage M p).ι).toFun y = x) : x = 0 := by
  refine resolutionTotal.eq_zero_of_π_eq_zero M fun j => ?_
  obtain ⟨y, hy⟩ := h (2 * j + 2)
  have hmem : x ∈ carrier M (2 * j + 2) := hy ▸ (stage M (2 * j + 2)).ι_mem y
  exact hmem.1 j (by omega)

/-- **Property (I)(1), completeness**: a compatible family in `lim I / Fᵖ I` of degree `n` comes
from a point of `Iⁿ`. Its `j`-th component is read off the term at index `2j + 2`, beyond which
the `j`-th component of the family no longer moves; the error `z - xᵖ` lies in `Fᵖ I` because
below `⌈p/2⌉` the components already agree and at `p = 2j + 1` the error is the single step
`x^{p+1} - xᵖ`, which lies in `Fᵖ I` by hypothesis. -/
theorem stage_complete (n : ℤ) (x : ℕ → (resolutionTotal M).M)
    (hx : ∀ p, x p ∈ (resolutionTotal M).grading n)
    (hstep : ∀ p, ∃ y, y ∈ (stage M p).obj.grading n ∧
      x (p + 1) - x p = ((stage M p).ι).toFun y) :
    ∃ z, z ∈ (resolutionTotal M).grading n ∧ ∀ p, ∃ y, y ∈ (stage M p).obj.grading n ∧
      z - x p = ((stage M p).ι).toFun y := by
  have hstep' : ∀ p, x (p + 1) - x p ∈ carrier M p := by
    intro p
    obtain ⟨y, -, hy⟩ := hstep p
    exact hy ▸ (stage M p).ι_mem y
  obtain ⟨z, hz, hzπ⟩ := resolutionTotal.exists_mem_grading M n
    (fun j => resolutionTotal.π M j (x (2 * j + 2)))
    fun j => (resolutionTotal.mem_grading_iff M (x (2 * j + 2))).1 (hx (2 * j + 2)) j
  refine ⟨z, hz, fun p => ?_⟩
  have hagree : ∀ j, 2 * j + 2 ≤ p → resolutionTotal.π M j (z - x p) = 0 := by
    intro j hj
    have h0 : resolutionTotal.π M j (x p - x (2 * j + 2)) = 0 :=
      (sub_mem_carrier_of_le M hstep' (2 * j + 2) p hj).1 j (by omega)
    rw [map_sub] at h0
    rw [map_sub, hzπ j, sub_eq_zero.mp h0, sub_self]
  have hodd : ∀ j, 2 * j + 1 = p →
      resolutionTotal.π M j (z - x p) ∈ LinearMap.range (resolutionSubHom M j).toFun := by
    intro j hj
    rw [show resolutionTotal.π M j (z - x p) = resolutionTotal.π M j (x (p + 1) - x p) from by
      rw [map_sub, map_sub, hzπ j, show 2 * j + 2 = p + 1 from by omega]]
    exact (hstep' p).2 j hj
  refine ⟨⟨z - x p, ⟨hagree, hodd⟩⟩, ?_, rfl⟩
  exact (GradedSub.mem_obj_grading (stage M p)).2 (Submodule.sub_mem _ hz (hx p))

end ResolutionFiltration

open ResolutionFiltration in
/-- **Stacks 09KU, the filtration half: the module `I` of Stacks 09KU has property (I).** The
stages are the differential graded submodules

`F_{2i} I = ∏_{j ≥ i} Iⱼ[-j]` and `F_{2i+1} I = I'ᵢ[-i] × ∏_{j ≥ i+1} Iⱼ[-j]`

of `I = ∏_j Iⱼ[-j]`, where `0 → I'ᵢ → Iᵢ → I''ᵢ → 0` is the admissible short exact sequence of
Stacks 09KT(3) at the `i`-th stage of the resolution tower. The graded pieces are `I''ᵢ[-i]` and
`I'ᵢ[-i]`, which are products of shifts of `A^∨` by
`DifferentialGradedModule.productDualShiftsShiftIso`.

This is one of the two halves of Stacks 09KU; the other is that the augmentation
`DifferentialGradedModule.resolutionAug` is a quasi-isomorphism, which is not proved here, so
the tag of Stacks 09KU is not placed. -/
def resolutionPropertyIFiltration : PropertyIFiltration (resolutionTotal M) where
  F p := (stage M p).obj
  ι p := (stage M p).ι
  injective p := (stage M p).ι_injective
  incl p := incl M p
  incl_comp p x := incl_ι M p x
  admissible p := stage_admissible M p
  top_surjective x := ⟨⟨x, ⟨fun j hj => by omega, fun j hj => by omega⟩⟩, rfl⟩
  separated x h := stage_separated M x h
  complete n x hx hstep := stage_complete M n x hx hstep
  quotientIndex p := (resolutionStep M (p / 2)).ι
  quotientDecidableEq p := (resolutionStep M (p / 2)).decEq
  quotientShift p := (piece M p).shifts
  quotientMap p := (piece M p).map
  quotient_surjective p := (piece M p).surjective
  quotient_ker p := (piece M p).ker

end DifferentialGradedModule

end
