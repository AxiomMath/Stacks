module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChangeTwist
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseTwist
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartExtension
public import StacksFrontier.AlgebraicGeometry.ModuleChartLocality.BaseChange

/-!
# The coefficient extension on the twists of a degreewise base change

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings which is a base change
**degreewise** along `𝒜₀ ⟶ ℬ₀`: every homogeneous piece of `ℬ` is `ℬ₀ ⊗_{𝒜₀} 𝒜ₙ`. For a
homogeneous `a` of positive degree, Tag 01MY's comparison on the `n`-th twist restricts over the
chart `D₊(ψ a)` to the coefficient extension

`ℬ₍ψ a₎ ⊗_{𝒜₍a₎} 𝒜(n)₍a₎ ⟶ ℬ(n)₍ψ a₎`

of `Stacks.AlgebraicGeometry.TwistChartLocality.twistDegreeZeroMap`. This file proves that that
extension is an isomorphism, for every `n : ℤ` and with no freeness and no degree-one hypothesis.

## The route: the twist is the regular module, shifted

`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf 𝒜 n` is by definition the sheaf of the
graded module `𝒜(n)`, the ring itself with its grading shifted by `n`, and the twist comparison
`twistDegreeZeroMap` is by the same token the module comparison
`Stacks.AlgebraicGeometry.ModuleChartLocality.moduleDegreeZeroMap` of that graded module along
the semilinear map `ψ` of regular modules. So nothing has to be proved about twists at all: the
statement is `Stacks.AlgebraicGeometry.ModuleChartLocality.isIso_moduleDegreeZeroExtension`, the
degreewise-base-change invertibility for an arbitrary graded module, read at the shift.

Two things stand between the two readings and are what this file supplies. The first is that the
comparison maps agree: `moduleDegreeZeroMap` is built from Mathlib's `LocalizedModule.liftOn`
and `twistDegreeZeroMap` from the identification of a localized module with a localized ring, so
the two are equal by induction on fractions and not by `rfl`. The second is the reindexing:
`isIso_moduleDegreeZeroExtension` asks for the degreewise base change in the module's degrees,
which run over `ℤ`, while what is available is the degreewise base change of `𝒜` itself, in
degrees running over `ℕ`. The degree-`i` piece of `𝒜(n)` is the piece `𝒜 k` with `i + n = k`
when `i + n ≥ 0` and is zero otherwise, so the hypothesis splits into those two cases.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistChartLocality.twistPieceEquiv` and `twistTargetPieceEquiv`: the
  degree-`i` piece of a twist, identified with a homogeneous piece in the source and in the
  target.

## Main results

* `Stacks.AlgebraicGeometry.TwistChartLocality.moduleDegreeZeroExtension_toSemilinearMap`: **the
  twist comparison is the module comparison of the shifted regular module**, with
  `moduleAwayMap_toSemilinearMap`, `moduleDegreeZeroMap_toSemilinearMap` the two steps
  towards it.
* `Stacks.AlgebraicGeometry.TwistChartLocality.isBaseChange_modulePieceMap_twist`: **the pieces of
  the twist base-change degreewise**, in every integer degree, from the base change of the pieces
  of the ring in every natural degree.
* `Stacks.AlgebraicGeometry.TwistChartLocality.isIso_twistDegreeZeroExtension_of_isBaseChange`:
  **the coefficient extension of the chart comparison on the `n`-th twist is an isomorphism** for
  a degreewise base change.

## Implementation notes

The twist grading used by `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf` is valued in
`Submodule ℤ`, while `isIso_moduleDegreeZeroExtension` consumes a grading valued in
`AddSubgroup`; `Stacks.Veronese.twistGradingAddSubgroup` is the same grading in the second
spelling, and the two give literally the same degree-zero localization, so no transport is
needed and all the statements below are phrased at the `AddSubgroup` spelling.

`Stacks.AlgebraicGeometry.ProjBaseChange.isIso_twistDegreeZeroExtension` proves the same
conclusion for the base change `𝒜 ⟶ S ⊗_R 𝒜` along a ring map, by cancelling base changes on a
chart; neither statement is an instance of the other, because its hypothesis is that `ℬ` is a
literal tensor product and the hypothesis here is the degreewise one.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization TensorProduct
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ModuleChartLocality
open Stacks.Veronese (twistGradingAddSubgroup)

universe u

namespace Stacks.AlgebraicGeometry.TwistChartLocality

/-! ### The pieces of a twist, reindexed -/

section Reindex

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

omit [GradedRing 𝒮] in
/-- The degree-`i` piece of the twist `𝒮(n)` is the homogeneous piece `𝒮 k`, for `i + n = k`. -/
public theorem mem_twistGradingAddSubgroup_iff {n i : ℤ} {k : ℕ} (h : i + n = (k : ℤ)) {x : S} :
    x ∈ twistGradingAddSubgroup 𝒮 n i ↔ x ∈ 𝒮 k := by
  have h1 : x ∈ twistGradingAddSubgroup 𝒮 n i ↔ x ∈ twistGrading (S := S) 𝒮 n i := Iff.rfl
  rw [h1, twistGrading_apply, h, integerGrading_natCast, mem_homogeneousSubmodule]

omit [GradedRing 𝒮] in
/-- In a degree `i` with `i + n < 0` the twist `𝒮(n)` vanishes. -/
public theorem eq_zero_of_mem_twistGradingAddSubgroup {n i : ℤ} (h : i + n < 0) {x : S}
    (hx : x ∈ twistGradingAddSubgroup 𝒮 n i) : x = 0 := by
  have h1 : x ∈ twistGrading (S := S) 𝒮 n i := hx
  rw [twistGrading_apply, integerGrading_neg (S := S) 𝒮 _ h] at h1
  simpa using h1

omit [GradedRing 𝒮] in
/-- A piece of `𝒮(n)` in a degree below `-n` has one element. -/
public theorem subsingleton_twistGradingAddSubgroup {n i : ℤ} (h : i + n < 0) :
    Subsingleton ↥(twistGradingAddSubgroup 𝒮 n i) :=
  ⟨fun x y => Subtype.ext ((eq_zero_of_mem_twistGradingAddSubgroup 𝒮 h x.2).trans
    (eq_zero_of_mem_twistGradingAddSubgroup 𝒮 h y.2).symm)⟩

end Reindex

/-- The degree-`i` piece of the twist `𝒮(n)`, as a module over the degree-zero part of `𝒮`, is
the homogeneous piece `𝒮 k` for `i + n = k`. -/
public def twistPieceEquiv {S : Type u} [CommRing S] (𝒮 : ℕ → AddSubgroup S) [GradedRing 𝒮]
    {n i : ℤ} {k : ℕ} (h : i + n = (k : ℤ)) :
    ↥(gradePieceSubmodule 𝒮 k) ≃ₗ[(𝒮 0)] ↥(twistGradingAddSubgroup 𝒮 n i) where
  toFun x := ⟨x.1, (mem_twistGradingAddSubgroup_iff 𝒮 h).mpr x.2⟩
  invFun x := ⟨x.1, (mem_twistGradingAddSubgroup_iff 𝒮 h).mp x.2⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

variable {A B : Type u} [CommRing A] [CommRing B]
  {𝒜 : ℕ → AddSubgroup A} {ℬ : ℕ → AddSubgroup B} [GradedRing 𝒜] [GradedRing ℬ]
  (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ)

/-! ### The twist comparison is the module comparison of the shifted regular module -/

omit [GradedRing 𝒜] [GradedRing ℬ] in
/-- A graded homomorphism carries the degree-`i` piece of `𝒜(n)` into that of `ℬ(n)`, read in
the `AddSubgroup` spelling of the twist grading. -/
public theorem map_mem_twistGradingAddSubgroup (i : ℤ) {m : A}
    (hm : m ∈ twistGradingAddSubgroup 𝒜 n i) :
    ψ.toRingHom.toSemilinearMap m ∈ twistGradingAddSubgroup ℬ n i :=
  Stacks.AlgebraicGeometry.ProjTwistCompare.map_mem_twistGrading 𝒜 ℬ ψ n i hm

omit [GradedRing 𝒜] [GradedRing ℬ] in
/-- **The map on localized modules induced by `ψ` on the regular module is the one the twist
comparison is built from.** Both carry `m / aᵏ` to `ψ m / (ψ a)ᵏ`, and `LocalizedModule` is
generated by its fractions. -/
public theorem moduleAwayMap_toSemilinearMap (f : A) :
    moduleAwayMap ψ ψ.toRingHom.toSemilinearMap f = awayModuleMap 𝒜 ℬ ψ f := by
  refine AddMonoidHom.ext fun z => ?_
  induction z using LocalizedModule.induction_on with
  | h m s =>
    rw [moduleAwayMap_mk, awayModuleMap_mk 𝒜 ℬ ψ f m s (by
      obtain ⟨k, hk⟩ := s.2; exact ⟨k, by rw [← hk, map_pow]⟩)]
    rfl

/-- **The algebraic chart comparison on the `n`-th twist is the module chart comparison of the
shifted regular module.** -/
public theorem moduleDegreeZeroMap_toSemilinearMap (f : A) :
    moduleDegreeZeroMap ψ ψ.toRingHom.toSemilinearMap
        (map_mem_twistGradingAddSubgroup ψ n) f =
      twistDegreeZeroMap 𝒜 ℬ ψ f n :=
  AddMonoidHom.ext fun z =>
    Subtype.ext (congrArg (fun F => F z.1) (moduleAwayMap_toSemilinearMap ψ f))

/-- **The coefficient extension on the `n`-th twist is the module coefficient extension of the
shifted regular module.** -/
public theorem moduleDegreeZeroExtension_toSemilinearMap (f : A) :
    moduleDegreeZeroExtension ψ ψ.toRingHom.toSemilinearMap
        (map_mem_twistGradingAddSubgroup ψ n) f =
      twistDegreeZeroChartExtension 𝒜 ℬ ψ (f := f) n :=
  congrArg (fun F => (ModuleCat.extendScalars (Away.map ψ f)).map F ≫
      (ModuleCat.extendRestrictScalarsAdj (Away.map ψ f)).counit.app
        (ModuleCat.of (Away ℬ (ψ f))
          (GradedModuleDegreeZeroLocalization ℬ (twistGrading (S := B) ℬ n) (ψ f))))
    (ModuleCat.hom_ext (LinearMap.ext fun z =>
      congrArg (fun F => F z) (moduleDegreeZeroMap_toSemilinearMap ψ n f)))

/-! ### The degreewise base change -/

section Degreewise

variable [Algebra (𝒜 0) (ℬ 0)]
  (halg : ∀ r : (𝒜 0), (algebraMap (𝒜 0) (ℬ 0) r : B) = ψ (r : A))

/-- The degree-`i` piece of the twist `ℬ(n)`, as a module over the degree-zero part of `ℬ`, is
the homogeneous piece `ℬ k` for `i + n = k`. This is the target-side companion of
`Stacks.AlgebraicGeometry.TwistChartLocality.twistPieceEquiv`, in the type synonym
`Stacks.AlgebraicGeometry.ModuleChartLocality.TargetPiece` that carries the graded ring `ℬ`. -/
public def twistTargetPieceEquiv {n i : ℤ} {k : ℕ} (h : i + n = (k : ℤ)) :
    ↥(gradePieceSubmodule ℬ k) ≃ₗ[(ℬ 0)]
      TargetPiece ℬ (twistGradingAddSubgroup ℬ n) i where
  toFun x := TargetPiece.ofPiece ⟨x.1, (mem_twistGradingAddSubgroup_iff ℬ h).mpr x.2⟩
  invFun x := ⟨(TargetPiece.toPiece x).1, (mem_twistGradingAddSubgroup_iff ℬ h).mp
    (TargetPiece.toPiece x).2⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- **The pieces of the twist base-change degreewise.** In a degree `i` with `i + n ≥ 0` this is
the base change of the piece `𝒜 (i + n)` of the ring, transported along the two identifications
of that piece with the degree-`i` piece of the twist; in a degree with `i + n < 0` both pieces
have one element, and a map between trivial modules is a base change for the cheapest
reason. -/
public theorem isBaseChange_modulePieceMap_twist
    (hfA : ∀ k : ℕ, IsBaseChange (ℬ 0) (Stacks.Proj.pieceMap ψ halg k)) (i : ℤ) :
    IsBaseChange (ℬ 0) (modulePieceMap ψ ψ.toRingHom.toSemilinearMap
      (map_mem_twistGradingAddSubgroup ψ n) halg i) := by
  by_cases hi : 0 ≤ i + n
  · have hk : i + n = (((i + n).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hi).symm
    refine (IsBaseChange.iff_of_equiv_comm (twistPieceEquiv 𝒜 hk)
      (twistTargetPieceEquiv hk) ?_).mp (hfA (i + n).toNat)
    exact LinearMap.ext fun x => Subtype.ext rfl
  · rw [not_le] at hi
    have hsub : Subsingleton ↥(twistGradingAddSubgroup 𝒜 n i) :=
      subsingleton_twistGradingAddSubgroup 𝒜 hi
    have hsub' : Subsingleton (TargetPiece ℬ (twistGradingAddSubgroup ℬ n) i) :=
      subsingleton_twistGradingAddSubgroup ℬ hi
    refine IsBaseChange.of_lift_unique _ fun Q _ _ _ _ g => ?_
    refine ⟨0, LinearMap.ext fun x => ?_, fun y _ => LinearMap.ext fun x => ?_⟩
    · rw [Subsingleton.elim x 0]
      simp
    · rw [Subsingleton.elim x 0, map_zero, map_zero]

/-- **The coefficient extension of the chart comparison on the `n`-th twist is an isomorphism**,
for a graded homomorphism which is a base change degreewise and at a homogeneous element of any
positive degree.

This is the twist analogue of
`Stacks.AlgebraicGeometry.ModuleChartLocality.isIso_moduleDegreeZeroExtension`, and it is that
theorem: the `n`-th twist is the regular module with its grading shifted by `n`, by
`Stacks.AlgebraicGeometry.TwistChartLocality.moduleDegreeZeroExtension_toSemilinearMap`, and its
pieces base-change degreewise by
`Stacks.AlgebraicGeometry.TwistChartLocality.isBaseChange_modulePieceMap_twist`. -/
public theorem isIso_twistDegreeZeroExtension_of_isBaseChange {d : ℕ} {a : A} (ha : a ∈ 𝒜 d)
    (hfA : ∀ k : ℕ, IsBaseChange (ℬ 0) (Stacks.Proj.pieceMap ψ halg k)) :
    IsIso (twistDegreeZeroChartExtension 𝒜 ℬ ψ (f := a) n) := by
  rw [← moduleDegreeZeroExtension_toSemilinearMap ψ n a]
  exact isIso_moduleDegreeZeroExtension ψ ψ.toRingHom.toSemilinearMap
    (map_mem_twistGradingAddSubgroup ψ n) halg ha
    (isBaseChange_modulePieceMap_twist ψ n halg hfA) hfA

end Degreewise

end Stacks.AlgebraicGeometry.TwistChartLocality

end
