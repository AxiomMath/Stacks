module

public import StacksFrontier.AlgebraicGeometry.Constructions.Cone
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistRelativeSpecInclusion
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The diagram of Tag 0EKG

Let `A` be a graded ring, `X = Spec A`, `Z = V(A₊) = Spec A₀`, `U = X ∖ Z`, `P = Proj A` and
`L = Proj B` for the truncation algebra `B = ⨁_{d ≥ 0} A_{≥ d}`, with cone projection `π : L ⟶ P`,
structure morphism `σ : L ⟶ X` and zero section `0 : P ⟶ L`. [Stacks, Tag 0EKG] summarises the
section "Proj and Spec" by the commutative diagram

```
Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ L = Spec_P(⨁_{m ≥ 0} 𝒪_P(m)) ⟶ P
         ‖                         ↓ σ                     ↓
         U          ⟶              X           ⟶           Z
```

in which `π` is a cone whose zero section `0` maps set theoretically onto the inverse image of `Z`
in `L`. This file assembles that statement from the pieces proved in the `ProjConeTwist*` and
`ProjAndSpec*` files, and supplies the two parts that were still missing: `π` *is a cone* in the
sense of [Stacks, Tag 062R], with grading `⨁_{m ≥ 0} 𝒪_P(m)`, and `0` is its vertex.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjConeTwist.truncationCone`: **the cone `π : L ⟶ P`** as an
  `AlgebraicGeometry.AbstractCone` over `P`, graded by the algebra of nonnegative twists.
* `Stacks.AlgebraicGeometry.ProjConeTwist.openUToProj`: the map `U ⟶ P`.

## Main results

* `Stacks.AlgebraicGeometry.ProjAndSpec.range_zToX`: the image of `Z ⟶ X` is `X ∖ U`.
* `Stacks.AlgebraicGeometry.ProjAndSpecTruncation.awayMap_tau_eq_zero`: `τ` kills the positive
  part of `(B_{ψ f})₀`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.zeroSection_appLE_coneIota_eq_zero`: **`0` is the
  vertex of the cone**.
* `Stacks.AlgebraicGeometry.ProjConeTwist.range_zeroSection_eq_preimage_range_zToX`: **`0` maps
  onto the inverse image of `Z` in `L`**.
* `Stacks.AlgebraicGeometry.ProjConeTwist.projAndSpec_diagram`: **the whole diagram**.

## Implementation notes

Uniqueness of the homogeneous decomposition of `π_* 𝒪_L` over an arbitrary open is reduced to the
standard opens `D₊(f)`, where the comparison out of the direct sum is bijective, by the sheaf
property of each piece; local existence is surjectivity on the standard opens. The degree-zero
piece is identified with `𝒪_P` by
`Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit`.

The vertex statement is checked on the charts `D₊(f)`: there the zero section is Mathlib's
`AlgebraicGeometry.Proj.map` for `τ`, which on functions is the map of degree-zero localizations
induced by `τ`, and a fraction `a⁽ᵏᵈ⁾ / (ψ f)ᵏ` of degree `m > 0` goes to `a_{kd} / fᵏ = 0`.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 062R](https://stacks.math.columbia.edu/tag/062R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory
open CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation
open Stacks.AlgebraicGeometry.ProjTwistComparison Stacks.AffineAlgebraEquivalence

namespace Stacks.AlgebraicGeometry.ProjAndSpec

universe u

section Base

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- A point of `X = Spec A` lies in `U = X ∖ V(A₊)` exactly when some homogeneous element of
positive degree is not in it. -/
theorem mem_openU_iff (x : Spec (CommRingCat.of A)) :
    x ∈ openU 𝒜 ↔ ∃ d, 0 < d ∧ ∃ f : 𝒜 d, (f : A) ∉ x.asIdeal := by
  constructor
  · intro hx
    obtain ⟨d, hx⟩ := Opens.mem_iSup.mp hx
    obtain ⟨hd, hx⟩ := Opens.mem_iSup.mp hx
    obtain ⟨f, hx⟩ := Opens.mem_iSup.mp hx
    exact ⟨d, hd, f, hx⟩
  · rintro ⟨d, hd, f, hf⟩
    exact Opens.mem_iSup.mpr ⟨d, Opens.mem_iSup.mpr ⟨hd, Opens.mem_iSup.mpr ⟨f, hf⟩⟩⟩

/-- **`Z = V(A₊)`**: the image of the closed immersion `Z = Spec A₀ ⟶ X = Spec A` is the
complement of `U = X ∖ V(A₊)`. -/
theorem range_zToX : Set.range (zToX 𝒜) = ((openU 𝒜 : Set (Spec (CommRingCat.of A))))ᶜ := by
  classical
  have hrange : Set.range (zToX 𝒜) =
      Set.range (PrimeSpectrum.comap (GradedRing.projZeroRingHom' 𝒜)) := rfl
  rw [hrange, range_comap_of_surjective _ _ (GradedRing.projZeroRingHom'_surjective 𝒜)]
  refine Set.ext fun x => ?_
  refine (PrimeSpectrum.mem_zeroLocus _ _).trans (Iff.trans ?_ (mem_openU_iff 𝒜 x).not.symm)
  simp only [not_exists, not_and, not_not]
  refine ⟨fun hx d hd f => hx (Subtype.ext ?_), fun hx a ha => ?_⟩
  · change (GradedRing.projZeroRingHom 𝒜 (f : A)) = 0
    rw [GradedRing.projZeroRingHom_apply, DirectSum.decompose_of_mem_ne 𝒜 f.2 hd.ne']
  · have ha0 : (DirectSum.decompose 𝒜 a 0 : A) = 0 :=
      congrArg Subtype.val (show GradedRing.projZeroRingHom' 𝒜 a = 0 from ha)
    rw [← DirectSum.sum_support_decompose 𝒜 a]
    refine Ideal.sum_mem _ fun i _ => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact ha0 ▸ Ideal.zero_mem _
    · exact hx i hi (DirectSum.decompose 𝒜 a i)

end Base

end Stacks.AlgebraicGeometry.ProjAndSpec

namespace Stacks.AlgebraicGeometry.ProjAndSpecTruncation

universe u

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **`τ` kills the positive-degree part of `(B_{ψ f})₀`**: the map
`(B_{ψ f})₀ ⟶ A_{(f)}` of degree-zero localizations induced by `τ : B ⟶ A` vanishes on the degree
`m` part `(A_f)_m` of `(B_{ψ f})₀ = ⨁_{m ≥ 0} (A_f)_m` for every `m > 0`. On a fraction
`a⁽ᵏᵈ⁾ / (ψ f)ᵏ` it is `a_{kd} / fᵏ`, and if `a / fᵏ` is homogeneous of degree `m > 0` then the
degree `kd` component of `a` is killed by a power of `f`. -/
theorem awayMap_tau_eq_zero {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) {m : ℕ} (hm : 0 < m)
    {y : HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f)} (hy : y ∈ awayGrading 𝒜 d hf m) :
    HomogeneousLocalization.Away.map (tau 𝒜) (psi 𝒜 f) y = 0 := by
  classical
  obtain ⟨k, a, ha, rfl⟩ := awayElt_surjective 𝒜 d hf y
  rw [mem_awayGrading_iff, awayToLocalization_awayElt] at hy
  obtain ⟨l, b, hb, hab⟩ := hy
  have hsum : awayFrac f k a + awayFrac f l (-b) = 0 := by
    rw [hab, ← awayFrac_neg, add_neg_cancel]
  rw [awayFrac_add, awayFrac_eq_zero_iff] at hsum
  obtain ⟨n, hn⟩ := hsum
  -- the degree `(n + l + k) d` component of `f ^ n * (f ^ k * (-b) + f ^ l * a) = 0`
  have hfn : ∀ j : ℕ, f ^ j ∈ 𝒜 (j * d) := fun j => by
    simpa [smul_eq_mul] using SetLike.pow_mem_graded j hf
  have hcomp := congrArg (fun z => (DirectSum.decompose 𝒜 z ((n + l) * d + k * d) : A)) hn
  simp only [mul_add, ← mul_assoc, ← pow_add, DirectSum.decompose_add, DirectSum.add_apply,
    AddMemClass.coe_add, DirectSum.decompose_zero, DirectSum.zero_apply,
    ZeroMemClass.coe_zero] at hcomp
  rw [DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 (hfn (n + l))] at hcomp
  have hb0 : (DirectSum.decompose 𝒜 (f ^ (n + k) * -b) ((n + l) * d + k * d) : A) = 0 := by
    rw [show (n + l) * d + k * d = (n + k) * d + l * d by ring,
      DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 (hfn (n + k)),
      DirectSum.decompose_of_mem_ne 𝒜 (neg_mem hb) (by omega), mul_zero]
  rw [hb0, zero_add] at hcomp
  -- now `f ^ (n + l) * a_{kd} = 0`, so `a_{kd} / f ^ k = 0`
  refine HomogeneousLocalization.val_injective _ ?_
  rw [awayElt, HomogeneousLocalization.Away.map, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.val_zero,
    Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨tau 𝒜 (psi 𝒜 f) ^ (n + l), n + l, rfl⟩, ?_⟩
  change tau 𝒜 (psi 𝒜 f) ^ (n + l) * tau 𝒜 (degElt 𝒜 (k * d) a ha) = 0
  rwa [tau_psi_apply, tau_degElt]

end Stacks.AlgebraicGeometry.ProjAndSpecTruncation

namespace Stacks.AlgebraicGeometry.ProjConeTwist

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- On sections over an open `U`, the map `pushforwardHomogeneousSum` along `coneIota 𝒜`, applied
to the direct sum of the pieces of `nonnegTwistAlgebra 𝒜`, equals the component of
`coneTwistDirectSumHom 𝒜` at `U`. -/
theorem pushforwardHomogeneousSum_coneIota (U : Opens (ProjectiveSpectrum.top 𝒜))
    (z : Π₀ n : ℤ, ((nonnegTwistAlgebra 𝒜).piece n).val.obj (op U)) :
    pushforwardHomogeneousSum (pi 𝒜) (nonnegTwistAlgebra 𝒜) (coneIota 𝒜) U z =
      (coneTwistDirectSumHom 𝒜).app (op U) z := by
  refine DFunLike.congr_fun (DFinsupp.addHom_ext
    (f := pushforwardHomogeneousSum (pi 𝒜) (nonnegTwistAlgebra 𝒜) (coneIota 𝒜) U)
    (g := Stacks.homToAddMonoidHom (fun m : ℤ => (nonnegTwistingSheaf 𝒜 m).val)
      (coneTwistDirectSumHom 𝒜) (op U)) fun m x => ?_) z
  simp only [pushforwardHomogeneousSum, DFinsupp.sumAddHom_single]
  exact (coneTwistDirectSumHom_app_incl 𝒜 m U x).symm

/-- Restriction in the objectwise direct sum is restriction in each component. -/
theorem directSumRestrict_apply {ι : Type} [DecidableEq ι] {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} (P : ι → PresheafOfModules.{u} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (z : Stacks.DirectSumType P X) (n : ι) :
    (show DirectSum ι (fun i => ((P i).obj Y : Type u)) from Stacks.directSumRestrict P f z) n =
      Stacks.sectionRestrict (P n) f
        ((show DirectSum ι (fun i => ((P i).obj X : Type u)) from z) n) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of i y =>
    rw [Stacks.directSumRestrict_of]
    by_cases h : i = n
    · subst h
      simp only [DirectSum.of_eq_same]
    · dsimp only
      rw [DirectSum.of_eq_of_ne i n _ (Ne.symm h), DirectSum.of_eq_of_ne i n _ (Ne.symm h),
        map_zero]
  | add a b ha hb => simp only [map_add, DirectSum.add_apply, ha, hb]

/-- **The decomposition of `π_* 𝒪_L` into homogeneous pieces is unique over every open of `P`.**
Over a standard open of a positive-degree homogeneous element this is the bijectivity of the
comparison out of the direct sum; over an arbitrary open each component is a section of a sheaf,
determined by its restrictions to the standard opens it contains. -/
theorem injective_coneTwistDirectSumHom_app (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    Function.Injective ((coneTwistDirectSumHom 𝒜).app (op U)).hom := by
  intro z w h
  refine DFinsupp.ext fun n => ?_
  refine Stacks.BasisRestriction.moduleSheafSection_ext_onBasis (nonnegTwistingSheaf 𝒜 n)
    (positiveBasicOpen 𝒜) (isBasis_positiveBasicOpen 𝒜) _ _ fun p hle => ?_
  have hz := PresheafOfModules.naturality_apply (coneTwistDirectSumHom 𝒜) (homOfLE hle).op z
  have hw := PresheafOfModules.naturality_apply (coneTwistDirectSumHom 𝒜) (homOfLE hle).op w
  have hzw := (bijective_coneTwistDirectSumHom_app 𝒜 p).1 (hz.trans ((congrArg _ h).trans hw.symm))
  have hn := congrArg (fun v : Stacks.DirectSumType (fun m : ℤ => (nonnegTwistingSheaf 𝒜 m).val)
    (op (positiveBasicOpen 𝒜 p)) => v n) hzw
  exact (directSumRestrict_apply _ _ z n).symm.trans (hn.trans (directSumRestrict_apply _ _ w n))

/-- **Every function on the cone over an open of `P` is locally a finite sum of homogeneous
ones**: over a standard open of a positive-degree homogeneous element inside the open, the
comparison out of the direct sum is surjective. -/
theorem exists_coneTwistDirectSumHom_app_eq (U : Opens (ProjectiveSpectrum.top 𝒜))
    (a : (Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val.obj (op U)) (x : U) :
    ∃ (V : Opens (ProjectiveSpectrum.top 𝒜)) (hVU : V ≤ U), x.1 ∈ V ∧
      ∃ z : Stacks.DirectSumType (fun m : ℤ => (nonnegTwistingSheaf 𝒜 m).val) (op V),
        (coneTwistDirectSumHom 𝒜).app (op V) z =
          (Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val.map (homOfLE hVU).op a := by
  obtain ⟨V, ⟨p, rfl⟩, hxV, hVU⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_positiveBasicOpen 𝒜) x.2
  obtain ⟨z, hz⟩ := (bijective_coneTwistDirectSumHom_app 𝒜 p).2
    ((Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val.map (homOfLE hVU).op a)
  exact ⟨positiveBasicOpen 𝒜 p, hVU, hxV, z, hz⟩

/-- The degree-zero piece of the algebra of nonnegative twists is the structure sheaf of `P`:
it is the untwisted sheaf `𝒪_P(0)`, identified with `𝒪_P` by
`Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit`. -/
def nonnegTwistDegreeZeroIso :
    (nonnegTwistAlgebra 𝒜).piece 0 ≅
      SheafOfModules.unit (AlgebraicGeometry.Proj 𝒜).ringCatSheaf :=
  Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit 𝒜

/-- The degree-zero identification read through `HomogeneousLocalization.val`. -/
theorem val_nonnegTwistDegreeZeroIso_hom_apply (U : Opens (ProjectiveSpectrum.top 𝒜))
    (a : ((nonnegTwistAlgebra 𝒜).piece 0).val.obj (op U)) (x : U) :
    HomogeneousLocalization.val
        (((nonnegTwistDegreeZeroIso 𝒜).hom.val.app (op U) a).1 x) =
      (show (twistingSheaf 𝒜 0).val.obj (op U) from a).1 x :=
  Stacks.AlgebraicGeometry.ProjEulerSequence.val_twistingSheafZeroIsoUnit_hom_apply 𝒜 U a x

/-- The degree-zero identification is multiplicative. -/
theorem nonnegTwistDegreeZeroIso_mul (U : Opens (ProjectiveSpectrum.top 𝒜))
    (a b : ((nonnegTwistAlgebra 𝒜).piece 0).val.obj (op U)) :
    ((nonnegTwistDegreeZeroIso 𝒜).hom.val.app (op U)
        (((nonnegTwistAlgebra 𝒜).mul 0 0).app (op U) a b) :
        (AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U)) =
      (show (AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U) from
          (nonnegTwistDegreeZeroIso 𝒜).hom.val.app (op U) a) *
        (show (AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U) from
          (nonnegTwistDegreeZeroIso 𝒜).hom.val.app (op U) b) := by
  refine Subtype.ext (funext fun x => HomogeneousLocalization.val_injective _ ?_)
  refine (val_nonnegTwistDegreeZeroIso_hom_apply 𝒜 U _ x).trans ?_
  refine Eq.trans ?_ (HomogeneousLocalization.val_mul _ _).symm
  rw [val_nonnegTwistDegreeZeroIso_hom_apply, val_nonnegTwistDegreeZeroIso_hom_apply]
  rfl

/-- The degree-zero identification is unital. -/
theorem nonnegTwistDegreeZeroIso_one (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    (show (AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U) from
        (nonnegTwistDegreeZeroIso 𝒜).hom.val.app (op U)
          ((nonnegTwistAlgebra 𝒜).one.eval (op U))) =
      (1 : (AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U)) := by
  refine Subtype.ext (funext fun x => HomogeneousLocalization.val_injective _ ?_)
  refine (val_nonnegTwistDegreeZeroIso_hom_apply 𝒜 U _ x).trans ?_
  exact HomogeneousLocalization.val_one.symm.trans rfl

/-- A section of the degree-zero piece is its image in `𝒪_P` acting on the unit section. -/
theorem nonnegTwist_degreeZero_eq_smul_one (U : Opens (ProjectiveSpectrum.top 𝒜))
    (a : ((nonnegTwistAlgebra 𝒜).piece 0).val.obj (op U)) :
    a = (show (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj.obj (op U) from
        (nonnegTwistDegreeZeroIso 𝒜).hom.val.app (op U) a) •
      (show ((nonnegTwistAlgebra 𝒜).piece 0).val.obj (op U) from (twistOne 𝒜).eval (op U)) := by
  refine twistSection_ext 𝒜 fun x => ?_
  change a.1 x = HomogeneousLocalization.val
      (((nonnegTwistDegreeZeroIso 𝒜).hom.val.app (op U) a).1 x) • (1 : _)
  rw [val_nonnegTwistDegreeZeroIso_hom_apply, smul_eq_mul, mul_one]

/-- **The inclusion of the degree-zero piece in `π_* 𝒪_L` is the structure map `𝒪_P ⟶ π_* 𝒪_L`**,
read through the identification of the degree-zero piece with `𝒪_P`. -/
theorem coneIota_zero_apply (U : Opens (ProjectiveSpectrum.top 𝒜))
    (a : ((nonnegTwistAlgebra 𝒜).piece 0).val.obj (op U)) :
    (coneIota 𝒜 0).val.app (op U) a =
      (pi 𝒜).c.app (op U) ((nonnegTwistDegreeZeroIso 𝒜).hom.val.app (op U) a) := by
  have key := map_smul (ConcreteCategory.hom ((coneIota 𝒜 0).val.app (op U)))
    (show (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.obj.obj (op U) from
        (nonnegTwistDegreeZeroIso 𝒜).hom.val.app (op U) a)
    (show ((nonnegTwistAlgebra 𝒜).piece 0).val.obj (op U) from (twistOne 𝒜).eval (op U))
  have hone : (show coneSections 𝒜 U from
      (coneIota 𝒜 0).val.app (op U) ((twistOne 𝒜).eval (op U))) = 1 := coneIota_one 𝒜 U
  refine (congrArg (fun z => (coneIota 𝒜 0).val.app (op U) z)
    (nonnegTwist_degreeZero_eq_smul_one 𝒜 U a)).trans (key.trans ?_)
  change (pi 𝒜).app U _ * (show coneSections 𝒜 U from
      (coneIota 𝒜 0).val.app (op U) ((twistOne 𝒜).eval (op U))) = _
  rw [hone, mul_one]

/-- **`π : L ⟶ P` is a cone over `P`** in the sense of [Stacks, Tag 062R], graded by the algebra
`⨁_{m ≥ 0} 𝒪_P(m)` of nonnegative twists: `π` is affine, the homogeneous pieces include in
`π_* 𝒪_L` by the degreewise inclusions `𝒪_P(m) ⟶ π_* 𝒪_L`, every function on the cone is locally
a unique finite sum of homogeneous ones, the inclusions are multiplicative, the negative pieces
vanish and the degree-zero piece is `𝒪_P`, included by the structure map. -/
@[stacks 0EKG "π : L → P is a cone over P, whose direct-image algebra is graded by the twists \
O_P(m), m ≥ 0"]
def truncationCone : AbstractCone (AlgebraicGeometry.Proj 𝒜) where
  C := AlgebraicGeometry.Proj (grading 𝒜)
  π := pi 𝒜
  isAffine := isAffineHom_pi 𝒜
  grading := nonnegTwistAlgebra 𝒜
  ι := coneIota 𝒜
  decomposition_unique U z w h :=
    injective_coneTwistDirectSumHom_app 𝒜 U
      ((pushforwardHomogeneousSum_coneIota 𝒜 U z).symm.trans
        (h.trans (pushforwardHomogeneousSum_coneIota 𝒜 U w)))
  decomposition_locally U a x hx := by
    obtain ⟨V, hVU, hxV, z, hz⟩ := exists_coneTwistDirectSumHom_app_eq 𝒜 U a ⟨x, hx⟩
    exact ⟨V, hVU, hxV, z, (pushforwardHomogeneousSum_coneIota 𝒜 V z).trans hz⟩
  ι_mul i j U a b := coneIota_mul 𝒜 i j U a b
  negative_isZero _ hn := isZero_nonnegTwistingSheaf 𝒜 hn
  degreeZero := nonnegTwistDegreeZeroIso 𝒜
  degreeZero_mul U a b := nonnegTwistDegreeZeroIso_mul 𝒜 U a b
  degreeZero_one U := nonnegTwistDegreeZeroIso_one 𝒜 U
  ι_zero U a := coneIota_zero_apply 𝒜 U a

/-- **The zero section `0 : P ⟶ L` maps set theoretically onto the inverse image of `Z` in `L`**:
its image is the inverse image under `σ : L ⟶ X` of the image of `Z = Spec A₀ ⟶ X`. -/
@[stacks 0EKG "the zero section maps set theoretically onto the inverse image of Z in L"]
theorem range_zeroSection_eq_preimage_range_zToX :
    Set.range (zeroSection 𝒜) = toSpecA 𝒜 ⁻¹' Set.range (ProjAndSpec.zToX 𝒜) := by
  rw [range_zeroSection, ProjAndSpec.range_zToX]
  rfl

attribute [local instance] isAffineHom_pi isAffineHom_pi_restrict

/-- The map `U ⟶ P` of the punctured cone read on `U ⊆ X`: the inverse of the isomorphism
`L ⊇ π⁻¹… ⊇ (part of L over U) ≅ U` induced by `σ : L ⟶ X`, followed by `π`. -/
def openUToProj : (ProjAndSpec.openU 𝒜).toScheme ⟶ AlgebraicGeometry.Proj 𝒜 :=
  @inv _ _ _ _ (toSpecA 𝒜 ∣_ ProjAndSpec.openU 𝒜) (isIso_toSpecA_restrict 𝒜) ≫
    (openUInL 𝒜).ι ≫ pi 𝒜

/-- The top-left arrow of the diagram lies over `P`. -/
theorem puncturedToConeProj_comp_pi :
    puncturedToConeProj 𝒜 ≫ pi 𝒜 = relativeSpecToBase (integerTwistAlgebraSheaf 𝒜) := by
  have hc : (coneProjIsoRelativeSpecTwistAlgebra 𝒜).inv ≫ pi 𝒜 =
      relativeSpecToBase (nonnegTwistAlgebraSheaf 𝒜) := by
    rw [Iso.inv_comp_eq, coneProjIsoRelativeSpecTwistAlgebra_hom_comp]
  rw [puncturedToConeProj, Category.assoc, hc]
  exact Over.w (puncturedToConeRelativeSpecTwistAlgebra 𝒜)

/-- The left identification `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ≅ U` is one over `P`. -/
theorem puncturedConeRelativeSpecTwistAlgebraIsoOpenU_hom_comp_openUToProj :
    (puncturedConeRelativeSpecTwistAlgebraIsoOpenU 𝒜).hom ≫ openUToProj 𝒜 =
      relativeSpecToBase (integerTwistAlgebraSheaf 𝒜) := by
  have he : (puncturedConeRelativeSpecTwistAlgebraIsoOpenU 𝒜).hom ≫
      @inv _ _ _ _ (toSpecA 𝒜 ∣_ ProjAndSpec.openU 𝒜) (isIso_toSpecA_restrict 𝒜) =
      ((Over.forget (AlgebraicGeometry.Proj 𝒜)).mapIso
        (puncturedConeRelativeSpecTwistAlgebraIso 𝒜)).inv := by
    rw [puncturedConeRelativeSpecTwistAlgebraIsoOpenU, Iso.trans_hom, Iso.symm_hom,
      Category.assoc]
    exact (congrArg (fun φ => _ ≫ φ)
      (@IsIso.hom_inv_id _ _ _ _ _ (isIso_toSpecA_restrict 𝒜))).trans (Category.comp_id _)
  refine Eq.trans ?_ (puncturedToConeProj_comp_pi 𝒜)
  rw [openUToProj, ← Category.assoc, he]
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun φ => φ ≫ pi 𝒜)
    (puncturedToConeRelativeSpecTwistAlgebra_left_comp_inv 𝒜).symm)

/-- The zero section followed by the cone projection is the identity, so every open of `P` lies
in the inverse image of its inverse image. -/
theorem le_zeroSection_preimage_pi_preimage (U : (AlgebraicGeometry.Proj 𝒜).Opens) :
    U ≤ zeroSection 𝒜 ⁻¹ᵁ (pi 𝒜 ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, zeroSection_comp_pi]
  exact le_rfl

/-- **The zero section is the vertex of the cone, over a standard open**: pulled back along
`0 : P ⟶ L`, a function on `π⁻¹(D₊(f)) = D₊(ψ f)` coming from a section of `𝒪_P(m)` with `m > 0`
vanishes. On the chart this is `awayMap_tau_eq_zero`. -/
theorem zeroSection_appLE_coneTwistApp_eq_zero (m : ℕ) (hm : 0 < m) {f : A} {d : ℕ}
    (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (s : (twistingSheaf 𝒜 (m : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (zeroSection 𝒜).appLE (pi 𝒜 ⁻¹ᵁ Proj.basicOpen 𝒜 f) (Proj.basicOpen 𝒜 f)
        (le_zeroSection_preimage_pi_preimage 𝒜 _) ((coneTwistApp 𝒜 m d hf hd).hom s) = 0 := by
  have hopen : Proj.basicOpen 𝒜 (tau 𝒜 (psi 𝒜 f)) = Proj.basicOpen 𝒜 f := by
    rw [tau_psi_apply]
  have h0 : Proj.basicOpen 𝒜 (tau 𝒜 (psi 𝒜 f)) ≤
      zeroSection 𝒜 ⁻¹ᵁ Proj.basicOpen (grading 𝒜) (psi 𝒜 f) := by
    change _ ≤ ProjAndSpec.zeroSection (truncationConeData 𝒜) ⁻¹ᵁ _
    rw [ProjAndSpec.zeroSection_eq_projMap]
    exact le_rfl
  rw [coneTwistApp_apply]
  have h5 := Scheme.Hom.map_appLE' (zeroSection 𝒜)
    (show Proj.basicOpen 𝒜 f ≤ zeroSection 𝒜 ⁻¹ᵁ Proj.basicOpen (grading 𝒜) (psi 𝒜 f) from
      (pi_preimage_basicOpen 𝒜 f d hf hd) ▸ le_zeroSection_preimage_pi_preimage 𝒜 _)
    (pi_preimage_basicOpen 𝒜 f d hf hd)
  refine (ConcreteCategory.congr_hom h5 _).trans ?_
  have h6 := Scheme.Hom.appLE_map (zeroSection 𝒜)
    (U := Proj.basicOpen (grading 𝒜) (psi 𝒜 f)) (V := Proj.basicOpen 𝒜 (tau 𝒜 (psi 𝒜 f)))
    h0 (eqToHom hopen.symm).op
  refine (ConcreteCategory.congr_hom h6.symm _).trans ?_
  have hmap := Proj.awayToSection_comp_appLE (tau 𝒜) (ProjAndSpec.irrelevant_le_map_tau
    (truncationConeData 𝒜)) ((psi 𝒜).map_mem hf)
  have hcongr := ProjChartSections.appLE_congr_hom
    (ProjAndSpec.zeroSection_eq_projMap (truncationConeData 𝒜))
    (Proj.basicOpen (grading 𝒜) (psi 𝒜 f)) (Proj.basicOpen 𝒜 (tau 𝒜 (psi 𝒜 f)))
    h0 (le_of_eq rfl)
  have hval : (zeroSection 𝒜).appLE (Proj.basicOpen (grading 𝒜) (psi 𝒜 f))
      (Proj.basicOpen 𝒜 (tau 𝒜 (psi 𝒜 f))) h0
        ((Proj.awayToSection (grading 𝒜) (psi 𝒜 f)).hom (coneTwistAwayHom 𝒜 m d hf hd s)) =
      0 := by
    rw [hcongr]
    refine (congrArg (fun φ => φ.hom (coneTwistAwayHom 𝒜 m d hf hd s)) hmap).trans ?_
    change (Proj.awayToSection 𝒜 (tau 𝒜 (psi 𝒜 f))).hom
      (HomogeneousLocalization.Away.map (tau 𝒜) (psi 𝒜 f) (coneTwistAwayHom 𝒜 m d hf hd s)) = 0
    rw [coneTwistAwayHom_apply,
      awayMap_tau_eq_zero 𝒜 hf hm ((awayGradingEquivSectionsTwist 𝒜 d hf hd m).symm s).2,
      map_zero]
  change ((AlgebraicGeometry.Proj 𝒜).presheaf.map (eqToHom hopen.symm).op).hom
    ((zeroSection 𝒜).appLE (Proj.basicOpen (grading 𝒜) (psi 𝒜 f))
      (Proj.basicOpen 𝒜 (tau 𝒜 (psi 𝒜 f))) h0
        ((Proj.awayToSection (grading 𝒜) (psi 𝒜 f)).hom (coneTwistAwayHom 𝒜 m d hf hd s))) = 0
  rw [hval, map_zero]

/-- **The zero section `0 : P ⟶ L` is the vertex of the cone `π : L ⟶ P`**: it is a section of
`π`, and pulling functions back along it kills every homogeneous piece `𝒪_P(m)`, `m > 0`, of
`π_* 𝒪_L = ⨁_{m ≥ 0} 𝒪_P(m)`, over every open of `P`. So `0` is the closed immersion cut out by the
positive part of the grading, `Spec_P(𝒪_P) ⟶ Spec_P(⨁_{m ≥ 0} 𝒪_P(m))`. -/
@[stacks 0EKG "the zero section 0 : P → L is the vertex of the cone π"]
theorem zeroSection_appLE_coneIota_eq_zero (m : ℤ) (hm : 0 < m)
    (U : Opens (ProjectiveSpectrum.top 𝒜)) (s : (nonnegTwistingSheaf 𝒜 m).val.obj (op U)) :
    (zeroSection 𝒜).appLE (pi 𝒜 ⁻¹ᵁ U) U (le_zeroSection_preimage_pi_preimage 𝒜 U)
      ((coneIota 𝒜 m).val.app (op U) s) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) := ⟨m.toNat, by omega⟩
  have hcover : U ≤ iSup (fun p : {p : PositiveElem 𝒜 // positiveBasicOpen 𝒜 p ≤ U} =>
      positiveBasicOpen 𝒜 p.1) := by
    intro x hx
    rw [Opens.mem_iSup]
    obtain ⟨V, ⟨a, rfl⟩, hxV, hVW⟩ :=
      Opens.isBasis_iff_nbhd.mp (isBasis_positiveBasicOpen 𝒜) (show x ∈ U from hx)
    exact ⟨⟨a, hVW⟩, hxV⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (AlgebraicGeometry.Proj 𝒜).sheaf
    (fun p : {p : PositiveElem 𝒜 // positiveBasicOpen 𝒜 p ≤ U} => positiveBasicOpen 𝒜 p.1) U
    (fun p => homOfLE p.2) hcover _ _ fun p => ?_
  obtain ⟨d, hd, hf⟩ := p.1.2
  have hle : Proj.basicOpen 𝒜 p.1.1 ≤ U := p.2
  refine Eq.trans ?_ (map_zero (ConcreteCategory.hom
    ((AlgebraicGeometry.Proj 𝒜).sheaf.obj.map (homOfLE p.2).op))).symm
  have hres := PresheafOfModules.naturality_apply (coneTwistHom 𝒜 n).val (homOfLE hle).op s
  change (coneTwistHom 𝒜 n).val.app (op (ProjectiveSpectrum.basicOpen 𝒜 p.1.1)) _ = _ at hres
  rw [coneTwistHom_app 𝒜 n hf hd] at hres
  have h1 := Scheme.Hom.appLE_map (zeroSection 𝒜) (le_zeroSection_preimage_pi_preimage 𝒜 U)
    (homOfLE hle).op
  have h2 := Scheme.Hom.map_appLE (zeroSection 𝒜)
    (le_zeroSection_preimage_pi_preimage 𝒜 (Proj.basicOpen 𝒜 p.1.1))
    ((Opens.map (pi 𝒜).base).map (homOfLE hle)).op
  refine (ConcreteCategory.congr_hom h1 _).trans ?_
  refine (ConcreteCategory.congr_hom h2.symm _).trans ?_
  refine (congrArg (fun z => ((zeroSection 𝒜).appLE (pi 𝒜 ⁻¹ᵁ Proj.basicOpen 𝒜 p.1.1)
      (Proj.basicOpen 𝒜 p.1.1) (le_zeroSection_preimage_pi_preimage 𝒜 _)).hom z) hres.symm).trans ?_
  exact zeroSection_appLE_coneTwistApp_eq_zero 𝒜 n (by omega) hf hd _

/-- **The diagram of [Stacks, Tag 0EKG].** Let `A` be a graded ring, `X = Spec A`,
`Z = V(A₊) = Spec A₀`, `U = X ∖ Z`, `P = Proj A`, and let `L = Proj B` for
`B = ⨁_{d ≥ 0} A_{≥ d}`, with cone projection `π : L ⟶ P`, structure morphism `σ : L ⟶ X` and zero
section `0 : P ⟶ L`. Then, writing `j : Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ L` for the top-left arrow and
`e : Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) ≅ U` for the left identification:

* `π` is a cone over `P` (`truncationCone`, graded by `⨁_{m ≥ 0} 𝒪_P(m)`, whose pieces are the
  twisting sheaves `𝒪_P(m)`, `m ≥ 0`), and `L = Spec_P(⨁_{m ≥ 0} 𝒪_P(m))` over `P`;
* `j` lies over `P`, it is an open immersion, and its image is the part of `L` over `U`;
* `e` is an identification over `P`;
* the left square `j ≫ σ = e ≫ (U ⟶ X)` and the right square `π ≫ (P ⟶ Z) = σ ≫ (X ⟶ Z)`
  commute;
* the zero section is a section of `π`, it is the vertex of the cone (pulling back along it kills
  the pieces `𝒪_P(m)`, `m > 0`, of `π_* 𝒪_L`), and it maps set theoretically onto the inverse image
  of `Z` in `L`. -/
@[stacks 0EKG "the commutative diagram Spec_P(⨁_{m ∈ ℤ} O_P(m)) → L = Spec_P(⨁_{m ≥ 0} O_P(m)) → P \
over U → X → Z, with π a cone whose zero section maps set theoretically onto the inverse image \
of Z in L", ega "II 8.6.3" "special case"]
theorem projAndSpec_diagram :
    -- `π` is a cone over `P`, graded by the nonnegative twists
    (truncationCone 𝒜).π = pi 𝒜 ∧
    (truncationCone 𝒜).grading = nonnegTwistAlgebra 𝒜 ∧
    (truncationCone 𝒜).ι = coneIota 𝒜 ∧
    (∀ m : ℕ, (truncationCone 𝒜).grading.piece m = twistingSheaf 𝒜 m) ∧
    (∀ m : ℤ, (integerTwistAlgebra 𝒜).piece m = twistingSheaf 𝒜 m) ∧
    -- `L = Spec_P(⨁_{m ≥ 0} 𝒪_P(m))` over `P`
    (coneProjIsoRelativeSpecTwistAlgebra 𝒜).hom ≫
        relativeSpecToBase (nonnegTwistAlgebraSheaf 𝒜) = pi 𝒜 ∧
    -- the top-left arrow lies over `P`, is an open immersion, with image the part of `L` over `U`
    puncturedToConeProj 𝒜 ≫ pi 𝒜 = relativeSpecToBase (integerTwistAlgebraSheaf 𝒜) ∧
    IsOpenImmersion (puncturedToConeProj 𝒜) ∧
    (puncturedToConeProj 𝒜).opensRange = openUInL 𝒜 ∧
    -- the left identification `Spec_P(⨁_{m ∈ ℤ} 𝒪_P(m)) = U` lies over `P`
    (puncturedConeRelativeSpecTwistAlgebraIsoOpenU 𝒜).hom ≫ openUToProj 𝒜 =
      relativeSpecToBase (integerTwistAlgebraSheaf 𝒜) ∧
    -- the left square
    puncturedToConeProj 𝒜 ≫ toSpecA 𝒜 =
      (puncturedConeRelativeSpecTwistAlgebraIsoOpenU 𝒜).hom ≫ (ProjAndSpec.openU 𝒜).ι ∧
    -- the right square
    pi 𝒜 ≫ Proj.toSpecZero 𝒜 = toSpecA 𝒜 ≫ ProjAndSpec.xToZ 𝒜 ∧
    -- the zero section
    zeroSection 𝒜 ≫ pi 𝒜 = 𝟙 (AlgebraicGeometry.Proj 𝒜) ∧
    (∀ (m : ℤ), 0 < m → ∀ (U : Opens (ProjectiveSpectrum.top 𝒜))
        (s : (nonnegTwistingSheaf 𝒜 m).val.obj (op U)),
      (zeroSection 𝒜).appLE (pi 𝒜 ⁻¹ᵁ U) U (le_zeroSection_preimage_pi_preimage 𝒜 U)
        ((coneIota 𝒜 m).val.app (op U) s) = 0) ∧
    Set.range (zeroSection 𝒜) = toSpecA 𝒜 ⁻¹' Set.range (ProjAndSpec.zToX 𝒜) :=
  ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, coneProjIsoRelativeSpecTwistAlgebra_hom_comp 𝒜,
    puncturedToConeProj_comp_pi 𝒜, inferInstance,
    opensRange_puncturedToConeRelativeSpecTwistAlgebra_left 𝒜,
    puncturedConeRelativeSpecTwistAlgebraIsoOpenU_hom_comp_openUToProj 𝒜,
    puncturedToConeProj_comp_toSpecA 𝒜, pi_comp_toSpecZero 𝒜, zeroSection_comp_pi 𝒜,
    zeroSection_appLE_coneIota_eq_zero 𝒜, range_zeroSection_eq_preimage_range_zToX 𝒜⟩

end Stacks.AlgebraicGeometry.ProjConeTwist
