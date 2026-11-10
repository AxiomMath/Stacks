module

public import StacksFrontier.AlgebraicGeometry.Divisors.ProjClosedSubschemeKernel
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjTrivialization.Basic

/-!
# Consecutive twists agree at a stalk, by multiplication by a degree-one element

Let `S` be a nonnegatively graded ring, `X = Proj(S)`, and let `x` be a point of `X`, that is a
homogeneous prime `p` not containing the irrelevant ideal. Let `f ∈ S₁` be a degree-one element
with `f ∉ p`. Then multiplication by `f ^ k` is an isomorphism

`(S(d))₍p₎ ≅ (S(d + k))₍p₎`

between the degree-zero parts of the localizations at `p` of consecutive twists of the regular
module. The reason is purely arithmetic: an element of `(S(d))₍p₎` is a sum of fractions `m / s`
with `m` and `s` homogeneous and `deg m - deg s = d`, multiplying the numerator by `f` raises
that difference by exactly one, and `f` is invertible in the localization at `p` because
`f ∉ p`.

Combined with the identification of `(S(0))₍p₎` with the local ring `S₍p₎` this gives the case
needed for the Euler sequence, `d = -1` and `k = 1`: **the stalk of `𝒪_X(-1)` at `x` is the
stalk of `𝒪_X` at `x`**. The passage from the stalk of the twisting sheaf to the degree-zero part
is `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalkLinearEquiv` of
Stacks Tag 01M7, and the passage from the structure-sheaf stalk to `S₍p₎` is
`AlgebraicGeometry.Proj.stalkIso'`.

This is the stalk form of the trivialization of the twisting sheaves over a standard open
`D₊(f)` proved in
`Stacks.AlgebraicGeometry.ProjTrivialization.twistingSheafOverBasicOpenIsoUnit`; it is proved
directly here rather than by localizing that statement, because the stalk is a submodule of the
localization at `p` cut out by a degree condition, so the argument is one line of degree
bookkeeping on each spanning fraction and needs no gluing.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.mulFiber`: multiplication by an element of
  the localization of `S` at the homogeneous prime of a point, as an endomorphism of the fibre.
* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.powFiber` and
  `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.powFiberInv`: `f ^ k` and its inverse in
  that localization.
* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.mulPowTwistEquiv`: multiplication by `f ^ k`
  as a linear equivalence from the `d`-th to the `(d + k)`-th twist at the point.
* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.toFiber` and
  `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroModuleAtZeroEquiv`: the local ring
  `S₍p₎` as the degree-zero part of the untwisted module.
* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.twistMinusOneEquiv` and
  `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.twistingSheafMinusOneStalkEquiv`: the
  identification of `𝒪(-1)` with `𝒪` at the point, at the degree-zero part and at the stalk.

## Main results

* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroModuleAt_twistGrading_eq_span`: the
  degree-zero part of a twist is spanned by the single fractions of the appropriate degrees.
* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.powFiber_smul_mem_degreeZeroModuleAt` and
  `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.powFiberInv_smul_mem_degreeZeroModuleAt`:
  multiplication by `f ^ k` raises the twist by `k` and division by `f ^ k` lowers it by `k`.
* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.mulPowTwistEquiv_mk`: the identification
  sends `m / s` to `f ^ k m / s`.
* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.range_toFiber`: the degree-zero part of the
  untwisted module is the set of multiples of `1 / 1`, so it is free of rank one over `S₍p₎`.
* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.val_twistMinusOneEquiv` and
  `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.val_twistingSheafMinusOneStalkEquiv_germ`:
  the identification of `𝒪(-1)` with `𝒪` sends `m / s` to `f m / s`, at the degree-zero part and
  on germs.
* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.exists_X_notMem_asHomogeneousIdeal`: at every
  point of `Proj R[T₀, …, Tₙ]` some variable is a degree-one element outside the homogeneous
  prime, so the hypotheses above are satisfiable at every point.

## Implementation notes

All equivalences are linear over `HomogeneousLocalization.AtPrime 𝒮 p`, the local ring `S₍p₎`,
because that is the ring `degreeZeroModuleAt` is a `Submodule` over. The stalk-level statements
are then read over the structure-sheaf stalk, which acts through
`AlgebraicGeometry.Proj.stalkIso'`, exactly as `associatedModuleSheafStalkLinearEquiv` does.

The whole file is pointwise arithmetic in one localization because of two definitional
coincidences recorded in
`StacksFrontier/AlgebraicGeometry/ProjTrivialization/Basic.lean`: `Localization p.primeCompl` and
`LocalizedModule p.primeCompl S` are the *same* type, both unfolding to `OreLocalization`, so
the fibres of every twist of the regular module are the one local ring; and the action of
`Localization p.primeCompl` on that module is ring multiplication. Only the degree condition
distinguishes one twist from the next, which is why `mulFiber` can be a single endomorphism of
the fibre whose restrictions to the various degree-zero parts are the comparison maps.

Two pitfalls cost time:

* The module structure in the type of
  `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroModuleAt` is introduced by `letI`
  in that declaration's statement. Repeating it as a `local instance` with the identical body,
  rather than repeating the `letI` in every statement here, is enough for the two to be
  identified.
* Rewriting inside the fibres produces goals that are "not type-correct under the `implicit`
  transparency level", the problem that
  `attribute [local instance_reducible] ProjectiveSpectrum.top` and
  `attribute [local implicit_reducible] TopCat.Sheaf sheafCompose` address in the neighbouring
  files. Here it is avoided instead: the germ computation rule chains the existing equations with
  `Eq.trans` rather than rewriting with them, so no transparency attribute is needed.

The general form of the last result — for `𝒮` generated in degree one over `𝒮 0`, every point of
`Proj 𝒮` has a degree-one element outside its homogeneous prime — is
`Stacks.AlgebraicGeometry.TwistRigidityDegreeOne.exists_degreeOne_notMem_of_adjoin_eq_top`, and
is not restated here.

## References

* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 0FMH](https://stacks.math.columbia.edu/tag/0FMH)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjStalkGlobalSections

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The homogeneous ideal of a point of `Proj 𝒮` is prime as an ideal of `S`. -/
local instance (x : ProjectiveSpectrum.top 𝒮) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

/-- The degree-zero prime localization `S₍ₓ₎` acts on the fibre at `x` through its inclusion
into the full localization of `S` at the homogeneous prime of `x`. -/
local instance fiberModule (x : ProjectiveSpectrum.top 𝒮) :
    Module (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x) :=
  Module.compHom _ (algebraMap
    (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
    (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))

/-- The degree-zero part of the localization of the twist `S(d)` at `x` is spanned by the single
fractions `m / s` with `s` homogeneous of some degree `j` and `m` of degree `j + d`. -/
theorem degreeZeroModuleAt_twistGrading_eq_span (d : ℤ) (x : ProjectiveSpectrum.top 𝒮) :
    degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 d) x =
      Submodule.span (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
        {z | ∃ (j : ℕ) (m : S) (s : x.asHomogeneousIdeal.toIdeal.primeCompl),
          m ∈ integerGrading 𝒮 ((j : ℤ) + d) ∧ (s : S) ∈ 𝒮 j ∧
            z = LocalizedModule.mk m s} := rfl

/-- Multiplication by an element of the localization of `S` at the homogeneous prime of `x`, as
an endomorphism of the fibre at `x` that is linear over the degree-zero subring `S₍ₓ₎`. -/
noncomputable def mulFiber (x : ProjectiveSpectrum.top 𝒮)
    (u : Localization x.asHomogeneousIdeal.toIdeal.primeCompl) :
    ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x
      →ₗ[HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal]
        ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x where
  toFun z := u • z
  map_add' _ _ := smul_add u _ _
  map_smul' r z := by
    change u • (HomogeneousLocalization.val r • z) =
      HomogeneousLocalization.val r • (u • z)
    rw [smul_smul, smul_smul, mul_comm]

/-- Multiplication by `a / b` sends the fraction `m / s` to `a m / b s`. -/
theorem mulFiber_mk (x : ProjectiveSpectrum.top 𝒮) (a : S)
    (b : x.asHomogeneousIdeal.toIdeal.primeCompl) (m : S)
    (s : x.asHomogeneousIdeal.toIdeal.primeCompl) :
    mulFiber 𝒮 x (Localization.mk a b) (LocalizedModule.mk m s) =
      LocalizedModule.mk (a * m) (b * s) :=
  LocalizedModule.mk_smul_mk _ _ _ _

/-- Multiplying by `v` and then by `u` is multiplying by `u * v`. -/
theorem mulFiber_mulFiber (x : ProjectiveSpectrum.top 𝒮)
    (u v : Localization x.asHomogeneousIdeal.toIdeal.primeCompl)
    (z : ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x) :
    mulFiber 𝒮 x u (mulFiber 𝒮 x v z) = mulFiber 𝒮 x (u * v) z :=
  smul_smul u v z

/-- Multiplication by `1` is the identity. -/
theorem mulFiber_one (x : ProjectiveSpectrum.top 𝒮)
    (z : ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x) :
    mulFiber 𝒮 x 1 z = z :=
  one_smul _ z

variable {f : S}

/-- The image `f ^ k / 1` of `f ^ k` in the localization of `S` at the homogeneous prime
of `x`. -/
noncomputable def powFiber (f : S) (k : ℕ) (x : ProjectiveSpectrum.top 𝒮) :
    Localization x.asHomogeneousIdeal.toIdeal.primeCompl :=
  Localization.mk (f ^ k) 1

/-- The inverse `1 / f ^ k` of `f ^ k` in the localization of `S` at the homogeneous prime of
`x`, which exists because `f` does not lie in that prime. -/
noncomputable def powFiberInv (f : S) (k : ℕ) {x : ProjectiveSpectrum.top 𝒮}
    (hx : f ∉ x.asHomogeneousIdeal) :
    Localization x.asHomogeneousIdeal.toIdeal.primeCompl :=
  Localization.mk 1 ⟨f ^ k, x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hx k⟩

/-- `f ^ k` and `1 / f ^ k` are inverse in the localization at `x`. -/
theorem powFiber_mul_powFiberInv (k : ℕ) {x : ProjectiveSpectrum.top 𝒮}
    (hx : f ∉ x.asHomogeneousIdeal) :
    powFiber 𝒮 f k x * powFiberInv 𝒮 f k hx = 1 := by
  rw [powFiber, powFiberInv, Localization.mk_mul, ← Localization.mk_one]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp [mul_comm]))

/-- `1 / f ^ k` and `f ^ k` are inverse in the localization at `x`. -/
theorem powFiberInv_mul_powFiber (k : ℕ) {x : ProjectiveSpectrum.top 𝒮}
    (hx : f ∉ x.asHomogeneousIdeal) :
    powFiberInv 𝒮 f k hx * powFiber 𝒮 f k x = 1 := by
  rw [mul_comm]; exact powFiber_mul_powFiberInv 𝒮 k hx

/-- To show multiplication by `u` sends the degree-zero part of `S(d)` into that of `S(d')`, it
suffices to check it on the spanning fractions. -/
private theorem mulFiber_mem_of_forall (d d' : ℤ) (x : ProjectiveSpectrum.top 𝒮)
    (u : Localization x.asHomogeneousIdeal.toIdeal.primeCompl)
    (h : ∀ (j : ℕ) (m : S) (s : x.asHomogeneousIdeal.toIdeal.primeCompl),
      m ∈ integerGrading 𝒮 ((j : ℤ) + d) → (s : S) ∈ 𝒮 j →
        mulFiber 𝒮 x u (LocalizedModule.mk m s) ∈
          degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 d') x)
    {z : ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x}
    (hz : z ∈ degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 d) x) :
    mulFiber 𝒮 x u z ∈ degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 d') x := by
  rw [degreeZeroModuleAt_twistGrading_eq_span] at hz
  exact (Submodule.map_span_le _ _ _).mpr
    (by rintro _ ⟨j, m, s, hm, hs, rfl⟩; exact h j m s hm hs) ⟨z, hz, rfl⟩

/-- **Multiplication by `f ^ k` raises the twist by `k`.** For `f` homogeneous of degree one,
multiplying the numerator of a degree-zero fraction of `S(d)` by `f ^ k` raises the difference
of the degrees of numerator and denominator by exactly `k`. -/
theorem powFiber_smul_mem_degreeZeroModuleAt (hf : f ∈ 𝒮 1) (k : ℕ) (d : ℤ)
    (x : ProjectiveSpectrum.top 𝒮)
    {z : ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x}
    (hz : z ∈ degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 d) x) :
    mulFiber 𝒮 x (powFiber 𝒮 f k x) z ∈
      degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 (d + k)) x := by
  have hfk : f ^ k ∈ 𝒮 k := by
    simpa using ProjTrivialization.pow_toNat_mem 𝒮 hf k
  refine mulFiber_mem_of_forall 𝒮 d (d + k) x _ ?_ hz
  intro j m s hm hs
  rw [powFiber, mulFiber_mk, one_mul, degreeZeroModuleAt_twistGrading_eq_span]
  refine Submodule.subset_span ⟨j, f ^ k * m, s, ?_, hs, rfl⟩
  have h := mul_mem_integerGrading 𝒮 hfk hm
  rwa [show (k : ℤ) + ((j : ℤ) + d) = (j : ℤ) + (d + k) by ring] at h

/-- **Division by `f ^ k` lowers the twist by `k`.** For `f` homogeneous of degree one outside
the homogeneous prime of `x`, multiplying the denominator of a degree-zero fraction of
`S(d + k)` by `f ^ k` lowers the difference of the degrees by exactly `k`. -/
theorem powFiberInv_smul_mem_degreeZeroModuleAt (hf : f ∈ 𝒮 1) (k : ℕ) (d : ℤ)
    {x : ProjectiveSpectrum.top 𝒮} (hx : f ∉ x.asHomogeneousIdeal)
    {z : ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x}
    (hz : z ∈ degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 (d + k)) x) :
    mulFiber 𝒮 x (powFiberInv 𝒮 f k hx) z ∈
      degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 d) x := by
  have hfk : f ^ k ∈ 𝒮 k := by
    simpa using ProjTrivialization.pow_toNat_mem 𝒮 hf k
  refine mulFiber_mem_of_forall 𝒮 (d + k) d x _ ?_ hz
  intro j m s hm hs
  rw [powFiberInv, mulFiber_mk, one_mul, degreeZeroModuleAt_twistGrading_eq_span]
  refine Submodule.subset_span ⟨j + k, m,
    ⟨f ^ k, x.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hx k⟩ * s, ?_, ?_, rfl⟩
  · rwa [show ((j + k : ℕ) : ℤ) + d = (j : ℤ) + (d + k) by push_cast; ring]
  · have h := SetLike.mul_mem_graded hfk hs
    rwa [show k + j = j + k by omega] at h

/-- **Multiplication by `f ^ k` identifies the twist by `d` with the twist by `d + k` at `x`.**
Here `f` is homogeneous of degree one and does not lie in the homogeneous prime of `x`, so it
becomes a unit in the localization there, while raising the numerator's degree by `k` raises the
difference of the degrees of numerator and denominator by exactly `k`. -/
noncomputable def mulPowTwistEquiv (hf : f ∈ 𝒮 1) {x : ProjectiveSpectrum.top 𝒮}
    (hx : f ∉ x.asHomogeneousIdeal) (d : ℤ) (k : ℕ) :
    degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 d) x
      ≃ₗ[HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal]
        degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 (d + k)) x :=
  LinearEquiv.ofLinearMap
    ((mulFiber 𝒮 x (powFiber 𝒮 f k x)).restrict
      (fun _ hz => powFiber_smul_mem_degreeZeroModuleAt 𝒮 hf k d x hz))
    ((mulFiber 𝒮 x (powFiberInv 𝒮 f k hx)).restrict
      (fun _ hz => powFiberInv_smul_mem_degreeZeroModuleAt 𝒮 hf k d hx hz))
    (LinearMap.ext fun z => Subtype.ext (by
      change mulFiber 𝒮 x (powFiber 𝒮 f k x)
        (mulFiber 𝒮 x (powFiberInv 𝒮 f k hx) (z : _)) = (z : _)
      rw [mulFiber_mulFiber, powFiber_mul_powFiberInv, mulFiber_one]))
    (LinearMap.ext fun z => Subtype.ext (by
      change mulFiber 𝒮 x (powFiberInv 𝒮 f k hx)
        (mulFiber 𝒮 x (powFiber 𝒮 f k x) (z : _)) = (z : _)
      rw [mulFiber_mulFiber, powFiberInv_mul_powFiber, mulFiber_one]))

/-- **The computation rule for the identification of the twists**: the degree-zero fraction
`m / s` of `S(d)` is sent to the degree-zero fraction `f ^ k m / s` of `S(d + k)`. -/
theorem mulPowTwistEquiv_mk (hf : f ∈ 𝒮 1) {x : ProjectiveSpectrum.top 𝒮}
    (hx : f ∉ x.asHomogeneousIdeal) (d : ℤ) (k : ℕ) {m : S}
    {s : x.asHomogeneousIdeal.toIdeal.primeCompl}
    (hz : LocalizedModule.mk m s ∈ degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 d) x) :
    (mulPowTwistEquiv 𝒮 hf hx d k ⟨LocalizedModule.mk m s, hz⟩ :
        ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x) =
      LocalizedModule.mk (f ^ k * m) s := by
  change mulFiber 𝒮 x (powFiber 𝒮 f k x) (LocalizedModule.mk m s) = _
  rw [powFiber, mulFiber_mk, one_mul]

/-- The local ring `S₍ₓ₎`, mapped into the fibre at `x` as the `S₍ₓ₎`-multiples of the fraction
`1 / 1`. -/
noncomputable def toFiber (x : ProjectiveSpectrum.top 𝒮) :
    HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal
      →ₗ[HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal]
        ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x :=
  LinearMap.toSpanSingleton _ _ (LocalizedModule.mk 1 1)

/-- The map into the fibre is the inclusion of a homogeneous fraction into the full
localization. -/
theorem toFiber_apply (x : ProjectiveSpectrum.top 𝒮)
    (r : HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal) :
    toFiber 𝒮 x r = HomogeneousLocalization.val r := by
  change HomogeneousLocalization.val r * Localization.mk (1 : S) 1 = _
  rw [Localization.mk_one, mul_one]

/-- The map of `S₍ₓ₎` into the fibre is injective, because the value of a homogeneous fraction
determines it. -/
theorem injective_toFiber (x : ProjectiveSpectrum.top 𝒮) :
    Function.Injective (toFiber 𝒮 x) := fun r r' h =>
  HomogeneousLocalization.val_injective _
    ((toFiber_apply 𝒮 x r).symm.trans (h.trans (toFiber_apply 𝒮 x r')))

/-- **The degree-zero part of the untwisted module at `x` is the set of `S₍ₓ₎`-multiples of
`1 / 1`**, hence free of rank one: a fraction `m / s` with `m` and `s` homogeneous of the same
degree is itself a scalar, and conversely every scalar is such a fraction. -/
theorem range_toFiber (x : ProjectiveSpectrum.top 𝒮) :
    LinearMap.range (toFiber 𝒮 x) = degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 0) x := by
  rw [toFiber, ← LinearMap.span_singleton_eq_range,
    degreeZeroModuleAt_twistGrading_eq_span]
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    refine Submodule.subset_span ⟨0, 1, 1, ?_, by simpa using SetLike.one_mem_graded 𝒮, rfl⟩
    simpa using ProjTrivialization.mem_integerGrading_natCast 𝒮
      (SetLike.one_mem_graded 𝒮)
  · rintro w ⟨j, m, s, hm, hs, rfl⟩
    have hmS : m ∈ 𝒮 j := by
      rw [show (j : ℤ) + 0 = ((j : ℕ) : ℤ) by ring, integerGrading_natCast] at hm
      simpa only [mem_homogeneousSubmodule] using hm
    refine Submodule.mem_span_singleton.mpr
      ⟨HomogeneousLocalization.mk ⟨j, ⟨m, hmS⟩, ⟨(s : S), hs⟩, s.2⟩, ?_⟩
    change mulFiber 𝒮 x
      (HomogeneousLocalization.val
        (HomogeneousLocalization.mk ⟨j, ⟨m, hmS⟩, ⟨(s : S), hs⟩, s.2⟩))
      (LocalizedModule.mk 1 1) = _
    rw [HomogeneousLocalization.val_mk, mulFiber_mk, mul_one, mul_one]

/-- **The degree-zero part of the untwisted module at `x`, identified with the local ring
`S₍ₓ₎`.** The identification sends `r` to the fraction `r · (1 / 1)`. -/
noncomputable def degreeZeroModuleAtZeroEquiv (x : ProjectiveSpectrum.top 𝒮) :
    HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal
      ≃ₗ[HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal]
        degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 0) x :=
  (LinearEquiv.ofInjective (toFiber 𝒮 x) (injective_toFiber 𝒮 x)).trans
    (LinearEquiv.ofEq _ _ (range_toFiber 𝒮 x))

/-- The inverse identification is pinned down by its value in the localization: a degree-zero
element of the untwisted fibre is the fraction it already is. -/
theorem val_degreeZeroModuleAtZeroEquiv_symm (x : ProjectiveSpectrum.top 𝒮)
    (w : degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 0) x) :
    HomogeneousLocalization.val ((degreeZeroModuleAtZeroEquiv 𝒮 x).symm w) =
      (w : ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x) :=
  (toFiber_apply 𝒮 x _).symm.trans
    (congrArg (fun z : degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 0) x =>
      (z : ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x))
      ((degreeZeroModuleAtZeroEquiv 𝒮 x).apply_symm_apply w))

/-- **The degree-zero part of `S(-1)` at `x` is the local ring `S₍ₓ₎`**, identified by
multiplication by a degree-one element `f` outside the homogeneous prime of `x`. Through
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalkLinearEquiv` this is
the statement that the stalk of `𝒪(-1)` at `x` is the stalk of `𝒪` at `x`. -/
noncomputable def twistMinusOneEquiv (hf : f ∈ 𝒮 1) {x : ProjectiveSpectrum.top 𝒮}
    (hx : f ∉ x.asHomogeneousIdeal) :
    degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 (-1)) x
      ≃ₗ[HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal]
        HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal :=
  ((mulPowTwistEquiv 𝒮 hf hx (-1) 1).trans
    (LinearEquiv.ofEq _ _ (by norm_num))).trans (degreeZeroModuleAtZeroEquiv 𝒮 x).symm

/-- **The computation rule for the identification of `S(-1)` with the local ring at `x`**: the
degree-zero fraction `m / s` of `S(-1)` is sent to the degree-zero fraction `f m / s`. -/
theorem val_twistMinusOneEquiv_mk (hf : f ∈ 𝒮 1) {x : ProjectiveSpectrum.top 𝒮}
    (hx : f ∉ x.asHomogeneousIdeal) {m : S}
    {s : x.asHomogeneousIdeal.toIdeal.primeCompl}
    (hz : LocalizedModule.mk m s ∈ degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 (-1)) x) :
    HomogeneousLocalization.val
        (twistMinusOneEquiv 𝒮 hf hx ⟨LocalizedModule.mk m s, hz⟩) =
      Localization.mk (f * m) s := by
  rw [twistMinusOneEquiv]
  rw [LinearEquiv.trans_apply, val_degreeZeroModuleAtZeroEquiv_symm]
  change (mulPowTwistEquiv 𝒮 hf hx (-1) 1 ⟨LocalizedModule.mk m s, hz⟩ :
    ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x) = _
  rw [mulPowTwistEquiv_mk, pow_one]
  rfl

/-- The computation rule in the form used at a stalk: an element of the degree-zero part of
`S(-1)` whose fraction is `m / s` is sent to the degree-zero fraction `f m / s`. -/
theorem val_twistMinusOneEquiv (hf : f ∈ 𝒮 1) {x : ProjectiveSpectrum.top 𝒮}
    (hx : f ∉ x.asHomogeneousIdeal)
    (w : degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 (-1)) x) {m : S}
    {s : x.asHomogeneousIdeal.toIdeal.primeCompl}
    (hw : (w : ProjectiveSpectrum.Proj.ModuleFiber (M := S) 𝒮 x) =
      LocalizedModule.mk m s) :
    HomogeneousLocalization.val (twistMinusOneEquiv 𝒮 hf hx w) =
      Localization.mk (f * m) s := by
  obtain ⟨w, hwmem⟩ := w
  subst hw
  exact val_twistMinusOneEquiv_mk 𝒮 hf hx hwmem

/-- The structure-sheaf stalk at `x` acts on the degree-zero parts at `x` through the canonical
identification `AlgebraicGeometry.Proj.stalkIso'` of that stalk with the local ring `S₍ₓ₎`. -/
noncomputable local instance stalkModuleDegreeZeroModuleAt (d : ℤ)
    (x : ProjectiveSpectrum.top 𝒮) :
    Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x)
      (degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 d) x) :=
  Module.compHom _ (Proj.stalkIso' 𝒮 x).toRingHom

/-- The identification of the degree-zero part of `S(-1)` at `x` with the local ring at `x`,
read over the structure-sheaf stalk: the stalk acts on both sides through
`AlgebraicGeometry.Proj.stalkIso'`. -/
noncomputable def twistMinusOneStalkLinearEquiv (hf : f ∈ 𝒮 1)
    {x : ProjectiveSpectrum.top 𝒮} (hx : f ∉ x.asHomogeneousIdeal) :
    degreeZeroModuleAt 𝒮 (twistGrading (S := S) 𝒮 (-1)) x
      ≃ₗ[(ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x]
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x where
  toFun z := (Proj.stalkIso' 𝒮 x).symm (twistMinusOneEquiv 𝒮 hf hx z)
  invFun c := (twistMinusOneEquiv 𝒮 hf hx).symm (Proj.stalkIso' 𝒮 x c)
  map_add' _ _ := by simp
  map_smul' c z := by
    change (Proj.stalkIso' 𝒮 x).symm
        (twistMinusOneEquiv 𝒮 hf hx ((Proj.stalkIso' 𝒮 x c) • z)) =
      c * (Proj.stalkIso' 𝒮 x).symm (twistMinusOneEquiv 𝒮 hf hx z)
    rw [map_smul]
    change (Proj.stalkIso' 𝒮 x).symm
      ((Proj.stalkIso' 𝒮 x c) * twistMinusOneEquiv 𝒮 hf hx z) = _
    rw [map_mul, RingEquiv.symm_apply_apply]
  left_inv _ := by simp
  right_inv _ := by simp

/-- **The stalk of `𝒪(-1)` at `x` is the stalk of `𝒪` at `x`.** The identification is
multiplication by a degree-one element `f` of `S` outside the homogeneous prime of `x`, which is
a unit of the local ring there and raises the twist from `-1` to `0`. -/
noncomputable def twistingSheafMinusOneStalkEquiv (hf : f ∈ 𝒮 1)
    {x : ProjectiveSpectrum.top 𝒮} (hx : f ∉ x.asHomogeneousIdeal) :
    associatedModuleSheafStalk 𝒮 (twistGrading (S := S) 𝒮 (-1)) x
      ≃ₗ[(ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x]
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x :=
  (associatedModuleSheafStalkLinearEquiv 𝒮 (twistGrading (S := S) 𝒮 (-1)) x).trans
    (twistMinusOneStalkLinearEquiv 𝒮 hf hx)

/-- **The computation rule at a stalk**: if a section `a` of `𝒪(-1)` over a neighbourhood of `x`
has value the fraction `m / s` at `x`, its germ is sent to the germ of `𝒪` whose value at `x` is
`f m / s`. -/
theorem val_twistingSheafMinusOneStalkEquiv_germ (hf : f ∈ 𝒮 1)
    {x : ProjectiveSpectrum.top 𝒮} (hx : f ∉ x.asHomogeneousIdeal)
    (U : Opens (ProjectiveSpectrum.top 𝒮)) (hxU : x ∈ U)
    (a : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮
      (twistGrading (S := S) 𝒮 (-1))).val.obj (op U))
    {m : S} {s : x.asHomogeneousIdeal.toIdeal.primeCompl}
    (ha : ((ProjectiveSpectrum.Proj.associatedModuleSheafSectionsEquiv 𝒮
        (twistGrading (S := S) 𝒮 (-1)) U).toFun a).1 ⟨x, hxU⟩ = LocalizedModule.mk m s) :
    HomogeneousLocalization.val (Proj.stalkIso' 𝒮 x
        (twistingSheafMinusOneStalkEquiv 𝒮 hf hx
          (associatedModuleSheafGerm 𝒮 (twistGrading (S := S) 𝒮 (-1)) x U hxU a))) =
      Localization.mk (f * m) s := by
  have h : twistingSheafMinusOneStalkEquiv 𝒮 hf hx
      (associatedModuleSheafGerm 𝒮 (twistGrading (S := S) 𝒮 (-1)) x U hxU a) =
      (Proj.stalkIso' 𝒮 x).symm (twistMinusOneEquiv 𝒮 hf hx
        (associatedModuleSheafStalkEquiv 𝒮 (twistGrading (S := S) 𝒮 (-1)) x
          (associatedModuleSheafGerm 𝒮 (twistGrading (S := S) 𝒮 (-1)) x U hxU a))) := rfl
  rw [h, RingEquiv.apply_symm_apply]
  exact val_twistMinusOneEquiv 𝒮 hf hx _
    ((associatedModuleSheafStalkEquiv_germ 𝒮 (twistGrading (S := S) 𝒮 (-1)) x U hxU a).trans ha)

/-! ### Degree-one elements outside a point -/

section Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **At every point of `Proj R[T₀, …, Tₙ]` some variable lies outside the homogeneous prime**,
because the standard opens `D₊(Tᵢ)` cover. This supplies the degree-one element that identifies
consecutive twists at a stalk. -/
theorem exists_X_notMem_asHomogeneousIdeal (R : Type u) [CommRing R] (n : ℕ)
    (x : AlgebraicGeometry.Proj (ProjPolyChart.polyGrading R n)) :
    ∃ i : Fin (n + 1),
      (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∉ x.asHomogeneousIdeal := by
  have hx : x ∈ (⨆ i : Fin (n + 1),
      AlgebraicGeometry.Proj.basicOpen (ProjPolyChart.polyGrading R n)
        (MvPolynomial.X i)) := by
    rw [ProjPolyChart.iSup_basicOpen_X_eq_top]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨i, (AlgebraicGeometry.Proj.mem_basicOpen _ _ x).mp hi⟩

end Polynomial

end Stacks.AlgebraicGeometry.ProjStalkGlobalSections

end
