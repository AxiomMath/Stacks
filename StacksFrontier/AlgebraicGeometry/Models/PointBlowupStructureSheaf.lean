module

public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Bijective
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.DenominatorLocalRatio.Cokernels
public import StacksFrontier.AlgebraicGeometry.Models.PushforwardStructureSheafReducedFibre
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibre.ProperOverDvr

/-!
# The structure sheaf along the blowup of a point of a model

Let `R` be a discrete valuation ring with uniformizer `ϖ` and `p : X ⟶ Spec R` a flat morphism
with reduced special fibre, `X` locally Noetherian. For the blowup `b : X' ⟶ X` of `X` in a closed
point of the special fibre, with `X'` flat over `R`, `𝒪_X = b_*𝒪_{X'}`. This is the degree-zero
input, on the total space, to the computation of the special fibres of the blowups and
contractions in the proof of [Stacks, Tag 0E97].

* A nonzero element of `R` is a nonzerodivisor on the sections of `𝒪_X` over every open: the
  stalks of `X` are flat over localizations of `R`, which are domains. In particular the generic
  fibre `D(ϖ)` is dense.
* For every affine open `U`, `Γ(X, U)/(ϖ)` is reduced: membership in `(ϖ)` is local, and the
  local rings modulo `ϖ` are those of the special fibre.
* `b` is an isomorphism over `D(ϖ)`, so surjective, and
  `Stacks.Models.isIso_unitToPushforwardObjUnit_of_isReduced_quotient` applies.

## Main results

* `Stacks.Models.eq_zero_of_mul_eq_zero_of_flat`: `r a = 0` implies `a = 0` for `r ≠ 0`.
* `Stacks.Models.dense_basicOpen_globalFunctionOfBase`: the generic fibre is dense.
* `Stacks.Models.isReduced_quotient_of_isReduced_fiber`: `Γ(X, U)/(ϖ)` is reduced.
* `Stacks.Models.surjective_blowUpToBase_point`: `b` is surjective.
* `Stacks.Models.isIso_unitToPushforwardObjUnit_blowUpToBase_point`: `𝒪_X = b_*𝒪_{X'}`.

## References

* [Stacks Project, Section 0C2R](https://stacks.math.columbia.edu/tag/0C2R)
* [Stacks Project, Tag 0E97](https://stacks.math.columbia.edu/tag/0E97)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.Models

variable {R : Type u} [CommRing R] [IsDomain R]

/-- The image of `r ∈ R` in `Γ(X, ⊤)` along `p : X ⟶ Spec R`. -/
abbrev globalFunctionOfBase {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (r : R) : Γ(X, ⊤) :=
  p.appTop ((Scheme.ΓSpecIso (.of R)).inv r)

/-- **A nonzero element of the base is a nonzerodivisor on a flat scheme over a domain**: for
`p : X ⟶ Spec R` flat and `r ≠ 0`, if `r a = 0` for a section `a` of `𝒪_X` over an open `U`,
then `a = 0`. On stalks, `𝒪_{X,x}` is flat over the localization `𝒪_{Spec R, p x}`, a domain in
which `r` is nonzero. -/
theorem eq_zero_of_mul_eq_zero_of_flat {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [Flat p]
    {r : R} (hr : r ≠ 0) (U : X.Opens) (a : Γ(X, U))
    (h : X.presheaf.map (homOfLE le_top).op (globalFunctionOfBase p r) * a = 0) : a = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf U a 0 fun x hx => ?_
  have hg := congrArg (X.presheaf.germ U x hx) h
  rw [map_mul, TopCat.Presheaf.germ_res_apply, map_zero] at hg
  rw [map_zero]
  set e : (Spec (.of R)).presheaf.stalk (p x) :=
    (Spec (.of R)).presheaf.germ ⊤ (p x) trivial ((Scheme.ΓSpecIso (.of R)).inv r) with he
  have hpe : p.stalkMap x e = X.presheaf.germ ⊤ x trivial (globalFunctionOfBase p r) :=
    Scheme.Hom.germ_stalkMap_apply p ⊤ x trivial _
  rw [← hpe] at hg
  have hne : e ≠ 0 := by
    intro h0
    have h1 : ((Scheme.ΓSpecIso (.of R)).inv r) = 0 :=
      germ_injective_of_isIntegral (Spec (.of R)) (U := ⊤) (p x) trivial
        (by rw [← he, h0, map_zero])
    apply hr
    have h2 := congrArg (Scheme.ΓSpecIso (.of R)).hom h1
    rwa [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero] at h2
  let := (p.stalkMap x).hom.toAlgebra
  have : Module.Flat _ (X.presheaf.stalk x) := Flat.stalkMap p x
  have hreg : IsSMulRegular (X.presheaf.stalk x) e :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hne)
  exact hreg (show e • (X.presheaf.germ U x hx a) = e • (0 : X.presheaf.stalk x) by
    rwa [Algebra.smul_def, Algebra.smul_def, mul_zero])

/-- **The special fibre being reduced, so is every affine chart modulo a uniformizer**: for
`p : X ⟶ Spec R` over a discrete valuation ring with reduced special fibre, a uniformizer `ϖ` and
an affine open `U`, the ring `Γ(X, U)/(ϖ)` is reduced. At a prime of `Γ(X, U)` containing `ϖ` the
localization modulo `ϖ` is a local ring of the special fibre
(`AlgebraicGeometry.isReduced_quotient_localization_of_isReduced_fiber`), and membership in
`(ϖ)` is local. -/
theorem isReduced_quotient_of_isReduced_fiber [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) [IsReduced (p.fiber (IsLocalRing.closedPoint (CommRingCat.of R)))]
    {ϖ : R} (hϖ : Irreducible ϖ) (U : X.affineOpens) :
    IsReduced (Γ(X, U) ⧸
      Ideal.span {X.presheaf.map (homOfLE le_top).op (globalFunctionOfBase p ϖ)}) := by
  let A := Γ(X, U)
  have hU : IsAffineOpen (U : X.Opens) := U.2
  let ψ : CommRingCat.of R ⟶ Γ(X, U) :=
    (Scheme.ΓSpecIso (.of R)).inv ≫ p.appLE ⊤ U le_top
  have he : Spec.map ψ = hU.fromSpec ≫ p := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  have hψ : ψ ϖ = X.presheaf.map (homOfLE le_top).op (globalFunctionOfBase p ϖ) := by
    simp only [ψ, globalFunctionOfBase, Scheme.Hom.appLE, Scheme.Hom.appTop]
    rfl
  rw [← hψ, ← Ideal.isRadical_iff_quotient_reduced]
  intro x ⟨n, hn⟩
  refine Ideal.mem_of_localization_maximal fun P hP => ?_
  rw [Ideal.map_span, Set.image_singleton]
  by_cases hPϖ : ψ ϖ ∈ P
  · let q : PrimeSpectrum A := ⟨P, hP.isPrime⟩
    let y : PrimeSpectrum R := PrimeSpectrum.comap ψ.hom q
    have hy : y = IsLocalRing.closedPoint (CommRingCat.of R) := by
      have hmem : ϖ ∈ y.asIdeal := hPϖ
      have hne : y.asIdeal ≠ ⊥ := fun h => hϖ.ne_zero (by rwa [h] at hmem)
      exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
        (Ring.DimensionLEOne.maximalOfPrime hne y.isPrime))
    have : IsReduced ((Spec.map (CommRingCat.ofHom ψ.hom)).fiber y) := by
      rw [hy]
      exact isReduced_fiber_of_isOpenImmersion_comp hU.fromSpec p _ he.symm _
    have hred := isReduced_quotient_localization_of_isReduced_fiber ψ.hom y q rfl hy ϖ hϖ
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    refine IsNilpotent.eq_zero ⟨n, ?_⟩
    rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    have := Ideal.mem_map_of_mem (algebraMap A (Localization.AtPrime P)) hn
    rwa [Ideal.map_span, Set.image_singleton] at this
  · rw [Ideal.span_singleton_eq_top.mpr
      ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P _).mpr hPϖ)]
    exact Submodule.mem_top

/-- **The generic fibre of a flat scheme over a domain is dense**: for `p : X ⟶ Spec R` flat
and `r ≠ 0`, the locus `D(r) ⊆ X` where `r` is invertible is dense, `r` being a nonzerodivisor on
every affine open. -/
theorem dense_basicOpen_globalFunctionOfBase {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [Flat p]
    {r : R} (hr : r ≠ 0) : Dense (X.basicOpen (globalFunctionOfBase p r) : Set X) := by
  choose V hVaff hV _ using fun x : X =>
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  have h := Stacks.DenominatorCokernel.dense_iSup_basicOpen X V hV hVaff
    (fun x => X.presheaf.map (homOfLE le_top).op (globalFunctionOfBase p r))
    (fun x => mem_nonZeroDivisors_iff_right.mpr fun a ha =>
      eq_zero_of_mul_eq_zero_of_flat p hr _ a (by rwa [mul_comm]))
  refine h.mono fun y hy => ?_
  obtain ⟨x, hx⟩ := Opens.mem_iSup.mp hy
  rw [Scheme.basicOpen_res] at hx
  exact hx.2

/-- A point over the closed point of `Spec R` is not in the generic fibre `D(ϖ)`. -/
theorem notMem_basicOpen_globalFunctionOfBase [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) {ϖ : R} (hϖ : Irreducible ϖ) {z : X}
    (hz : p z = IsLocalRing.closedPoint (CommRingCat.of R)) :
    z ∉ X.basicOpen (globalFunctionOfBase p ϖ) := by
  intro h0
  have h : z ∈ p ⁻¹ᵁ (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv ϖ) := by
    rwa [Scheme.preimage_basicOpen]
  change p z ∈ (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv ϖ) at h
  rw [basicOpen_eq_of_affine, hz] at h
  exact h (show ϖ ∈ IsLocalRing.maximalIdeal R from
    (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit)

/-- The generic fibre `D(ϖ)` misses the support of the vanishing ideal of a point `z` over the
closed point of `Spec R`. -/
theorem basicOpen_subset_compl_support_vanishingIdeal [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) {ϖ : R} (hϖ : Irreducible ϖ) {z : X}
    (hz : IsClosed ({z} : Set X)) (hpz : p z = IsLocalRing.closedPoint (CommRingCat.of R)) :
    (X.basicOpen (globalFunctionOfBase p ϖ) : Set X) ⊆
      ((Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X)).support : Set X)ᶜ := by
  have hsupp :
      ((Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X)).support : Set X) = {z} := by
    simp
  rw [hsupp]
  rintro x hx rfl
  exact notMem_basicOpen_globalFunctionOfBase p hϖ hpz hx

variable [IsDiscreteValuationRing R]

/-- **The blowup of a flat scheme over `R` in a point of the special fibre is surjective**: it is
proper and an isomorphism over the dense generic fibre. -/
theorem surjective_blowUpToBase_point {X : Scheme.{u}} [IsLocallyNoetherian X]
    (p : X ⟶ Spec (.of R)) [Flat p] (z : X) (hz : IsClosed ({z} : Set X))
    (hpz : p z = IsLocalRing.closedPoint (CommRingCat.of R)) :
    Surjective (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X))) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X)
  set b := blowUpToBase I
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmem : (X.basicOpen (globalFunctionOfBase p ϖ) : Set X) ⊆ Set.range b.base := fun x hx =>
    exists_blowUpToBase_eq_of_notMem_support I
      (basicOpen_subset_compl_support_vanishingIdeal p hϖ hz hpz hx)
  exact (surjective_iff b).mpr (Set.range_eq_univ.mp (Set.eq_univ_of_univ_subset
    ((dense_basicOpen_globalFunctionOfBase p hϖ.ne_zero).closure_eq ▸
      closure_minimal hmem b.isClosedMap.isClosed_range)))

/-- **`𝒪_X = b_*𝒪_{X'}` for the blowup `b` of a model in a point of its special fibre.** Let
`p : X ⟶ Spec R` be flat with reduced special fibre, `X` locally Noetherian, `z` a closed point
over the closed point of `Spec R`, and `b : X' ⟶ X` the blowup in `z`, with `X'` flat over `R`.
Then `𝒪_X ⟶ b_*𝒪_{X'}` is an isomorphism: `b` is an isomorphism over the generic fibre `D(ϖ)`,
which is dense, so `b` is surjective, and `Γ(X, U)/(ϖ)` is reduced for every affine open `U`
(`Stacks.Models.isIso_unitToPushforwardObjUnit_of_isReduced_quotient`). -/
theorem isIso_unitToPushforwardObjUnit_blowUpToBase_point {X : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (.of R)) [Flat p]
    [IsReduced (p.fiber (IsLocalRing.closedPoint (CommRingCat.of R)))] (z : X)
    (hz : IsClosed ({z} : Set X)) (hpz : p z = IsLocalRing.closedPoint (CommRingCat.of R))
    [Flat (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X)) ≫ p)] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit (blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X))).toRingCatSheafHom) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X)
  set b := blowUpToBase I
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : Surjective b := surjective_blowUpToBase_point p z hz hpz
  exact isIso_unitToPushforwardObjUnit_of_isReduced_quotient b (globalFunctionOfBase p ϖ)
    (eq_zero_of_mul_eq_zero_of_flat p hϖ.ne_zero)
    (fun V c hc => eq_zero_of_mul_eq_zero_of_flat (b ≫ p) hϖ.ne_zero V c
      (by rwa [globalFunctionOfBase, Scheme.Hom.comp_appTop]))
    (isIso_blowUpToBase_restrict_of_subset_compl_support I _
      (basicOpen_subset_compl_support_vanishingIdeal p hϖ hz hpz))
    (isReduced_quotient_of_isReduced_fiber p hϖ)

end Stacks.Models

end
