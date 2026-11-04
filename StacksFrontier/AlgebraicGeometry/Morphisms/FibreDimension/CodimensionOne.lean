module

public import StacksFrontier.AlgebraicGeometry.AffineAmbientMinimalPrimes.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.RingTheory.Ideal.Over.HeightOne

/-!
# Fibre dimension over a point of codimension at most one

Let `f : X ⟶ Y` be locally of finite type and let `x` be a point of `X` whose image has
Noetherian local ring of Krull dimension at most one. If the fibre of `f` through the generic
point of every irreducible component of `X` containing `x` has dimension zero there, then the
fibre through `x` has dimension zero at `x`; equivalently, `f` is quasi-finite at `x` as soon as
it is quasi-finite at the generic point of every component through `x`.

The lower bound is the semicontinuity of the fibre dimension along a specialization. For the
upper bound the local dimension of the fibre at `x` is the largest dimension of an irreducible
component of the fibre through `x`, and each such component is shown to be a single point: its
generic point `η` has residue field finite over that of `f η`, because `f` is quasi-finite at a
generic point `ν` of a component of `X` through `η` and the local ring of `Y` at `f η` has
dimension at most one. That last step is the finiteness half of Krull–Akizuki, in the form
`IsLocalRing.finite_residueField_of_quasiFiniteAt`; it is read off on a compatible pair of affine
open neighbourhoods of `η` and of `f η`, where the local rings of `X` at `η` and of `Y` at `f η`
are localizations of the rings of sections, and the residue fields are the residue fields of the
corresponding primes.

## Main results

* `AlgebraicGeometry.finite_residueField_of_quasiFiniteAt_specializes`: the residue field
  extension at a point over which the target has dimension at most one is finite as soon as the
  morphism is quasi-finite at some generalization of that point.
* `AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_zero_of_ringKrullDim_stalk_le_one`: the
  dimension of the fibre at `x` is zero.

## Implementation notes

Generic points of irreducible components are the points of `genericPoints`, and the point of the
scheme-theoretic fibre determined by a point of the source is `Scheme.Hom.asFiber`. Points of a
fibre over an arbitrary point of the target are produced by `Scheme.Hom.fiberHomeo`, which makes
the identification with the set-theoretic fibre available; the two descriptions agree for the
image point by definition of `Scheme.Hom.asFiber`.

## References

* [Stacks Project, Tag 00PG](https://stacks.math.columbia.edu/tag/00PG)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- Evaluating a section of the target at the image of a point and transporting it along the
morphism agree. -/
private lemma appLE_comp_evaluation (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (x : V) :
    f.appLE U V h ≫ X.evaluation V x x.2 =
      Y.evaluation U (f x) (h x.2) ≫ f.residueFieldMap x := by
  simp only [Scheme.evaluation, Scheme.Hom.appLE, Category.assoc,
    TopCat.Presheaf.germ_res_assoc, Scheme.residue_residueFieldMap]
  exact (f.germ_stalkMap_assoc U x (h x.2) (X.residue x)).symm

/-- **Residue fields in codimension one.** If `f` is quasi-finite at a generalization `ν` of `η`
and the local ring of the target at `f η` is Noetherian of Krull dimension at most one, then the
residue field of `η` is finite over the residue field of `f η`.

This is the finiteness half of Krull–Akizuki read on a morphism of schemes: a generalization at
which `f` is quasi-finite makes `f` generically finite along a component through `η`, and over a
point of codimension at most one generic finiteness propagates to finiteness. -/
public theorem finite_residueField_of_quasiFiniteAt_specializes
    (f : X ⟶ Y) [LocallyOfFiniteType f] {ν η : X} (hνη : ν ⤳ η)
    (hY : IsNoetherianRing (Y.presheaf.stalk (f η)))
    (hYdim : ringKrullDim (Y.presheaf.stalk (f η)) ≤ 1)
    (hqf : quasiFiniteAt f ν) :
    letI := (f.residueFieldMap η).hom.toAlgebra
    Module.Finite (Y.residueField (f η)) (X.residueField η) := by
  let _ := (f.residueFieldMap η).hom.toAlgebra
  obtain ⟨_, ⟨U : Y.Opens, hU, rfl⟩, hfη, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f η)) isOpen_univ
  obtain ⟨_, ⟨V : X.Opens, hV, rfl⟩, hηV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hfη (f ⁻¹ᵁ U).2
  have hνV : ν ∈ V := hνη.mem_open V.2 hηV
  let algSR : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  set P : Ideal Γ(X, V) := (hV.primeIdealOf ⟨η, hηV⟩).asIdeal
  set Q : Ideal Γ(Y, U) := (hU.primeIdealOf ⟨f η, hVU hηV⟩).asIdeal
  set P₀ : Ideal Γ(X, V) := (hV.primeIdealOf ⟨ν, hνV⟩).asIdeal
  have hPprime : P.IsPrime := (hV.primeIdealOf ⟨η, hηV⟩).isPrime
  have hQprime : Q.IsPrime := (hU.primeIdealOf ⟨f η, hVU hηV⟩).isPrime
  have hP₀prime : P₀.IsPrime := (hV.primeIdealOf ⟨ν, hνV⟩).isPrime
  -- `P₀ ≤ P` because `ν` specializes to `η`
  have hP₀P : P₀ ≤ P := by
    have h1 : (⟨ν, hνV⟩ : ↥V) ⤳ ⟨η, hηV⟩ := by
      rw [← Topology.IsInducing.subtypeVal.specializes_iff]; exact hνη
    have h2 : hV.primeIdealOf ⟨ν, hνV⟩ ⤳ hV.primeIdealOf ⟨η, hηV⟩ :=
      h1.map hV.isoSpec.hom.continuous
    exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr
      ((PrimeSpectrum.le_iff_specializes _ _).mpr h2)
  have hPQ : P.LiesOver Q :=
    ⟨(congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hηV)).symm⟩
  -- quasi-finiteness at `ν` read on the chart
  have htfae := (quasiFiniteAt_tfae f ν).out 1 4
  have hqfP₀ : Algebra.QuasiFiniteAt Γ(Y, U) P₀ :=
    htfae.mp hqf ⟨U, hU⟩ ⟨V, hV⟩ hνV hVU
  -- the local rings at `f η` and at `η`, as localizations of the charts
  let A := Localization.AtPrime Q
  let B := Localization.AtPrime P
  let algAB : Algebra A B := Localization.AtPrime.algebraOfLiesOver Q P
  have hliesAlg : Localization.AtPrime.IsLiesOverAlgebra Q P := ⟨rfl⟩
  have hlocalhom : IsLocalHom (algebraMap A B) := by infer_instance
  -- `A` is the stalk of `Y` at `f η`
  let algsec : Algebra Γ(Y, U) (Y.presheaf.stalk (f η)) :=
    Y.presheaf.algebra_section_stalk (⟨f η, hVU hηV⟩ : U)
  have hlocstalk : IsLocalization.AtPrime (Y.presheaf.stalk (f η)) Q :=
    hU.isLocalization_stalk ⟨f η, hVU hηV⟩
  let eA : Y.presheaf.stalk (f η) ≃ₐ[Γ(Y, U)] A :=
    IsLocalization.algEquiv Q.primeCompl _ _
  have hAnoeth : IsNoetherianRing A := isNoetherianRing_of_ringEquiv _ eA.toRingEquiv
  have hAdim : ringKrullDim A ≤ 1 := by
    rw [← ringKrullDim_eq_of_ringEquiv eA.toRingEquiv]; exact hYdim
  -- the prime of `B` determined by `P₀`
  have hqprime : (Ideal.map (algebraMap Γ(X, V) B) P₀).IsPrime :=
    Ideal.isPrime_map_of_isLocalizationAtPrime P (S := B) hP₀P
  have hqunder : Ideal.under Γ(X, V) (Ideal.map (algebraMap Γ(X, V) B) P₀) = P₀ :=
    Ideal.under_map_of_isLocalizationAtPrime P (S := B) hP₀P
  have towSRB : IsScalarTower Γ(Y, U) Γ(X, V) B := by infer_instance
  have hqQF : Algebra.QuasiFiniteAt Γ(Y, U) (Ideal.map (algebraMap Γ(X, V) B) P₀) :=
    Algebra.QuasiFiniteAt.of_surjectiveOnStalks P₀ (IsScalarTower.toAlgHom Γ(Y, U) Γ(X, V) B)
      (RingHom.surjectiveOnStalks_of_isLocalization P.primeCompl B) _ hqunder.symm
  have towSAB : IsScalarTower Γ(Y, U) A B := by infer_instance
  have towSAq : IsScalarTower Γ(Y, U) A
      (Localization.AtPrime (Ideal.map (algebraMap Γ(X, V) B) P₀)) := by infer_instance
  have hqQFA : Algebra.QuasiFiniteAt A (Ideal.map (algebraMap Γ(X, V) B) P₀) :=
    Algebra.QuasiFinite.of_restrictScalars Γ(Y, U) A _
  have hfinQP : Module.Finite Q.ResidueField P.ResidueField :=
    IsLocalRing.finite_residueField_of_quasiFiniteAt
      (Ideal.map (algebraMap Γ(X, V) B) P₀) hAdim
  -- transport the finiteness to the residue fields of the schemes
  let algYrf : Algebra Γ(Y, U) (Y.residueField (f η)) :=
    (Y.evaluation U (f η) (hVU hηV)).hom.toAlgebra
  let algXrf : Algebra Γ(X, V) (X.residueField η) := (X.evaluation V η hηV).hom.toAlgebra
  let eY := hU.residueFieldAlgEquivIdealResidueField (hVU hηV) Q rfl
  let eX := hV.residueFieldAlgEquivIdealResidueField hηV P rfl
  have hext : ∀ g₁ g₂ : Q.ResidueField →+* X.residueField η,
      (∀ s : Γ(Y, U), g₁ (algebraMap Γ(Y, U) Q.ResidueField s)
        = g₂ (algebraMap Γ(Y, U) Q.ResidueField s)) → g₁ = g₂ := by
    intro g₁ g₂ h
    refine IsLocalization.ringHom_ext (nonZeroDivisors (Γ(Y, U) ⧸ Q)) (RingHom.ext fun a => ?_)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    simpa [Ideal.algebraMap_quotient_residueField_mk] using h a
  refine Module.Finite.of_equiv_equiv eY.toRingEquiv.symm eX.toRingEquiv.symm
    (hext _ _ fun s => ?_)
  have hY1 : eY.toRingEquiv.symm (algebraMap Γ(Y, U) Q.ResidueField s)
      = algebraMap Γ(Y, U) (Y.residueField (f η)) s := eY.symm.commutes s
  have hX1 : eX.toRingEquiv.symm
        (algebraMap Γ(X, V) P.ResidueField (algebraMap Γ(Y, U) Γ(X, V) s))
      = algebraMap Γ(X, V) (X.residueField η) (algebraMap Γ(Y, U) Γ(X, V) s) :=
    eX.symm.commutes _
  have hQP : algebraMap Q.ResidueField P.ResidueField
        (algebraMap Γ(Y, U) Q.ResidueField s)
      = algebraMap Γ(X, V) P.ResidueField (algebraMap Γ(Y, U) Γ(X, V) s) := by
    rw [← IsScalarTower.algebraMap_apply Γ(Y, U) Q.ResidueField P.ResidueField,
      ← IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) P.ResidueField]
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
  rw [hY1, hQP, hX1]
  exact (DFunLike.congr_fun
    (congrArg CommRingCat.Hom.hom (appLE_comp_evaluation f hVU ⟨η, hηV⟩)) s).symm

/-- A point of a fibre is closed there as soon as the point of the fibre over the same image
point it determines is. -/
private lemma isClosed_singleton_fiberHomeo_symm (f : X ⟶ Y) {η : X} {y : Y} (hy : f η = y)
    (h : IsClosed ({f.asFiber η} : Set (f.fiber (f η)))) :
    IsClosed ({(f.fiberHomeo y).symm ⟨η, hy⟩} : Set (f.fiber y)) := by
  subst hy
  exact h

/-- **The fibre dimension over a point of codimension at most one.** Let `f` be locally of
finite type and let `x` be a point of the source whose image has Noetherian local ring of Krull
dimension at most one. If the fibre through every generic point of an irreducible component of
the source containing `x` has dimension zero there, then so does the fibre through `x`.

This is the case `d = 0` of the Stacks Project's formula for the dimension of a fibre over a
point of codimension at most one. -/
public theorem topologicalKrullDimAt_fiber_eq_zero_of_ringKrullDim_stalk_le_one
    (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X)
    (hY : IsNoetherianRing (Y.presheaf.stalk (f x)))
    (hYdim : ringKrullDim (Y.presheaf.stalk (f x)) ≤ 1)
    (hgen : ∀ η : X, closure {η} ∈ irreducibleComponents X → x ∈ closure {η} →
      topologicalKrullDimAt (f.fiber (f η)) (f.asFiber η) = 0) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = 0 := by
  have hqf : ∀ η : X, closure {η} ∈ irreducibleComponents X → x ∈ closure {η} →
      quasiFiniteAt f η := fun η h₁ h₂ =>
    (quasiFiniteAt_iff_fiberDimensionAt_eq_zero f η).mpr (hgen η h₁ h₂)
  -- every point whose closure contains `x` is the specialization of a point at which `f` is
  -- quasi-finite, namely the generic point of an irreducible component through it
  have hspec : ∀ z : X, x ∈ closure {z} → ∃ w : X, w ⤳ z ∧ quasiFiniteAt f w := by
    intro z hz
    let Z : irreducibleComponents X :=
      ⟨irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩
    refine ⟨genericPoints.ofComponent Z,
      (genericPoints.isGenericPoint_ofComponent Z).specializes mem_irreducibleComponent,
      hqf _ (genericPoints.ofComponent Z).2 ?_⟩
    rw [(genericPoints.isGenericPoint_ofComponent Z).def]
    exact closure_minimal (Set.singleton_subset_iff.mpr mem_irreducibleComponent)
      isClosed_irreducibleComponent hz
  obtain ⟨w, hwx, hqfw⟩ := hspec x (subset_closure rfl)
  refine le_antisymm ?_ ?_
  · -- the local dimension of the fibre is the largest dimension of a component through the point
    have hft : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
      show LocallyOfFiniteType (Limits.pullback.snd f (Y.fromSpecResidueField (f x)))
      infer_instance
    rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents (Y.residueField (f x))
      (f.fiber (f x)) (f.fiberToSpecResidueField (f x)) (f.asFiber x)]
    refine iSup_le fun C => iSup_le fun hC => ?_
    obtain ⟨hCcomp, hzC⟩ := hC
    -- the generic point of the component, and the point of `X` it comes from
    set ξ : f.fiber (f x) := hCcomp.1.genericPoint
    have hξC : IsGenericPoint ξ C :=
      hCcomp.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hCcomp)
    set η : X := f.fiberι (f x) ξ
    have hηy : f η = f x := (f.range_fiberι (f x)).subset ⟨ξ, rfl⟩
    have hηx : η ⤳ x := by
      have h := (hξC.specializes hzC).map (f.fiberι (f x)).continuous
      rwa [Scheme.Hom.fiberι_asFiber] at h
    -- `f` is quasi-finite at a generalization of `η`
    obtain ⟨v, hvη, hqfv⟩ := hspec η (specializes_iff_mem_closure.mp hηx)
    have hfin := finite_residueField_of_quasiFiniteAt_specializes f hvη
      (hηy ▸ hY) (hηy ▸ hYdim) hqfv
    -- hence `η` is closed in its fibre, so the component is a single point
    have hclosed : IsClosed ({(f.fiberHomeo (f x)).symm ⟨η, hηy⟩} : Set (f.fiber (f x))) :=
      isClosed_singleton_fiberHomeo_symm f hηy
        ((isClosed_asFiber_iff_finite_residueField f η).mpr hfin)
    have hξeq : (f.fiberHomeo (f x)).symm ⟨η, hηy⟩ = ξ :=
      (f.fiberι (f x)).isEmbedding.injective (Scheme.Hom.fiberι_fiberHomeo_symm f (f x) _)
    rw [hξeq] at hclosed
    have hCsingle : C = {ξ} := by rw [← hξC.def, hclosed.closure_eq]
    have : Subsingleton (C : Type u) := by rw [hCsingle]; infer_instance
    exact topologicalKrullDim_zero_of_discreteTopology _
  · rw [← (quasiFiniteAt_iff_fiberDimensionAt_eq_zero f w).mp hqfw]
    exact fiberDimensionAt_le_of_specializes f hwx

end AlgebraicGeometry

end
