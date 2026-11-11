module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalEtaleLocalStructureAssembly
public import StacksFrontier.AlgebraicGeometry.NodalContraction.SmoothAt
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.RingTheory.NodalChart.Smooth

/-!
# Nodal chart neighbourhoods of an at-worst-nodal family

Let `f : X ⟶ S` be at-worst-nodal of relative dimension one. At every point `x` of `X` the family
is, étale locally on source and target, a nodal chart `Spec B[u, v]/(uv - h)` over an affine
étale neighbourhood `Spec B` of the image of `x`; this is the chart form
`Stacks.NodalEtaleLocalStructure.NodalChartNeighbourhood f x` of the étale local structure.

The two cases are those of the proof of [Stacks, Tag 0CDD].

* At a point where the fibre is singular, [Stacks, Tag 0CBY]
  (`Stacks.NodalEtaleLocalStructure.nonempty_standardNodalDiagram_of_isAtWorstNodal`) gives the
  diagram `StandardNodalDiagram f x`. Its étale base `V` is shrunk to an affine open `Spec B`
  around the image of the chosen point; there the parameter `V ⟶ Spec ℤ[a]` is an element `h` of
  `B`, and the local model, being the base change of the standard family along it, is the nodal
  chart `Spec B[u, v]/(uv - h)` (`Stacks.NodalEtaleLocalStructure.chartIsoOfIsPullback`).
* At a point where the fibre is smooth, `f` is smooth at `x` (flatness and [Stacks, Tag 01V9]),
  and its fibre has dimension one there; a standard smooth chart around `x` then has relative
  dimension one, so it is étale over the affine line `Spec A[t]` ([Stacks, Tag 054L]). After the
  translation `t ↦ t + 1` if necessary the image of `x` lies in the standard open `D(t)`, whose
  coordinate ring `A[t]_t` is the nodal chart `A[u, v]/(uv - 1)`.

## Main results

* `Stacks.NodalEtaleLocalStructure.StandardNodalDiagram.nonempty_nodalChartNeighbourhood` — the
  diagram form of Tag 0CBY gives the chart form.
* `AlgebraicGeometry.exists_affine_chart_isStandardSmoothOfRelativeDimension` — a smooth
  morphism has, at a point whose fibre has dimension `n`, an affine chart which is standard smooth
  of relative dimension `n`.
* `Stacks.NodalEtaleLocalStructure.nonempty_nodalChartNeighbourhood_one_of_smoothAt` — at a smooth
  point with one-dimensional fibre the chart form holds with parameter `1`.
* `Stacks.NodalEtaleLocalStructure.nonempty_nodalChartNeighbourhood_of_atWorstNodal` — the chart
  form at every point of an at-worst-nodal family of relative dimension one.

## References

* [Stacks Project, Tag 0CBY](https://stacks.math.columbia.edu/tag/0CBY)
* [Stacks Project, Tag 054L](https://stacks.math.columbia.edu/tag/054L)
* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks

universe u

namespace AlgebraicGeometry

/-- **A standard smooth chart of prescribed relative dimension.** If `f` is smooth and its fibre
through `x` has dimension `n` at `x`, there are affine opens `U` of the target and `V ∋ x` of the
source, with `V` mapping into `U`, on which `f` is standard smooth of relative dimension `n`: a
standard smooth chart computes the local fibre dimension as the dimension of its presentation. -/
public theorem exists_affine_chart_isStandardSmoothOfRelativeDimension {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Smooth f] (x : X) (n : ℕ)
    (hdim : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = n) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V)
      (hVU : V ≤ f ⁻¹ᵁ U), (f.appLE U V hVU).hom.IsStandardSmoothOfRelativeDimension n := by
  obtain ⟨U, hU, V, hV, hxV, hVU, hstd⟩ := Smooth.exists_isStandardSmooth f x
  have : IsAffine V.toScheme := hV
  have : IsAffine U.toScheme := hU
  let A := ToType Γ(Y, U)
  let B := ToType Γ(X, V)
  let : Algebra A B := (f.appLE U V hVU).hom.toAlgebra
  have hs : Algebra.IsStandardSmooth A B := hstd.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hs.out
  let : P.toPresentation.IsRelativeGlobalCompleteIntersection :=
    P.isRelativeGlobalCompleteIntersection
  let j : Spec Γ(X, V) ⟶ X := hV.fromSpec
  let i : Spec Γ(Y, U) ⟶ Y := hU.fromSpec
  let g : Spec Γ(X, V) ⟶ Spec Γ(Y, U) := Spec.map (f.appLE U V hVU)
  have hcomp : j ≫ f = g ≫ i := (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU).symm
  let q : Spec (CommRingCat.of B) := hV.primeIdealOf ⟨x, hxV⟩
  have hjq : j q = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hdimP : P.dimension = n := by
    have hdimP' : topologicalKrullDimAt (g.fiber (g q)) (g.asFiber q) =
        (P.dimension : WithBot ℕ∞) := by
      simpa [Algebra.Presentation.dimension, g, RingHom.algebraMap_toAlgebra] using
        AlgebraicGeometry.fiberDimensionAt_eq_card_sub_card P.toPresentation q
    rw [fiberDimensionAt_eq_of_open_square j f g i hcomp q, hjq, hdim] at hdimP'
    exact_mod_cast hdimP'.symm
  exact ⟨U, hU, V, hV, hxV, hVU, P.isStandardSmoothOfRelativeDimension hdimP⟩

end AlgebraicGeometry

namespace Stacks.NodalEtaleLocalStructure

/-- Two ring maps out of the integers, placed in any universe, agree. -/
private theorem ringHom_ulift_int_ext {B : Type u} [CommRing B] (φ ψ : ULift.{u} ℤ →+* B) :
    φ = ψ := by
  have h := RingHom.ext_int (φ.comp (ULift.ringEquiv (R := ℤ)).symm.toRingHom)
    (ψ.comp (ULift.ringEquiv (R := ℤ)).symm.toRingHom)
  ext n
  exact RingHom.congr_fun h n.down

/-- **The diagram form of Tag 0CBY gives the chart form.** Shrink the étale base `V` of the
diagram to an affine open `Spec B` around the image of the chosen point. The parameter
`Spec B ⟶ V ⟶ Spec ℤ[a]` classifies an element `h` of `B`, and the restriction of the local
model `W` to `Spec B` is the base change of the standard family along it, hence the nodal chart
`Spec B[u, v]/(uv - h)`. -/
public theorem StandardNodalDiagram.nonempty_nodalChartNeighbourhood {X S : Scheme.{u}}
    {f : X ⟶ S} {x : X} (d : StandardNodalDiagram f x) :
    Nonempty (NodalChartNeighbourhood f x) := by
  have := d.etale_toSource
  have := d.etale_toBase
  have := d.etale_toModel
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hv, -⟩ := d.V.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (d.familyU d.pt)) isOpen_univ
  let j : Spec Γ(d.V, V₀) ⟶ d.V := hV₀.fromSpec
  have : IsOpenImmersion j := hV₀.isOpenImmersion_fromSpec
  obtain ⟨b, hb⟩ : d.familyU d.pt ∈ Set.range j.base := by rwa [hV₀.range_fromSpec]
  let φ : Polynomial (ULift.{u} ℤ) →+* Γ(d.V, V₀) := (Spec.preimage (j ≫ d.classifyV)).hom
  have hφ : nodalParameterMap (intRingHom Γ(d.V, V₀)) (φ Polynomial.X) = j ≫ d.classifyV := by
    rw [nodalParameterMap, ← eq_eval₂RingHom (intRingHom _) φ (ringHom_ulift_int_ext _ _)]
    exact Spec.map_preimage _
  have hW : IsPullback (pullback.fst d.familyW j ≫ d.classifyW) (pullback.snd d.familyW j)
      (standardNodalFamily (ULift.{u} ℤ))
      (nodalParameterMap (intRingHom Γ(d.V, V₀)) (φ Polynomial.X)) := by
    rw [hφ]
    exact (IsPullback.of_hasPullback d.familyW j).paste_horiz d.isPullback_model
  let eW := chartIsoOfIsPullback (intRingHom Γ(d.V, V₀)) (φ Polynomial.X) hW
  have heW : eW.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap Γ(d.V, V₀) (nodalChartRing Γ(d.V, V₀) (φ Polynomial.X)))) =
      pullback.snd d.familyW j :=
    IsPullback.isoIsPullback_hom_snd _ _ _ (isPullback_specMap_chartClassify _ _)
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := d.familyW) (g := j)
    (d.toModel d.pt) b (by
      rw [hb]
      exact congrArg (fun k : d.U ⟶ d.V => k d.pt) d.comm_model)
  obtain ⟨u, hu₁, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := d.toModel) (g := pullback.fst d.familyW j) d.pt w hw₁.symm
  refine ⟨{
    base := Γ(d.V, V₀)
    param := φ Polynomial.X
    U := pullback d.toModel (pullback.fst d.familyW j)
    toSource := pullback.fst d.toModel (pullback.fst d.familyW j) ≫ d.toSource
    toBase := j ≫ d.toBase
    toChart := pullback.snd d.toModel (pullback.fst d.familyW j) ≫ eW.hom
    pt := u
    etale_toSource := inferInstance
    etale_toBase := inferInstance
    etale_toChart := inferInstance
    pt_mem := ?_
    comm := ?_ }⟩
  · change d.toSource (pullback.fst d.toModel (pullback.fst d.familyW j) u) = x
    rw [hu₁]
    exact d.pt_mem
  · rw [Category.assoc, Category.assoc, reassoc_of% heW, d.comm_left, ← d.comm_model,
      Category.assoc, pullback.condition_assoc, pullback.condition_assoc (f := d.familyW)]

/-- The translation `t ↦ t + c` by `c = 0` or `c = 1` moves the coordinate of `A[t]` out of
any given prime of `B`, for a ring map `A[t] → B`. -/
private theorem exists_map_X_add_C_notMem {A B : Type*} [CommRing A] [CommRing B]
    (g : MvPolynomial (Fin 1) A →+* B) {p : Ideal B} (hp : p.IsPrime) :
    ∃ c : A, g (MvPolynomial.X 0 + MvPolynomial.C c) ∉ p := by
  by_cases ha : g (MvPolynomial.X 0) ∈ p
  · refine ⟨1, fun h ↦ hp.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)⟩
    simpa using p.sub_mem h ha
  · exact ⟨0, by simpa using ha⟩

/-- The translation `t ↦ t + c` is a ring isomorphism `A[t] ≃ A[t]`. -/
private theorem bijective_eval₂RingHom_X_add_C {A : Type*} [CommRing A] (c : A) :
    Function.Bijective (Polynomial.eval₂RingHom (MvPolynomial.C : A →+* MvPolynomial (Fin 1) A)
      (MvPolynomial.X 0 + MvPolynomial.C c)) := by
  let φ : Polynomial A →+* MvPolynomial (Fin 1) A :=
    Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0 + MvPolynomial.C c)
  let φinv : MvPolynomial (Fin 1) A →+* Polynomial A :=
    MvPolynomial.eval₂Hom Polynomial.C (fun _ ↦ Polynomial.X - Polynomial.C c)
  refine Function.bijective_iff_has_inverse.mpr ⟨φinv, fun p ↦ ?_, fun p ↦ ?_⟩
  · have : φinv.comp φ = RingHom.id _ := Polynomial.ringHom_ext (fun a ↦ by simp [φ, φinv])
      (by simp [φ, φinv])
    exact RingHom.congr_fun this p
  · have : φ.comp φinv = RingHom.id _ :=
      MvPolynomial.ringHom_ext (fun a ↦ by simp [φ, φinv]) (fun i ↦ by
        fin_cases i
        simp [φ, φinv])
    exact RingHom.congr_fun this p

/-- If `g : A[t] → B` is étale over `f : A → B`, then `A[u, v]/(uv - 1)` maps étale to the
localization of `B` away from the image `e` of the translated coordinate `t + c`, compatibly
with `f`. -/
private theorem exists_etale_nodalChartRing_one_of_etale_mvPolynomial {A B : Type u} [CommRing A]
    [CommRing B] (g : MvPolynomial (Fin 1) A →+* B) (hgE : g.Etale) (c : A) (f : A →+* B)
    (hgC : g.comp MvPolynomial.C = f) :
    ∃ ψ : nodalChartRing A 1 →+* Localization.Away (g (MvPolynomial.X 0 + MvPolynomial.C c)),
      ψ.Etale ∧ ψ.comp (algebraMap A (nodalChartRing A 1)) = (algebraMap B _).comp f := by
  let e : B := g (MvPolynomial.X 0 + MvPolynomial.C c)
  let φ : Polynomial A →+* MvPolynomial (Fin 1) A :=
    Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0 + MvPolynomial.C c)
  let τ : Polynomial A →+* B := g.comp φ
  have hτE : τ.Etale := RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (bijective_eval₂RingHom_X_add_C c)) hgE
  have hτX : τ Polynomial.X = e := by simp [τ, φ, e]
  have hτC (a : A) : τ (Polynomial.C a) = f a := by simp [τ, φ, ← hgC]
  let L := Localization.Away e
  have : IsLocalization ((Submonoid.powers (Polynomial.X : Polynomial A)).map τ) L := by
    rw [Submonoid.map_powers, hτX]
    infer_instance
  let ψ₀ : Localization.Away (Polynomial.X : Polynomial A) →+* L :=
    IsLocalization.map L τ (Submonoid.powers (Polynomial.X : Polynomial A)).le_comap_map
  have hψ₀ : ψ₀.Etale := RingHom.Etale.isStableUnderBaseChange.isLocalization_map
    (Submonoid.powers (Polynomial.X : Polynomial A)) τ hτE
  refine ⟨ψ₀.comp (nodalChartRingOneEquiv A).toRingHom, RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (nodalChartRingOneEquiv A).bijective) hψ₀, ?_⟩
  ext a
  simp only [ψ₀, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe,
    AlgEquiv.commutes]
  rw [IsScalarTower.algebraMap_apply A (Polynomial A), Polynomial.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, IsLocalization.map_eq, hτC]

/-- **At a smooth point with one-dimensional fibre the chart form holds with parameter `1`.** A
standard smooth chart of relative dimension one is étale over the affine line `Spec A[t]`. After
replacing `t` by `t + 1` if necessary the chosen point lies over the standard open `D(t)`, and
`A[t]_t` is the nodal chart `A[u, v]/(uv - 1)`. -/
public theorem nonempty_nodalChartNeighbourhood_one_of_smoothAt {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (hf : InfinitesimalLifting.SmoothAt f x)
    (hdim : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = 1) :
    Nonempty (NodalChartNeighbourhood f x) := by
  classical
  obtain ⟨U₀, hxU₀, hU₀⟩ := (InfinitesimalLifting.smoothAt_iff_exists_open_smooth_comp f x).mp hf
  let f' := U₀.ι ≫ f
  let x' : U₀.toScheme := ⟨x, hxU₀⟩
  have hd : topologicalKrullDimAt (f'.fiber (f' x')) (f'.asFiber x') = ((1 : ℕ) : WithBot ℕ∞) :=
    (fiberDimensionAt_eq_of_open_square U₀.ι f f' (𝟙 S) (by simp [f']) x').trans
      (by exact_mod_cast hdim)
  obtain ⟨U, hU, V, hV, hxV, hVU, hsd⟩ :=
    exists_affine_chart_isStandardSmoothOfRelativeDimension f' x' 1 hd
  obtain ⟨g, hgC, hgE⟩ := hsd.exists_etale_mvPolynomial
  let A := Γ(S, U)
  let B := Γ(U₀.toScheme, V)
  let q : Spec B := hV.primeIdealOf ⟨x', hxV⟩
  have hq : hV.fromSpec q = x' := hV.fromSpec_primeIdealOf ⟨x', hxV⟩
  obtain ⟨c, hc⟩ := exists_map_X_add_C_notMem g q.isPrime
  let e := g (MvPolynomial.X 0 + MvPolynomial.C c)
  let L := Localization.Away e
  obtain ⟨ψ, hψE, hψalg⟩ : ∃ ψ : nodalChartRing A 1 →+* L, ψ.Etale ∧
      ψ.comp (algebraMap A (nodalChartRing A 1)) =
        (algebraMap B L).comp (f'.appLE U V hVU).hom :=
    exists_etale_nodalChartRing_one_of_etale_mvPolynomial g hgE c _ hgC
  have : Algebra.Etale B L := Algebra.Etale.of_isLocalizationAway e
  obtain ⟨q', hq'⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap B L)) := by
    rwa [PrimeSpectrum.localization_away_comap_range L e]
  refine ⟨{
    base := A
    param := 1
    U := Spec (.of L)
    toSource := Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ hV.fromSpec ≫ U₀.ι
    toBase := hU.fromSpec
    toChart := Spec.map (CommRingCat.ofHom ψ)
    pt := q'
    etale_toSource := ?_
    etale_toBase := inferInstance
    etale_toChart := HasRingHomProperty.Spec_iff.mpr hψE
    pt_mem := ?_
    comm := ?_ }⟩
  · have : Etale (Spec.map (CommRingCat.ofHom (algebraMap B L))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
    infer_instance
  · change U₀.ι (hV.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap B L)) q')) = x
    rw [show Spec.map (CommRingCat.ofHom (algebraMap B L)) q' = q from hq', hq]
    rfl
  · simp only [Category.assoc]
    rw [show U₀.ι ≫ f = f' from rfl, ← IsAffineOpen.SpecMap_appLE_fromSpec f' hU hV hVU,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_hom (f'.appLE U V hVU),
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hψalg]

/-- **The chart form of the étale local structure at every point of a nodal family.** Let
`f : X ⟶ S` be at-worst-nodal of relative dimension one and `x` a point of `X`. If the fibre is
singular at `x` this is [Stacks, Tag 0CBY] read in chart form; if the fibre is smooth at `x`,
then `f` is smooth at `x` and its fibre has dimension one, and the chart has parameter `1`. -/
public theorem nonempty_nodalChartNeighbourhood_of_atWorstNodal {X S : Scheme.{u}}
    (f : X ⟶ S) (hf : IsAtWorstNodalOfRelativeDimensionOne f) (x : X) :
    Nonempty (NodalChartNeighbourhood f x) := by
  by_cases hsm : InfinitesimalLifting.SmoothAt (f.fiberToSpecResidueField (f x)) (f.asFiber x)
  · have : LocallyOfFinitePresentation f := locallyOfFinitePresentation hf.1.1
    exact nonempty_nodalChartNeighbourhood_one_of_smoothAt f x
      (smoothAt_of_flat_of_smoothAt_fiber f (flat hf.1.1) x hsm) (by exact_mod_cast hf.1.2 x)
  · obtain ⟨d⟩ := nonempty_standardNodalDiagram_of_isAtWorstNodal f hf hsm
    exact StandardNodalDiagram.nonempty_nodalChartNeighbourhood d

end Stacks.NodalEtaleLocalStructure

end
