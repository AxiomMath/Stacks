module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.PrimeIdealOfTop
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.BaseChangeEtaleChart
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ChartEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormulaGeneral
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.QuasiFiniteSlices

/-!
# Feeding the globalization of Stacks Tag 0CAW its two sides

The proof of Stacks Tag 0CAW ends with two rings and a prime of each: an étale algebra `D` over
an affine chart of `S`, whose spectrum is the `V` of the tag, and an étale algebra over the chart
ring `B ⊗_C D` of `Y ×_{T, τ} V`, whose spectrum is the `W`. The passage from such data to an
elementary étale neighbourhood is `AlgebraicGeometry.IsAffineOpen.etaleNeighborhoodOfChart`
(`ChartEtaleNeighborhood.lean`), stated for an arbitrary scheme and point. This file performs the
two *feedings* of that machinery: it hands it the data of the `V` side at `(S, s)`, and the data
of the `W` side at `(Y ×_{T, τ} V, (y, v))`.

The two sides are not symmetric, and only one of them needs a theorem.

On the `V` side the chart of `S` is given, so the only work is the morphism to the second base:
a ring map `C = Γ(T, W_T) → D` compatible with `R = Γ(S, U_S) → D` over `R → C` determines
`τ : Spec D ⟶ T` with `τ ≫ h = V.toBase`, and the prime of `D` lying over the prime of `t`
makes `τ v = t`. Both are `AlgebraicGeometry.IsAffineOpen.specMap_fromSpec_comp` and
`AlgebraicGeometry.IsAffineOpen.specMap_fromSpec_apply` applied verbatim, so
`StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_chart_over` below is a
composition of existing lemmas and proves nothing new; it is stated because its conclusion is
exactly the input of the `W` side, including the inequality `⊤ ≤ τ ⁻¹ᵁ W_T` that the chart
lemmas of `BaseChangeSpecChart.lean` require.

On the `W` side the chart is *not* given: the scheme is a fibre product, and the chart of it that
the construction works in — `pr₁ ⁻¹ᵁ V_Y`, affine by
`AlgebraicGeometry.isAffineOpen_preimage_pullback_fst_of_preimage_eq_top` with ring of sections
`D ⊗_{Γ(T, W_T)} Γ(Y, V_Y)` by
`AlgebraicGeometry.exists_ringEquiv_tensorProduct_sections_pullback_fst_of_preimage_eq_top` —
carries the point `(y, v)` only as a prime of that tensor product, and the two projections of
the point have to be read off from the two contractions of the prime. That is the content of
`StacksDraft.ArtinApproximation.exists_point_etale_chart_pullback_tensorProduct`.

## Main results

* `StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_chart_over`: the `V` side.
  An étale algebra `D` over an affine chart of `S` with a residually trivial prime over the prime
  of `s`, together with a compatible ring map from an affine chart of `T`, gives an elementary
  étale neighbourhood `(V, v)` of `(S, s)` and a morphism `τ : V ⟶ T` over `S` carrying `v` to
  `t` and factoring through the chart of `T`.
* `StacksDraft.ArtinApproximation.exists_point_etale_chart_pullback_tensorProduct`: the `W` side.
  A prime `q` of `Γ(Y, V_Y) ⊗_{Γ(T, W_T)} Λ` contracting to the prime of `y` on the left and to
  a prime `v` of `Λ` on the right cuts out a point of `Y ×_T Spec Λ` whose two projections are
  `y` and `v`; and an étale ring map out of that tensor product with a residually trivial prime
  becomes an étale ring map out of the chart ring of `Y ×_T Spec Λ` with a residually trivial
  prime over the prime of that point — which is what
  `AlgebraicGeometry.IsAffineOpen.etaleNeighborhoodOfChart` and
  `AlgebraicGeometry.IsAffineOpen.isElementary_etaleNeighborhoodOfChart` consume.
* `StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_pair_chart`: the two
  composed. The `V` side's `τ` is the `W` side's `b`, and the `W` side's two chart hypotheses hold
  of it by construction, so one statement carries both neighbourhoods: from the ring data of the
  source's last step it produces clause (2), the `v`-and-`τ` part of clause (1), the
  `w ↦ (y, v)` part of clause (1), and clause (4).

## Implementation notes

*What is and is not proved.* These are steps of the proof of Tag 0CAW, not clauses of it, and
nothing here is registered for it. Clauses (4) and (5) of Tag 0CAW are **not** proved by this
file: the `W` side's theorem takes as hypotheses the étale ring map and the two primes, which at
Tag 0CAW's own data are produced by
`Ideal.exists_isPrime_comap_eq_and_residueField_map_bijective_tensorProduct_of_descent`
(`StacksFrontier/RingTheory/Flat/ElementaryEtaleStageDescent.lean`) out of the descent of the
earlier steps, and the chaining of the six steps of the source's proof that reaches that data —
together with the chase of clause (5) through the replacement of `B'` by the base change of
`B''`, and clause (3) — is not carried out here. The same is true of the composition
`exists_elementaryEtaleNeighborhood_pair_chart`: it shows that the two feedings fit together and
that the four clause fragments listed above follow from the ring data, which is not the same as
following from Tag 0CAW's hypotheses. The two clause-wise registrations of Tag 0CAW remain
`StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_baseApproximation` and
`StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_relativeApproximation`.

*Why the `W` side does not state the neighbourhood itself.* The hypothesis of
`AlgebraicGeometry.IsAffineOpen.etaleNeighborhoodOfChart` is étaleness of a *morphism of schemes*,
`Etale (Spec.map (CommRingCat.ofHom ρ))`, which is an instance argument; producing the
neighbourhood inside an existential would therefore force the étaleness witness to be bound by
the existential and re-installed as an instance inside it. The theorem instead returns the chart,
the ring map `ρ`, its étaleness as a `RingHom.Etale`, the contraction of the prime and the
bijectivity of the residue field extension — all five arguments of
`etaleNeighborhoodOfChart` and of `isElementary_etaleNeighborhoodOfChart` — so that a caller
builds the neighbourhood and its elementariness in two lines.

*Why the tensor factors are in the order `Γ(Y, V_Y) ⊗ Λ`.* That is the order of the source's
`B ⊗_C D`, and the order in which the prime of the point `(y, v)` and the prime of `w` are
produced by the descent. The chart lemma
`AlgebraicGeometry.exists_ringEquiv_tensorProduct_sections_pullback_fst_of_preimage_eq_top`
produces the other order, `Λ ⊗ Γ(Y, V_Y)`, inherited from
`AlgebraicGeometry.sectionsTensorEquiv`; the exchange is performed inside the proof by
`Algebra.TensorProduct.comm`, so that the statement speaks the order its consumer holds.

*Why the two legs of `ρ` are pinned down.* Without them the conclusion would be the existence of
*some* étale ring map out of *some* chart ring, which says nothing: the content is that the
`Λ`-algebra and `Γ(Y, V_Y)`-algebra structures on the chart ring are the geometric ones. So
`ρ` is computed on the restrictions of `pr₁` and of `pr₂` on sections, the latter read through
`AlgebraicGeometry.Scheme.ΓSpecIso` since `Λ` is not literally `Γ(Spec Λ, ⊤)`.

*Why `Λ` is not assumed local.* On the `W` side of Tag 0CAW the second factor is `V = Spec D`
with `D` an étale algebra over a chart ring, which is not local; what holds instead is that `τ`
factors through the chart `W_T` of `T` by construction, and that is the hypothesis `hbT`. A
caller whose `b` is `Spec.map (CommRingCat.ofHom c) ≫ hWT.fromSpec` — which is the only case
that arises — discharges `hbT` by `AlgebraicGeometry.preimage_fromSpec_comp` and the algebra
hypothesis `hΛ` by `AlgebraicGeometry.appLE_fromSpec_comp`, as the `V` side's theorem does.

## References

* [Stacks Project, Tag 0CAW](https://stacks.math.columbia.edu/tag/0CAW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct IsLocalRing AlgebraicGeometry

universe u

namespace StacksDraft.ArtinApproximation

attribute [local instance] PrimeSpectrum.isPrime

/-! ### The `V` side: the neighbourhood of `(S, s)` and its morphism to `T` -/

/-- The chart morphism built from `c : Γ(T, W_T) → D` lies over the one built from `c ∘ h^♯`. -/
private theorem specMap_fromSpec_comp_eq_of_comp_eq {S T : Scheme.{u}} (h : T ⟶ S)
    {US : S.Opens} (hUS : IsAffineOpen US) {WT : T.Opens} (hWT : IsAffineOpen WT)
    (hWU : WT ≤ h ⁻¹ᵁ US) {D : Type u} [CommRing D] (r : Γ(S, US) →+* D) (c : Γ(T, WT) →+* D)
    (hc : c.comp (h.appLE US WT hWU).hom = r) :
    (Spec.map (CommRingCat.ofHom c) ≫ hWT.fromSpec) ≫ h =
      Spec.map (CommRingCat.ofHom r) ≫ hUS.fromSpec :=
  (hWT.specMap_fromSpec_comp h hUS hWU c).trans
    (congrArg (fun k : Γ(S, US) →+* D => Spec.map (CommRingCat.ofHom k) ≫ hUS.fromSpec) hc)

/-- **The `V` side of the last step of Stacks Tag 0CAW.** Let `h : T ⟶ S`, let `U_S` be an affine
open of `S` containing `s`, let `W_T` be an affine open of `T` containing `t` with
`W_T ≤ h ⁻¹ᵁ U_S`, let `r : Γ(S, U_S) → D` have étale spectrum, and let `c : Γ(T, W_T) → D`
satisfy `c ∘ h^♯ = r`. If a prime `v` of `D` contracts to the prime of `s` along `r` with
bijective residue field extension, and to the prime of `t` along `c`, then `Spec D` is an
elementary étale neighbourhood of `(S, s)` at `v` and carries a morphism `τ` to `T` over `S`
with `τ v = t` which factors through `W_T`.

Read at Tag 0CAW, `D` is the ring the final application of Tag 0CAU produces, `V = Spec D` is the
tag's `V`, and `τ` is the tag's `τ`; the conclusion is clause (1) for `v` and `τ` together with
clause (2), and the last inequality is the hypothesis that the chart lemmas of the `W` side need.

Nothing is proved here that is not already in the library: the neighbourhood is
`AlgebraicGeometry.IsAffineOpen.etaleNeighborhoodOfChart`, its elementariness is
`AlgebraicGeometry.IsAffineOpen.isElementary_etaleNeighborhoodOfChart`, the point identity is
`AlgebraicGeometry.IsAffineOpen.specMap_fromSpec_apply`, the triangle over `S` is
`AlgebraicGeometry.IsAffineOpen.specMap_fromSpec_comp`, and the inequality is
`AlgebraicGeometry.preimage_fromSpec_comp`. The theorem exists because its conclusion is exactly
the input of `StacksDraft.ArtinApproximation.exists_point_etale_chart_pullback_tensorProduct`.
Clauses (3), (4) and (5) of Tag 0CAW are not established by it, and nothing here is registered
for that tag. -/
theorem exists_elementaryEtaleNeighborhood_chart_over {S T : Scheme.{u}} (h : T ⟶ S)
    {US : S.Opens} (hUS : IsAffineOpen US) {WT : T.Opens} (hWT : IsAffineOpen WT)
    (hWU : WT ≤ h ⁻¹ᵁ US) {s : S} (hsU : s ∈ US) {t : T} (htW : t ∈ WT)
    {D : Type u} [CommRing D] (r : Γ(S, US) →+* D)
    [Etale (Spec.map (CommRingCat.ofHom r))] (c : Γ(T, WT) →+* D)
    (hc : c.comp (h.appLE US WT hWU).hom = r) (v : PrimeSpectrum D)
    (hvS : Ideal.comap r v.asIdeal = (hUS.primeIdealOf ⟨s, hsU⟩).asIdeal)
    (hvT : Ideal.comap c v.asIdeal = (hWT.primeIdealOf ⟨t, htW⟩).asIdeal)
    (hres : Function.Bijective
      (Ideal.ResidueField.map (hUS.primeIdealOf ⟨s, hsU⟩).asIdeal v.asIdeal r hvS.symm)) :
    ∃ V : EtaleNeighborhood S s, V.IsElementary ∧
      ∃ (τ : V.scheme ⟶ T) (_ : τ V.point = t), τ ≫ h = V.toBase ∧
        (⊤ : V.scheme.Opens) ≤ τ ⁻¹ᵁ WT :=
  ⟨hUS.etaleNeighborhoodOfChart hsU r v hvS,
    hUS.isElementary_etaleNeighborhoodOfChart hsU r v hvS hres,
    Spec.map (CommRingCat.ofHom c) ≫ hWT.fromSpec,
    hWT.specMap_fromSpec_apply htW c v hvT,
    specMap_fromSpec_comp_eq_of_comp_eq h hUS hWT hWU r c hc,
    (preimage_fromSpec_comp hWT (CommRingCat.ofHom c)).ge⟩

/-! ### The `W` side: the point of the base change and the étale map on its chart -/

/-- **The `W` side of the last step of Stacks Tag 0CAW.** Let `g : Y ⟶ T`, let
`b : Spec Λ ⟶ T` factor through an affine open `W_T` of `T` in the sense that
`⊤ ≤ b ⁻¹ᵁ W_T`, let `V_Y` be an affine open of `Y` over `W_T` containing `y`, and let `Λ` and
`Γ(Y, V_Y)` carry the `Γ(T, W_T)`-algebra structures the two restriction maps on sections give
them. Let `q` be a prime of `Γ(Y, V_Y) ⊗_{Γ(T, W_T)} Λ` contracting to the prime of `y` on the
left factor and to a prime `v` of `Λ` on the right, and let `r` be an étale ring map out of that
tensor product with a prime `Q` over `q` whose residue field extension is bijective.

Then the affine chart `pr₁ ⁻¹ᵁ V_Y` of `Y ×_T Spec Λ` contains a point `(y, v)` whose two
projections are `y` and `v`, and `r` becomes an étale ring map `ρ` out of the ring of sections of
that chart, carrying the prime of `(y, v)` back from `Q` with bijective residue field extension,
and equal on the two tensor factors to the restrictions on sections of `pr₁` and of `pr₂`.

Read at Tag 0CAW: `Λ = D` is the ring the final application of Tag 0CAU produces, `b = τ`,
`Γ(Y, V_Y) ⊗_{Γ(T, W_T)} Λ` is the source's `B ⊗_C D`, the prime `q` is the point `(y, v)` of
`Y ×_{T, τ} V`, and `r` with its prime `Q` is the étale algebra `B'' ⊗_{R'} D` with the point `w`
— both produced by
`Ideal.exists_isPrime_comap_eq_and_residueField_map_bijective_tensorProduct_of_descent`. Handing
the conclusion to `AlgebraicGeometry.IsAffineOpen.etaleNeighborhoodOfChart` and
`AlgebraicGeometry.IsAffineOpen.isElementary_etaleNeighborhoodOfChart` is then clause (4), and
the first projection identity together with
`StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_chart_over` is the part of
clause (1) concerning `w` and `(y, v)`.

This is a step of the proof of Tag 0CAW and not one of its clauses: clause (4) at the tag's own
hypotheses needs in addition the chaining of the six steps of the source's proof that produces
`q`, `r` and `Q`, and clause (5) needs the chase of the congruence. Nothing here is registered
for Tag 0CAW. -/
theorem exists_point_etale_chart_pullback_tensorProduct {T Y : Scheme.{u}} (g : Y ⟶ T)
    {Λ : CommRingCat.{u}} (b : Spec Λ ⟶ T)
    {WT : T.Opens} (hWT : IsAffineOpen WT) (hbT : (⊤ : (Spec Λ).Opens) ≤ b ⁻¹ᵁ WT)
    {VY : Y.Opens} (hVY : IsAffineOpen VY) (hVYW : VY ≤ g ⁻¹ᵁ WT)
    {y : Y} (hyV : y ∈ VY) (v : PrimeSpectrum Λ)
    [Algebra Γ(T, WT) Λ] [Algebra Γ(T, WT) Γ(Y, VY)]
    (hΛ : ∀ a : Γ(T, WT), algebraMap Γ(T, WT) Λ a =
      (Scheme.ΓSpecIso Λ).hom.hom ((b.appLE WT ⊤ hbT).hom a))
    (hB : ∀ a : Γ(T, WT),
      algebraMap Γ(T, WT) Γ(Y, VY) a = (g.appLE WT VY hVYW).hom a)
    (q : Ideal (Γ(Y, VY) ⊗[Γ(T, WT)] Λ)) [q.IsPrime]
    (hqY : (hVY.primeIdealOf ⟨y, hyV⟩).asIdeal =
      q.comap (Algebra.TensorProduct.includeLeftRingHom : Γ(Y, VY) →+* _))
    (hqv : v.asIdeal =
      q.comap (Algebra.TensorProduct.includeRight :
        Λ →ₐ[Γ(T, WT)] Γ(Y, VY) ⊗[Γ(T, WT)] Λ).toRingHom)
    {M : Type u} [CommRing M] (r : (Γ(Y, VY) ⊗[Γ(T, WT)] Λ) →+* M) (hr : r.Etale)
    (Q : Ideal M) [Q.IsPrime] (hQ : Ideal.comap r Q = q)
    (hres : Function.Bijective (Ideal.ResidueField.map q Q r hQ.symm)) :
    ∃ (U : (pullback g b : Scheme.{u}).Opens) (hU : IsAffineOpen U)
      (yv : (pullback g b : Scheme.{u})) (hyvU : yv ∈ U)
      (hUY : U ≤ pullback.fst g b ⁻¹ᵁ VY)
      (ρ : Γ(pullback g b, U) →+* M)
      (hρ : Ideal.comap ρ Q = (hU.primeIdealOf ⟨yv, hyvU⟩).asIdeal),
      pullback.fst g b yv = y ∧ pullback.snd g b yv = v ∧ ρ.Etale ∧
        Function.Bijective (Ideal.ResidueField.map (hU.primeIdealOf ⟨yv, hyvU⟩).asIdeal Q ρ
          hρ.symm) ∧
        (∀ a : Γ(Y, VY), ρ (((pullback.fst g b).appLE VY U hUY).hom a) = r (a ⊗ₜ 1)) ∧
        (∀ l : Λ, ρ (((pullback.snd g b).appLE ⊤ U le_top).hom
            ((Scheme.ΓSpecIso Λ).inv.hom l)) = r (1 ⊗ₜ l)) := by
  have hUY : IsAffineOpen (pullback.fst g b ⁻¹ᵁ VY) :=
    isAffineOpen_preimage_pullback_fst_of_preimage_eq_top g b hWT hbT hVY hVYW
  obtain ⟨χ₀, hχl, hχr⟩ :=
    exists_ringEquiv_tensorProduct_sections_pullback_fst_of_preimage_eq_top g b hWT hbT hVY
      hVYW hΛ hB
  -- the chart ring, with the tensor factors in the order the descent produces them
  let χ : (Γ(Y, VY) ⊗[Γ(T, WT)] Λ) ≃+* Γ(pullback g b, pullback.fst g b ⁻¹ᵁ VY) :=
    (Algebra.TensorProduct.comm Γ(T, WT) Γ(Y, VY) Λ).toRingEquiv.trans χ₀
  have hχL : ∀ a : Γ(Y, VY), χ (a ⊗ₜ 1) =
      ((pullback.fst g b).appLE VY (pullback.fst g b ⁻¹ᵁ VY) le_rfl).hom a := fun a => by
    change χ₀ ((Algebra.TensorProduct.comm Γ(T, WT) Γ(Y, VY) Λ) (a ⊗ₜ 1)) = _
    rw [Algebra.TensorProduct.comm_tmul]
    exact hχr a
  have hχR : ∀ l : Λ, χ (1 ⊗ₜ l) =
      ((pullback.snd g b).appLE ⊤ (pullback.fst g b ⁻¹ᵁ VY) le_top).hom
        ((Scheme.ΓSpecIso Λ).inv.hom l) := fun l => by
    change χ₀ ((Algebra.TensorProduct.comm Γ(T, WT) Γ(Y, VY) Λ) (1 ⊗ₜ l)) = _
    rw [Algebra.TensorProduct.comm_tmul]
    exact hχl l
  -- the prime of the chart ring, and the point of the fibre product it cuts out
  have hqcχ : (q.comap χ.symm.toRingHom).comap χ.toRingHom = q := by
    rw [Ideal.comap_comap, show χ.symm.toRingHom.comp χ.toRingHom = RingHom.id _ from
      RingHom.ext χ.symm_apply_apply, Ideal.comap_id]
  set qc : PrimeSpectrum Γ(pullback g b, pullback.fst g b ⁻¹ᵁ VY) :=
    ⟨q.comap χ.symm.toRingHom, inferInstance⟩ with hqc
  set yv : (pullback g b : Scheme.{u}) := hUY.fromSpec qc
  have hyvU : yv ∈ pullback.fst g b ⁻¹ᵁ VY := mem_of_fromSpec hUY qc
  have hIJ : (hUY.primeIdealOf ⟨yv, hyvU⟩).asIdeal = q.comap χ.symm.toRingHom :=
    congrArg PrimeSpectrum.asIdeal (primeIdealOf_fromSpec hUY qc)
  -- the first projection: the contraction of `q` to `Γ(Y, V_Y)`
  have hfst : pullback.fst g b yv = y := by
    refine hUY.apply_fromSpec_of_comap_eq (pullback.fst g b) hVY le_rfl qc hyV ?_
    have hmap : ((pullback.fst g b).appLE VY (pullback.fst g b ⁻¹ᵁ VY) le_rfl).hom =
        χ.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom : Γ(Y, VY) →+* _) :=
      RingHom.ext fun a => (hχL a).symm
    rw [hmap, ← Ideal.comap_comap, hqc, hqcχ, ← hqY]
  -- the second projection: the contraction of `q` to `Λ`
  have hsnd : pullback.snd g b yv = v := by
    refine hUY.apply_fromSpec_of_comap_eq (pullback.snd g b) (isAffineOpen_top (Spec Λ))
      le_top qc trivial ?_
    have hmap : ((pullback.snd g b).appLE ⊤ (pullback.fst g b ⁻¹ᵁ VY) le_top).hom =
        (χ.toRingHom.comp
          (Algebra.TensorProduct.includeRight :
            Λ →ₐ[Γ(T, WT)] Γ(Y, VY) ⊗[Γ(T, WT)] Λ).toRingHom).comp
          (Scheme.ΓSpecIso Λ).hom.hom := by
      refine RingHom.ext fun z => ?_
      have hz := (hχR ((Scheme.ΓSpecIso Λ).hom.hom z)).symm
      rwa [show (Scheme.ΓSpecIso Λ).inv.hom ((Scheme.ΓSpecIso Λ).hom.hom z) = z from
        congr($((Scheme.ΓSpecIso Λ).hom_inv_id).hom z)] at hz
    rw [hmap, ← Ideal.comap_comap, ← Ideal.comap_comap, hqc, hqcχ, ← hqv,
      primeIdealOf_top_spec Λ v]
    rfl
  -- the étale ring map on the chart, and its residually trivial prime
  have hρ : Ideal.comap (r.comp χ.symm.toRingHom) Q =
      (hUY.primeIdealOf ⟨yv, hyvU⟩).asIdeal := by
    rw [← Ideal.comap_comap, hQ, hIJ]
  refine ⟨pullback.fst g b ⁻¹ᵁ VY, hUY, yv, hyvU, le_rfl, r.comp χ.symm.toRingHom, hρ,
    hfst, hsnd,
    RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective χ.symm.bijective) hr,
    Ideal.ResidueField.map_bijective_comp_ringEquiv χ.symm r hIJ hQ.symm hres hρ.symm,
    fun a => ?_, fun l => ?_⟩
  · simp [← hχL a]
  · simp [← hχR l]

/-! ### The two sides composed -/

/-- **Clauses (1), (2) and (4) of Stacks Tag 0CAW from the ring data of the last step.** The two
feedings above composed: the `V` side's morphism `τ` is the `b` of the `W` side, its two chart
hypotheses holding by construction (`AlgebraicGeometry.preimage_fromSpec_comp` and
`AlgebraicGeometry.appLE_fromSpec_comp`).

So: let `h : T ⟶ S` and `g : Y ⟶ T`, let `U_S ∋ s`, `W_T ∋ t` and `V_Y ∋ y` be affine opens with
`W_T ≤ h ⁻¹ᵁ U_S` and `V_Y ≤ g ⁻¹ᵁ W_T`, let `D` be a `Γ(T, W_T)`-algebra whose structure map
restricted along `Γ(S, U_S) → Γ(T, W_T)` is a ring map `ρ_S` with étale spectrum, and let `v` be
a prime of `D` over the prime of `s` with bijective residue field extension and over the prime of
`t`. Let `q` be a prime of `Γ(Y, V_Y) ⊗_{Γ(T, W_T)} D` over the prime of `y` and over `v`, and
let `r` be étale out of that tensor product with a prime `Q` over `q` with bijective residue
field extension. Then there are an elementary étale neighbourhood `(V, v)` of `(S, s)`, a
morphism `τ : V ⟶ T` over `S` with `τ v = t`, a point `(y, v)` of `Y ×_{T, τ} V` whose two
projections are `y` and `v`, and an elementary étale neighbourhood `(W, w)` of
`(Y ×_{T, τ} V, (y, v))` with affine scheme.

Read at Tag 0CAW this is clause (2), the `v`-and-`τ` part of clause (1), the `w ↦ (y, v)` part of
clause (1) (which is `W.map_point`), and clause (4) — all four from the ring data of the source's
last step. **It is not clause (4) at Tag 0CAW's own hypotheses, and nothing here is registered
for the tag:** `D`, `q`, `r` and `Q` are hypotheses, and producing them from the tag's `σ` and
`φ` is the chaining of the six steps of the source's proof, which is not carried out. Clauses (3)
and (5) are likewise not established — clause (5) in particular requires the morphism `f` and the
chase of the congruence, and a `V` and `τ` chosen without reference to `φ` can make it
unsatisfiable, which is why `D` must come from the smooth stage and not from `Γ(T, W_T)`. -/
theorem exists_elementaryEtaleNeighborhood_pair_chart {S T Y : Scheme.{u}} (h : T ⟶ S)
    (g : Y ⟶ T) {US : S.Opens} (hUS : IsAffineOpen US) {WT : T.Opens} (hWT : IsAffineOpen WT)
    (hWU : WT ≤ h ⁻¹ᵁ US) {VY : Y.Opens} (hVY : IsAffineOpen VY) (hVYW : VY ≤ g ⁻¹ᵁ WT)
    {s : S} (hsU : s ∈ US) {t : T} (htW : t ∈ WT) {y : Y} (hyV : y ∈ VY)
    {D : Type u} [CommRing D] [Algebra Γ(T, WT) D] [Algebra Γ(T, WT) Γ(Y, VY)]
    (hB : ∀ a : Γ(T, WT),
      algebraMap Γ(T, WT) Γ(Y, VY) a = (g.appLE WT VY hVYW).hom a)
    (rS : Γ(S, US) →+* D) [Etale (Spec.map (CommRingCat.ofHom rS))]
    (hrS : (algebraMap Γ(T, WT) D).comp (h.appLE US WT hWU).hom = rS)
    (v : PrimeSpectrum D)
    (hvS : Ideal.comap rS v.asIdeal = (hUS.primeIdealOf ⟨s, hsU⟩).asIdeal)
    (hvT : Ideal.comap (algebraMap Γ(T, WT) D) v.asIdeal =
      (hWT.primeIdealOf ⟨t, htW⟩).asIdeal)
    (hvres : Function.Bijective
      (Ideal.ResidueField.map (hUS.primeIdealOf ⟨s, hsU⟩).asIdeal v.asIdeal rS hvS.symm))
    (q : Ideal (Γ(Y, VY) ⊗[Γ(T, WT)] D)) [q.IsPrime]
    (hqY : (hVY.primeIdealOf ⟨y, hyV⟩).asIdeal =
      q.comap (Algebra.TensorProduct.includeLeftRingHom : Γ(Y, VY) →+* _))
    (hqv : v.asIdeal =
      q.comap (Algebra.TensorProduct.includeRight :
        D →ₐ[Γ(T, WT)] Γ(Y, VY) ⊗[Γ(T, WT)] D).toRingHom)
    {M : Type u} [CommRing M] (r : (Γ(Y, VY) ⊗[Γ(T, WT)] D) →+* M) (hr : r.Etale)
    (Q : Ideal M) [Q.IsPrime] (hQ : Ideal.comap r Q = q)
    (hQres : Function.Bijective (Ideal.ResidueField.map q Q r hQ.symm)) :
    ∃ V : EtaleNeighborhood S s, V.IsElementary ∧
      ∃ (τ : V.scheme ⟶ T) (_ : τ V.point = t), τ ≫ h = V.toBase ∧
        ∃ (yv : (pullback g τ : Scheme.{u})) (_ : pullback.fst g τ yv = y)
          (_ : pullback.snd g τ yv = V.point),
          ∃ W : EtaleNeighborhood (pullback g τ : Scheme.{u}) yv,
            W.IsElementary ∧ IsAffine W.scheme := by
  -- the `V` side
  set τ : Spec (CommRingCat.of D) ⟶ T :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(T, WT) D)) ≫ hWT.fromSpec
  have hbT : (⊤ : (Spec (CommRingCat.of D)).Opens) ≤ τ ⁻¹ᵁ WT :=
    (preimage_fromSpec_comp hWT (CommRingCat.ofHom (algebraMap Γ(T, WT) D))).ge
  -- the algebra structure on `D` is the one `τ` induces on sections
  have hΛ : ∀ a : Γ(T, WT), algebraMap Γ(T, WT) (CommRingCat.of D) a =
      (Scheme.ΓSpecIso (CommRingCat.of D)).hom.hom ((τ.appLE WT ⊤ hbT).hom a) := by
    intro a
    have happ : τ.appLE WT ⊤ hbT =
        CommRingCat.ofHom (algebraMap Γ(T, WT) D) ≫
          (Scheme.ΓSpecIso (CommRingCat.of D)).inv :=
      appLE_fromSpec_comp hWT (CommRingCat.ofHom (algebraMap Γ(T, WT) D))
    rw [happ, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    exact congr($((Scheme.ΓSpecIso (CommRingCat.of D)).inv_hom_id).hom
      (algebraMap Γ(T, WT) D a)).symm
  -- the `W` side, fed with `τ`
  obtain ⟨U, hU, yv, hyvU, hUY, ρ, hρ, hfst, hsnd, hρE, hρres, -, -⟩ :=
    exists_point_etale_chart_pullback_tensorProduct g τ hWT hbT hVY hVYW hyV v hΛ hB q hqY hqv
      r hr Q hQ hQres
  have : Etale (Spec.map (CommRingCat.ofHom ρ)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hρE
  refine ⟨hUS.etaleNeighborhoodOfChart hsU rS v hvS,
    hUS.isElementary_etaleNeighborhoodOfChart hsU rS v hvS hvres, τ,
    hWT.specMap_fromSpec_apply htW (algebraMap Γ(T, WT) D) v hvT,
    specMap_fromSpec_comp_eq_of_comp_eq h hUS hWT hWU rS _ hrS,
    yv, hfst, hsnd, hU.etaleNeighborhoodOfChart hyvU ρ ⟨Q, inferInstance⟩ hρ,
    hU.isElementary_etaleNeighborhoodOfChart hyvU ρ ⟨Q, inferInstance⟩ hρ hρres,
    hU.isAffine_etaleNeighborhoodOfChart hyvU ρ ⟨Q, inferInstance⟩ hρ⟩

end StacksDraft.ArtinApproximation

end
