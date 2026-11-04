module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Specializations
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGeneralizations
public import StacksFrontier.RingTheory.Spectrum.Prime.DimensionTwoOpens
public import StacksFrontier.Topology.Jacobson.CounterexampleQuasiCompact
public import StacksFrontier.Topology.Sober.StableSubspace
public import StacksFrontier.Topology.Specialization.Constructible

/-!
# Proper generalizations of a point of a decent algebraic space

Let `X` be a decent algebraic space over `S` and let `x` be a point of `X`. The *proper
generalizations* of `x` are the points `x'` of `X` with `x' ⤳ x` and `x' ≠ x`, with the
subspace topology induced from the point topology of Stacks 03BX. This subspace is sober, and
when `X` is moreover locally Noetherian it is a spectral and a Jacobson topological space.

## Main results

* `AlgebraicGeometry.Space.stacksSober_properGeneralizations` is the sobriety half of
  **Stacks 0ED2**.
* `AlgebraicGeometry.Space.spectralSpace_properGeneralizations` is the spectral half of
  **Stacks 0ED2**.
* `AlgebraicGeometry.Space.jacobsonSpace_properGeneralizations` is the Jacobson half of
  **Stacks 0ED2**.

## Implementation notes

Sobriety needs only decency, not local Noetherianity: the point space of a decent algebraic
space is sober by Stacks 03K6, the proper generalizations of a point form a subset stable
under generalization, and a subspace of a quasi-sober space stable under generalization is
quasi-sober.

The source obtains spectrality by exhibiting `|X|` as a spectral space and cutting out a
quasi-compact open of `W ∪ {x}`. Here the Noetherian half of Stacks 0ED2 is already
available, and a Noetherian sober space is spectral, so the route through
`SpectralSpace.of_noetherianSpace` is shorter and needs no separate spectrality statement
for `|X|`.

For the Jacobson property the argument is the one of the source. If `W` is not Jacobson then,
being spectral, it has by Stacks 02I7 a point `x'` whose singleton is locally closed but not
closed, so there is a proper specialization `x' ⤳ x'₁` inside `W`. Lifting the chain
`x' ⤳ x'₁ ⤳ x` twice along an affine étale chart by Stacks 03K2 produces three distinct
points of the chart in a specialization chain, hence two strict inclusions of primes in the
local ring of the chart at the image of `x`. The quotient of that local ring by the smallest
of the three therefore has dimension at least two, so each of its nonempty opens is infinite
by Stacks 02IG, while the preimage there of the open part of `{x'}` meets only the two finite
chart fibres above `x'` and above `x`.

`AlgebraicGeometry.Space.pointTopology` is a plain definition rather than an instance and is
made a local instance here.

## References

* [Stacks Project, Tag 02I7](https://stacks.math.columbia.edu/tag/02I7)
* [Stacks Project, Tag 02IG](https://stacks.math.columbia.edu/tag/02IG)
* [Stacks Project, Tag 03K2](https://stacks.math.columbia.edu/tag/03K2)
* [Stacks Project, Tag 03K6](https://stacks.math.columbia.edu/tag/03K6)
* [Stacks Project, Tag 0ED2](https://stacks.math.columbia.edu/tag/0ED2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-- A space in which every nonempty open set is infinite cannot map, injectively and
continuously, into a space in which the open part of a locally closed singleton `{w₀}` pulls
back into the union of two finite fibres.

Here `w₀` is a point of the subspace of proper generalizations of `x₁` lying over `x₀`, and
`hchain` says that the whole image of `lift` lies between `x₀` and `x₁`. The open `G`
cutting out `{w₀}` pulls back to a nonempty open of `Z`, hence an infinite one, while each of
its points is carried either to `x₁` or — being a point of the subspace lying in both the
open and the closed part of `{w₀}` — to `x₀`. -/
private theorem false_of_finite_fibres_of_infinite_opens {Z : Type*} [TopologicalSpace Z]
    (hInf : ∀ G : Set Z, IsOpen G → G.Nonempty → G.Infinite)
    {P : Type*} [TopologicalSpace P] {x₀ x₁ : P}
    (w₀ : {q : P // q ⤳ x₁ ∧ q ≠ x₁}) (hw₀ : (w₀ : P) = x₀)
    (hLC : IsLocallyClosed ({w₀} : Set {q : P // q ⤳ x₁ ∧ q ≠ x₁}))
    {T : Type*} (lift : Z → T) (map : T → P)
    (hlift : Function.Injective lift) (hcont : Continuous (map ∘ lift))
    (q₀ : Z) (hq₀ : map (lift q₀) = x₀)
    (hchain : ∀ q : Z, x₀ ⤳ map (lift q) ∧ map (lift q) ⤳ x₁)
    (hfin₀ : (map ⁻¹' {x₀}).Finite) (hfin₁ : (map ⁻¹' {x₁}).Finite) : False := by
  obtain ⟨O, C, hO, hC, hEq⟩ := hLC
  have hw₀OC : w₀ ∈ O ∩ C := by rw [← hEq]; exact rfl
  obtain ⟨G, hG, hGO⟩ := isOpen_induced_iff.mp hO
  have hq₀G : q₀ ∈ (map ∘ lift) ⁻¹' G := by
    have hwG : (w₀ : P) ∈ G := by
      have hmem : w₀ ∈ O := hw₀OC.1
      rw [← hGO] at hmem
      exact hmem
    show map (lift q₀) ∈ G
    simpa [hq₀, hw₀] using hwG
  have hInfinite := hInf ((map ∘ lift) ⁻¹' G) (hG.preimage hcont) ⟨q₀, hq₀G⟩
  refine hInfinite.not_finite (Set.Finite.subset
    ((hfin₀.preimage hlift.injOn).union (hfin₁.preimage hlift.injOn)) fun q hq ↦ ?_)
  change map (lift q) ∈ G at hq
  have hqx := hchain q
  by_cases hq₁ : map (lift q) = x₁
  · exact Or.inr hq₁
  refine Or.inl ?_
  have hwEq : (⟨map (lift q), hqx.2, hq₁⟩ : {q : P // q ⤳ x₁ ∧ q ≠ x₁}) = w₀ := by
    have hwO : (⟨map (lift q), hqx.2, hq₁⟩ : {q : P // q ⤳ x₁ ∧ q ≠ x₁}) ∈ O := by
      rw [← hGO]; exact hq
    have hcl : (⟨map (lift q), hqx.2, hq₁⟩ : {q : P // q ⤳ x₁ ∧ q ≠ x₁}) ∈
        closure ({w₀} : Set {q : P // q ⤳ x₁ ∧ q ≠ x₁}) := by
      rw [closure_subtype, Set.image_singleton]
      simpa [hw₀] using specializes_iff_mem_closure.mp hqx.1
    have hwC : (⟨map (lift q), hqx.2, hq₁⟩ : {q : P // q ⤳ x₁ ∧ q ≠ x₁}) ∈ C :=
      hC.closure_subset (closure_mono (Set.singleton_subset_iff.mpr hw₀OC.2) hcl)
    exact Set.mem_singleton_iff.mp (hEq ▸ ⟨hwO, hwC⟩)
  show map (lift q) = x₀
  exact (congrArg Subtype.val hwEq).trans hw₀

/-- The contradiction behind the Jacobson property of Stacks 0ED2, isolated at the level of a
scheme. Three distinct points `a ⤳ b ⤳ c` of a locally Noetherian scheme `Y` give two strict
inclusions of primes in the local ring of `Y` at `c`, so the quotient of that local ring by
the prime corresponding to `a` is a Noetherian local domain of dimension at least two. Its
spectrum maps injectively and continuously into `Y`, carrying its generic point to `a` and
its closed point to `c`, and every nonempty open of it is infinite by Stacks 02IG; that is
incompatible with `{w₀}` being locally closed when the fibres of `map` above `x₀` and `x₁`
are finite. -/
@[ega "IV 5.1.10" "more general"]
private theorem false_of_specializes_chain_of_finite_fibres {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] {P : Type*} [TopologicalSpace P] (map : Y → P)
    (hmap : Continuous map) {a b c : Y} (hab : a ⤳ b) (hbc : b ⤳ c) (hab' : a ≠ b)
    (hbc' : b ≠ c) {x₀ x₁ : P} (ha : map a = x₀) (hc : map c = x₁)
    (w₀ : {q : P // q ⤳ x₁ ∧ q ≠ x₁}) (hw₀ : (w₀ : P) = x₀)
    (hLC : IsLocallyClosed ({w₀} : Set {q : P // q ⤳ x₁ ∧ q ≠ x₁}))
    (hfin₀ : (map ⁻¹' {x₀}).Finite) (hfin₁ : (map ⁻¹' {x₁}).Finite) : False := by
  obtain ⟨qa, hqa⟩ : a ∈ Set.range (Y.fromSpecStalk c) := by
    rw [Scheme.range_fromSpecStalk]; exact hab.trans hbc
  obtain ⟨qb, hqb⟩ : b ∈ Set.range (Y.fromSpecStalk c) := by
    rw [Scheme.range_fromSpecStalk]; exact hbc
  have hlt : ∀ s t : PrimeSpectrum (Y.presheaf.stalk c),
      Y.fromSpecStalk c s ⤳ Y.fromSpecStalk c t → Y.fromSpecStalk c s ≠ Y.fromSpecStalk c t →
      s.asIdeal < t.asIdeal := fun s t h hne ↦
    lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes s t).mpr
      ((Y.fromSpecStalk c).isEmbedding.isInducing.specializes_iff.mp h)) fun he ↦
        hne (by rw [PrimeSpectrum.ext he])
  have hlt₁ : qa.asIdeal < qb.asIdeal :=
    hlt qa qb (by rw [hqa, hqb]; exact hab) (by rw [hqa, hqb]; exact hab')
  have hlt₂ : qb.asIdeal < (IsLocalRing.closedPoint (Y.presheaf.stalk c)).asIdeal :=
    hlt _ _ (by rw [hqb, Scheme.fromSpecStalk_closedPoint]; exact hbc)
      (by rw [hqb, Scheme.fromSpecStalk_closedPoint]; exact hbc')
  have _ : qa.asIdeal.IsPrime := qa.isPrime
  have _ : IsLocalRing (Y.presheaf.stalk c ⧸ qa.asIdeal) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk qa.asIdeal) Ideal.Quotient.mk_surjective
  have _ : IsDomain (Y.presheaf.stalk c ⧸ qa.asIdeal) := Ideal.Quotient.isDomain qa.asIdeal
  have _ : IsNoetherianRing (Y.presheaf.stalk c ⧸ qa.asIdeal) := inferInstance
  have hcomapBot : PrimeSpectrum.comap (Ideal.Quotient.mk qa.asIdeal)
      (⊥ : PrimeSpectrum (Y.presheaf.stalk c ⧸ qa.asIdeal)) = qa := by
    apply PrimeSpectrum.ext
    show Ideal.comap (Ideal.Quotient.mk qa.asIdeal)
      (⊥ : Ideal (Y.presheaf.stalk c ⧸ qa.asIdeal)) = qa.asIdeal
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hcomapMax : PrimeSpectrum.comap (Ideal.Quotient.mk qa.asIdeal)
      (IsLocalRing.closedPoint (Y.presheaf.stalk c ⧸ qa.asIdeal)) =
      IsLocalRing.closedPoint (Y.presheaf.stalk c) :=
    have _ : IsLocalHom (Ideal.Quotient.mk qa.asIdeal) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    IsLocalRing.comap_closedPoint (Ideal.Quotient.mk qa.asIdeal)
  set e := Ideal.primeSpectrumQuotientOrderIsoZeroLocus qa.asIdeal
  have hlt' : ∀ u v : PrimeSpectrum (Y.presheaf.stalk c ⧸ qa.asIdeal),
      PrimeSpectrum.comap (Ideal.Quotient.mk qa.asIdeal) u <
        PrimeSpectrum.comap (Ideal.Quotient.mk qa.asIdeal) v → u < v :=
    fun u v h ↦ e.lt_iff_lt.mp h
  obtain ⟨r, hr⟩ : ∃ r, PrimeSpectrum.comap (Ideal.Quotient.mk qa.asIdeal) r = qb :=
    ⟨e.symm ⟨qb, (PrimeSpectrum.mem_zeroLocus qb _).2 hlt₁.le⟩,
      congrArg Subtype.val (e.apply_symm_apply _)⟩
  have hbotlt : (⊥ : PrimeSpectrum (Y.presheaf.stalk c ⧸ qa.asIdeal)) < r :=
    hlt' _ _ (by rw [hcomapBot, hr]; exact hlt₁)
  have hltmax : r < IsLocalRing.closedPoint (Y.presheaf.stalk c ⧸ qa.asIdeal) :=
    hlt' _ _ (by rw [hr, hcomapMax]; exact hlt₂)
  have hdim : 2 ≤ ringKrullDim (Y.presheaf.stalk c ⧸ qa.asIdeal) := by
    have hlen := Order.LTSeries.length_le_krullDim
      (((RelSeries.singleton {p : PrimeSpectrum (Y.presheaf.stalk c ⧸ qa.asIdeal) ×
          PrimeSpectrum (Y.presheaf.stalk c ⧸ qa.asIdeal) | p.1 < p.2}
        (IsLocalRing.closedPoint (Y.presheaf.stalk c ⧸ qa.asIdeal))).cons _ hltmax).cons
        ⊥ hbotlt)
    rwa [show (((RelSeries.singleton
        {p : PrimeSpectrum (Y.presheaf.stalk c ⧸ qa.asIdeal) ×
          PrimeSpectrum (Y.presheaf.stalk c ⧸ qa.asIdeal) | p.1 < p.2}
        (IsLocalRing.closedPoint (Y.presheaf.stalk c ⧸ qa.asIdeal))).cons _ hltmax).cons
        ⊥ hbotlt).length = 2 from rfl] at hlen
  have hcontg : Continuous ((fun v ↦ map v) ∘ fun q ↦
      Y.fromSpecStalk c (PrimeSpectrum.comap (Ideal.Quotient.mk qa.asIdeal) q)) :=
    hmap.comp ((Y.fromSpecStalk c).continuous.comp (PrimeSpectrum.continuous_comap _))
  refine false_of_finite_fibres_of_infinite_opens
    (PrimeSpectrum.infinite_of_two_le_ringKrullDim _ hdim) w₀ hw₀ hLC
    (fun q ↦ Y.fromSpecStalk c (PrimeSpectrum.comap (Ideal.Quotient.mk qa.asIdeal) q))
    map (fun s t hst ↦ PrimeSpectrum.comap_injective_of_surjective _
      Ideal.Quotient.mk_surjective ((Y.fromSpecStalk c).isEmbedding.injective hst))
    hcontg ⊥ ?_ (fun q ↦ ⟨?_, ?_⟩) hfin₀ hfin₁
  · show map (Y.fromSpecStalk c (PrimeSpectrum.comap _ ⊥)) = x₀
    rw [hcomapBot, hqa]; exact ha
  · have h := ((PrimeSpectrum.le_iff_specializes
      (⊥ : PrimeSpectrum (Y.presheaf.stalk c ⧸ qa.asIdeal)) q).mp bot_le).map hcontg
    change map (Y.fromSpecStalk c (PrimeSpectrum.comap _ ⊥)) ⤳ _ at h
    rwa [hcomapBot, hqa, ha] at h
  · have h := ((PrimeSpectrum.le_iff_specializes q (IsLocalRing.closedPoint
      (Y.presheaf.stalk c ⧸ qa.asIdeal))).mp le_top).map hcontg
    change _ ⤳ map (Y.fromSpecStalk c (PrimeSpectrum.comap _
      (IsLocalRing.closedPoint (Y.presheaf.stalk c ⧸ qa.asIdeal)))) at h
    rwa [hcomapMax, Scheme.fromSpecStalk_closedPoint, hc] at h

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Stacks 0ED2, sobriety.** The proper generalizations of a point `x` of a decent
algebraic space over `S` form a sober topological space, sobriety being that of Stacks 004X:
every irreducible closed subset has a unique generic point. -/
@[stacks 0ED2 "sobriety"]
theorem stacksSober_properGeneralizations (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (x : points B S hS X) :
    StacksSober {x' : points B S hS X // x' ⤳ x ∧ x' ≠ x} :=
  have _ : T0Space (points B S hS X) := t0Space_points_of_isDecentSpace B S hS hX hdec
  have _ : QuasiSober (points B S hS X) := quasiSober_points_of_isDecentSpace B S hS hX hdec
  stacksSober_iff_t0_and_quasiSober.mpr
    ⟨Subtype.t0Space, quasiSober_properGeneralizations x⟩

/-- **Stacks 0ED2, spectrality.** The proper generalizations of a point `x` of a decent
locally Noetherian algebraic space over `S` form a spectral topological space. -/
@[stacks 0ED2 "spectrality"]
theorem spectralSpace_properGeneralizations (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (x : points B S hS X) :
    SpectralSpace {x' : points B S hS X // x' ⤳ x ∧ x' ≠ x} :=
  have _ : NoetherianSpace {x' : points B S hS X // x' ⤳ x ∧ x' ≠ x} :=
    noetherianSpace_properGeneralizations B S hS X hX hN x
  have _ : T0Space (points B S hS X) := t0Space_points_of_isDecentSpace B S hS hX hdec
  have _ : QuasiSober (points B S hS X) := quasiSober_points_of_isDecentSpace B S hS hX hdec
  have _ : QuasiSober {x' : points B S hS X // x' ⤳ x ∧ x' ≠ x} :=
    quasiSober_properGeneralizations x
  have _ : T0Space {x' : points B S hS X // x' ⤳ x ∧ x' ≠ x} := Subtype.t0Space
  SpectralSpace.of_noetherianSpace _

/-- **Stacks 0ED2, the Jacobson property.** The proper generalizations of a point `x` of a
decent locally Noetherian algebraic space over `S` form a Jacobson topological space. -/
@[stacks 0ED2 "the Jacobson property"]
theorem jacobsonSpace_properGeneralizations (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (x : points B S hS X) :
    JacobsonSpace {x' : points B S hS X // x' ⤳ x ∧ x' ≠ x} := by
  have hspec : SpectralSpace {x' : points B S hS X // x' ⤳ x ∧ x' ≠ x} :=
    spectralSpace_properGeneralizations B S hS X hX hdec hN x
  have _ : T0Space {x' : points B S hS X // x' ⤳ x ∧ x' ≠ x} := hspec.toT0Space
  -- Condition `(γ)` of Stacks 03JX: every affine étale chart has finite fibres.
  have hγ : HasFiniteChartAndRelationFibersAtEveryPoint B S hS X :=
    (isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint B S hS X hX).mp hdec
  -- An affine étale chart of `X` through `x`, locally Noetherian because it is étale over a
  -- locally Noetherian chart.
  obtain ⟨U, φ, hUaff, hUN, hφ, p, hp⟩ :
      ∃ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X),
        IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) ∧
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf φ ∧
        ∃ p : points B S hS (yoneda.obj U), pointsMap B S hS (yoneda.obj U) φ p = x := by
    obtain ⟨U₀, φ₀, hsurj₀, hφ₀, hU₀N⟩ := hN
    obtain ⟨p₀, hp₀⟩ := (surjective_iff_surjective_pointsMap B S hS X hX U₀ φ₀).mp hsurj₀ x
    obtain ⟨V, j, v, hVaff, hjEt, hjv⟩ := exists_isAffine_etaleChart_pointsMap_eq B S hS U₀ p₀
    have _ := inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
    have _ : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition _
    have _ : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U₀) := hU₀N
    have _ : Etale ((BigFppfOver.toScheme B S hS).map j) :=
      (presheaf_yoneda_map_iff B S hS
        AlgebraicGeometry.Etale.etale_isStableUnderBaseChange j).1 hjEt
    refine ⟨V, yoneda.map j ≫ φ₀, hVaff,
      LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map j),
      MorphismProperty.comp_mem _ (yoneda.map j) φ₀ hjEt hφ₀, v, ?_⟩
    rw [pointsMap_comp_apply, hjv]
    exact hp₀
  have _ : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) := hUN
  by_contra hJ
  obtain ⟨y, hyclosed, hyLC⟩ := main_theorem02I7 _ hspec.toPrespectralSpace hJ
  -- `{y}` is not closed, so `y` admits a proper specialization `z` inside the subspace.
  obtain ⟨z, hzy, hzne⟩ : ∃ z : {x' : points B S hS X // x' ⤳ x ∧ x' ≠ x},
      z ∈ closure ({y} : Set {x' : points B S hS X // x' ⤳ x ∧ x' ≠ x}) ∧ z ≠ y := by
    by_contra hcon
    refine hyclosed (closure_eq_iff_isClosed.mp
      (subset_antisymm (fun w hw ↦ ?_) subset_closure))
    by_cases hwy : w = y
    · exact Set.mem_singleton_iff.mpr hwy
    · exact absurd ⟨w, hw, hwy⟩ hcon
  have hyz : (y : points B S hS X) ⤳ (z : points B S hS X) :=
    (specializes_iff_mem_closure.mpr hzy).map continuous_subtype_val
  -- Lift the chain `y ⤳ z ⤳ x` to the chart twice, by Stacks 03K2.
  obtain ⟨pz, hpzp, hpzmap⟩ := exists_specializes_pointsMap_eq_of_isEtale B S hS hX z.2.1
    (fun V hV ψ hψ ↦ (hγ (z : points B S hS X) V hV ψ hψ).1) U φ hφ p hp
  obtain ⟨py, hpypz, hpymap⟩ := exists_specializes_pointsMap_eq_of_isEtale B S hS hX hyz
    (fun V hV ψ hψ ↦ (hγ (y : points B S hS X) V hV ψ hψ).1) U φ hφ pz hpzmap
  -- Read the three chart points as points of the representing scheme, by Stacks 03BX (1).
  have hmapcont : Continuous (fun v ↦ pointsMap B S hS (yoneda.obj U) φ
      ((schemePointsHomeomorph B S hS U).symm v)) :=
    (continuous_pointsMap B S hS φ).comp (schemePointsHomeomorph B S hS U).symm.continuous
  have hvalue : ∀ q : points B S hS (yoneda.obj U),
      pointsMap B S hS (yoneda.obj U) φ
        ((schemePointsHomeomorph B S hS U).symm (schemePointsHomeomorph B S hS U q)) =
      pointsMap B S hS (yoneda.obj U) φ q := by
    intro q
    rw [Homeomorph.symm_apply_apply]
  have hfibre : ∀ t : points B S hS X, ((fun v ↦ pointsMap B S hS (yoneda.obj U) φ
      ((schemePointsHomeomorph B S hS U).symm v)) ⁻¹' {t}).Finite := by
    intro t
    have h : ((schemePointsHomeomorph B S hS U).symm ⁻¹'
        (pointsMap B S hS (yoneda.obj U) φ ⁻¹' {t})).Finite :=
      Set.Finite.preimage
        (Function.Injective.injOn (schemePointsHomeomorph B S hS U).symm.injective)
        (hγ t U hUaff φ hφ).1
    exact h
  refine false_of_specializes_chain_of_finite_fibres _ hmapcont
    (hpypz.map (schemePointsHomeomorph B S hS U).continuous)
    (hpzp.map (schemePointsHomeomorph B S hS U).continuous) (fun h ↦ ?_) (fun h ↦ ?_)
    ((hvalue py).trans hpymap) ((hvalue p).trans hp) y rfl hyLC (hfibre _) (hfibre _)
  · exact hzne (Subtype.ext (by
      rw [← hpzmap, ← (schemePointsHomeomorph B S hS U).injective h, hpymap]))
  · exact z.2.2 (by rw [← hpzmap, (schemePointsHomeomorph B S hS U).injective h, hp])

end AlgebraicGeometry.Space

end
