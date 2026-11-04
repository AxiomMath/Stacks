module

public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.FirstBlowupPoints
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.FirstBlowupStrictCentre
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.SecondBlowupFamily
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaConicChart
public import StacksFrontier.AlgebraicGeometry.Perfect.InvertibleFibreEulerConstant
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Bijective
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.PushforwardTwist

/-!
# Hironaka's local model: the family over the first centre

Let `k` be a field, `A = k[x, y, z]`, `I = (x, y)`, `J = (x - y², z)`, and let
`T : Bl_{J'}(Bl_I Spec A) ⟶ Spec A` be the two-step tower of Hironaka's example (the source of
[Stacks, Tag 08J1]): blow up `I`, then the strict transform `J'` of `V(J)`
(`AlgebraicGeometry.TwoStepTower.strictTower`).

This file proves that the base change of `T` to the line `V(I) = Spec k[z]` is a proper flat
family over a connected base, and deduces that the Euler characteristic of an invertible module
on the source of `T` is the same on the fibres of `T` over all `k`-points of `V(I)`.

Flatness is checked on two opens of the source of `T`.

* Over the chart `U₂ = Spec k[x₁, y, z]` (`x = x₁·y`) of the first blow-up, after the change of
  coordinates `v = x₁ - y`, the second blow-up is `Bl_{(v,z)} Spec k[v, y, z]`
  ([Stacks, Tag 0805]), whose base change to `V(I)` is flat by
  `Stacks.Examples.HironakaLocalModel.flat_secondBlowup_line`.
* Over the chart `U₁ = Spec k[x, y₁, z]` (`y = x·y₁`), the base change to `V(I)` lies over
  `V(x)`, which is inside the basic open `D(1 - x·y₁²)` missing the strict transform
  `V(1 - x·y₁², z)`. Over that basic open the second blow-up is an isomorphism
  ([Stacks, Tag 02OS]), and the base change of `Spec k[x, y₁, z]_{1 - x·y₁²}` to `V(I)` is
  `Spec k[y₁, z]`, flat over `k[z]`.

## Main results

* `Stacks.Examples.HironakaLocalModel.flat_strictTower_line`: the base change of the tower to
  `V(x, y) = Spec k[z]` is flat over `k[z]`.
* `Stacks.Examples.HironakaLocalModel.isProper_strictTower`: the tower is proper.
* `Stacks.Examples.HironakaLocalModel.eulerSum_eq_of_isPullback_modelKPoint`: for an invertible
  `H` on the source of the tower and two `k`-points `c`, `c'` of `V(x, y)`, the fibres of the
  tower over `c` and `c'` give the same Euler characteristic of the restriction of `H`.

## References

* [Stacks Project, Tag 08J1](https://stacks.math.columbia.edu/tag/08J1)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0BDJ](https://stacks.math.columbia.edu/tag/0BDJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.TwoStepTower AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace Stacks.Examples.HironakaLocalModel

/-! ### Generalities on open immersions and base change -/

/-- In a cartesian square whose right side `f` is an open immersion, every point of the left
corner `Y` mapping into the range of `f` is in the range of the top side. -/
theorem mem_range_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ Y} {snd : P ⟶ X}
    {g : Y ⟶ Z} {f : X ⟶ Z} [IsOpenImmersion f] (h : IsPullback fst snd g f) (y : Y)
    (hy : g y ∈ Set.range f) : y ∈ Set.range fst := by
  obtain ⟨w, rfl⟩ : y ∈ Set.range (pullback.fst g f) := by
    rwa [IsOpenImmersion.range_pullbackFst]
  exact ⟨h.isoPullback.inv w, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]⟩

/-- **Base change of an open of the source.** For an open immersion `e : Y ⟶ X` with
`e ≫ f = m`, the base change `Y ×_Z S ⟶ X ×_Z S` along any `g : S ⟶ Z` is an open immersion over
`S`, whose range contains every point lying over the range of `e`. -/
theorem exists_openImmersion_pullback {X Y Z S : Scheme.{u}} (f : X ⟶ Z) (g : S ⟶ Z)
    (e : Y ⟶ X) [IsOpenImmersion e] (m : Y ⟶ Z) (he : e ≫ f = m) :
    ∃ j : pullback m g ⟶ pullback f g, IsOpenImmersion j ∧
      j ≫ pullback.snd f g = pullback.snd m g ∧
      ∀ x, pullback.fst f g x ∈ Set.range e → x ∈ Set.range j := by
  subst he
  let j : pullback (e ≫ f) g ⟶ pullback f g :=
    pullback.lift (pullback.fst _ _ ≫ e) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition)
  have hj₂ : j ≫ pullback.snd f g = pullback.snd (e ≫ f) g := pullback.lift_snd _ _ _
  have hj₁ : j ≫ pullback.fst f g = pullback.fst (e ≫ f) g ≫ e := pullback.lift_fst _ _ _
  have hleft : IsPullback j (pullback.fst (e ≫ f) g) (pullback.fst f g) e := by
    refine IsPullback.of_right (h₁₂ := pullback.snd f g) (v₁₃ := g) (h₂₂ := f) ?_ hj₁
      (IsPullback.of_hasPullback f g).flip
    rw [hj₂]
    exact (IsPullback.of_hasPullback (e ≫ f) g).flip
  exact ⟨j, MorphismProperty.of_isPullback (P := @IsOpenImmersion) hleft.flip inferInstance, hj₂,
    fun x hx => mem_range_of_isPullback hleft x hx⟩

/-- A point of `Spec S` mapped by `Spec φ` has the inverse image prime. -/
theorem specMap_asIdeal {R S : CommRingCat.{u}} (φ : R ⟶ S) (x : Spec S) :
    (Spec.map φ x).asIdeal = Ideal.comap φ.hom x.asIdeal := rfl

variable (k : Type u) [Field k]

/-- A point on the support of the ideal sheaf of `K` has its prime containing `K`. -/
theorem le_asIdeal_of_mem_support (K : Ideal (Ring3 k)) (q : ambient k)
    (hq : q ∈ (idealSheafOf k K).support) : K ≤ q.asIdeal := by
  change (q : ambient k) ∈ (((idealSheafOf k K).support : TopologicalSpace.Closeds (ambient k)) :
    Set (ambient k)) at hq
  rw [Scheme.IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus] at hq
  intro f hf
  exact hq (show gammaEquiv k f ∈ K.map (gammaEquiv k : Ring3 k →+* Γ(ambient k, ⊤)) from
    Ideal.mem_map_of_mem _ hf)

/-! ### The chart `U₂`: a change of coordinates -/

/-- The change of coordinates `x₁ ↦ v + y` from `U₂ = Spec k[x₁, y, z]` to `Spec k[v, y, z]`. -/
def shiftHom : Ring3 k →ₐ[k] Ring3 k := aeval ![X 0 + X 1, X 1, X 2]

/-- The inverse change of coordinates `v ↦ x₁ - y`. -/
def shiftInv : Ring3 k →ₐ[k] Ring3 k := aeval ![X 0 - X 1, X 1, X 2]

/-- `shiftHom` is a left inverse of `shiftInv`. -/
theorem shiftHom_comp_shiftInv : (shiftHom k).comp (shiftInv k) = AlgHom.id k _ := by
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;> simp [shiftHom, shiftInv]

/-- `shiftInv` is a left inverse of `shiftHom`. -/
theorem shiftInv_comp_shiftHom : (shiftInv k).comp (shiftHom k) = AlgHom.id k _ := by
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;> simp [shiftHom, shiftInv]

/-- The change of coordinates followed by the chart map of `U₂` is the map of the tower. -/
theorem shiftHom_comp_chartHom_one : (shiftHom k).comp (chartHom k 1) = towerMap k := by
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;> simp [shiftHom, chartHom_one_eq, towerMap]

/-- The change of coordinates `shiftHom` is an isomorphism of rings, with inverse `shiftInv`. -/
instance : IsIso (CommRingCat.ofHom (shiftHom k : Ring3 k →+* Ring3 k)) :=
  ⟨⟨CommRingCat.ofHom (shiftInv k : Ring3 k →+* Ring3 k),
    CommRingCat.hom_ext (congrArg AlgHom.toRingHom (shiftInv_comp_shiftHom k)),
    CommRingCat.hom_ext (congrArg AlgHom.toRingHom (shiftHom_comp_shiftInv k))⟩⟩

/-- The change of coordinates carries the strict transform `(x₁ - y, z)` on `U₂` to the
coordinate line `(v, z)`. -/
theorem comap_shift_idealSheafOf :
    (idealSheafOf k (Ideal.span {X 0 - X 1, X 2})).comap
        (Spec.map (CommRingCat.ofHom (shiftHom k : Ring3 k →+* Ring3 k))) =
      idealSheafSpec (secondCentre k) := by
  rw [comap_specMap_idealSheafOf, Ideal.map_span, Set.image_pair]
  congr 3 <;> simp [shiftHom]

/-- **The second blow-up over `U₂`.** There is an open immersion of
`Bl_{(v,z)} Spec k[v, y, z]` into the source of the tower, over `Spec A`, whose range contains
every point lying over the chart `U₂`. -/
theorem exists_chartTwo_openImmersion :
    ∃ e : blowUp (idealSheafSpec (secondCentre k)) ⟶
        blowUp (strictCentre (centreIdeal k) (curveIdeal k)),
      IsOpenImmersion e ∧ e ≫ strictTower (centreIdeal k) (curveIdeal k) = secondBlowupToBase k ∧
      ∀ w, blowUpToBase (strictCentre (centreIdeal k) (curveIdeal k)) w ∈ Set.range (chartι k 1) →
        w ∈ Set.range e := by
  obtain ⟨h₂, sq₂⟩ := exists_isPullback_blowUp_of_comap_eq
    (strictCentre (centreIdeal k) (curveIdeal k)) (chartι k 1) _ (comap_chartι_one_strictCentre k)
  obtain ⟨h₁, sq₁⟩ := exists_isPullback_blowUp_of_comap_eq
    (idealSheafOf k (Ideal.span {X 0 - X 1, X 2}))
    (Spec.map (CommRingCat.ofHom (shiftHom k : Ring3 k →+* Ring3 k))) _ (comap_shift_idealSheafOf k)
  have sq := sq₁.flip.paste_horiz sq₂.flip
  refine ⟨h₁ ≫ h₂, MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq.flip inferInstance,
    ?_, fun w hw => mem_range_of_isPullback sq w ?_⟩
  · rw [strictTower, Category.assoc, ← Category.assoc h₂, ← sq₂.w, Category.assoc,
      chartι_comp_blowUpToBase, ← Category.assoc h₁, ← sq₁.w, Category.assoc, ← Spec.map_comp,
      secondBlowupToBase, ← CommRingCat.ofHom_comp]
    congr 3
    exact congrArg AlgHom.toRingHom (shiftHom_comp_chartHom_one k)
  · obtain ⟨u, hu⟩ := hw
    obtain ⟨u', rfl⟩ :=
      (Spec.map (CommRingCat.ofHom (shiftHom k : Ring3 k →+* Ring3 k))).surjective u
    exact ⟨u', by rw [Scheme.Hom.comp_apply, hu]⟩

/-! ### The chart `U₁`: off the strict transform -/

/-- The equation `1 - x·y₁²` of the strict transform on `U₁ = Spec k[x, y₁, z]`. -/
abbrev unitEq : Ring3 k := 1 - X 0 * X 1 ^ 2

/-- The coordinate ring `k[x, y₁, z]_{1 - x·y₁²}` of the basic open of `U₁` off the strict
transform. -/
abbrev offRing : Type u := Localization.Away (unitEq k)

/-- The basic open `D(1 - x·y₁²)` of `U₁`, as an open of the first blow-up. -/
abbrev offι : Spec (CommRingCat.of (offRing k)) ⟶ blowUp (centreIdeal k) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Ring3 k) (offRing k))) ≫ chartι k 0

/-- The basic open `D(1 - x·y₁²)` of `U₁` over `Spec A`. -/
abbrev offMap : Spec (CommRingCat.of (offRing k)) ⟶ ambient k :=
  Spec.map (CommRingCat.ofHom ((algebraMap (Ring3 k) (offRing k)).comp
    (chartHom k 0 : Ring3 k →+* Ring3 k)))

/-- The basic open `offι` followed by the first blow-up map is `offMap`. -/
theorem offι_comp_blowUpToBase : offι k ≫ blowUpToBase (centreIdeal k) = offMap k := by
  rw [offι, Category.assoc, chartι_comp_blowUpToBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The basic open `D(1 - x·y₁²)` misses the strict transform of `V(J)`. -/
theorem range_offι_subset :
    ((offι k).opensRange : Set (blowUp (centreIdeal k))) ⊆
      ((strictCentre (centreIdeal k) (curveIdeal k)).support : Set (blowUp (centreIdeal k)))ᶜ := by
  rintro _ ⟨d, rfl⟩ hd
  rw [Scheme.Hom.comp_apply] at hd
  have hd' : Spec.map (CommRingCat.ofHom (algebraMap (Ring3 k) (offRing k))) d ∈
      ((strictCentre (centreIdeal k) (curveIdeal k)).comap (chartι k 0)).support := by
    rwa [Scheme.IdealSheafData.support_comap]
  rw [comap_chartι_zero_strictCentre] at hd'
  have hmem := le_asIdeal_of_mem_support k _ _ hd' (Ideal.subset_span (Set.mem_insert _ _))
  rw [specMap_asIdeal, Ideal.mem_comap] at hmem
  exact d.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
    (IsLocalization.Away.algebraMap_isUnit (unitEq k)))

/-- A point of `U₁` on `V(x)` lies in the basic open `D(1 - x·y₁²)`. -/
theorem chartι_zero_mem_range_offι (q : ambient k) (hq : (X 0 : Ring3 k) ∈ q.asIdeal) :
    chartι k 0 q ∈ Set.range (offι k) := by
  have hf : unitEq k ∉ q.asIdeal := fun h => q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := q.asIdeal.add_mem h (q.asIdeal.mul_mem_right (X 1 ^ 2) hq)
    simpa using this))
  have hr : q ∈ Set.range (PrimeSpectrum.comap (algebraMap (Ring3 k) (offRing k))) := by
    rwa [PrimeSpectrum.localization_away_comap_range (offRing k) (unitEq k)]
  obtain ⟨d, hd⟩ := hr
  let d' : Spec (CommRingCat.of (offRing k)) := d
  have hd' : Spec.map (CommRingCat.ofHom (algebraMap (Ring3 k) (offRing k))) d' = q := hd
  exact ⟨d', by rw [offι, Scheme.Hom.comp_apply, hd']⟩

/-- **The second blow-up over `D(1 - x·y₁²)` is an isomorphism**: an open immersion of
`Spec k[x, y₁, z]_{1 - x·y₁²}` into the source of the tower, over `Spec A`, whose range contains
every point lying over that basic open. -/
theorem exists_off_openImmersion :
    ∃ e : Spec (CommRingCat.of (offRing k)) ⟶
        blowUp (strictCentre (centreIdeal k) (curveIdeal k)),
      IsOpenImmersion e ∧ e ≫ strictTower (centreIdeal k) (curveIdeal k) = offMap k ∧
      ∀ w, blowUpToBase (strictCentre (centreIdeal k) (curveIdeal k)) w ∈ Set.range (offι k) →
        w ∈ Set.range e := by
  set J' := strictCentre (centreIdeal k) (curveIdeal k)
  set W := (offι k).opensRange
  have := isIso_blowUpToBase_restrict_of_subset_compl_support J' W (range_offι_subset k)
  let e : Spec (CommRingCat.of (offRing k)) ⟶ blowUp J' :=
    (offι k).isoOpensRange.hom ≫ inv (blowUpToBase J' ∣_ W) ≫ (blowUpToBase J' ⁻¹ᵁ W).ι
  have he : e ≫ blowUpToBase J' = offι k := by
    simp only [e, Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, Scheme.Hom.isoOpensRange_hom_ι]
  refine ⟨e, inferInstance, ?_, fun w hw => ?_⟩
  · rw [strictTower, ← Category.assoc, he, offι_comp_blowUpToBase]
  · obtain ⟨d, hd⟩ := hw
    have h1 : blowUpToBase J' (e d) = offι k d := by rw [← Scheme.Hom.comp_apply, he]
    refine ⟨d, blowUpToBase_injective_of_notMem_support J' ?_ (h1.trans hd)⟩
    rw [h1]
    exact range_offι_subset k ⟨d, rfl⟩

/-! ### The base change of `D(1 - x·y₁²)` to the line -/

/-- The reduction `k[x, y₁, z] ⟶ k[y₁, z]` modulo `x`. -/
def offReduce : Ring3 k →ₐ[k] MvPolynomial (Fin 2) k := aeval ![0, X 0, X 1]

/-- The section `k[y₁, z] ⟶ k[x, y₁, z]`. -/
def offSection : MvPolynomial (Fin 2) k →ₐ[k] Ring3 k := aeval ![X 1, X 2]

/-- The reduction of `1 - x·y₁²` modulo `x` is a unit of `k[y₁, z]`. -/
theorem isUnit_offReduce_unitEq :
    IsUnit ((offReduce k : Ring3 k →+* MvPolynomial (Fin 2) k) (unitEq k)) := by
  simp [offReduce]

/-- The reduction of `k[x, y₁, z]_{1 - x·y₁²}` modulo `x`: `k[y₁, z]`. -/
def offLineMap : offRing k →+* MvPolynomial (Fin 2) k :=
  IsLocalization.Away.lift (unitEq k) (isUnit_offReduce_unitEq k)

/-- `offLineMap` restricts to `offReduce` on `k[x, y₁, z]`. -/
theorem offLineMap_algebraMap (p : Ring3 k) :
    offLineMap k (algebraMap (Ring3 k) (offRing k) p) = offReduce k p :=
  IsLocalization.Away.lift_eq _ _ p

/-- The kernel of the reduction `k[x, y₁, z] ⟶ k[y₁, z]` is the ideal `(x)`. -/
theorem ker_offReduce :
    RingHom.ker (offReduce k : Ring3 k →+* MvPolynomial (Fin 2) k) = Ideal.span {X 0} := by
  refine ker_eq_of_sub_mem _ (offSection k : MvPolynomial (Fin 2) k →+* Ring3 k) _ ?_ ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    simp [offReduce]
  · refine sub_mem_of_forall (((offSection k).comp (offReduce k) : Ring3 k →ₐ[k] _) :
      Ring3 k →+* _) _ ?_ ?_
    · exact fun c => by simp
    · intro i
      fin_cases i <;> simp [offReduce, offSection]

/-- The reduction `offLineMap` of `k[x, y₁, z]_{1 - x·y₁²}` modulo `x` is surjective. -/
theorem offLineMap_surjective : Function.Surjective (offLineMap k) := by
  intro q
  refine ⟨algebraMap (Ring3 k) (offRing k) (offSection k q), ?_⟩
  rw [offLineMap_algebraMap]
  change ((offReduce k).comp (offSection k)) q = q
  have : (offReduce k).comp (offSection k) = AlgHom.id k _ := by
    refine MvPolynomial.algHom_ext fun i => ?_
    fin_cases i <;> simp [offReduce, offSection]
  rw [this]
  rfl

/-- The kernel of `offLineMap` is the ideal generated by `x` in `k[x, y₁, z]_{1 - x·y₁²}`. -/
theorem ker_offLineMap :
    RingHom.ker (offLineMap k) = Ideal.span {algebraMap (Ring3 k) (offRing k) (X 0)} := by
  refine le_antisymm (fun z hz => ?_) ?_
  · obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (unitEq k)) z
    dsimp only at hz ⊢
    have hs : IsUnit (offLineMap k (algebraMap (Ring3 k) (offRing k) (s : Ring3 k))) :=
      (IsLocalization.map_units (offRing k) s).map _
    have ha : offLineMap k (algebraMap (Ring3 k) (offRing k) a) = 0 := by
      rw [← IsLocalization.mk'_spec (offRing k) a s, map_mul, RingHom.mem_ker.1 hz, zero_mul]
    rw [offLineMap_algebraMap] at ha
    have ha' : a ∈ RingHom.ker (offReduce k : Ring3 k →+* MvPolynomial (Fin 2) k) := ha
    rw [ker_offReduce, Ideal.mem_span_singleton] at ha'
    obtain ⟨b, rfl⟩ := ha'
    rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change _ ∈ RingHom.ker _
    rw [RingHom.mem_ker, offLineMap_algebraMap]
    simp [offReduce]

/-- **The base change of `D(1 - x·y₁²)` to `V(x, y)`** is `Spec k[y₁, z]`, over `Spec k[z]` by
`z ↦ z`. -/
theorem isPushout_off :
    IsPushout (CommRingCat.ofHom ((algebraMap (Ring3 k) (offRing k)).comp
        (chartHom k 0 : Ring3 k →+* Ring3 k)))
      (CommRingCat.ofHom (lineMap k : MvPolynomial (Fin 3) k →+* Polynomial k))
      (CommRingCat.ofHom (offLineMap k))
      (CommRingCat.ofHom (lineToChartTwo k : Polynomial k →+* MvPolynomial (Fin 2) k)) := by
  refine isPushout_of_surjective _ _ _ _ ?_ (lineMap_surjective k) (offLineMap_surjective k) ?_
  · refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, offLineMap_algebraMap]
      simp [offReduce, chartHom_zero_eq, lineMap, lineToChartTwo]
    · simp only [RingHom.coe_comp, Function.comp_apply, offLineMap_algebraMap]
      fin_cases i <;> simp [offReduce, chartHom_zero_eq, lineMap, lineToChartTwo]
  · rw [ker_offLineMap, ker_lineMap, Ideal.map_span, Set.image_pair]
    refine le_antisymm ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      refine Ideal.subset_span (Or.inl ?_)
      simp [chartHom_zero_eq]
    · rw [Ideal.span_le]
      rintro _ (rfl | rfl)
      · exact Ideal.subset_span (by simp [chartHom_zero_eq])
      · change _ ∈ Ideal.span _
        rw [Ideal.mem_span_singleton]
        exact ⟨algebraMap (Ring3 k) (offRing k) (X 1), by simp [chartHom_zero_eq]⟩

/-- The base change of `D(1 - x·y₁²)` to the line `V(x, y) = Spec k[z]` is flat over `k[z]`. -/
theorem flat_off_line : Flat (pullback.snd (offMap k) (lineι k)) := by
  have h := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_off k)
  rw [← h.isoPullback_inv_snd]
  have : Flat (Spec.map (CommRingCat.ofHom
      (lineToChartTwo k : Polynomial k →+* MvPolynomial (Fin 2) k))) := by
    rw [Flat.SpecMap_iff]
    exact flat_lineToChartTwo k
  infer_instance

/-! ### Flatness of the family over `V(x, y)` -/

/-- A point of the source of the tower lying over the line `V(x, y)` and over the chart `U₁` has
its `U₁`-coordinate on `V(x)`. -/
theorem mem_asIdeal_of_chartι_zero {w : blowUp (strictCentre (centreIdeal k) (curveIdeal k))}
    {s : Spec (CommRingCat.of (Polynomial k))}
    (hw : strictTower (centreIdeal k) (curveIdeal k) w = lineι k s) {q : ambient k}
    (hq : chartι k 0 q = blowUpToBase (strictCentre (centreIdeal k) (curveIdeal k)) w) :
    (X 0 : Ring3 k) ∈ q.asIdeal := by
  have h : Spec.map (CommRingCat.ofHom (chartHom k 0 : Ring3 k →+* Ring3 k)) q = lineι k s := by
    rw [← hw, strictTower, Scheme.Hom.comp_apply, ← hq, ← Scheme.Hom.comp_apply,
      chartι_comp_blowUpToBase]
  have h' := congrArg PrimeSpectrum.asIdeal h
  rw [specMap_asIdeal, specMap_asIdeal] at h'
  have hX : (X 0 : Ring3 k) ∈ Ideal.comap (CommRingCat.ofHom (lineMap k :
      MvPolynomial (Fin 3) k →+* Polynomial k)).hom s.asIdeal := by
    rw [Ideal.mem_comap]
    simp [lineMap]
  rw [← h', Ideal.mem_comap] at hX
  simpa [chartHom_zero_eq] using hX

/-- **(M1) The family of Hironaka's local model over the first centre is flat**: the base change
of the tower `Bl_{J'}(Bl_I Spec A) ⟶ Spec A` to the line `V(I) = V(x, y) = Spec k[z]` is flat
over `k[z]`. -/
theorem flat_strictTower_line :
    Flat (pullback.snd (strictTower (centreIdeal k) (curveIdeal k)) (lineι k)) := by
  set T := strictTower (centreIdeal k) (curveIdeal k)
  obtain ⟨e₁, he₁, hT₁, hr₁⟩ := exists_off_openImmersion k
  obtain ⟨e₂, he₂, hT₂, hr₂⟩ := exists_chartTwo_openImmersion k
  obtain ⟨j₁, hj₁, hs₁, hc₁⟩ := exists_openImmersion_pullback T (lineι k) e₁ _ hT₁
  obtain ⟨j₂, hj₂, hs₂, hc₂⟩ := exists_openImmersion_pullback T (lineι k) e₂ _ hT₂
  refine flat_of_two_opens _ j₁ j₂ (fun x => ?_) ?_ ?_
  · set w := pullback.fst T (lineι k) x
    have hw : T w = lineι k (pullback.snd T (lineι k) x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    obtain ⟨i, q, hq⟩ := exists_chartι_eq k (blowUpToBase _ w)
    fin_cases i
    · exact Or.inl (hc₁ x (hr₁ w (hq ▸ chartι_zero_mem_range_offι k q
        (mem_asIdeal_of_chartι_zero k hw hq))))
    · exact Or.inr (hc₂ x (hr₂ w ⟨q, hq⟩))
  · rw [hs₁]
    exact flat_off_line k
  · rw [hs₂]
    exact flat_secondBlowup_line k

/-! ### Properness and the Euler characteristic of the fibres -/

/-- The tower of the local model is proper. -/
theorem isProper_strictTower : IsProper (strictTower (centreIdeal k) (curveIdeal k)) := by
  have hI := isFiniteType_of_isLocallyNoetherian (centreIdeal k)
  have := isProper_blowUpToBase hI
  have := isProper_blowUpToBase (isFiniteType_strictCentre hI (curveIdeal k))
  infer_instance

/-- The `k`-point `z = t` of the line `V(x, y) = Spec k[z]`. -/
abbrev linePoint (t : k) : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom t))

/-- A `k`-point of `Spec A` on `V(x, y)` is a `k`-point of the line. -/
theorem linePoint_comp_lineι (c : Fin 3 → k) (hc0 : c 0 = 0) (hc1 : c 1 = 0) :
    linePoint k (c 2) ≫ lineι k = HironakaConicChart.modelKPoint k c := by
  rw [linePoint, lineι, ← Spec.map_comp, ← CommRingCat.ofHom_comp, HironakaConicChart.modelKPoint]
  congr 2
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp [lineMap]
  · fin_cases i <;> simp [lineMap, hc0, hc1]

/-- A fibre of the tower over a `k`-point of `V(x, y)` is a fibre of the family over the line. -/
theorem exists_isPullback_line (c : Fin 3 → k) (hc0 : c 0 = 0) (hc1 : c 1 = 0) {Z : Scheme.{u}}
    (q : Z ⟶ blowUp (strictCentre (centreIdeal k) (curveIdeal k))) (g : Z ⟶ Spec (.of k))
    (sq : IsPullback q g (strictTower (centreIdeal k) (curveIdeal k))
      (HironakaConicChart.modelKPoint k c)) :
    ∃ q₁ : Z ⟶ pullback (strictTower (centreIdeal k) (curveIdeal k)) (lineι k),
      q₁ ≫ pullback.fst _ _ = q ∧
      IsPullback q₁ g (pullback.snd (strictTower (centreIdeal k) (curveIdeal k)) (lineι k))
        (linePoint k (c 2)) := by
  have hpt := linePoint_comp_lineι k c hc0 hc1
  refine ⟨pullback.lift q (g ≫ linePoint k (c 2)) (by rw [Category.assoc, hpt]; exact sq.w),
    pullback.lift_fst _ _ _, ?_⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rwa [pullback.lift_fst, hpt]

/-- The Euler characteristic of an invertible module is the same on the fibres of the tower over
two `k`-points of `V(x, y)`, with the centres spelled `centreIdeal`, `curveIdeal`. -/
theorem eulerSum_eq_of_isPullback_linePoint
    (H : (blowUp (strictCentre (centreIdeal k) (curveIdeal k))).Modules)
    [hH : SheafOfModules.IsInvertible
      (blowUp (strictCentre (centreIdeal k) (curveIdeal k))).presheaf
      (blowUp (strictCentre (centreIdeal k) (curveIdeal k))).ringCatSheaf.2 H]
    (c c' : Fin 3 → k) (hc0 : c 0 = 0) (hc1 : c 1 = 0) (hc'0 : c' 0 = 0) (hc'1 : c' 1 = 0)
    {Z Z' : Scheme.{u}}
    (q : Z ⟶ blowUp (strictCentre (centreIdeal k) (curveIdeal k))) (g : Z ⟶ Spec (.of k))
    (sq : IsPullback q g (strictTower (centreIdeal k) (curveIdeal k))
      (HironakaConicChart.modelKPoint k c))
    (q' : Z' ⟶ blowUp (strictCentre (centreIdeal k) (curveIdeal k))) (g' : Z' ⟶ Spec (.of k))
    (sq' : IsPullback q' g' (strictTower (centreIdeal k) (curveIdeal k))
      (HironakaConicChart.modelKPoint k c')) :
    eulerSum k g ((Scheme.Modules.pullback q).obj H) =
      eulerSum k g' ((Scheme.Modules.pullback q').obj H) := by
  set T := strictTower (centreIdeal k) (curveIdeal k)
  have := isProper_strictTower k
  have := flat_strictTower_line k
  have : PreconnectedSpace (Spec (CommRingCat.of (Polynomial k))) :=
    inferInstanceAs (PreconnectedSpace (PrimeSpectrum (Polynomial k)))
  have : SheafOfModules.IsInvertible (pullback T (lineι k)).presheaf
      (pullback T (lineι k)).ringCatSheaf.2
      ((Scheme.Modules.pullback (pullback.fst T (lineι k))).obj H) :=
    SheafOfModules.isInvertible_pullback _ H
  obtain ⟨q₁, hq₁, sq₁⟩ := exists_isPullback_line k c hc0 hc1 q g sq
  obtain ⟨q₁', hq₁', sq₁'⟩ := exists_isPullback_line k c' hc'0 hc'1 q' g' sq'
  have key := eulerSum_eq_of_isPullback_of_isInvertible (pullback.snd T (lineι k))
    ((Scheme.Modules.pullback (pullback.fst T (lineι k))).obj H) _ _ q₁ g sq₁ q₁' g' sq₁'
  rwa [← eulerSum_pullback_comp, ← eulerSum_pullback_comp, hq₁, hq₁'] at key

/-- **The Euler characteristic of an invertible module is the same on the fibres of the tower over
all `k`-points of `V(x, y)`.** For the tower `T : Bl_{J'}(Bl_I Spec A) ⟶ Spec A`, `A = k[x, y, z]`,
`I = (x, y)`, `J = (x - y², z)`, an invertible module `H` on its source, and two `k`-points
`c`, `c'` of `V(x, y)` with fibres given by cartesian squares, `χ(T_c, H|_{T_c}) =
χ(T_{c'}, H|_{T_{c'}})`: the family `T ×_{Spec A} V(x, y) ⟶ V(x, y) = Spec k[z]` is proper and
flat over a connected base ([Stacks, Tag 0BDJ]). -/
theorem eulerSum_eq_of_isPullback_modelKPoint
    (H : (blowUp (strictCentre (HironakaConicChart.modelIdealSheafI k)
      (HironakaConicChart.modelIdealSheafJ k))).Modules)
    [SheafOfModules.IsInvertible (blowUp (strictCentre (HironakaConicChart.modelIdealSheafI k)
      (HironakaConicChart.modelIdealSheafJ k))).presheaf
      (blowUp (strictCentre (HironakaConicChart.modelIdealSheafI k)
        (HironakaConicChart.modelIdealSheafJ k))).ringCatSheaf.2 H]
    (c c' : Fin 3 → k) (hc0 : c 0 = 0) (hc1 : c 1 = 0) (hc'0 : c' 0 = 0) (hc'1 : c' 1 = 0)
    {Z Z' : Scheme.{u}}
    (q : Z ⟶ blowUp (strictCentre (HironakaConicChart.modelIdealSheafI k)
      (HironakaConicChart.modelIdealSheafJ k))) (g : Z ⟶ Spec (.of k))
    (sq : IsPullback q g (strictTower (HironakaConicChart.modelIdealSheafI k)
      (HironakaConicChart.modelIdealSheafJ k)) (HironakaConicChart.modelKPoint k c))
    (q' : Z' ⟶ blowUp (strictCentre (HironakaConicChart.modelIdealSheafI k)
      (HironakaConicChart.modelIdealSheafJ k))) (g' : Z' ⟶ Spec (.of k))
    (sq' : IsPullback q' g' (strictTower (HironakaConicChart.modelIdealSheafI k)
      (HironakaConicChart.modelIdealSheafJ k)) (HironakaConicChart.modelKPoint k c')) :
    eulerSum k g ((Scheme.Modules.pullback q).obj H) =
      eulerSum k g' ((Scheme.Modules.pullback q').obj H) :=
  eulerSum_eq_of_isPullback_linePoint k H (hH := ‹_›) c c' hc0 hc1 hc'0 hc'1 q g sq q' g' sq'

end Stacks.Examples.HironakaLocalModel

end
