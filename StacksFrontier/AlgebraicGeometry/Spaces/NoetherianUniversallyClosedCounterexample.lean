module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.AffineSpaceFibreChartConstants
public import StacksFrontier.AlgebraicGeometry.Scheme.ClosedPointRationalPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.Examples.Spaces.NonSeparatedGroupSpace

/-!
# A universally closed morphism of finite type without the existence part

Over a field `k` of characteristic zero, the structure morphism `𝔸¹_k/ℤ ⟶ Spec k` of the
quotient of the affine line by the integer translations is of finite type over the Noetherian
scheme `Spec k` and universally closed (Stacks 03IV), but it does not satisfy the existence part
of the valuative criterion, as the introduction of Stacks section 03K9 records. Hence the
implication from (1) to (2) of Stacks 0H1Y fails for a morphism of finite type over a locally
Noetherian algebraic space, and the five conditions there are not equivalent in that
generality.

## Main results

* `AlgebraicGeometry.AffineLineTranslation.not_valuativeCriterion_existence_structureMap`: the
  structure morphism of `𝔸¹_k/ℤ` does not satisfy the existence part of the valuative criterion.
* `AlgebraicGeometry.AffineLineTranslation.not_isDecent_structureMap`: nor is it decent.
* `AlgebraicGeometry.Space.exists_universallyClosed_not_valuativeCriterion_existence`: there is
  a universally closed morphism of finite type of algebraic spaces with locally Noetherian
  target which does not satisfy the existence part of the valuative criterion.
* `AlgebraicGeometry.Space.not_forall_universallyClosed_tfae_of_isLocallyNoetherian`: the five
  conditions of Stacks 0H1Y are not equivalent for every morphism of finite type with locally
  Noetherian target.

## Implementation notes

The valuative square is the one of the point `1/t` of the line with values in the field
`K = k((t))` of Laurent series, the fraction field of the discrete valuation ring `R = k[[t]]`;
the argument works for any valuation ring with a nonzero element `t` of its maximal ideal. Let
`R ⟶ R'` be a local homomorphism of valuation rings, with fraction field `K'` over `K`, and
suppose `Spec R' ⟶ 𝔸¹_k/ℤ` extends the point. The chart of the quotient is locally surjective,
so over a flat morphism `c ⟶ Spec R'` locally of finite presentation whose image contains the
closed point the extension is the image of a function `a` on `c`. As the morphism is flat, a
point `u'` of `c` over the generic point specializes to a point `u` over the closed point. Over
the residue field at `u'` the two lifts `a` and `1/t` of one point of the quotient differ by an
integer `n`, the kernel pair of the chart being the graph of the action. So the function
`t (a - n) - 1` vanishes at `u'`, hence at its specialization `u`, where `t` vanishes: a
contradiction.

## References

* [Stacks Project, Tag 0H1Y](https://stacks.math.columbia.edu/tag/0H1Y)
* [Stacks Project, Tag 03IV](https://stacks.math.columbia.edu/tag/03IV)
* [Stacks Project, Tag 03K9](https://stacks.math.columbia.edu/tag/03K9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Polynomial

universe u

namespace AlgebraicGeometry.AffineLineTranslation

open AffineLineInvolution Stacks.Groupoids

variable (k : Type u) [Field k] [CharZero k] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of k)))
  [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]

/-- The structure morphism of `𝔸¹_k/ℤ` does not satisfy the existence part of the valuative
criterion, as soon as the site contains the spectrum of a valuation ring `R` over `k` with a
nonzero element `t` of its maximal ideal, and that of its fraction field `K`: the `K`-point
`1/t` of `𝔸¹_k/ℤ` extends to no valuation ring dominating `R` in an extension of `K`. -/
theorem not_valuativeCriterion_existence_of_mem_maximalIdeal
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : B.Contains (Spec (.of R))) (hK : B.Contains (Spec (.of K)))
    (base : Spec (.of R) ⟶ Spec (.of k)) (t : R) (ht0 : t ≠ 0)
    (htmax : t ∈ IsLocalRing.maximalIdeal R) :
    ¬ Space.ValuativeCriterion.Existence
      (structureMap k B hS (contains_affineLine k B hS)) := by
  classical
  intro hex
  have hU : B.Contains (affineLine k).left := contains_affineLine k B hS
  let J := BigFppfOver.topology B (Spec (.of k)) hS
  let F : BigFppfOver B (Spec (.of k)) hS ⥤ Over (Spec (.of k)) := Over.post B.inclusion
  have : F.Full := inferInstanceAs (Over.post (X := B.obj hS) B.inclusion).Full
  have : F.Faithful := inferInstanceAs (Over.post (X := B.obj hS) B.inclusion).Faithful
  let V : BigFppfOver B (Spec (.of k)) hS := siteAffineLine k B hS hU
  let jr : PreRelation (Space.actionRelationScheme (affineLine k) (Multiplicative ℤ))
      (F.obj V) := Space.actionRelation (affineLine k) (Multiplicative ℤ) (translationAction k)
  have hjEER : Stacks.Groupoids.IsEtaleEquivalenceRelation jr :=
    isEtaleEquivalenceRelation_translationActionRelation k
  have : Mono jr := @mono_of_isEtaleEquivalenceRelation _ _ _ jr hjEER
  let X : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u := translationQuotient k B hS hU
  let chart : yoneda.obj V ⟶ X := quotientChart J F V jr
  have hchartnat : ∀ {T T' : BigFppfOver B (Spec (.of k)) hS} (f : T' ⟶ T) (x : T ⟶ V),
      chart.app (op T') (f ≫ x) = X.map f.op (chart.app (op T) x) := by
    intro T T' f x
    simpa using congrArg (fun g ↦ g x) (chart.naturality f.op)
  have ht0' : algebraMap R K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ht0
  -- The `K`-point `1/t` of the line.
  let G : BigFppfOver B (Spec (.of k)) hS :=
    siteObject B (Spec (.of k)) hS hK (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base)
  let a : G ⟶ V := Over.homMk
    (⟨AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base)
      (fun _ ↦ (Scheme.ΓSpecIso (.of K)).inv (algebraMap R K t)⁻¹)⟩)
    (by
      apply ObjectProperty.hom_ext
      exact AffineSpace.homOfVector_over _ _)
  have hacoord : lineCoord k (F.map a) =
      (Scheme.ΓSpecIso (.of K)).inv (algebraMap R K t)⁻¹ :=
    AffineSpace.homOfVector_appTop_coord _ _ _
  let sq : Space.ValuativeSquare (structureMap k B hS hU) :=
    { R := R
      K := K
      ring_mem := hR
      field_mem := hK
      base := base
      generic := yoneda.map a ≫ chart
      special := (Space.yonedaMkIdTerminal B (Spec (.of k)) hS).from _
      comm := (Space.yonedaMkIdTerminal B (Spec (.of k)) hS).hom_ext _ _ }
  obtain ⟨e, ⟨l⟩⟩ := hex sq
  have := e.isLocalHom
  let R' := e.square.R
  let K' := e.square.K
  let T : BigFppfOver B (Spec (.of k)) hS :=
    siteObject B (Spec (.of k)) hS e.square.ring_mem e.square.base
  let TK : BigFppfOver B (Spec (.of k)) hS :=
    siteObject B (Spec (.of k)) hS e.square.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ e.square.base)
  let ginc : TK ⟶ T := Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) :
      B.obj e.square.field_mem ⟶ B.obj e.square.ring_mem)
  -- The section of the quotient over `Spec R'` given by the dotted arrow.
  let s : X.obj (op T) := yonedaEquiv l.map
  have hsgen : X.map ginc.op s = chart.app (op TK) (e.genericOver ≫ a) := by
    have h := congrArg yonedaEquiv (l.generic_comm.trans e.generic_comm)
    rw [← yonedaEquiv_naturality] at h
    refine h.trans ?_
    show yonedaEquiv (yoneda.map e.genericOver ≫ yoneda.map a ≫ chart) = _
    rw [← Category.assoc, ← Functor.map_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  -- It lifts to the chart over a flat arrow through the closed point of `Spec R'`.
  have : Presheaf.IsLocallySurjective J chart := isLocallySurjective_quotientChart J F V jr
  obtain ⟨c, q, ⟨ℓ, hℓ⟩, hflat, -, ⟨u, hu⟩⟩ := BigFppfOver.exists_mem_of_mem_topology B
    (Spec (.of k)) hS (Presheaf.IsLocallySurjective.imageSieve_mem (J := J) (f := chart)
      (show ToType (X.obj (op T)) from s))
    (show (BigFppfOver.toScheme B (Spec (.of k)) hS).obj T from IsLocalRing.closedPoint R')
  let C := (BigFppfOver.toScheme B (Spec (.of k)) hS).obj c
  let qm : C ⟶ Spec (.of R') := (BigFppfOver.toScheme B (Spec (.of k)) hS).map q
  have hqw : qm ≫ e.square.base = B.inclusion.map c.hom := by
    have h := congrArg B.inclusion.map (Over.w q)
    rwa [Functor.map_comp] at h
  have hqu : qm u = IsLocalRing.closedPoint R' := hu
  -- A point of `c` over the generic point of `Spec R'` specializing to `u`.
  let η : PrimeSpectrum R' := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : η ⤳ qm u := by
    rw [hqu]
    exact (PrimeSpectrum.le_iff_specializes η _).mp bot_le
  have : Flat qm := hflat
  obtain ⟨u', hu'u, hu'η⟩ := Flat.generalizingMap qm hη
  -- The residue field at `u'`, a field of the site over the fraction field `K'`.
  have hN : B.Contains (Spec (C.residueField u')) :=
    (Scheme.size_le_of_mono_quasiCompact (C.fromSpecResidueField u')).trans_lt c.left.property
  obtain ⟨ψ, hψ, hψinj⟩ : ∃ ψ : CommRingCat.of R' ⟶ C.residueField u',
      Spec.map ψ = C.fromSpecResidueField u' ≫ qm ∧ Function.Injective ψ.hom := by
    refine ⟨Spec.preimage (C.fromSpecResidueField u' ≫ qm), Spec.map_preimage _, ?_⟩
    let : (qm u').asIdeal.IsPrime := (qm u').isPrime
    have h0 : Function.Injective (algebraMap R' (qm u').asIdeal.ResidueField) := by
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_algebraMap_residueField, hu'η]
    rw [Spec.preimage_fromSpecResidueField_comp qm u', CommRingCat.hom_comp,
      CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp, CommRingCat.hom_ofHom]
    exact (qm.residueFieldMap u').hom.injective.comp
      ((Scheme.Spec.residueFieldIso _ (qm u')).inv.hom.injective.comp h0)
  let g : R' →+* C.residueField u' := ψ.hom
  obtain ⟨ψ', hψ'0⟩ : ∃ ψ' : K' →+* C.residueField u', ψ'.comp (algebraMap R' K') = g :=
    ⟨IsFractionRing.lift (A := R') (K := K') (g := g) hψinj,
      RingHom.ext fun x ↦ IsFractionRing.lift_algebraMap (A := R') (K := K') (g := g) hψinj x⟩
  have hψ' : CommRingCat.ofHom (algebraMap R' K') ≫ CommRingCat.ofHom ψ' = ψ := by
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, hψ'0]
  let N : BigFppfOver B (Spec (.of k)) hS :=
    Over.mk (⟨C.fromSpecResidueField u' ≫ B.inclusion.map c.hom⟩ : B.obj hN ⟶ B.obj hS)
  let wc : N ⟶ c := Over.homMk (⟨C.fromSpecResidueField u'⟩ : B.obj hN ⟶ c.left)
    (by
      apply ObjectProperty.hom_ext
      rfl)
  let wK : N ⟶ TK := Over.homMk (⟨Spec.map (CommRingCat.ofHom ψ')⟩ :
      B.obj hN ⟶ B.obj e.square.field_mem) (by
    apply ObjectProperty.hom_ext
    show Spec.map (CommRingCat.ofHom ψ') ≫ Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
      e.square.base = C.fromSpecResidueField u' ≫ B.inclusion.map c.hom
    rw [← Category.assoc, ← Spec.map_comp, hψ', hψ, Category.assoc, hqw])
  have hcomm : wc ≫ q = wK ≫ ginc := by
    refine BigFppfOver.hom_ext ?_
    rw [Functor.map_comp, Functor.map_comp]
    show C.fromSpecResidueField u' ≫ qm =
      Spec.map (CommRingCat.ofHom ψ') ≫ Spec.map (CommRingCat.ofHom (algebraMap R' K'))
    rw [← Spec.map_comp, hψ', hψ]
  -- The two lifts to the line of the point of the quotient over the residue field.
  have hNeq : chart.app (op N) (wc ≫ ℓ) = chart.app (op N) (wK ≫ e.genericOver ≫ a) := by
    rw [hchartnat wc ℓ, hℓ, hchartnat wK (e.genericOver ≫ a), ← hsgen,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hcomm]
  have : Unique (F.obj N).left := by
    show Unique (Spec (C.residueField u'))
    infer_instance
  have hrel : jr.Rel (F.map (wc ≫ ℓ)) (F.map (wK ≫ e.genericOver ≫ a)) :=
    (quotientChart_app_eq_iff_rel J F V jr
      (isPreEquivalenceRelation_of_isEtaleEquivalenceRelation jr)
      (isSheaf_points B (Spec (.of k)) hS _) (isSheaf_points B (Spec (.of k)) hS _)
      (wc ≫ ℓ) (wK ≫ e.genericOver ≫ a)).1 hNeq
  obtain ⟨gz, hgz⟩ := Space.exists_smul_eq_of_actionRelation_rel (affineLine k)
    (Multiplicative ℤ) (translationAction k) hrel
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, Multiplicative.ofAdd n = gz := ⟨gz.toAdd, ofAdd_toAdd gz⟩
  have hinj := (Scheme.ΓSpecIso (C.residueField u')).commRingCatIsoToRingEquiv.symm.injective
  -- Read on coordinates at `u'`: the function `A` on `c` takes the value `1/t + n` there.
  let ρ : R →+* R' := e.ringMap
  let φ : K →+* K' := e.fieldMap
  let A : Γ(C, ⊤) := lineCoord k (F.map ℓ)
  have e1 : lineCoord k (F.map (wc ≫ ℓ)) =
      (Scheme.ΓSpecIso (C.residueField u')).inv (C.Γevaluation u' A) := by
    rw [Functor.map_comp]
    exact (lineCoord_comp k (F.map wc) (F.map ℓ)).trans
      (Scheme.fromSpecResidueField_appTop_apply u' A)
  have e2 : lineCoord k (F.map (wK ≫ e.genericOver ≫ a) ≫
      (translationAction k (Multiplicative.ofAdd n)).asIso.hom) =
      (Scheme.ΓSpecIso (C.residueField u')).inv (ψ' (φ (algebraMap R K t)⁻¹) + n) := by
    refine (lineCoord_comp k _ _).trans ?_
    show (F.map (wK ≫ e.genericOver ≫ a)).left.appTop
      (((translationAction k (Multiplicative.ofAdd n)).asIso.hom.left).appTop
        (AffineSpace.coord (Spec (.of k)) PUnit.unit)) = _
    rw [translationAction_apply]
    refine ((F.map (wK ≫ e.genericOver ≫ a)).left.appTop.hom.map_add _ _).trans ?_
    rw [map_add]
    refine congrArg₂ (· + ·) ?_ ((map_intCast _ n).trans (map_intCast _ n).symm)
    show lineCoord k (F.map wK ≫ F.map e.genericOver ≫ F.map a) = _
    rw [lineCoord_comp, lineCoord_comp k (F.map e.genericOver) (F.map a), hacoord]
    show (Spec.map (CommRingCat.ofHom ψ')).appTop
      ((B.inclusion.map e.genericOver.left).appTop _) = _
    rw [e.genericOver_left, Scheme.specMap_appTop_ΓSpecIso_inv,
      Scheme.specMap_appTop_ΓSpecIso_inv]
    rfl
  have hA : C.Γevaluation u' A = ψ' (φ (algebraMap R K t)⁻¹) + n :=
    hinj (e1.symm.trans ((congrArg (lineCoord k) hgz).trans e2))
  -- The function `t` on `c`, pulled back from `Spec R'`.
  let tc : Γ(C, ⊤) := qm.appTop ((Scheme.ΓSpecIso (.of R')).inv (ρ t))
  have htc : C.Γevaluation u' tc = ψ' (φ (algebraMap R K t)) := by
    apply hinj
    show (Scheme.ΓSpecIso (C.residueField u')).inv _ = (Scheme.ΓSpecIso _).inv _
    rw [← Scheme.fromSpecResidueField_appTop_apply, ← CommRingCat.comp_apply,
      ← Scheme.Hom.comp_appTop, ← hψ, Scheme.specMap_appTop_ΓSpecIso_inv]
    congr 1
    show g (ρ t) = _
    rw [← hψ'0, RingHom.comp_apply, ← RingHom.comp_apply (algebraMap R' K') ρ, e.fraction_comm,
      RingHom.comp_apply]
  -- The function `t (A - n) - 1` vanishes at `u'`, hence at its specialization `u`.
  let f₀ : Γ(C, ⊤) := tc * (A - n) - 1
  have hu'f : C.Γevaluation u' f₀ = 0 := by
    simp only [f₀, map_sub, map_mul, map_one, map_intCast, htc, hA, add_sub_cancel_right]
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ ht0', map_one, map_one, sub_self]
  have huf : C.Γevaluation u f₀ = 0 := by
    refine (C.evaluation_eq_zero_iff_notMem_basicOpen u (U := ⊤) trivial f₀).mpr fun hmem ↦ ?_
    exact (C.evaluation_eq_zero_iff_notMem_basicOpen u' (U := ⊤) trivial f₀).mp hu'f
      (hu'u.mem_open (C.basicOpen f₀).isOpen hmem)
  -- But `t` vanishes at `u`, which lies over the closed point.
  have hρt : ρ t ∈ IsLocalRing.maximalIdeal R' := map_nonunit ρ t htmax
  have hut : C.Γevaluation u tc = 0 := by
    refine (C.evaluation_eq_zero_iff_notMem_basicOpen u (U := ⊤) trivial tc).mpr fun hmem ↦ ?_
    change u ∈ C.basicOpen (qm.app ⊤ _) at hmem
    rw [← Scheme.preimage_basicOpen, basicOpen_eq_of_affine] at hmem
    change qm u ∈ PrimeSpectrum.basicOpen (ρ t) at hmem
    rw [hqu] at hmem
    exact (PrimeSpectrum.mem_basicOpen (ρ t) (IsLocalRing.closedPoint R')).mp hmem hρt
  have : C.Γevaluation u f₀ = -1 := by
    simp only [f₀, map_sub, map_mul, map_one, hut, zero_mul, zero_sub]
  exact one_ne_zero (neg_eq_zero.mp (this.symm.trans huf))

/-- **The structure morphism of `𝔸¹_k/ℤ` does not satisfy the existence part of the valuative
criterion.** For a field `k` of characteristic zero, the point `1/t` of `𝔸¹_k/ℤ` with values in
the field `k((t))` of Laurent series extends to no valuation ring dominating `k[[t]]` in any
extension of `k((t))`.

This is the failure recorded in the introduction of Stacks section 03K9; the morphism is
nevertheless universally closed, by Stacks 03IV. -/
theorem not_valuativeCriterion_existence_structureMap :
    ¬ Space.ValuativeCriterion.Existence
      (structureMap k B hS (contains_affineLine k B hS)) := by
  have hpow : Cardinal.mk k ^ Cardinal.aleph0 ≤ (Spec (.of k)).size ^ Cardinal.aleph0 :=
    Cardinal.power_le_power_right (by rw [Scheme.size_Spec]; exact le_max_right _ _)
  have key : ∀ (A : Type u) [CommRing A] (ι : Type) [Countable ι] (f : A → ι → k),
      Function.Injective f → B.Contains (Spec (.of A)) := fun A _ ι _ f hf ↦ by
    refine Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit (.of A) hS
      ((Cardinal.mk_le_of_injective hf).trans ?_ |>.trans hpow)
    simpa using Cardinal.power_le_power_left (Cardinal.mk_ne_zero k)
      (show Cardinal.lift.{u} (Cardinal.mk ι) ≤ _ by simp)
  refine not_valuativeCriterion_existence_of_mem_maximalIdeal k B hS (PowerSeries k)
    (LaurentSeries k)
    (key _ ℕ (fun f n ↦ PowerSeries.coeff n f) (fun _ _ h ↦ PowerSeries.ext (congrFun h)))
    (key _ ℤ HahnSeries.coeff HahnSeries.coeff_injective)
    (Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k)))) PowerSeries.X
    PowerSeries.X_ne_zero ?_
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
  simp

/-- The structure morphism of `𝔸¹_k/ℤ` is not decent, for a field `k` of characteristic zero:
its source is not a decent algebraic space (Stacks 03ID), while a decent morphism to the
decent space `Spec k` has a decent source. -/
theorem not_isDecent_structureMap :
    ¬ Space.IsDecent B (Spec (.of k)) hS (structureMap k B hS (contains_affineLine k B hS)) :=
  fun hdec ↦ not_isDecentSpace_translationQuotient k B hS
    (Scheme.size_Spec_lt_of_isLocalization B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      (nonZeroDivisors k[X]) (RatFunc k)
      (Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit k k[X] hS))
    (Space.isDecentSpace_of_isDecent B (Spec (.of k)) hS
      (Stacks.Examples.NonSeparatedGroupSpace.isAlgebraicSpace_translationQuotient k B hS)
      (isAlgebraicSpace_yoneda B (Spec (.of k)) hS _) _
      (Space.isDecentSpace_yoneda B (Spec (.of k)) hS _) hdec)

end AlgebraicGeometry.AffineLineTranslation

namespace AlgebraicGeometry.Space

open AffineLineTranslation Stacks.Examples.NonSeparatedGroupSpace

/-- Pullbacks of presheaves on a big fppf site (instance search times out without this
shortcut). -/
instance (priority := high) hasPullback_presheaf_noetherianUniversallyClosedCounterexample
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Universal closedness does not give the existence part of the valuative criterion over a
locally Noetherian base.** There is a universally closed morphism `f : X ⟶ Y` of finite type of
algebraic spaces over a scheme `S`, with `Y` locally Noetherian, which does not satisfy the
existence part of the valuative criterion, and which is not decent.

The morphism is the structure morphism `𝔸¹_ℚ/ℤ ⟶ Spec ℚ` of Stacks 03IV. -/
theorem exists_universallyClosed_not_valuativeCriterion_existence :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
      (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X)
      (_ : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y),
      IsFiniteType B S hS f ∧
        HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) ∧
        UniversallyClosed B S hS f ∧ ¬ ValuativeCriterion.Existence f ∧
        ¬ IsDecent B S hS f := by
  obtain ⟨B, hB⟩ := BigFppfSite.exists_contains (Spec (.of (ULift.{u} ℚ)))
  let : CharZero (ULift.{u} ℚ) := (ULift.ringEquiv : ULift.{u} ℚ ≃+* ℚ).toRingHom.charZero
  let := BigFppfOver.hasSheafify_type B (Spec (.of (ULift.{u} ℚ))) hB
  refine ⟨B, _, hB, _, _, isAlgebraicSpace_translationQuotient _ B hB,
    isAlgebraicSpace_yoneda B _ hB _, structureMap _ B hB (contains_affineLine _ B hB),
    isFiniteType_translationQuotient _ B hB, ?_, universallyClosed_structureMap _ B hB _,
    not_valuativeCriterion_existence_structureMap _ B hB, not_isDecent_structureMap _ B hB⟩
  refine hasEtaleLocalProperty_of_representable B _ hB _ _ _ (Iso.refl _) ?_
  exact inferInstanceAs (IsLocallyNoetherian (Spec (.of (ULift.{u} ℚ))))

/-- **The five conditions of Stacks 0H1Y are not equivalent for every morphism of finite type
over a locally Noetherian algebraic space.** For the structure morphism `𝔸¹_ℚ/ℤ ⟶ Spec ℚ`
condition (1), universal closedness, holds and condition (2), the existence part of the valuative
criterion, fails. The equivalence does hold for a decent morphism, which is
`AlgebraicGeometry.Space.universallyClosed_tfae_of_isLocallyNoetherian`. -/
theorem not_forall_universallyClosed_tfae_of_isLocallyNoetherian :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS X →
        IsAlgebraicSpace B S hS Y → ∀ f : X ⟶ Y, IsFiniteType B S hS f →
        HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) →
        List.TFAE
          [UniversallyClosed B S hS f,
            ValuativeCriterion.Existence f,
            ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
              IsSurjective B S hS g ∧ IsEtale B S hS g ∧
                ∀ n : ℕ, ∃ (W : BigFppfOver B S hS) (a : W ⟶ V),
                  IsAffineSpaceOver B S hS V W n a ∧
                    IsClosedMorphism B S hS (pullback.fst (yoneda.map a ≫ g) f),
            ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
              ∃ e : q.DominatingExtension,
                IsDiscreteValuationRing e.square.R ∧
                  (letI := e.fieldMap.toAlgebra
                   Module.Finite q.K e.square.K ∧ Algebra.IsSeparable q.K e.square.K) ∧
                  Nonempty e.square.Lift,
            ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
              ∃ e : q.DominatingExtension, Nonempty e.square.Lift] := by
  intro h
  obtain ⟨B, S, hS, X, Y, hX, hY, f, hft, hnoeth, huc, hex, -⟩ :=
    exists_universallyClosed_not_valuativeCriterion_existence.{u}
  exact hex (((h B S hS X Y hX hY f hft hnoeth).out 1 2).mp huc)

end AlgebraicGeometry.Space

end
