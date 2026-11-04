module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindRepresentation.ReductionToIntegral

/-!
# Integral schemes over a closed point of a Dedekind base

The cap product of a bivariant class with the fundamental class of an integral scheme lying over a
closed point of the base, computed through a Gysin map with trivial normal bundle.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Integral schemes over a closed point of the base -/

section ClosedCase

variable {C : ChowSituation.{u}}

/-- **A closed point of a Dedekind base is cut out on an integral neighbourhood with trivial
normal bundle.** This is `Stacks.Chow.IsDedekindChowBase.exists_isIntegral_zeroScheme_eq` with,
in addition, the restriction of the invertible module to the zero scheme trivial: the module is
the restriction of the structure sheaf of a neighbourhood. -/
theorem IsDedekindChowBase.exists_isIntegral_zeroScheme_eq_isTrivial (hS : IsDedekindChowBase C)
    {t s : C.S} (hts : t ⤳ s) (hne : t ≠ s) :
    ∃ (V : C.S.Opens) (hsV : s ∈ V) (L : (V : Scheme.{u}).Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible (V : Scheme.{u}).sheaf.obj
        (V : Scheme.{u}).ringCatSheaf.property L) (σ : Γ(L, ⊤)),
      IsIntegral (V : Scheme.{u}) ∧
        Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ =
          integralComponentAt (⟨s, hsV⟩ : (V : Scheme.{u})) ∧
        AlgebraicGeometry.SheafOfModules.IsTrivial
          (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subscheme.sheaf.obj
          (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subscheme.ringCatSheaf.property
          ((Scheme.Modules.pullback
            (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι).obj
            L) := by
  obtain ⟨U, hsU, π, hπ⟩ := hS.exists_zeroScheme_unit_eq hts hne
  obtain ⟨U₀, hsU₀, hU₀, hded⟩ := hS.1 s
  have hsV : s ∈ U ⊓ U₀ := ⟨hsU, hsU₀⟩
  have _ : Nonempty U₀ := ⟨⟨s, hsU₀⟩⟩
  have _ : IsIntegral (U₀ : Scheme.{u}) := isIntegral_of_isOpenImmersion hU₀.isoSpec.hom
  have _ : Nonempty (U ⊓ U₀ : C.S.Opens) := ⟨⟨s, hsV⟩⟩
  have hVU : U ⊓ U₀ ≤ U := inf_le_left
  refine ⟨U ⊓ U₀, hsV, _, Stacks.Divisors.pullback_isInvertible (C.S.homOfLE hVU)
    (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf),
    pullbackGlobalSections (C.S.homOfLE hVU) (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)
      π, isIntegral_of_isOpenImmersion (C.S.homOfLE (inf_le_right : U ⊓ U₀ ≤ U₀)), ?_,
    Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections (C.S.homOfLE hVU)
      (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) π
      ⟨Stacks.AlgebraicGeometry.ProjTwistMono.pullbackObjUnitIso _⟩⟩
  refine ((Stacks.Divisors.zeroScheme_pullback (C.S.homOfLE hVU)
    (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) π).trans
      (congrArg (fun J ↦ J.comap (C.S.homOfLE hVU)) hπ)).trans ?_
  rw [show (⟨s, hsU⟩ : (U : Scheme.{u})) = (C.S.homOfLE hVU).base ⟨s, hsV⟩ from
      (Scheme.homOfLE_apply' hVU s hsV).symm]
  exact comap_integralComponentAt_of_isOpenImmersion (C.S.homOfLE hVU) _

/-- The identification `X ×_S D ≅ Z(σ')` of the base change of a zero scheme with the zero scheme
of the pulled-back section is a morphism over the base. -/
private theorem bivariantDivisorBaseChangeIso_hom_comp_fst_comp {Y T : Scheme.{u}} (g : Y ⟶ C.S)
    (t : T ⟶ C.S) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    (bivariantDivisorBaseChangeIso g t L s).hom ≫
        (Stacks.Divisors.zeroScheme (pullback g t)
          ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
          (pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫ pullback.fst g t ≫ g =
      pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ g := by
  rw [← Category.assoc, bivariantDivisorBaseChangeIso_hom_subschemeι, ← Category.assoc,
    bivariantBaseChangeMap_fst]

/-- The inverse of the identification `X ×_S D ≅ Z(σ')` of the base change of a zero scheme with
the zero scheme of the pulled-back section is a morphism over the base. -/
theorem bivariantDivisorBaseChangeIso_inv_fst_comp {Y T : Scheme.{u}} (g : Y ⟶ C.S) (t : T ⟶ C.S)
    (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    (bivariantDivisorBaseChangeIso g t L s).inv ≫
        pullback.fst g ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ t) ≫ g =
      (Stacks.Divisors.zeroScheme (pullback g t)
          ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
          (pullbackGlobalSections (pullback.snd g t) L s)).subschemeι ≫ pullback.fst g t ≫ g := by
  rw [Iso.inv_comp_eq]
  exact (bivariantDivisorBaseChangeIso_hom_comp_fst_comp g t L s).symm

/-- **The coefficients of the Gysin map on cycles of Stacks 0B6Z.** At a point `d` of the zero
scheme `D` of `σ`, the coefficient of the image of `δ` is the sum over the components
`closure {i}` of `δ` not contained in `D` of `δ(i)` times the multiplicity of `d` in
`closure {i} ∩ D`. -/
theorem gysinCycleMap_apply {Y : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q] (k : ℤ)
    (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (σ : Γ(L, ⊤))
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme Y L σ).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme Y L σ).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme Y L σ).subschemeι).obj L))
    (δ : CycleGroup C q (k + 1)) (d : (Stacks.Divisors.zeroScheme Y L σ).subscheme) :
    (gysinCycleMap C q k L σ htriv δ).1 d = ∑ᶠ i : cycleSupportIndex δ, δ.1 i.1 *
      (open Classical in
        if Stacks.Divisors.zeroScheme Y L σ ≤ integralComponentAt i.1 then 0 else
          closedSubschemeCycleCoeff C ((Stacks.Divisors.zeroScheme Y L σ).subschemeι ≫ q)
            ((integralComponentAt i.1).comap
              (Stacks.Divisors.zeroScheme Y L σ).subschemeι).subschemeι k d) := by
  classical
  show ((gysinCycleMapRule C q k L σ).extendCycleGroup δ).1 d = _
  rw [GysinChernCap.extendCycleGroup_eq_finsum_cycle]
  refine finsum_congr fun i ↦ ?_
  show (δ.1 i.1 • gysinCycleMapComponent C q k L σ _ (isIntegral_integralComponentAt i.1)
    (schemeDeltaDimension_cycleSupportIndex δ i)).1 d = _
  split_ifs with hle
  · rw [gysinCycleMapComponent_of_le C q k L σ _ _ _ hle]
    simp
  · rw [gysinCycleMapComponent_of_not_le C q k L σ _ _ _ hle]
    rfl

/-- A point of a closed subscheme maps into the support of its ideal sheaf. -/
private theorem subschemeι_base_mem_support {P : Scheme.{u}} (E : P.IdealSheafData)
    (z : E.subscheme) : E.subschemeι.base z ∈ (E.support : Set P) := by
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨z, rfl⟩

/-- A specialization of a point `x` whose singleton is closed is trivial. -/
private theorem eq_of_specializes_of_isClosed_singleton {α : Type*} [TopologicalSpace α]
    {x y : α} (hx : IsClosed ({x} : Set α)) (h : x ⤳ y) : y = x :=
  h.mem_closed hx rfl

/-- **One term of the flat pullback of a Gysin map on cycles.** Let `E ⊆ P` be a closed subscheme
of a scheme `P` over `X`, with `j : P ⟶ X` an open immersion, let `e : Q ≅ E` and let
`q : R ⟶ Q` be flat of relative dimension `r`, the composite `R ⟶ X` being `f`. For a point `i`
of `P` of delta-dimension `k + 1` off `E`, the multiplicity of `closure {i} ∩ E` at the image of
a point `w` of `R`, times the flat pullback multiplicity at `w`, is the multiplicity at `w` of the
inverse image of `closure {j i}` under `f`. -/
theorem closedSubschemeCycleCoeff_comap_mul_flatPullbackWeight {X P Q R : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (j : P ⟶ X) [IsOpenImmersion j]
    [LocallyOfFiniteType (j ≫ sX)] (E : P.IdealSheafData) (sQ : Q ⟶ C.S) [LocallyOfFiniteType sQ]
    (e : Q ≅ E.subscheme) (he : e.hom ≫ E.subschemeι ≫ j ≫ sX = sQ) (q : R ⟶ Q)
    [LocallyOfFiniteType q] [Flat q] (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension q r)
    (f : R ⟶ X) [LocallyOfFiniteType (f ≫ sX)] (hf : q ≫ e.hom ≫ E.subschemeι ≫ j = f)
    (k : ℤ) (i : P) (hi : relativeDimension C.dimensionFunction (j ≫ sX) i = k + 1)
    (hiE : i ∉ (E.support : Set P)) (w : R) :
    closedSubschemeCycleCoeff C (E.subschemeι ≫ j ≫ sX)
        ((integralComponentAt i).comap E.subschemeι).subschemeι k (e.hom.base (q.base w)) *
      flatPullbackWeight C (f ≫ sX) q (k + r) w =
      closedSubschemeCycleCoeff C (f ≫ sX) ((integralComponentAt (j.base i)).comap f).subschemeι
        (k + r) w := by
  set I := (integralComponentAt i).comap E.subschemeι with hI
  have hbase : q ≫ sQ = f ≫ sX := by rw [← he, ← hf]; simp only [Category.assoc]
  -- the dimension of `I.comap e.hom`
  have hdim : schemeDeltaDimension C ((I.comap e.hom).subschemeι ≫ sQ) ≤ (k : EInt) := by
    refine schemeDeltaDimension_le_of_forall_relativeDimension_le C sQ _ fun z ↦ ?_
    set y := (I.comap e.hom).subschemeι.base z with hy
    have hy1 : y ∈ ((I.comap e.hom).support : Set Q) := subschemeι_base_mem_support _ z
    rw [coe_support_comap, Set.mem_preimage, hI, coe_support_comap, Set.mem_preimage,
      coe_support_integralComponentAt] at hy1
    have hne : i ≠ E.subschemeι.base (e.hom.base y) := fun h ↦
      hiE (h ▸ subschemeι_base_mem_support E (e.hom.base y))
    have hrel : relativeDimension C.dimensionFunction sQ y =
        relativeDimension C.dimensionFunction (j ≫ sX) (E.subschemeι.base (e.hom.base y)) := by
      rw [← he, relativeDimension_comp_isOpenImmersion, relativeDimension_comp_closedImmersion]
    rw [hrel]
    obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction C.isUniversallyCatenary
      C.dimensionFunction (j ≫ sX)
    have hlt := d.strictAnti_specializes (specializes_iff_mem_closure.mpr hy1) hne
    rw [hd, hd, hi] at hlt
    exact Int.le_sub_one_of_lt (by omega) |>.trans (by omega)
  -- transport along `e`
  have hiso : closedSubschemeCycleCoeff C (E.subschemeι ≫ j ≫ sX) I.subschemeι k
      (e.hom.base (q.base w)) =
      closedSubschemeCycleCoeff C sQ (I.comap e.hom).subschemeι k (q.base w) := by
    rw [closedSubschemeCycleCoeff_of_isIso_ambient C sQ (E.subschemeι ≫ j ≫ sX) e.hom he
      (I.comap e.hom).subschemeι k (q.base w)]
    exact (closedSubschemeCycleCoeff_eq_of_iso C _ ((I.comap e.hom).subschemeι ≫ e.hom)
      I.subschemeι (comapSubschemeIsoOfIsIso e.hom I) (comapSubschemeIsoOfIsIso_hom_subschemeι
        e.hom I) k _).symm
  rw [hiso, ← closedSubschemeCycleCoeff_comap C (f ≫ sX) sQ q hbase r hr (I.comap e.hom) k hdim w]
  refine closedSubschemeCycleCoeff_congr C _ ?_ _ w
  rw [hI, ← comap_integralComponentAt_of_isOpenImmersion j i]
  simp only [← Scheme.IdealSheafData.comap_comp]
  rw [← hf]

/-- **The flat pullback of a Gysin map on cycles, summed over the components.** In the situation
of `Stacks.Chow.closedSubschemeCycleCoeff_comap_mul_flatPullbackWeight`, let `E` be the inverse
image of a closed point `s` of a Dedekind base which is not a generic point, let `R` lie over `s`,
and let `Γ` be the Gysin image on `E` of the restriction `δ` to `P` of a cycle `a` on `X`. Then the
coefficient at `w` of the flat pullback of `Γ` to `R` is the sum, over the components
`closure {x}` of `a` dominating a component of the base, of `a(x)` times the multiplicity at `w`
of the inverse image of `closure {x}`. -/
theorem gysinCycle_mul_flatPullbackWeight_eq_finsum (hS : IsDedekindChowBase C) {s : C.S}
    (hs : s ∉ genericPoints C.S) {X P Q R : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (j : P ⟶ X) [IsOpenImmersion j] [LocallyOfFiniteType (j ≫ sX)] (E : P.IdealSheafData)
    (hEsupp : ∀ i, i ∈ (E.support : Set P) ↔ sX.base (j.base i) = s) (sQ : Q ⟶ C.S)
    [LocallyOfFiniteType sQ] (e : Q ≅ E.subscheme) (he : e.hom ≫ E.subschemeι ≫ j ≫ sX = sQ)
    (q : R ⟶ Q) [LocallyOfFiniteType q] [Flat q] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension q r) (f : R ⟶ X) [LocallyOfFiniteType (f ≫ sX)]
    (hf : q ≫ e.hom ≫ E.subschemeι ≫ j = f) (hfpt : ∀ w, sX.base (f.base w) = s) (k : ℤ)
    (a : CycleGroup C sX (k + 1)) (δ : CycleGroup C (j ≫ sX) (k + 1))
    (hδ : ∀ i, δ.1 i = a.1 (j.base i)) (Γ : CycleGroup C (E.subschemeι ≫ j ≫ sX) k)
    (hΓ : ∀ d, Γ.1 d = ∑ᶠ i : cycleSupportIndex δ, δ.1 i.1 *
      (open Classical in if E ≤ integralComponentAt i.1 then 0 else
        closedSubschemeCycleCoeff C (E.subschemeι ≫ j ≫ sX)
          ((integralComponentAt i.1).comap E.subschemeι).subschemeι k d)) (w : R) :
    Γ.1 (e.hom.base (q.base w)) * flatPullbackWeight C (f ≫ sX) q (k + r) w =
      ∑ᶠ x : X, open Classical in if DominatesBaseComponent C sX x then
        a.1 x * closedSubschemeCycleCoeff C (f ≫ sX)
          ((integralComponentAt x).comap f).subschemeι (k + r) w else 0 := by
  classical
  -- a nonzero multiplicity at `w` forces `f w` into the closure of `x`
  have hcl : ∀ x : X, closedSubschemeCycleCoeff C (f ≫ sX)
      ((integralComponentAt x).comap f).subschemeι (k + r) w ≠ 0 →
        f.base w ∈ closure ({x} : Set X) := by
    intro x hx
    have hmem := support_cycleAssociatedToClosedSubscheme_subset C _ _ _ hx
    rwa [Scheme.IdealSheafData.range_subschemeι, coe_support_comap, Set.mem_preimage,
      coe_support_integralComponentAt] at hmem
  -- off the components through `f w` over `s` the multiplicity vanishes
  have hzero : ∀ x : X, sX.base x ≠ s → ¬ DominatesBaseComponent C sX x →
      closedSubschemeCycleCoeff C (f ≫ sX) ((integralComponentAt x).comap f).subschemeι
        (k + r) w = 0 := by
    intro x hxs hdom
    by_contra hx
    have h1 := (specializes_iff_mem_closure.mpr (hcl x hx)).map sX.continuous
    have hclosed := (hS.exists_specializes_of_notMem_genericPoints (s := sX.base x) hdom).1
    exact hxs (hfpt w ▸ (eq_of_specializes_of_isClosed_singleton hclosed h1).symm)
  rw [hΓ, finsum_mul]
  set F : P → ℤ := fun i ↦ δ.1 i * (if E ≤ integralComponentAt i then 0 else
    closedSubschemeCycleCoeff C (E.subschemeι ≫ j ≫ sX)
      ((integralComponentAt i).comap E.subschemeι).subschemeι k (e.hom.base (q.base w))) *
    flatPullbackWeight C (f ≫ sX) q (k + r) w with hF
  refine ((finsum_subtype_eq_finsum_cond (f := F) (fun i ↦ δ.1 i ≠ 0)).trans ?_)
  have hall : ∑ᶠ (i : P) (_ : δ.1 i ≠ 0), F i = ∑ᶠ i, F i := by
    refine finsum_congr fun i ↦ ?_
    rw [finsum_eq_if]
    split_ifs with hi
    · rfl
    · rw [hF]
      dsimp only
      rw [not_not.mp hi, zero_mul, zero_mul]
  rw [hall]
  set H : X → ℤ := fun x ↦ if DominatesBaseComponent C sX x then
    a.1 x * closedSubschemeCycleCoeff C (f ≫ sX)
      ((integralComponentAt x).comap f).subschemeι (k + r) w else 0 with hH
  have hsupp : Function.support H ⊆ Set.range j.base := by
    intro x hx
    have hx' : H x ≠ 0 := hx
    rw [hH] at hx'
    dsimp only at hx'
    split_ifs at hx' with hdom
    · have h1 := hcl x (right_ne_zero_of_mul hx')
      have hfw : f.base w = j.base (E.subschemeι.base (e.hom.base (q.base w))) := by
        rw [← hf]
        simp only [Scheme.Hom.comp_apply]
      rw [hfw] at h1
      exact (specializes_iff_mem_closure.mpr h1).mem_open j.isOpenEmbedding.isOpen_range
        ⟨_, rfl⟩
    · exact absurd rfl hx'
  symm
  rw [← finsum_mem_univ H, finsum_mem_inter_support_eq H Set.univ (Set.range j.base)
    (by rw [Set.univ_inter, Set.inter_eq_right.mpr hsupp]),
    finsum_mem_range j.isOpenEmbedding.injective]
  refine finsum_congr fun i ↦ ?_
  rw [hH, hF]
  dsimp only
  rw [hδ]
  by_cases hiE : E ≤ integralComponentAt i
  · have hs' : sX.base (j.base i) = s :=
      (hEsupp i).1 ((le_integralComponentAt_iff_mem_support E i).1 hiE)
    have hdom : ¬ DominatesBaseComponent C sX (j.base i) := fun h ↦ hs (hs' ▸ h)
    rw [if_neg hdom, if_pos hiE]
    simp
  · rw [if_neg hiE]
    by_cases ha : a.1 (j.base i) = 0
    · simp [ha]
    have hδi : δ.1 i ≠ 0 := by rwa [hδ]
    have hi : relativeDimension C.dimensionFunction (j ≫ sX) i = k + 1 :=
      (mem_cyclesOfDimension_iff_forall_point C _ _ δ.1).1 δ.2 i hδi
    have hiE' : i ∉ (E.support : Set P) := fun h ↦
      hiE ((le_integralComponentAt_iff_mem_support E i).2 h)
    rw [mul_assoc, closedSubschemeCycleCoeff_comap_mul_flatPullbackWeight sX j E sQ e he q r hr f
      hf k i hi hiE' w]
    split_ifs with hdom
    · rfl
    · have hs' : sX.base (j.base i) ≠ s := fun h ↦ hiE' ((hEsupp i).2 h)
      rw [hzero _ hs' hdom, mul_zero]

/-- The zero scheme of a section cutting out the reduced point `s'` of an open `V` of the base,
over a closed point `s`, is supported at `s'`. -/
theorem coe_support_zeroScheme_eq_singleton {s : C.S} (hclosed : IsClosed ({s} : Set C.S))
    (V : C.S.Opens) (s' : (V : Scheme.{u})) (hs' : V.ι.base s' = s) (L : (V : Scheme.{u}).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (V : Scheme.{u}).sheaf.obj
      (V : Scheme.{u}).ringCatSheaf.property L] (σ : Γ(L, ⊤))
    (hσ : Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ = integralComponentAt s') :
    ((Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).support : Set (V : Scheme.{u})) = {s'} := by
  have hs'closed : IsClosed ({s'} : Set (V : Scheme.{u})) := by
    have h1 : (V.ι.base ⁻¹' {s} : Set (V : Scheme.{u})) = {s'} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h ↦ V.ι.isOpenEmbedding.injective (h.trans hs'.symm), fun h ↦ h ▸ hs'⟩
    rw [← h1]
    exact hclosed.preimage V.ι.continuous
  rw [hσ, coe_support_integralComponentAt, hs'closed.closure_eq]

/-- Every point of the zero scheme of a section cutting out the reduced point `s'` of an open `V`
of the base, over a closed point, is `s'`. -/
theorem zeroScheme_subschemeι_apply_eq {s : C.S} (hclosed : IsClosed ({s} : Set C.S))
    (V : C.S.Opens) (s' : (V : Scheme.{u})) (hs' : V.ι.base s' = s) (L : (V : Scheme.{u}).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (V : Scheme.{u}).sheaf.obj
      (V : Scheme.{u}).ringCatSheaf.property L] (σ : Γ(L, ⊤))
    (hσ : Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ = integralComponentAt s')
    (z : (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subscheme) :
    (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι.base z = s' := by
  have hz := subschemeι_base_mem_support (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ) z
  rwa [coe_support_zeroScheme_eq_singleton hclosed V s' hs' L σ hσ, Set.mem_singleton_iff] at hz

variable {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The exterior product with an integral scheme over a closed point is a flat pullback of a
Gysin map**, on cycles. Let `s` be a closed point of a Dedekind base, cut out on an open `V ∋ s`
by a section `σ` of an invertible module with trivial restriction to the zero scheme `D = {s}`,
and let `h : T ⟶ D` be flat of relative dimension `r` with `T` integral. For a cycle `a` on `X`
whose restriction to `X ×_S V` is `δ`, the flat pullback along `X ×_S T ⟶ X ×_S D` of the Gysin
map on cycles of Stacks 0B6Z of `δ` is `a × [T]`: a component `closure {x}` of `a` dominating a
component of the base meets `X ×_S D` in `closure {x} ×_S D`, whose inverse image is
`closure {x} ×_S T`; a component over `s` lies in the divisor and contributes nothing; a component
over another closed point does not meet `X ×_S T`. -/
theorem flatPullback_gysinCycleMap_apply (hS : IsDedekindChowBase C) {s : C.S}
    (hs : s ∉ genericPoints C.S) (V : C.S.Opens) (hsV : s ∈ V) (L : (V : Scheme.{u}).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (V : Scheme.{u}).sheaf.obj
      (V : Scheme.{u}).ringCatSheaf.property L] (σ : Γ(L, ⊤))
    (hσ : Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ =
      integralComponentAt (⟨s, hsV⟩ : (V : Scheme.{u})))
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback sX V.ι).sheaf.obj
      (pullback sX V.ι).ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd sX V.ι)).obj L)]
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme (pullback sX V.ι)
        ((Scheme.Modules.pullback (pullback.snd sX V.ι)).obj L)
        (pullbackGlobalSections (pullback.snd sX V.ι) L σ)).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme (pullback sX V.ι)
        ((Scheme.Modules.pullback (pullback.snd sX V.ι)).obj L)
        (pullbackGlobalSections (pullback.snd sX V.ι) L σ)).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme (pullback sX V.ι)
        ((Scheme.Modules.pullback (pullback.snd sX V.ι)).obj L)
        (pullbackGlobalSections (pullback.snd sX V.ι) L σ)).subschemeι).obj
          ((Scheme.Modules.pullback (pullback.snd sX V.ι)).obj L)))
    {T : Scheme.{u}} [IsIntegral T]
    (h : T ⟶ (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subscheme)
    [LocallyOfFiniteType h] [Flat h] (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension h r)
    (k n : ℤ) (hn : n = k + 1) (a : CycleGroup C sX n)
    (δ : CycleGroup C (pullback.fst sX V.ι ≫ sX) (k + 1))
    (hδ : ∀ i, δ.1 i = a.1 ((pullback.fst sX V.ι).base i)) (m : ℤ)
    (hm : relativeDimension C.dimensionFunction
      (h ≫ (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι) (genericPoint T) = m)
    (hmr : m = r)
    (w : (pullback sX
      (h ≫ (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι) : Scheme.{u})) :
    (flatPullback C
        (pullback.fst sX (h ≫ (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι) ≫
          sX)
        (pullback.fst sX ((Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι) ≫ sX)
        (testBaseChangeMapOfEq sX
          ((Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι)
          h _ rfl)
        (testBaseChangeMapOfEq_fst_assoc _ _ _ _ _ _) r
        (AlgebraicGeometry.RelativeDimension.of_isPullback
          (isPullback_testBaseChangeMapOfEq _ _ _ _ _) hr) k
        (properPushforward C _ _ (bivariantDivisorBaseChangeIso sX V.ι L σ).inv
          (bivariantDivisorBaseChangeIso_inv_fst_comp sX V.ι L σ) k
          (gysinCycleMap C (pullback.fst sX V.ι ≫ sX) k _ _ htriv δ))).1 w =
      (exteriorProductDedekindCycles C sX
        (h ≫ (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι) n m a
        (fundamentalCycle C _ m)).1 w := by
  classical
  subst hn
  have hclosed : IsClosed ({s} : Set C.S) := (hS.exists_specializes_of_notMem_genericPoints hs).1
  set s' : (V : Scheme.{u}) := ⟨s, hsV⟩ with hs'
  have hsuppD := coe_support_zeroScheme_eq_singleton hclosed V s' rfl L σ hσ
  have hDpt := zeroScheme_subschemeι_apply_eq hclosed V s' rfl L σ hσ
  have hEsupp : ∀ i : (pullback sX V.ι : Scheme.{u}),
      i ∈ ((Stacks.Divisors.zeroScheme (pullback sX V.ι)
        ((Scheme.Modules.pullback (pullback.snd sX V.ι)).obj L)
        (pullbackGlobalSections (pullback.snd sX V.ι) L σ)).support :
          Set (pullback sX V.ι : Scheme.{u})) ↔
        sX.base ((pullback.fst sX V.ι).base i) = s := by
    intro i
    rw [Stacks.Divisors.zeroScheme_pullback, coe_support_comap, Set.mem_preimage, hsuppD,
      Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact ⟨fun h ↦ by rw [h]; rfl, fun h ↦ V.ι.isOpenEmbedding.injective h⟩
  have hfpt : ∀ y, sX.base ((pullback.fst sX
      (h ≫ (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι)).base y) = s := by
    intro y
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hDpt]
    rfl
  have he := bivariantDivisorBaseChangeIso_hom_comp_fst_comp sX V.ι L σ
  have hf : testBaseChangeMapOfEq sX ((Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫
      V.ι) h _ rfl ≫ (bivariantDivisorBaseChangeIso sX V.ι L σ).hom ≫
      (Stacks.Divisors.zeroScheme (pullback sX V.ι)
        ((Scheme.Modules.pullback (pullback.snd sX V.ι)).obj L)
        (pullbackGlobalSections (pullback.snd sX V.ι) L σ)).subschemeι ≫ pullback.fst sX V.ι =
      pullback.fst sX (h ≫ (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι) := by
    rw [← Category.assoc (bivariantDivisorBaseChangeIso sX V.ι L σ).hom,
      bivariantDivisorBaseChangeIso_hom_subschemeι, bivariantBaseChangeMap_fst,
      testBaseChangeMapOfEq_fst]
  have hgenT : ¬ DominatesBaseComponent C
      (h ≫ (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι)
        (genericPoint T) := by
    intro hd
    refine hs ?_
    have hpt : (h ≫ (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι).base
        (genericPoint T) = s := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hDpt]
      rfl
    rw [← hpt]
    exact hd
  rw [flatPullback_apply, exteriorProductDedekindCycles_fundamentalCycle_apply C sX _ (k + 1) m hm
    a w]
  have hy : ∀ y, (bivariantDivisorBaseChangeIso sX V.ι L σ).inv.base
      ((bivariantDivisorBaseChangeIso sX V.ι L σ).hom.base y) = y :=
    Scheme.hom_inv_apply _
  rw [← hy ((testBaseChangeMapOfEq sX _ h _ rfl).base w),
    properPushforward_apply_of_isIso,
    gysinCycle_mul_flatPullbackWeight_eq_finsum hS hs sX (pullback.fst sX V.ι) _ hEsupp _
      (bivariantDivisorBaseChangeIso sX V.ι L σ) he _ r _ _ hf hfpt k a δ hδ _
      (gysinCycleMap_apply (pullback.fst sX V.ι ≫ sX) k _ _ htriv δ) w]
  · refine finsum_congr fun x ↦ ?_
    simp only [hgenT, or_false]
    rw [show k + 1 + m - 1 = k + (r : ℤ) by omega]
  · exact AlgebraicGeometry.RelativeDimension.of_isPullback
      (isPullback_testBaseChangeMapOfEq _ _ _ _ _) hr

/-- **An integral scheme over a closed point of a Dedekind base is flat over the reduced point.**
If the generic point of the integral scheme `T` lies over a point `s` of the base which is not a
generic point, then `s` is closed, cut out on an integral neighbourhood `V` by a section of an
invertible module with trivial restriction to the reduced point `D = {s}`, and `T ⟶ S` factors
through a morphism `T ⟶ D`, flat of relative dimension the relative dimension of `T`. -/
theorem IsDedekindChowBase.exists_lift_zeroScheme_of_notMem_genericPoints
    (hS : IsDedekindChowBase C) {T : Scheme.{u}} [IsIntegral T] (t : T ⟶ C.S)
    [LocallyOfFiniteType t] (hgen : t.base (genericPoint T) ∉ genericPoints C.S) :
    ∃ (V : C.S.Opens) (hsV : t.base (genericPoint T) ∈ V) (L : (V : Scheme.{u}).Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible (V : Scheme.{u}).sheaf.obj
        (V : Scheme.{u}).ringCatSheaf.property L) (σ : Γ(L, ⊤)),
      IsIntegral (V : Scheme.{u}) ∧
        Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ =
          integralComponentAt (⟨t.base (genericPoint T), hsV⟩ : (V : Scheme.{u})) ∧
        AlgebraicGeometry.SheafOfModules.IsTrivial
          (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subscheme.sheaf.obj
          (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subscheme.ringCatSheaf.property
          ((Scheme.Modules.pullback
            (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι).obj
            L) ∧
        ∃ (h : T ⟶ (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subscheme)
          (_ : LocallyOfFiniteType h) (_ : Flat h) (r : ℕ),
          AlgebraicGeometry.RelativeDimension h r ∧
            h ≫ (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι = t ∧
            relativeDimension C.dimensionFunction t (genericPoint T) = r := by
  obtain ⟨hclosed, t₀, hts, hne⟩ := hS.exists_specializes_of_notMem_genericPoints hgen
  obtain ⟨V, hsV, L, hL, σ, hVint, hσ, htriv⟩ :=
    hS.exists_isIntegral_zeroScheme_eq_isTrivial hts hne
  refine ⟨V, hsV, L, hL, σ, hVint, hσ, htriv, ?_⟩
  set η := genericPoint T with hη
  set s := t.base η with hs
  set s' : (V : Scheme.{u}) := ⟨s, hsV⟩ with hs'
  set D := Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ with hD
  have hrange : ∀ w : T, t.base w = s := by
    intro w
    exact eq_of_specializes_of_isClosed_singleton hclosed
      (((genericPoint_spec T).specializes (Set.mem_univ w)).map t.continuous)
  have hDpt : ∀ z : D.subscheme, D.subschemeι.base z = s' :=
    zeroScheme_subschemeι_apply_eq hclosed V s' rfl L σ hσ
  have _ : IsIntegral D.subscheme := by rw [hσ]; exact isIntegral_integralComponentAt s'
  have _ : Subsingleton D.subscheme :=
    ⟨fun a b ↦ D.subschemeι.isClosedEmbedding.injective (by rw [hDpt a, hDpt b])⟩
  have hδs : C.dimensionFunction s = 0 := hS.2.1 _ hclosed
  have hsub : Set.range t.base ⊆ Set.range V.ι.base := by
    rintro _ ⟨w, rfl⟩
    exact ⟨s', (hrange w).symm⟩
  set g₀ : T ⟶ (V : Scheme.{u}) := IsOpenImmersion.lift V.ι t hsub with hg₀def
  have hg₀ : g₀ ≫ V.ι = t := IsOpenImmersion.lift_fac _ _ _
  have hg₀pt : ∀ w, g₀.base w = s' := by
    intro w
    refine V.ι.isOpenEmbedding.injective ?_
    rw [← Scheme.Hom.comp_apply, hg₀, hrange]
    rfl
  have hker : D.subschemeι.ker ≤ g₀.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range, hσ]
    refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
    rw [← SetLike.coe_subset_coe, TopologicalSpace.Closeds.coe_closure,
      TopologicalSpace.Closeds.coe_closure]
    refine closure_mono ?_
    rintro _ ⟨w, rfl⟩
    exact hg₀pt w
  set h : T ⟶ D.subscheme := IsClosedImmersion.lift D.subschemeι g₀ hker with hhdef
  have hhfac : h ≫ D.subschemeι ≫ V.ι = t := by
    rw [← Category.assoc, IsClosedImmersion.lift_fac, hg₀]
  have _ : Flat h := inferInstance
  have _ : LocallyOfFiniteType (h ≫ D.subschemeι ≫ V.ι) := by rw [hhfac]; infer_instance
  have _ : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h (D.subschemeι ≫ V.ι)
  have hnn : 0 ≤ relativeDimension C.dimensionFunction t η := by
    show 0 ≤ C.dimensionFunction s + (Cardinal.toNat (residueTrdeg t η) : ℤ)
    omega
  set r := (relativeDimension C.dimensionFunction t η).toNat with hrdef
  have hr : AlgebraicGeometry.RelativeDimension h r := by
    refine relativeDimension_of_flat_of_coheight C h (D.subschemeι ≫ V.ι) r fun w ↦ ?_
    have hmax : Order.coheight (h.base w) = 0 :=
      Order.coheight_eq_zero.mpr fun b _ ↦ le_of_eq (Subsingleton.elim _ _)
    rw [hmax, zero_add, hhfac, relativeDimension_comp_closedImmersion, ← Category.comp_id V.ι,
      relativeDimension_opensι_comp, relativeDimension_id, hDpt]
    show (r : ℕ∞) = ((relativeDimension C.dimensionFunction t η -
      C.dimensionFunction s).toNat : ℕ∞)
    rw [hδs, sub_zero]
  exact ⟨h, inferInstance, inferInstance, r, hr, hhfac, by rw [hrdef, Int.toNat_of_nonneg hnn]⟩

/-- Transport along an equality of degrees, written with `Eq.mp`, of a class heterogeneously equal
to the class of a cycle is the class of a cycle with the same coefficients. -/
theorem exists_eq_mp_eq_mk {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] {i j k : ℤ}
    (h : i = j) (hk : k = j) (x : chowGroup C q i) (ρ : CycleGroup C q k)
    (hx : x ≍ QuotientAddGroup.mk' (rationalEquivalences C q k) ρ) :
    ∃ δ : CycleGroup C q j, δ.1 = ρ.1 ∧
      Eq.mp (congrArg (chowGroup C q) h) x =
        QuotientAddGroup.mk' (rationalEquivalences C q j) δ := by
  subst h hk
  exact ⟨ρ, rfl, eq_of_heq hx⟩

/-- **Capping the fundamental class of an open of the base.** The restriction of `c ∩ [S]₁` to
`X ×_S V` is `c ∩ [V]₁`, `c` commuting with flat pullback along the open immersion `V ⟶ S`. -/
theorem cap_fundamentalChowClass_opensι_eq_mk (hS : IsDedekindChowBase C) (p : ℤ)
    (c : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (κ : CycleGroup C (pullback.fst sX (𝟙 C.S) ≫ sX) (1 - p))
    (hκ : c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C) =
      QuotientAddGroup.mk' (rationalEquivalences C _ (1 - p)) κ) (V : C.S.Opens) :
    c.cap V.ι 1 (fundamentalChowClass C (V.ι ≫ 𝟙 C.S) 1) =
      QuotientAddGroup.mk' _ (cycleGroupRestrict C (pullback.fst sX (𝟙 C.S) ≫ sX)
        (pullback.fst sX V.ι ≫ sX) (testBaseChangeMapOfEq sX (𝟙 C.S) V.ι V.ι (Category.comp_id _))
        (testBaseChangeMapOfEq_fst_assoc _ _ _ _ _ _) (1 - p) κ) := by
  have hdim1 : schemeDeltaDimension C (𝟙 C.S ≫ 𝟙 C.S) ≤ ((1 : ℤ) : EInt) :=
    hS.schemeDeltaDimension_le_one (𝟙 C.S ≫ 𝟙 C.S)
  have hres := BivariantClass.cap_chowGroupRestrict C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX
    (Category.comp_id sX) p c (𝟙 C.S) V.ι V.ι (Category.comp_id _)
    (testBaseChangeMapOfEq sX (𝟙 C.S) V.ι V.ι (Category.comp_id _))
    (isPullback_testBaseChangeMapOfEq _ _ _ _ _) (testBaseChangeMapOfEq_fst _ _ _ _ _) 1 (by simp)
    (testBaseChangeMapOfEq_fst_assoc _ _ _ _ _ _) (baseFundamentalChowClass C)
  rw [hκ, chowGroupRestrict_mk, baseFundamentalChowClass,
    chowGroupRestrict_fundamentalChowClass C _ _ _ _ 1 hdim1] at hres
  exact hres.symm

/-- **The Gysin step.** On an integral open `V` of a Dedekind base in which a closed point `s`,
not a generic point, is the zero scheme `D` of a section `σ` of an invertible module, `[D]₀` is
the Gysin image of `[V]₁` (Stacks 0B79), so `c ∩ [D]₀` is the Gysin image of `c ∩ [V]₁`
(Stacks 0B76 (3)); when `c ∩ [V]₁` is the class of a cycle and the normal bundle is trivial, this
is the class of the Gysin map on cycles of Stacks 0B6Z, read on `X ×_S D`. -/
theorem exists_cap_fundamentalChowClass_zeroScheme_eq_mk (hS : IsDedekindChowBase C) (p : ℤ)
    (c : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p)
    {s : C.S} (hs : s ∉ genericPoints C.S) (V : C.S.Opens) (hsV : s ∈ V)
    [IsIntegral (V : Scheme.{u})] (L : (V : Scheme.{u}).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (V : Scheme.{u}).sheaf.obj
      (V : Scheme.{u}).ringCatSheaf.property L] (σ : Γ(L, ⊤))
    (hσ : Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ =
      integralComponentAt (⟨s, hsV⟩ : (V : Scheme.{u})))
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback sX V.ι).sheaf.obj
      (pullback sX V.ι).ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd sX V.ι)).obj L)]
    (htriv' : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme (pullback sX V.ι)
        ((Scheme.Modules.pullback (pullback.snd sX V.ι)).obj L)
        (pullbackGlobalSections (pullback.snd sX V.ι) L σ)).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme (pullback sX V.ι)
        ((Scheme.Modules.pullback (pullback.snd sX V.ι)).obj L)
        (pullbackGlobalSections (pullback.snd sX V.ι) L σ)).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme (pullback sX V.ι)
        ((Scheme.Modules.pullback (pullback.snd sX V.ι)).obj L)
        (pullbackGlobalSections (pullback.snd sX V.ι) L σ)).subschemeι).obj
        ((Scheme.Modules.pullback (pullback.snd sX V.ι)).obj L)))
    (ρ : CycleGroup C (pullback.fst sX V.ι ≫ sX) (1 - p))
    (hρ : c.cap V.ι 1 (fundamentalChowClass C (V.ι ≫ 𝟙 C.S) 1) =
      QuotientAddGroup.mk' _ ρ) :
    ∃ δ : CycleGroup C (pullback.fst sX V.ι ≫ sX) (0 - p + 1), δ.1 = ρ.1 ∧
      c.cap ((Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι) 0
          (fundamentalChowClass C
            (((Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι) ≫ 𝟙 C.S) 0) =
        QuotientAddGroup.mk' _ (properPushforward C _ _
          (bivariantDivisorBaseChangeIso sX V.ι L σ).inv
          (bivariantDivisorBaseChangeIso_inv_fst_comp sX V.ι L σ) (0 - p)
          (gysinCycleMap C (pullback.fst sX V.ι ≫ sX) (0 - p) _ _ htriv' δ)) := by
  obtain ⟨hclosed, t₀, hts, hne⟩ := hS.exists_specializes_of_notMem_genericPoints hs
  set s' : (V : Scheme.{u}) := ⟨s, hsV⟩ with hs'
  have hsupp := coe_support_zeroScheme_eq_singleton hclosed V s' rfl L σ hσ
  have htV : t₀ ∈ V := hts.mem_open V.isOpen hsV
  have hδV : relativeDimension C.dimensionFunction (V.ι ≫ 𝟙 C.S)
      (genericPoint (V : Scheme.{u})) = 0 + 1 := by
    rw [relativeDimension_comp_isOpenImmersion, relativeDimension_id, zero_add]
    refine hS.2.2 _ fun hc ↦ ?_
    have h1 : genericPoint (V : Scheme.{u}) ⤳ ⟨t₀, htV⟩ :=
      (genericPoint_spec (V : Scheme.{u})).specializes (Set.mem_univ _)
    have h2 : genericPoint (V : Scheme.{u}) ⤳ s' :=
      (genericPoint_spec (V : Scheme.{u})).specializes (Set.mem_univ _)
    exact hne ((eq_of_specializes_of_isClosed_singleton hc (h1.map V.ι.continuous)).trans
      (eq_of_specializes_of_isClosed_singleton hc (h2.map V.ι.continuous)).symm)
  have hDne : ¬ Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ ≤ ⊥ := by
    intro hle
    have h1 := Scheme.IdealSheafData.support_antitone hle
    have hall : ∀ z : (V : Scheme.{u}), z = s' := fun z ↦ by
      have h2 : z ∈
          ((Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).support : Set (V : Scheme.{u})) :=
        h1 (by rw [Scheme.IdealSheafData.support_bot]; trivial)
      rw [hsupp] at h2
      exact h2
    exact hne (congrArg Subtype.val (hall ⟨t₀, htV⟩))
  have hres' : c.cap V.ι (0 + 1) (fundamentalChowClass C (V.ι ≫ 𝟙 C.S) (0 + 1)) ≍
      QuotientAddGroup.mk' _ ρ :=
    (heq_cap_of_heq C _ sX (𝟙 C.S) sX _ p c V.ι (by ring : (0 : ℤ) + 1 = 1)
      (fundamentalChowClass_heq C _ (by ring))).trans (heq_of_eq hρ)
  obtain ⟨δ, hδ, hδmk⟩ := exists_eq_mp_eq_mk _ (by ring : 0 + 1 - p = 0 - p + 1)
    (by ring : 1 - p = 0 - p + 1) _ ρ hres'
  have hbaseE := bivariantDivisorBaseChangeIso_hom_comp_fst_comp sX V.ι L σ
  have hgn := c.gysin_naturality V.ι L σ 0 (bivariantDivisorBaseChangeIso sX V.ι L σ)
    (bivariantDivisorBaseChangeIso_hom_subschemeι sX V.ι L σ) hbaseE
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (fundamentalChowClass C (V.ι ≫ 𝟙 C.S) (0 + 1))
  rw [gysinSystemOfInvertible_onChow_fundamentalChowClass_of_isIntegral C _ L σ 0 hδV hDne, hδmk,
    gysinSystemOfInvertible_onChowEqGysinCycleMap C _ _ _ htriv' (0 - p)] at hgn
  refine ⟨δ, hδ, ?_⟩
  have hcyc : properPushforward C _ _ (bivariantDivisorBaseChangeIso sX V.ι L σ).hom hbaseE (0 - p)
      (properPushforward C _ _ (bivariantDivisorBaseChangeIso sX V.ι L σ).inv
        (bivariantDivisorBaseChangeIso_inv_fst_comp sX V.ι L σ) (0 - p)
        (gysinCycleMap C (pullback.fst sX V.ι ≫ sX) (0 - p) _ _ htriv' δ)) =
      gysinCycleMap C (pullback.fst sX V.ι ≫ sX) (0 - p) _ _ htriv' δ := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun d ↦ ?_)
    have h1 := properPushforward_apply_of_isIso C _ _ (bivariantDivisorBaseChangeIso sX V.ι L σ).hom
      hbaseE (0 - p) (properPushforward C _ _ (bivariantDivisorBaseChangeIso sX V.ι L σ).inv
        (bivariantDivisorBaseChangeIso_inv_fst_comp sX V.ι L σ) (0 - p)
        (gysinCycleMap C (pullback.fst sX V.ι ≫ sX) (0 - p) _ _ htriv' δ))
      ((bivariantDivisorBaseChangeIso sX V.ι L σ).inv.base d)
    have h2 := properPushforward_apply_of_isIso C _ _ (bivariantDivisorBaseChangeIso sX V.ι L σ).inv
      (bivariantDivisorBaseChangeIso_inv_fst_comp sX V.ι L σ) (0 - p)
      (gysinCycleMap C (pullback.fst sX V.ι ≫ sX) (0 - p) _ _ htriv' δ) d
    have h3 : (bivariantDivisorBaseChangeIso sX V.ι L σ).hom.base
        ((bivariantDivisorBaseChangeIso sX V.ι L σ).inv.base d) = d := by
      exact Scheme.inv_hom_apply _ d
    exact (congrArg (fun z ↦ (properPushforward C _ _ (bivariantDivisorBaseChangeIso sX V.ι L σ).hom
      hbaseE (0 - p) (properPushforward C _ _ (bivariantDivisorBaseChangeIso sX V.ι L σ).inv
        (bivariantDivisorBaseChangeIso_inv_fst_comp sX V.ι L σ) (0 - p)
        (gysinCycleMap C (pullback.fst sX V.ι ≫ sX) (0 - p) _ _ htriv' δ))).1 z) h3.symm).trans
      (h1.trans h2)
  refine chowPushforwardOfIso_injective C _ _ (bivariantDivisorBaseChangeIso sX V.ι L σ).hom
    hbaseE (0 - p) ?_
  unfold chowPushforwardOfIso
  refine hgn.trans ?_
  exact (congrArg (QuotientAddGroup.mk' _) hcyc).symm

/-- **Capping the fundamental class of an integral scheme over a closed point**, read on the
reduced point. Let `s` be a closed point of a Dedekind base which is not a generic point, cut out
on an integral open `V` by a section `σ` of an invertible module with trivial restriction to
`D = {s}`, and let `h : T ⟶ D` be flat of relative dimension `r`, `T` integral. If
`c ∩ [S]₁` is the class of a cycle `κ` on `X ×_S S`, then `c ∩ [T] = a × [T]` for the pushforward
`a` of `κ` to `X`.

This is the closed-point paragraph of the proof of Stacks 0FC5: `[T] = h^*[D]₀`, `[D]₀ = i^*[V]₁`
for the Gysin map `i^*` of the divisor `D` (Stacks 0B79) and `[V]₁ = [S]₁|_V`, so that `c ∩ [T]`
is the flat pullback along `X ×_S T ⟶ X ×_S D` of the Gysin image of the restriction of
`c ∩ [S]₁` to `X ×_S V`; on cycles this is `a × [T]`, by
`Stacks.Chow.flatPullback_gysinCycleMap_apply`. -/
theorem cap_fundamentalCycle_heq_of_zeroScheme (hS : IsDedekindChowBase C) (p : ℤ)
    (c : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (κ : CycleGroup C (pullback.fst sX (𝟙 C.S) ≫ sX) (1 - p))
    (hκ : c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C) =
      QuotientAddGroup.mk' (rationalEquivalences C _ (1 - p)) κ)
    {s : C.S} (hs : s ∉ genericPoints C.S) (V : C.S.Opens) (hsV : s ∈ V)
    [IsIntegral (V : Scheme.{u})] (L : (V : Scheme.{u}).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (V : Scheme.{u}).sheaf.obj
      (V : Scheme.{u}).ringCatSheaf.property L] (σ : Γ(L, ⊤))
    (hσ : Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ =
      integralComponentAt (⟨s, hsV⟩ : (V : Scheme.{u})))
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback
        (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι).obj L))
    {T : Scheme.{u}} [IsIntegral T]
    (h : T ⟶ (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subscheme)
    [LocallyOfFiniteType h] [Flat h] (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension h r)
    (hrel : relativeDimension C.dimensionFunction
      (h ≫ (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι)
      (genericPoint T) = r) :
    c.cap (h ≫ (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι) r
        (chowGroupCongr C (Category.comp_id _).symm r (QuotientAddGroup.mk' _
          (fundamentalCycle C
            (h ≫ (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι) r))) ≍
      QuotientAddGroup.mk' (rationalEquivalences C _ (1 - p + r - 1))
        (exteriorProductDedekindCycles C sX
          (h ≫ (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι)
          (1 - p) r
          (properPushforward C _ sX (pullback.fst sX (𝟙 C.S)) rfl (1 - p) κ)
          (fundamentalCycle C _ r)) := by
  have hclosed : IsClosed ({s} : Set C.S) := (hS.exists_specializes_of_notMem_genericPoints hs).1
  set s' : (V : Scheme.{u}) := ⟨s, hsV⟩ with hs'
  have hDpt := zeroScheme_subschemeι_apply_eq hclosed V s' rfl L σ hσ
  have hdimD : schemeDeltaDimension C
      (((Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι) ≫ 𝟙 C.S) ≤
      ((0 : ℤ) : EInt) := by
    refine schemeDeltaDimension_le_of_forall_relativeDimension_le C (V.ι ≫ 𝟙 C.S)
      (Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι fun w ↦ ?_
    rw [relativeDimension_comp_isOpenImmersion, relativeDimension_id, hDpt]
    exact (hS.2.1 s hclosed).le
  have _ := Stacks.Divisors.pullback_isInvertible (pullback.snd sX V.ι) L
  have htriv' := Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections
    (pullback.snd sX V.ι) L σ htriv
  obtain ⟨δ, hδ, hY⟩ := exists_cap_fundamentalChowClass_zeroScheme_eq_mk sX hS p c hs V hsV L σ hσ
    htriv' _ (cap_fundamentalChowClass_opensι_eq_mk sX hS p c κ hκ V)
  have hr' : AlgebraicGeometry.RelativeDimension
      (testBaseChangeMapOfEq sX
        ((Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι) h _ rfl)
        r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback
      (isPullback_testBaseChangeMapOfEq _ _ _ _ _) hr
  have hnat := BivariantClass.flat_naturality_of_eq C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX
    (Category.comp_id sX) p c
    ((Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι) h _ rfl r hr
    _
    (isPullback_testBaseChangeMapOfEq _ _ _ _ _) (testBaseChangeMapOfEq_fst _ _ _ _ _) 0 (by simp)
    hr' (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (fundamentalChowClass C
      (((Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).subschemeι ≫ V.ι) ≫ 𝟙 C.S)
      0)
  rw [flatPullbackChow_fundamentalChowClass C _ _ h _ r hr 0 _ hdimD, hY, flatPullbackChow_mk]
    at hnat
  show c.cap _ r (chowGroupCongr C _ r (fundamentalChowClass C _ r)) ≍ _
  rw [chowGroupCongr_fundamentalChowClass]
  refine ((heq_cap_of_heq C _ sX (𝟙 C.S) sX _ p c _ (by ring : (r : ℤ) = 0 + r)
    (fundamentalChowClass_heq C _ (by ring))).trans hnat).trans ?_
  refine mk_heq_mk_of_val_eq _ (by ring) _ _ (Function.locallyFinsuppWithin.ext fun w ↦ ?_)
  refine flatPullback_gysinCycleMap_apply sX hS hs V hsV L σ hσ htriv' h r hr (0 - p) (1 - p)
    (by ring) _ _ (fun i ↦ ?_) r hrel rfl w
  have hfi : (pullback.fst sX V.ι).base i = (pullback.fst sX (𝟙 C.S)).base
      ((testBaseChangeMapOfEq sX (𝟙 C.S) V.ι V.ι (Category.comp_id _)).base i) := by
    rw [← Scheme.Hom.comp_apply, testBaseChangeMapOfEq_fst]
  rw [hfi, properPushforward_apply_of_isIso, hδ]
  rfl

end ClosedCase

end Stacks.Chow

end
