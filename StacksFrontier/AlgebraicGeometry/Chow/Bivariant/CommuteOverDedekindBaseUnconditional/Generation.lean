module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseUnconditional.CentralClasses

/-!
# Generation of the Chow groups by central classes, and Stacks 0FC6

This part finishes the proof of **Stacks 0FC6** over a base as in section 42.63 with no
zero-dimensional component. The generators `∑_j [y_j]` of `CH_{1-p}(X)` from the proof of
Stacks 0FC5 are images of central classes, over generic points of the base
(`Stacks.Chow.exists_cycle_mem_central_of_mem_genericPoints`) and over closed points
(`Stacks.Chow.exists_cycle_mem_central_of_notMem_genericPoints`); hence every class is central
(`Stacks.Chow.isCentralOverBase_of_isDedekindChowBase`) and every class towards the base commutes
with every bivariant class (`Stacks.Chow.bivariantCommuteOverBase_of_isDedekindChowBase`).

## References

* [Stacks Project, Tag 0FC6](https://stacks.math.columbia.edu/tag/0FC6)
* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Generation of the Chow groups by images of central classes -/

section Generation

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (p : ℤ)

/-- **The generators reached by central classes.** Let `(y_j)` be a family of points of `X` of
delta-dimension `1 - p` whose closures form a locally finite family, `g : W = ∐_j closure{y_j} ⟶ X`
the induced proper morphism, and `ξ ∈ A^p(W ⟶ S)` a central class capping `[S]₁` to
`[W]_{1-p}`. Then the cycle `∑_j [y_j]` is the image under the canonical map of Stacks 0FC5 of a
central class, namely `g_* ∘ ξ` (Stacks 0EPK). -/
theorem exists_cycle_mem_central_of_sigma {J : Type u} (y : J → X)
    [IsProper (Sigma.desc fun j ↦ (integralComponentAt (y j)).subschemeι)]
    (hδ : ∀ j, relativeDimension C.dimensionFunction sX (y j) = 1 - p)
    (ξ : BivariantClass C (gysinSystemOfInvertible C)
      ((Sigma.desc fun j ↦ (integralComponentAt (y j)).subschemeι) ≫ sX) (𝟙 C.S)
      ((Sigma.desc fun j ↦ (integralComponentAt (y j)).subschemeι) ≫ sX) (Category.comp_id _) p)
    (hξc : IsCentralOverBase C (gysinSystemOfInvertible C)
      ((Sigma.desc fun j ↦ (integralComponentAt (y j)).subschemeι) ≫ sX) p ξ)
    (hξ : bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C)
        ((Sigma.desc fun j ↦ (integralComponentAt (y j)).subschemeι) ≫ sX) p ξ =
      fundamentalChowClass C
        ((Sigma.desc fun j ↦ (integralComponentAt (y j)).subschemeι) ≫ sX) (1 - p)) :
    ∃ P : CycleGroup C sX (1 - p),
      QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) P ∈
          (centralOverBaseSubgroup C (gysinSystemOfInvertible C) sX p).map
            (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p) ∧
        ∀ x, P.1 x = ∑ᶠ j ∈ y ⁻¹' {x}, (1 : ℤ) := by
  have _ : ∀ j, IsIntegral (integralComponentAt (y j)).subscheme := fun j ↦
    isIntegral_integralComponentAt _
  have hπ : ∀ j, (integralComponentAt (y j)).subschemeι.base
      (genericPoint (integralComponentAt (y j)).subscheme) = y j := fun j ↦
    genericPointOf_integralComponentAt _
  refine ⟨properPushforward C _ sX (Sigma.desc fun j ↦ (integralComponentAt (y j)).subschemeι)
    rfl (1 - p) (fundamentalCycle C _ (1 - p)),
    ⟨bivariantProperPushforwardOfInvertible C _ sX (𝟙 C.S)
      (Sigma.desc fun j ↦ (integralComponentAt (y j)).subschemeι) sX rfl (Category.comp_id sX)
      p ξ, fun _ _ sZ _ w _ q c' ↦ ?_, ?_⟩,
    fun x ↦ properPushforward_fundamentalCycle_sigma_apply C sX _ _ y hπ (1 - p) hδ x⟩
  · exact bivariantCommuteOverBase_of_isBivariantProperPushforward C _ sX sZ w _
      (properPushforwardDescends C) p q _ ξ c'
      (isBivariantProperPushforward_bivariantProperPushforwardOfInvertible C _ sX (𝟙 C.S) _ sX rfl
        (Category.comp_id sX) p ξ) (hξc sZ w q c')
  · rw [bivariantCapBaseFundamentalClass_bivariantProperPushforward, hξ]
    rfl

/-- **The flat generators are reached by central classes.** Over a base as in section 42.63, the
cycle `∑_j [y_j]` attached to a locally finite family of points of delta-dimension `1 - p` lying
over generic points of the base at which the dimension function is one is the image under the
canonical map of Stacks 0FC5 of a central class: the flat-pullback class of Stacks 0B78 of
`∐_j closure{y_j} ⟶ S` is built by the operations of chapter 42. -/
theorem exists_cycle_mem_central_of_mem_genericPoints_of_dimensionFunction_eq_one
    (hS : IsDedekindChowBase C) {J : Type u} (y : J → X)
    (hlf : LocallyFinite fun j ↦ Set.range (integralComponentAt (y j)).subschemeι)
    (hδ : ∀ j, relativeDimension C.dimensionFunction sX (y j) = 1 - p)
    (hgen : ∀ j, sX.base (y j) ∈ genericPoints C.S)
    (hδ1 : ∀ j, C.dimensionFunction (sX.base (y j)) = 1) :
    ∃ P : CycleGroup C sX (1 - p),
      QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) P ∈
          (centralOverBaseSubgroup C (gysinSystemOfInvertible C) sX p).map
            (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p) ∧
        ∀ x, P.1 x = ∑ᶠ j ∈ y ⁻¹' {x}, (1 : ℤ) := by
  by_cases hJ : IsEmpty J
  · refine ⟨0, zero_mem _, fun x ↦ ?_⟩
    rw [Set.eq_empty_of_isEmpty (y ⁻¹' {x}), finsum_mem_empty]
    rfl
  obtain ⟨j₀⟩ := not_isEmpty_iff.mp hJ
  have hp : p ≤ 0 := by
    have h1 := hδ j₀
    have h2 : C.dimensionFunction (sX.base (y j₀)) ≤
        relativeDimension C.dimensionFunction sX (y j₀) := by
      show _ ≤ C.dimensionFunction (sX.base (y j₀)) +
        (Cardinal.toNat (residueTrdeg sX (y j₀)) : ℤ)
      omega
    rw [hδ1] at h2
    omega
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, p = -(r : ℤ) := ⟨(-p).toNat, by omega⟩
  set Zs := fun j ↦ (integralComponentAt (y j)).subscheme with hZs
  set v : ∀ j, Zs j ⟶ X := fun j ↦ (integralComponentAt (y j)).subschemeι with hv
  have _ : IsProper (Sigma.desc v) := isProper_sigmaDesc_of_locallyFinite Zs v hlf
  have hflat : ∀ j, Flat (v j ≫ sX) := fun j ↦ by
    have _ := isIntegral_integralComponentAt (y j)
    refine hS.flat_of_mem_genericPoints _ ?_
    rw [Scheme.Hom.comp_apply, subschemeι_genericPoint_integralComponentAt]
    exact hgen j
  have hdesc : Sigma.desc v ≫ sX = Sigma.desc fun j ↦ v j ≫ sX := by
    refine Sigma.hom_ext _ _ fun j ↦ ?_
    simp
  have _ : Flat (Sigma.desc v ≫ sX) := by
    have := hflat
    rw [hdesc]
    infer_instance
  have hr : AlgebraicGeometry.RelativeDimension (Sigma.desc v ≫ sX) r := by
    refine AlgebraicGeometry.RelativeDimension.of_sigmaι_comp Zs _ fun j ↦ ?_
    have _ := hflat j
    have h := hS.relativeDimension_integralComponentAt_comp sX (y j) (hgen j)
    have e : (relativeDimension C.dimensionFunction sX (y j) -
        C.dimensionFunction (sX.base (y j))).toNat = r := by
      rw [hδ j, hδ1]
      omega
    rw [e] at h
    exact AlgebraicGeometry.RelativeDimension.of_eq (Sigma.ι_desc_assoc _ _ _).symm h
  have hφ : IsBivariantFlatPullback C (gysinSystemOfInvertible C) (Sigma.desc v ≫ sX) (𝟙 C.S)
      (Sigma.desc v ≫ sX) (Category.comp_id _) r hr (flatPullbackDescends C)
      (flatPullbackBivariantClassOfInvertible C (Sigma.desc v ≫ sX) (𝟙 C.S) (Sigma.desc v ≫ sX)
        (Category.comp_id _) r hr) :=
    isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C (Sigma.desc v ≫ sX)
      (𝟙 C.S) (Sigma.desc v ≫ sX) (Category.comp_id _) r hr
  exact exists_cycle_mem_central_of_sigma C sX (-(r : ℤ)) y hδ
    (flatPullbackBivariantClassOfInvertible C (Sigma.desc v ≫ sX) (𝟙 C.S) (Sigma.desc v ≫ sX)
        (Category.comp_id _) r hr)
    (IsChowOperationClassOverBase.flat _ r hr _
      (isFlatPullbackOverBase_flatPullbackBivariantClass C _ _ r hr _ hφ)).isCentralOverBase
    (bivariantCapBaseFundamentalClass_flatPullbackBivariantClass C _ _ r hr _ hφ
      (hS.schemeDeltaDimension_le_one (𝟙 C.S ≫ 𝟙 C.S)))

/-- **The flat generators are reached by central classes.** Over a base as in section 42.63 with
no zero-dimensional component, the cycle `∑_j [y_j]` attached to a locally finite family of
points of delta-dimension `1 - p` lying over generic points of the base is the image under the
canonical map of Stacks 0FC5 of a central class: the flat-pullback class of Stacks 0B78 of
`∐_j closure{y_j} ⟶ S` is built by the operations of chapter 42. -/
theorem exists_cycle_mem_central_of_mem_genericPoints (hS : IsDedekindChowBase C)
    (hS1 : HasNoZeroDimensionalComponent C) {J : Type u} (y : J → X)
    (hlf : LocallyFinite fun j ↦ Set.range (integralComponentAt (y j)).subschemeι)
    (hδ : ∀ j, relativeDimension C.dimensionFunction sX (y j) = 1 - p)
    (hgen : ∀ j, sX.base (y j) ∈ genericPoints C.S) :
    ∃ P : CycleGroup C sX (1 - p),
      QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) P ∈
          (centralOverBaseSubgroup C (gysinSystemOfInvertible C) sX p).map
            (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p) ∧
        ∀ x, P.1 x = ∑ᶠ j ∈ y ⁻¹' {x}, (1 : ℤ) :=
  exists_cycle_mem_central_of_mem_genericPoints_of_dimensionFunction_eq_one C sX p hS y hlf hδ hgen
    fun j ↦ hS.dimensionFunction_eq_one_of_mem_genericPoints hS1 (hgen j)

/-- **The vertical generators are reached by central classes.** Over a base as in section 42.63,
the cycle `∑_j [y_j]` attached to a locally finite family of points of delta-dimension `1 - p`
lying over closed points of the base is the image under the canonical map of Stacks 0FC5 of a
central class.

On `W = ∐_j Z_j`, `Z_j = closure{y_j}` lying over the closed point `s_j`, the class
`d_j = (Z_j ⟶ W)_* ∘ e_j`, with `e_j` the class of
`Stacks.Chow.exists_isChowOperationClassOverBase_cap_eq_of_closedPoint`, is built by the
operations of chapter 42. The class `ξ` assembled by Stacks 0FDZ from the restrictions of the
`d_j` to the pieces caps like `d_j` on the `j`-th piece, so it is central by
`Stacks.Chow.bivariantCommuteOverBase_of_forall_piece`, and it caps `[S]₁` to `[W]_{1-p}` since
it does so on each piece. -/
theorem exists_cycle_mem_central_of_notMem_genericPoints (hS : IsDedekindChowBase C)
    {J : Type u} (y : J → X)
    (hlf : LocallyFinite fun j ↦ Set.range (integralComponentAt (y j)).subschemeι)
    (hδ : ∀ j, relativeDimension C.dimensionFunction sX (y j) = 1 - p)
    (hgen : ∀ j, sX.base (y j) ∉ genericPoints C.S) :
    ∃ P : CycleGroup C sX (1 - p),
      QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) P ∈
          (centralOverBaseSubgroup C (gysinSystemOfInvertible C) sX p).map
            (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p) ∧
        ∀ x, P.1 x = ∑ᶠ j ∈ y ⁻¹' {x}, (1 : ℤ) := by
  set Zs := fun j ↦ (integralComponentAt (y j)).subscheme with hZs
  set v : ∀ j, Zs j ⟶ X := fun j ↦ (integralComponentAt (y j)).subschemeι with hv
  have _ : ∀ j, IsIntegral (Zs j) := fun j ↦ isIntegral_integralComponentAt _
  have _ : IsProper (Sigma.desc v) := isProper_sigmaDesc_of_locallyFinite Zs v hlf
  have hπ : ∀ j, (v j).base (genericPoint (Zs j)) = y j := fun j ↦
    genericPointOf_integralComponentAt _
  set sW := Sigma.desc v ≫ sX with hsW
  -- the closed points and their neighbourhoods
  have hcl := fun j ↦ hS.exists_specializes_of_notMem_genericPoints (hgen j)
  choose hclosed t₀ hts hne using hcl
  choose V hsV L hL σ hVint hσ using fun j ↦ hS.exists_isIntegral_zeroScheme_eq (hts j) (hne j)
  -- every point of `Z_j` lies over `s_j`
  have hZpt : ∀ j (z : Zs j), sX.base ((v j).base z) = sX.base (y j) := by
    intro j z
    have hz : (v j).base z ∈ closure ({y j} : Set X) := by
      rw [← coe_support_integralComponentAt, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨z, rfl⟩
    have h1 := specializes_iff_mem_closure.mpr hz |>.map sX.continuous
    have h2 := specializes_iff_mem_closure.mp h1
    rwa [(hclosed j).closure_eq, Set.mem_singleton_iff] at h2
  set UX : J → (∐ Zs : Scheme.{u}).Opens := fun j ↦ (Sigma.ι Zs j).opensRange with hUX
  have hX : IsClopenDecomposition UX := isClopenDecomposition_opensRange_sigmaι Zs
  have hpt : ∀ j (w : Zs j), (Sigma.ι Zs j ≫ sW).base w = sX.base (y j) := by
    intro j w
    rw [hsW, ← Category.assoc, Sigma.ι_desc, Scheme.Hom.comp_apply, hZpt]
  have hUXpt : ∀ j (w : (UX j : Scheme.{u})), sW.base ((UX j).ι.base w) = sX.base (y j) := by
    intro j w
    obtain ⟨z, hz⟩ := w.2
    show sW.base w.1 = _
    rw [← hz, ← Scheme.Hom.comp_apply]
    exact hpt j z
  have ha : ∀ j, UX j ≤ sW ⁻¹ᵁ V j := by
    intro j w hw
    have h1 := hUXpt j ⟨w, hw⟩
    show sW.base w ∈ V j
    change sW.base w = _ at h1
    rw [h1]
    exact hsV j
  -- the central classes on the summands
  have hδj : ∀ j, relativeDimension C.dimensionFunction (Sigma.ι Zs j ≫ sW)
      (genericPoint (Zs j)) = 1 - p := fun j ↦
    relativeDimension_sigmaι_genericPoint C sX Zs v y hπ (1 - p) hδ j
  have hZ : ∀ j, schemeDeltaDimension C (𝟙 (Zs j) ≫ Sigma.ι Zs j ≫ sW) ≤ ((1 - p : ℤ) : EInt) :=
    fun j ↦ by
      rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_comp_closedImmersion]
      simpa using (hδj j).le
  have _ : ∀ j, IsProper (Sigma.ι Zs j) := fun j ↦ by
    have : IsProper (Sigma.ι Zs j ≫ Sigma.desc v) := by rw [Sigma.ι_desc]; infer_instance
    exact IsProper.of_comp (Sigma.ι Zs j) (Sigma.desc v)
  choose e heop hecap using fun j ↦ exists_isChowOperationClassOverBase_cap_eq_of_closedPoint hS
    (hclosed j) (hts j) (hne j) (Sigma.ι Zs j ≫ sW) (hpt j) p (hδj j)
  set d : J → BivariantClass C (gysinSystemOfInvertible C) sW (𝟙 C.S) sW (Category.comp_id sW) p :=
    fun j ↦ bivariantProperPushforwardOfInvertible C (Sigma.ι Zs j ≫ sW) sW (𝟙 C.S) (Sigma.ι Zs j)
      sW rfl (Category.comp_id sW) p (e j) with hd
  have hdc : ∀ j, IsCentralOverBase C (gysinSystemOfInvertible C) sW p (d j) := fun j ↦
    (IsChowOperationClassOverBase.pushforward sW (Sigma.ι Zs j) p (e j) (heop j) (d j)
      (isBivariantProperPushforward_bivariantProperPushforwardOfInvertible C _ sW (𝟙 C.S)
        (Sigma.ι Zs j) sW rfl (Category.comp_id sW) p (e j))).isCentralOverBase
  set c := fun j ↦ bivariantPieceRestriction C (gysinSystemOfInvertible C) sW (𝟙 C.S) sW
    (Category.comp_id sW) p UX V (fun j ↦ j) ha j
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) (d j) with hcdef
  set ξ := bivariantPieceAssembly C (gysinSystemOfInvertible C) sW (𝟙 C.S) sW
    (Category.comp_id sW) UX V (fun j ↦ j) ha hX p
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) c with hξdef
  -- on each piece the assembled class caps like the pushed-forward class
  have hrestr : ∀ j {T : Scheme.{u}} (g : T ⟶ C.S) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (g ≫ 𝟙 C.S) k),
      chowGroupRestrict C (pullback.fst sW g ≫ sW)
          (pullback.fst (pieceMap sW UX V (fun j ↦ j) ha j)
            (g.resLE (V j) (g ⁻¹ᵁ V j) le_rfl) ≫ ((UX j).ι ≫ sW))
          (pieceImmersion sW UX V (fun j ↦ j) ha g j)
          (pieceImmersion_comp_structureMorphism C sW sW UX V (fun j ↦ j) ha g j) (k - p)
          (ξ.cap g k α) =
        chowGroupRestrict C (pullback.fst sW g ≫ sW)
          (pullback.fst (pieceMap sW UX V (fun j ↦ j) ha j)
            (g.resLE (V j) (g ⁻¹ᵁ V j) le_rfl) ≫ ((UX j).ι ≫ sW))
          (pieceImmersion sW UX V (fun j ↦ j) ha g j)
          (pieceImmersion_comp_structureMorphism C sW sW UX V (fun j ↦ j) ha g j) (k - p)
          ((d j).cap g k α) := by
    intro j T g _ k α
    rw [isBivariantPieceAssembly_bivariantPieceRestriction C _ sW (𝟙 C.S) sW
        (Category.comp_id sW) UX V (fun j ↦ j) ha hX p
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) (d j) g k α,
      hξdef, bivariantPieceAssembly_cap, bivariantPieceAssemblyCap_restrict,
      bivariantPieceAssemblyCap_restrict]
  -- the assembled class is central
  have hξc : IsCentralOverBase C (gysinSystemOfInvertible C) sW p ξ := by
    intro Y Z sZ _ w _ q c'
    refine bivariantCommuteOverBase_of_forall_piece C _ sW sZ w p q UX hX ξ d c'
      (fun j ↦ hdc j sZ w q c') fun j T g _ k α ↦ ?_
    refine chowGroupRestrict_eq_of_opensRange_le C _ _ _
      (pieceImmersion sW UX V (fun j ↦ j) ha g j)
      (pieceImmersion_comp_structureMorphism C sW sW UX V (fun j ↦ j) ha g j) _ rfl ?_ _
      (hrestr j g k α)
    rw [Scheme.Opens.opensRange_ι, opensRange_pieceImmersion]
  -- the classes on the pieces, on fundamental classes of integral opens
  have hc : ∀ j {V' : Scheme.{u}} (t : V' ⟶ (V j : Scheme.{u})) [IsOpenImmersion t]
      [LocallyOfFiniteType t] [IsIntegral V'] (x x' : V')
      (_hx : (V j).ι.base (t.base x) = sX.base (y j)) (_hx' : (V j).ι.base (t.base x') = t₀ j),
      (c j).cap t 1 (fundamentalChowClass C (t ≫ ((V j).ι ≫ 𝟙 C.S)) 1) =
        fundamentalChowClass C (pullback.fst (pieceMap sW UX V (fun j ↦ j) ha j) t ≫
          ((UX j).ι ≫ sW)) (1 - p) := by
    intro j V' t _ _ _ x x' hx hx'
    rw [hcdef, bivariantPieceRestriction_cap, bivariantPieceRestrictionCap_apply]
    have hβ : chowGroupCongr C (Category.assoc t (V j).ι (𝟙 C.S)).symm 1
        (fundamentalChowClass C (t ≫ ((V j).ι ≫ 𝟙 C.S)) 1) =
        fundamentalChowClass C ((t ≫ (V j).ι) ≫ 𝟙 C.S) 1 :=
      eq_of_heq ((chowGroupCongr_heq C _ _ _).trans
        (fundamentalChowClass_heq_of_hom_eq C (Category.assoc t (V j).ι (𝟙 C.S)).symm 1))
    rw [hβ, hd, isBivariantProperPushforward_bivariantProperPushforwardOfInvertible,
      bivariantProperPushforwardCap_apply,
      hecap j (t ≫ (V j).ι) x x' (by rw [Scheme.Hom.comp_apply]; exact hx)
        (by rw [Scheme.Hom.comp_apply]; exact hx')]
    have sq := isPullback_bivariantPushforwardBaseChange (Sigma.ι Zs j) sW (t ≫ (V j).ι)
    have _ : IsProper (bivariantPushforwardBaseChange (Sigma.ι Zs j) sW (t ≫ (V j).ι)) :=
      MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    have _ : IsOpenImmersion (bivariantPushforwardBaseChange (Sigma.ι Zs j) sW (t ≫ (V j).ι)) :=
      MorphismProperty.of_isPullback sq (P := @IsOpenImmersion) inferInstance
    have _ : IsOpenImmersion (pullback.fst (Sigma.ι Zs j ≫ sW) (t ≫ (V j).ι)) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback (Sigma.ι Zs j ≫ sW)
        (t ≫ (V j).ι)).flip (P := @IsOpenImmersion) inferInstance
    refine chowGroupRestrict_properChowPushforward_fundamentalChowClass C _ _ _ _ _ _ _ ?_ _ _ ?_
    · rw [opensRange_pieceComparison]
      rintro z hz
      have hrange := IsOpenImmersion.range_pullbackFst (Sigma.ι Zs j)
        (pullback.fst sW (t ≫ (V j).ι))
      obtain ⟨a, ha'⟩ : z ∈ Set.range (pullback.fst (pullback.fst sW (t ≫ (V j).ι))
          (Sigma.ι Zs j)).base := by
        rw [hrange]
        exact hz
      refine ⟨sq.flip.isoPullback.inv.base a, ?_⟩
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, ha']
    · rw [← schemeDeltaDimension_congr C (Category.id_comp
        (pullback.fst (Sigma.ι Zs j ≫ sW) (t ≫ (V j).ι) ≫ Sigma.ι Zs j ≫ sW))]
      refine schemeDeltaDimension_le_of_forall_relativeDimension_le C _ (𝟙 _) fun w ↦ ?_
      have h1 := relativeDimension_le_of_schemeDeltaDimension_le C _ (𝟙 (Zs j)) (hZ j)
        ((pullback.fst (Sigma.ι Zs j ≫ sW) (t ≫ (V j).ι)).base w)
      simpa [relativeDimension_comp_isOpenImmersion] using h1
  -- the assembled class caps `[S]₁` to `[W]_{1-p}`
  have hWdim : schemeDeltaDimension C sW ≤ ((1 - p : ℤ) : EInt) := by
    rw [← schemeDeltaDimension_congr C (Category.id_comp sW)]
    refine schemeDeltaDimension_le_of_forall_relativeDimension_le C sW (𝟙 _) fun w ↦ ?_
    obtain ⟨j, z, rfl⟩ := exists_mem_range_sigmaι Zs w
    have h1 := relativeDimension_le_of_schemeDeltaDimension_le C _ (𝟙 (Zs j)) (hZ j) z
    rw [relativeDimension_comp_isOpenImmersion] at h1
    simpa using h1
  have hWdim' : schemeDeltaDimension C (pullback.fst sW (𝟙 C.S) ≫ sW) ≤ ((1 - p : ℤ) : EInt) :=
    (schemeDeltaDimension_comp_iso C (asIso (pullback.fst sW (𝟙 C.S))) sW).le.trans hWdim
  have hcap : ξ.cap (𝟙 C.S) 1 (baseFundamentalChowClass C) =
      fundamentalChowClass C (pullback.fst sW (𝟙 C.S) ≫ sW) (1 - p) := by
    refine (chowGroupPullbackPieceEquiv C sW sW UX V (fun j ↦ j) ha hX (𝟙 C.S) (1 - p)).injective
      (funext fun j ↦ ?_)
    rw [chowGroupPullbackPieceEquiv_apply, chowGroupPullbackPieceEquiv_apply, hξdef,
      bivariantPieceAssembly_cap, bivariantPieceAssemblyCap_restrict, baseFundamentalChowClass,
      chowGroupRestrict_fundamentalChowClass C _ _ _ _ 1
        (hS.schemeDeltaDimension_le_one (𝟙 C.S ≫ 𝟙 C.S)),
      chowGroupRestrict_fundamentalChowClass C _ _ _ _ (1 - p) hWdim']
    have _ : IsOpenImmersion (Scheme.Hom.resLE (𝟙 C.S) (V j) ((𝟙 C.S) ⁻¹ᵁ V j) le_rfl) := by
      delta Scheme.Hom.resLE; infer_instance
    have _ := hVint j
    have _ : Nonempty ((𝟙 C.S) ⁻¹ᵁ V j : Scheme.{u}) := ⟨⟨_, hsV j⟩⟩
    have _ : IsIntegral ((𝟙 C.S) ⁻¹ᵁ V j : Scheme.{u}) :=
      isIntegral_of_isOpenImmersion (Scheme.Hom.resLE (𝟙 C.S) (V j) ((𝟙 C.S) ⁻¹ᵁ V j) le_rfl)
    have hx : sX.base (y j) ∈ (𝟙 C.S) ⁻¹ᵁ V j := hsV j
    have hx' : t₀ j ∈ (𝟙 C.S) ⁻¹ᵁ V j := (hts j).mem_open (V j).isOpen (hsV j)
    refine hc j (Scheme.Hom.resLE (𝟙 C.S) (V j) ((𝟙 C.S) ⁻¹ᵁ V j) le_rfl) ⟨_, hx⟩ ⟨_, hx'⟩ ?_ ?_ <;>
      exact (Scheme.Hom.coe_resLE_apply _ _ _).trans rfl
  refine exists_cycle_mem_central_of_sigma C sX p y hδ ξ hξc ?_
  rw [bivariantCapBaseFundamentalClass_apply, hcap, basePullbackPushforward_eq_chowPushforwardOfIso,
    chowPushforwardOfIso_fundamentalChowClass]

/-- **From families of generators to cycles with prescribed multiplicities**, for an arbitrary
subgroup `K` of `CH_{1-p}(X)`. Let `Q` be a property of points of `X` such that for every locally
finite family `(y_j)` of points of delta-dimension `1 - p` satisfying `Q` some cycle
`∑_j [y_j]` has its class in `K`. Then for a `(1-p)`-cycle `a` and multiplicities `M` on its
support, so does the cycle with coefficient `M(x)` at each `x` of the support satisfying `Q` and
zero elsewhere: repeat each such point `M(x)` times. -/
theorem exists_cycle_mem_of_multiplicity (K : AddSubgroup (chowGroup C sX (1 - p)))
    (a : CycleGroup C sX (1 - p)) (Q : X → Prop)
    (hQ : ∀ {J : Type u} (y : J → X),
      LocallyFinite (fun j ↦ Set.range (integralComponentAt (y j)).subschemeι) →
      (∀ j, relativeDimension C.dimensionFunction sX (y j) = 1 - p) → (∀ j, Q (y j)) →
      ∃ P : CycleGroup C sX (1 - p),
        QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) P ∈ K ∧
          ∀ x, P.1 x = ∑ᶠ j ∈ y ⁻¹' {x}, (1 : ℤ))
    (M : ↥(Function.support (a.1 : X → ℤ)) → ℕ) :
    ∃ P : CycleGroup C sX (1 - p),
      QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) P ∈ K ∧
        ∀ x, P.1 x = open Classical in
          if h : x ∈ Function.support (a.1 : X → ℤ) ∧ Q x then (M ⟨x, h.1⟩ : ℤ) else 0 := by
  classical
  let I := {i : ↥(Function.support (a.1 : X → ℤ)) // Q i}
  let y : (Σ i : I, Fin (M i.1)) → X := fun j ↦ (j.1.1 : X)
  have hlf : LocallyFinite fun j ↦ Set.range (integralComponentAt (y j)).subschemeι :=
    locallyFinite_sigma_fst (f := fun i : I ↦ Set.range (integralComponentAt (i.1 : X)).subschemeι)
      ((locallyFinite_range_subschemeι_support C sX _ a).comp_injective Subtype.val_injective)
  obtain ⟨P, hP, hPy⟩ := hQ y hlf
    (fun j ↦ (mem_cyclesOfDimension_iff_forall_point C sX _ a.1).1 a.2 _ j.1.1.2)
    (fun j ↦ j.1.2)
  refine ⟨P, hP, fun x ↦ ?_⟩
  rw [hPy]
  by_cases hx : x ∈ Function.support (a.1 : X → ℤ) ∧ Q x
  · rw [dif_pos hx]
    exact (finsum_mem_preimage_sigma_fst_one (fun i : I ↦ ((i.1 : _) : X))
      (fun i i' h ↦ Subtype.ext (Subtype.ext h)) ⟨⟨x, hx.1⟩, hx.2⟩).trans (by simp)
  · rw [dif_neg hx]
    refine (finsum_mem_congr (Set.eq_empty_of_forall_notMem fun j hj ↦ hx ?_)
      fun _ _ ↦ rfl).trans finsum_mem_empty
    have hj' : (j.1.1 : X) = x := hj
    exact hj' ▸ ⟨j.1.1.2, j.1.2⟩

/-- **A subgroup of `CH_{1-p}(X)` containing the generators is everything.** Let `K` be a
subgroup of `CH_{1-p}(X)` containing, for every locally finite family `(y_j)` of points of
delta-dimension `1 - p` all lying over generic points of the base, or all lying over non-generic
points, the class of a cycle `∑_j [y_j]`. Then `K` contains every class: write it as that of a
cycle, and separate its part over generic points from its part over other points and the
positive from the negative coefficients. -/
theorem mem_of_forall_cycle_generators (K : AddSubgroup (chowGroup C sX (1 - p)))
    (hh : ∀ {J : Type u} (y : J → X),
      LocallyFinite (fun j ↦ Set.range (integralComponentAt (y j)).subschemeι) →
      (∀ j, relativeDimension C.dimensionFunction sX (y j) = 1 - p) →
      (∀ j, sX.base (y j) ∈ genericPoints C.S) →
      ∃ P : CycleGroup C sX (1 - p),
        QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) P ∈ K ∧
          ∀ x, P.1 x = ∑ᶠ j ∈ y ⁻¹' {x}, (1 : ℤ))
    (hv : ∀ {J : Type u} (y : J → X),
      LocallyFinite (fun j ↦ Set.range (integralComponentAt (y j)).subschemeι) →
      (∀ j, relativeDimension C.dimensionFunction sX (y j) = 1 - p) →
      (∀ j, sX.base (y j) ∉ genericPoints C.S) →
      ∃ P : CycleGroup C sX (1 - p),
        QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) P ∈ K ∧
          ∀ x, P.1 x = ∑ᶠ j ∈ y ⁻¹' {x}, (1 : ℤ))
    (α : chowGroup C sX (1 - p)) : α ∈ K := by
  classical
  induction α using QuotientAddGroup.induction_on with
  | H a =>
  have hh' := fun M ↦ exists_cycle_mem_of_multiplicity C sX p K a
    (fun x ↦ sX.base x ∈ genericPoints C.S) (fun y hlf hδ hQ ↦ hh y hlf hδ hQ) M
  have hv' := fun M ↦ exists_cycle_mem_of_multiplicity C sX p K a
    (fun x ↦ sX.base x ∉ genericPoints C.S) (fun y hlf hδ hQ ↦ hv y hlf hδ hQ) M
  obtain ⟨P₁, hP₁, hP₁y⟩ := hh' fun i ↦ (a.1 i).toNat
  obtain ⟨P₂, hP₂, hP₂y⟩ := hh' fun i ↦ (-a.1 i).toNat
  obtain ⟨P₃, hP₃, hP₃y⟩ := hv' fun i ↦ (a.1 i).toNat
  obtain ⟨P₄, hP₄, hP₄y⟩ := hv' fun i ↦ (-a.1 i).toNat
  have hsub : a = P₁ - P₂ + (P₃ - P₄) := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
    show a.1 x = P₁.1 x - P₂.1 x + (P₃.1 x - P₄.1 x)
    rw [hP₁y, hP₂y, hP₃y, hP₄y]
    by_cases hx : x ∈ Function.support (a.1 : X → ℤ)
    · by_cases hg : sX.base x ∈ genericPoints C.S
      · rw [dif_pos ⟨hx, hg⟩, dif_pos ⟨hx, hg⟩, dif_neg (fun h ↦ h.2 hg),
          dif_neg (fun h ↦ h.2 hg)]
        simp only
        omega
      · rw [dif_neg (fun h ↦ hg h.2), dif_neg (fun h ↦ hg h.2), dif_pos ⟨hx, hg⟩,
          dif_pos ⟨hx, hg⟩]
        simp only
        omega
    · rw [dif_neg (fun h ↦ hx h.1), dif_neg (fun h ↦ hx h.1), dif_neg (fun h ↦ hx h.1),
        dif_neg (fun h ↦ hx h.1)]
      simpa using hx
  rw [hsub]
  show QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) (P₁ - P₂ + (P₃ - P₄)) ∈ K
  rw [map_add, map_sub, map_sub]
  exact add_mem (sub_mem hP₁ hP₂) (sub_mem hP₃ hP₄)

end Generation

/-! ### Stacks 0FC6 -/

section Dedekind

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (p : ℤ)

/-- **Stacks 0FC6, centrality form.** Over a base as in section 42.63 with no zero-dimensional
component, every `c ∈ A^p(X ⟶ S)` is central over the base. The central classes form a subgroup
whose image under the canonical map `c ↦ c ∩ [S]₁` of Stacks 0FC5 contains the generators of
`CH_{1-p}(X)`, hence is everything; that map being injective, every class is central. -/
theorem isCentralOverBase_of_isDedekindChowBase (hS : IsDedekindChowBase C)
    (hS1 : HasNoZeroDimensionalComponent C)
    (c : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p) :
    IsCentralOverBase C (gysinSystemOfInvertible C) sX p c := by
  have hmem := mem_of_forall_cycle_generators C sX p
    ((centralOverBaseSubgroup C (gysinSystemOfInvertible C) sX p).map
      (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p))
    (fun y hlf hδ hgen ↦ exists_cycle_mem_central_of_mem_genericPoints C sX p hS hS1 y hlf hδ hgen)
    (fun y hlf hδ hgen ↦ exists_cycle_mem_central_of_notMem_genericPoints C sX p hS y hlf hδ hgen)
    (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p c)
  obtain ⟨c', hc', he⟩ := AddSubgroup.mem_map.mp hmem
  rw [← bivariantCapBaseFundamentalClass_injective C sX p hS hS1 he]
  exact hc'

/-- **Stacks 0FC6**, over a base of pure dimension one. Let `(S, δ)` be as in section 42.63 of the
Stacks Project with no zero-dimensional component, let `X` be a scheme locally of finite type
over `S` and let `c ∈ A^p(X ⟶ S)`. Let `Y ⟶ Z` be a morphism of schemes locally of finite type
over `S` and let `c' ∈ A^q(Y ⟶ Z)`. Then `c ∘ c' = c' ∘ c`: capping with `c` and capping with `c'`
may be performed in either order, the two results being read on `X ×_S (Y ×_Z T)` and
`Y ×_Z (X ×_S T)` through the canonical comparison isomorphism. -/
theorem bivariantCommuteOverBase_of_isDedekindChowBase (hS : IsDedekindChowBase C)
    (hS1 : HasNoZeroDimensionalComponent C) {Y Z : Scheme.{u}} (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (w : Y ⟶ Z) [LocallyOfFiniteType w] (q : ℤ)
    (c : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (c' : BivariantClass C (gysinSystemOfInvertible C) (w ≫ sZ) sZ w rfl q) :
    BivariantCommuteOverBase C (gysinSystemOfInvertible C) sX sZ w p q c c' :=
  isCentralOverBase_of_isDedekindChowBase C sX p hS hS1 c sZ w q c'

end Dedekind

end Stacks.Chow

end
