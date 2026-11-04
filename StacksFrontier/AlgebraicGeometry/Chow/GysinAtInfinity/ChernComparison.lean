module

public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionIndependence
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.DivisorOfSectionCycle
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.SituationData
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponentModuleIso
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapClosedImmersionInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles.LineChartDifference
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDivisorPrincipal
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.Infinity
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeFactorization
public import StacksFrontier.AlgebraicGeometry.Chow.GysinPushforwardChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapRuleIndependence
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardRationalEquivalence.ClosedImmersion

/-!
# The first Chern classes of the divisors at zero and at infinity agree

Let `q : V ⟶ 𝐏¹_S` be a morphism from a scheme locally of finite type over the base of chapter 42,
and let `M₀`, `M_∞` be invertible modules on `V` with sections whose zero schemes are the inverse
images of `D_0` and `D_∞` and whose normal bundles are trivial. Then `c₁(M₀) ∩ α = c₁(M_∞) ∩ α`
for every cycle `α`: on an integral `W ⊆ V` meeting neither divisor generically the two component
classes are the classes of `[W ∩ q⁻¹D_0]` and `[W ∩ q⁻¹D_∞]` (Stacks 02SK), whose difference is
the principal divisor of the coordinate of `𝐏¹` (Stacks 02RQ), and on a component inside one of
the divisors both classes vanish. By Stacks 02T9 the two Gysin maps agree after pushforward to
`V`.

## Main results

* `Stacks.Chow.GysinAtInfinity.firstChernClassCapOfInvertible_eq_of_zeroScheme_eq_comap`
* `Stacks.Chow.GysinAtInfinity.chowPushforward_onChow_zero_eq_infinity`

## References

* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 02SK](https://stacks.math.columbia.edu/tag/02SK)
* [Stacks Project, Tag 02T9](https://stacks.math.columbia.edu/tag/02T9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

namespace GysinAtInfinity

section Component

/-- A dimension equal to `k + 1` is equal to some `N` with `k = N - 1`. -/
private theorem exists_eq_sub_one_of_eq_add_one {d : EInt} {k : ℤ} (h : d = ((k + 1 : ℤ) : EInt)) :
    ∃ N : ℤ, k = N - 1 ∧ d = (N : EInt) :=
  ⟨k + 1, by ring, h⟩

variable (C : ChowSituation.{u}) {V : Scheme.{u}} (sV : V ⟶ C.S) [LocallyOfFiniteType sV] (k : ℤ)
  (M : V.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property M]

/-- The component class of an invertible module vanishes on an integral closed subscheme over
which the module is trivial. -/
theorem firstChernComponentClass_eq_zero_of_isTrivial (W : V.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ sV) = ((k + 1 : ℤ) : EInt))
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial W.subscheme.sheaf.obj
      W.subscheme.ringCatSheaf.property ((Scheme.Modules.pullback W.subschemeι).obj M)) :
    firstChernComponentClass C sV k M W hW hDim = 0 := by
  have := hW
  have : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ sV)
  obtain ⟨e0⟩ := htriv
  let e : (Scheme.Modules.pullback W.subschemeι).obj M ≅ Stacks.Ample.unitModule W.subscheme := e0
  let f : Stacks.Ample.unitModule W.subscheme ⟶ (Scheme.Modules.pullback W.subschemeι).obj M :=
    e.inv
  have : IsIso f := e.symm.isIso_hom
  have hU : ∀ x : W.subscheme, Stacks.Divisors.IsTrivializedNear
      (Stacks.Ample.unitModule W.subscheme) x :=
    fun x ↦ ⟨⊤, trivial,
      show Γ(Stacks.Ample.unitModule W.subscheme, ⊤) from (1 : Γ(W.subscheme, ⊤)),
      fun y hy ↦ isStalkBasis_germ_one ⊤ y hy⟩
  have hM : ∀ x : W.subscheme, Stacks.Divisors.IsTrivializedNear
      ((Scheme.Modules.pullback W.subschemeι).obj M) x := fun x ↦
    have := isInvertible_presheaf_modulePullback M W.subschemeι
    Stacks.Divisors.isTrivializedNear_of_isInvertible _ x
  set s0 := ((Stacks.Ample.unitModule W.subscheme).presheaf.germ ⊤
    (genericPoint W.subscheme) trivial)
      (show Γ(Stacks.Ample.unitModule W.subscheme, ⊤) from (1 : Γ(W.subscheme, ⊤)))
  have hs0 : Stacks.Divisors.IsStalkBasis (Stacks.Ample.unitModule W.subscheme)
      (genericPoint W.subscheme) s0 := isStalkBasis_germ_one ⊤ _ trivial
  have hs : AlgebraicGeometry.stalkLinearMap _ _ f (genericPoint W.subscheme) s0 ≠ 0 :=
    Stacks.Divisors.IsStalkBasis.ne_zero
      (Stacks.Divisors.IsStalkBasis.mapStalkLinearMap _ _ f _ hs0)
      (Stacks.Divisors.exists_ne_zero_genericStalk (hM (genericPoint W.subscheme)))
  rw [firstChernComponentClass_eq_mk_of_ne_zero C sV k M W hDim hs,
    chernComponentCycle_mapStalkLinearMap C (W.subschemeι ≫ sV) hDim _ _ f hU _ s0]
  have hz : chernComponentCycle C (W.subschemeι ≫ sV) hDim hU s0 = 0 := by
    refine Subtype.ext ?_
    show weilDivisorAlgebraicCycle (Stacks.Divisors.weilDivisorOfMeromorphicSection hU s0) = 0
    rw [weilDivisorOfMeromorphicSection_eq_zero_of_isStalkBasis_germ hU (U := ⊤) (fun _ ↦ trivial)
      (fun y hy ↦ isStalkBasis_germ_one ⊤ y hy)]
    ext x
    simp [weilDivisorAlgebraicCycle, weilDivisorCoeff]
  rw [hz]
  rfl

/-- The component class of an invertible module on an integral closed subscheme `W` over which a
global section does not vanish identically is the class of the zero scheme of that section on
`W`: Stacks 02SK on `W`. -/
theorem firstChernComponentClass_eq_mk_zeroScheme (σ : Γ(M, ⊤)) (W : V.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ sV) = ((k + 1 : ℤ) : EInt))
    (hσ : AlgebraicGeometry.pullbackGlobalSections W.subschemeι M σ ≠ 0) :
    firstChernComponentClass C sV k M W hW hDim =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C (W.subschemeι ≫ sV)
        (Stacks.Divisors.zeroScheme W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj M)
          (AlgebraicGeometry.pullbackGlobalSections W.subschemeι M σ)).subschemeι k) := by
  have := hW
  have : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ sV)
  have hinv' := Stacks.ChernCap42.isInvertible_sheafObj_modulePullback M W.subschemeι
  obtain ⟨N, rfl, hN⟩ := exists_eq_sub_one_of_eq_add_one hDim
  have hσ' : Stacks.Divisors.genericValue ((Scheme.Modules.pullback W.subschemeι).obj M)
      (Stacks.ChernCap42.meromorphicSectionOfSection _
        (AlgebraicGeometry.pullbackGlobalSections W.subschemeι M σ)) ≠ 0 := by
    rw [Stacks.Divisors.genericValue_meromorphicSectionOfSection]
    exact Stacks.ChernCap42.germ_ne_zero_of_ne_zero _ _ hσ _
  refine (firstChernComponentClass_eq_mk_of_ne_zero C sV (N - 1) M W hDim hσ').trans ?_
  refine (congrArg QuotientAddGroup.mk (Subtype.ext rfl :
    chernComponentCycle C (W.subschemeι ≫ sV) hDim _ _ =
      divisorOfMeromorphicSectionCycle C (W.subschemeι ≫ sV) N hN
        ((Scheme.Modules.pullback W.subschemeι).obj M)
        (Stacks.ChernCap42.meromorphicSectionOfSection _
          (AlgebraicGeometry.pullbackGlobalSections W.subschemeι M σ))
        (Stacks.ChernCap42.isRegularMeromorphicSection_of_ne_zero _ _ _ hσ))).trans ?_
  rw [Stacks.ChernCap42.divisorOfMeromorphicSectionCycle_eq_cycleAssociatedToZeroScheme C
    (W.subschemeι ≫ sV) N hN _ _ hσ]

end Component

section Comparison

variable (C : ChowSituation.{u}) {V : Scheme.{u}} (sV : V ⟶ C.S) [LocallyOfFiniteType sV]
  (q : V ⟶ relativeProjectiveLine C.S) (M₀ Mi : V.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property M₀]
  [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property Mi]
  (σ₀ : Γ(M₀, ⊤)) (σi : Γ(Mi, ⊤))
  (h₀ : Stacks.Divisors.zeroScheme V M₀ σ₀ = (lineZeroDivisor C.S).comap q)
  (hi : Stacks.Divisors.zeroScheme V Mi σi = (lineInfinityDivisor C.S).comap q)
  (htriv₀ : AlgebraicGeometry.SheafOfModules.IsTrivial
    (Stacks.Divisors.zeroScheme V M₀ σ₀).subscheme.sheaf.obj
    (Stacks.Divisors.zeroScheme V M₀ σ₀).subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme V M₀ σ₀).subschemeι).obj M₀))
  (htrivi : AlgebraicGeometry.SheafOfModules.IsTrivial
    (Stacks.Divisors.zeroScheme V Mi σi).subscheme.sheaf.obj
    (Stacks.Divisors.zeroScheme V Mi σi).subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme V Mi σi).subschemeι).obj Mi))

omit [LocallyOfFiniteType sV] in
/-- The zero scheme of a section presenting the inverse image of a divisor, restricted to a closed
subscheme, is the inverse image of the divisor there. -/
theorem zeroScheme_restrict_eq_comap {M : V.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property M]
    {σ : Γ(M, ⊤)} {D : (relativeProjectiveLine C.S).IdealSheafData}
    (h : Stacks.Divisors.zeroScheme V M σ = D.comap q) (W : V.IdealSheafData) :
    Stacks.Divisors.zeroScheme W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj M)
        (AlgebraicGeometry.pullbackGlobalSections W.subschemeι M σ) =
      D.comap (W.subschemeι ≫ q) := by
  rw [Stacks.Divisors.zeroScheme_pullback, h, Scheme.IdealSheafData.comap_comp]

omit [LocallyOfFiniteType sV] in
/-- If a section restricts to zero on `W`, then `W` maps into the divisor it presents. -/
theorem range_subset_of_pullbackGlobalSections_eq_zero {M : V.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property M]
    {σ : Γ(M, ⊤)} {D : (relativeProjectiveLine C.S).IdealSheafData}
    (h : Stacks.Divisors.zeroScheme V M σ = D.comap q) (W : V.IdealSheafData)
    (hσ : AlgebraicGeometry.pullbackGlobalSections W.subschemeι M σ = 0) (x : W.subscheme) :
    (W.subschemeι ≫ q).base x ∈ (D.support : Set (relativeProjectiveLine C.S)) := by
  obtain ⟨g, hg⟩ := (AlgebraicGeometry.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme V M σ
    W.subschemeι).1 hσ
  have hx : W.subschemeι.base x ∈ Set.range (Stacks.Divisors.zeroScheme V M σ).subschemeι.base :=
    ⟨g.base x, by rw [← Scheme.Hom.comp_apply, hg]⟩
  rwa [Scheme.IdealSheafData.range_subschemeι, h, Scheme.IdealSheafData.support_comap] at hx

omit [LocallyOfFiniteType sV] in
/-- If `W` maps into `D` and `D'` is disjoint from `D`, the inverse image of `D'` on `W` is
empty. -/
private theorem isEmpty_comap_of_range_subset {W : V.IdealSheafData}
    {D D' : (relativeProjectiveLine C.S).IdealSheafData}
    (hDD' : Disjoint (D.support : Set (relativeProjectiveLine C.S)) D'.support)
    (hx : ∀ x : W.subscheme, (W.subschemeι ≫ q).base x ∈ (D.support : Set _)) :
    IsEmpty (D'.comap (W.subschemeι ≫ q)).subscheme := by
  refine ⟨fun y ↦ ?_⟩
  have hy : (D'.comap (W.subschemeι ≫ q)).subschemeι.base y ∈
      Set.range (D'.comap (W.subschemeι ≫ q)).subschemeι.base := ⟨y, rfl⟩
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap] at hy
  exact Set.disjoint_left.mp hDD' (hx _) hy

omit [LocallyOfFiniteType sV] in
/-- If the generic point of `W` does not lie on the inverse image of `D`, it lies over the open
complement of `D`. -/
private theorem genericPoint_mem_preimage_of_notMem_comap (W : V.IdealSheafData)
    [IsIntegral W.subscheme] (D : (relativeProjectiveLine C.S).IdealSheafData) {P : Scheme.{u}}
    (c : P ⟶ relativeProjectiveLine C.S) [IsOpenImmersion c]
    (hc : (Set.range c.base)ᶜ = (D.support : Set _))
    (hg : genericPoint W.subscheme ∉ Set.range (D.comap (W.subschemeι ≫ q)).subschemeι.base) :
    genericPoint W.subscheme ∈ (W.subschemeι ≫ q) ⁻¹ᵁ (c ''ᵁ ⊤) := by
  show (W.subschemeι ≫ q).base (genericPoint W.subscheme) ∈ (c ''ᵁ ⊤ : Set _)
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.coe_opensRange]
  by_contra hcon
  refine hg ?_
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
  show (W.subschemeι ≫ q).base (genericPoint W.subscheme) ∈ (D.support : Set _)
  rw [← hc]
  exact hcon

/-- If a section presenting `q⁻¹ D` with trivial normal bundle vanishes on `W`, and a section of
`M'` presents `q⁻¹ D'` for `D'` disjoint from `D`, the component classes of `M` and `M'` on `W`
agree: both vanish. -/
private theorem firstChernComponentClass_eq_of_pullbackGlobalSections_eq_zero {M M' : V.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property M]
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property M']
    {σ : Γ(M, ⊤)} {σ' : Γ(M', ⊤)} {D D' : (relativeProjectiveLine C.S).IdealSheafData}
    (h : Stacks.Divisors.zeroScheme V M σ = D.comap q)
    (h' : Stacks.Divisors.zeroScheme V M' σ' = D'.comap q)
    (hDD' : Disjoint (D.support : Set (relativeProjectiveLine C.S)) D'.support)
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme V M σ).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme V M σ).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme V M σ).subschemeι).obj M))
    (k : ℤ) (W : V.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ sV) = ((k + 1 : ℤ) : EInt))
    (hσ : AlgebraicGeometry.pullbackGlobalSections W.subschemeι M σ = 0) :
    firstChernComponentClass C sV k M W hW hDim =
      firstChernComponentClass C sV k M' W hW hDim := by
  have := hW
  have : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ sV)
  obtain ⟨g, hg⟩ :=
    (AlgebraicGeometry.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme V M σ
      W.subschemeι).1 hσ
  have hσ' : AlgebraicGeometry.pullbackGlobalSections W.subschemeι M' σ' ≠ 0 := fun hσ' ↦
    Set.disjoint_left.mp hDD'
      (range_subset_of_pullbackGlobalSections_eq_zero C q h W hσ (genericPoint W.subscheme))
      (range_subset_of_pullbackGlobalSections_eq_zero C q h' W hσ' (genericPoint W.subscheme))
  rw [firstChernComponentClass_eq_zero_of_isTrivial C sV k M W hW hDim
      (AlgebraicGeometry.SheafOfModules.isTrivial_modulePullback_scheme_of_comp g _ _ hg htriv),
    firstChernComponentClass_eq_mk_zeroScheme C sV k M' σ' W hW hDim hσ',
    zeroScheme_restrict_eq_comap C q h' W]
  have := isEmpty_comap_of_range_subset C q hDD'
    (range_subset_of_pullbackGlobalSections_eq_zero C q h W hσ)
  rw [cycleAssociatedToClosedSubscheme_eq_zero_of_isEmpty]
  rfl

include h₀ hi htriv₀ htrivi in
/-- On every integral closed subscheme the component classes of the two modules agree. -/
theorem firstChernComponentClass_zero_eq_infinity (k : ℤ) (W : V.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ sV) = ((k + 1 : ℤ) : EInt)) :
    firstChernComponentClass C sV k M₀ W hW hDim = firstChernComponentClass C sV k Mi W hW hDim :=
        by
  have := hW
  have : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ sV)
  have hdisj := disjoint_support_lineZeroDivisor_lineInfinityDivisor C.S
  by_cases a₀ : AlgebraicGeometry.pullbackGlobalSections W.subschemeι M₀ σ₀ = 0
  · exact firstChernComponentClass_eq_of_pullbackGlobalSections_eq_zero C sV q h₀ hi hdisj
      htriv₀ k W hW hDim a₀
  by_cases ai : AlgebraicGeometry.pullbackGlobalSections W.subschemeι Mi σi = 0
  · exact (firstChernComponentClass_eq_of_pullbackGlobalSections_eq_zero C sV q hi h₀ hdisj.symm
      htrivi k W hW hDim ai).symm
  have hgen₀ := Stacks.ChernCap42.genericPoint_notMem_range_subschemeι_zeroScheme _ _ a₀
  have hgeni := Stacks.ChernCap42.genericPoint_notMem_range_subschemeι_zeroScheme _ _ ai
  rw [zeroScheme_restrict_eq_comap C q h₀ W] at hgen₀
  rw [zeroScheme_restrict_eq_comap C q hi W] at hgeni
  rw [firstChernComponentClass_eq_mk_zeroScheme C sV k M₀ σ₀ W hW hDim a₀,
    firstChernComponentClass_eq_mk_zeroScheme C sV k Mi σi W hW hDim ai,
    zeroScheme_restrict_eq_comap C q h₀ W, zeroScheme_restrict_eq_comap C q hi W]
  have hη1 : genericPoint W.subscheme ∈ (W.subschemeι ≫ q) ⁻¹ᵁ chartOpen C.S :=
    genericPoint_mem_preimage_of_notMem_comap C q W (lineInfinityDivisor C.S) (affineChart C.S)
      (by rw [compl_range_affineChart, coe_support_lineInfinityDivisor]) hgeni
  have hη2 : genericPoint W.subscheme ∈ (W.subschemeι ≫ q) ⁻¹ᵁ yChartOpen C.S :=
    genericPoint_mem_preimage_of_notMem_comap C q W (lineZeroDivisor C.S) (affineYChart C.S)
      (by rw [compl_range_affineYChart, coe_support_lineZeroDivisor]) hgen₀
  obtain ⟨N, rfl, hN⟩ := exists_eq_sub_one_of_eq_add_one hDim
  have hdiff := principalDivisorCycle_eq_sub_lineFibreCycles C (W.subschemeι ≫ sV)
    (W.subschemeι ≫ q) hN hη1 hη2 hgen₀ hgeni
  have hf : lineChartFunction (W.subschemeι ≫ q) hη1 ≠ 0 :=
    left_ne_zero_of_mul_eq_one (lineChartFunction_mul_lineYChartFunction _ hη1 hη2)
  refine QuotientAddGroup.eq_iff_sub_mem.2 ((mem_rationalEquivalences C _ _ _).2 ?_)
  rw [← hdiff]
  exact isRationallyEquivalentToZero_principalDivisorCycle C _ hN hf

include h₀ hi htriv₀ htrivi in
/-- **The first Chern classes of the divisors at zero and at infinity agree.** For `q : V ⟶ 𝐏¹`
and invertible modules with sections presenting `q⁻¹ D₀` and `q⁻¹ D_∞` as zero schemes with
trivial normal bundles, `c₁(M₀) ∩ α = c₁(M_∞) ∩ α` for every cycle `α`. -/
theorem firstChernClassCapOfInvertible_eq_of_zeroScheme_eq_comap (k : ℤ)
    (α : CycleGroup C sV (k + 1)) :
    firstChernClassCapOfInvertible C sV k M₀ α = firstChernClassCapOfInvertible C sV k Mi α :=
  firstChernClassCap_congr C sV k _ _ (fun W hW hDim ↦ QuotientAddGroup.eq_iff_sub_mem.1
    (firstChernComponentClass_zero_eq_infinity C sV q M₀ Mi σ₀ σi h₀ hi htriv₀ htrivi k W hW
      hDim)) α

include h₀ hi htriv₀ htrivi in
/-- **The two Gysin maps agree after pushforward**: `i_{0,*} i_0^* x = i_{∞,*} i_∞^* x`, by
Stacks 02T9 and
`Stacks.Chow.GysinAtInfinity.firstChernClassCapOfInvertible_eq_of_zeroScheme_eq_comap`. -/
theorem chowPushforward_onChow_zero_eq_infinity (k : ℤ) (x : chowGroup C sV (k + 1)) :
    chowPushforwardOfIsClosedImmersion C ((Stacks.Divisors.zeroScheme V M₀ σ₀).subschemeι ≫ sV) sV
        (Stacks.Divisors.zeroScheme V M₀ σ₀).subschemeι rfl k
        ((gysinSystemOfInvertible C).onChow sV M₀ σ₀ k x) =
      chowPushforwardOfIsClosedImmersion C
        ((Stacks.Divisors.zeroScheme V Mi σi).subschemeι ≫ sV) sV
        (Stacks.Divisors.zeroScheme V Mi σi).subschemeι rfl k
        ((gysinSystemOfInvertible C).onChow sV Mi σi k x) := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    exact (properChowPushforward_gysinHomomorphismOfInvertible C sV k M₀ σ₀ c).trans
      ((firstChernClassCapOfInvertible_eq_of_zeroScheme_eq_comap C sV q M₀ Mi σ₀ σi
        h₀ hi htriv₀ htrivi k c).trans
        (properChowPushforward_gysinHomomorphismOfInvertible C sV k Mi σi c).symm)

end Comparison

end GysinAtInfinity

end Stacks.Chow

end
