module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.KoszulDetection
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.OneStep
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.UnitLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.TopCohomologyFinitenessGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFiniteTypeQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsRestrict
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectRetract
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteKernel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitude
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Summands
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DistinguishedTrianglesGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceGeneral

/-!
# Approximation by perfect complexes on an algebraic space with a final affine chart

Let `X` be an algebraic space whose small étale site has a final object with affine underlying
scheme, for instance an affine algebraic space, and let `a₁, …, a_r` be global functions on `X`
whose unit loci cover exactly the complement of a subset `Z ⊆ |X|`. Approximation holds for every
triple `(Z, E, m)` with `E` in `D_QCoh(𝒪_X)` `m`-pseudo-coherent and `Hⁱ(E)` supported on `Z` for
`i ≥ m - r + 1`. This is the content of Stacks 08HM, proved on the étale site itself: the
approximating objects are built from Koszul objects on powers of the `aᵢ`.

## Main results

* `AlgebraicGeometry.Space.supportOfSheaf_subset_of_unitLocus`,
  `AlgebraicGeometry.Space.subsingleton_sections_of_supportOfSheaf_subset`: support in `Z` is
  vanishing on the charts where some `aᵢ` is a unit.
* `AlgebraicGeometry.Space.isLE_koszul`, `AlgebraicGeometry.Space.isPerfect_koszul`: Koszul
  objects are perfect and lie in degrees `≤ 0`.
* `AlgebraicGeometry.Space.homKoszul_eq_zero_of_isLE`: a Koszul object on `r` functions has no
  nonzero morphism into an object of `D_QCoh` concentrated in degrees `≤ -r - 1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS}

/-- The ring of global functions on `X`: compatible families of sections of `𝒪_X`. -/
local notation "globalRing" hX:max =>
  Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (AlgebraicGeometry.RingedSite.O (smallEtaleRingedSite _ _ _ _ hX)))

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-! ### Support and unit loci -/

section Support

variable (l : List (globalRing X.2)) (Z : Set (points B S hS X.1))

/-- A global function which is a unit on a chart is a unit on every chart over it. -/
private theorem isUnit_restrict_of_isUnit (a : globalRing X.2) {U W : SmallEtale B S hS X.1}
    (g : W ⟶ U) (hu : IsUnit (a.1 (op U))) : IsUnit (a.1 (op W)) :=
  (a.2 g.op) ▸ hu.map (((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.map g.op).hom

/-- **A module with no sections over the unit loci of the `aᵢ` is supported on `Z`**, when every
point outside `Z` lies in the image of a chart on which some `aᵢ` is a unit. -/
theorem supportOfSheaf_subset_of_unitLocus
    (hZ : ∀ x ∉ Z, ∃ U : SmallEtale B S hS X.1,
      x ∈ Set.range (pointsMap B S hS _ (chartToSpace B S hS X U).hom) ∧
        ∃ a ∈ l, IsUnit (a.1 (op U)))
    (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : ∀ U : SmallEtale B S hS X.1, (∃ a ∈ l, IsUnit (a.1 (op U))) →
      Subsingleton (F.val.obj (op U))) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) ⊆ Z := by
  intro x hx
  by_contra hxZ
  obtain ⟨U, ⟨y, rfl⟩, a, ha, hu⟩ := hZ x hxZ
  have h0 : IsZero ((etaleModulePullback B S hS (chartToSpace B S hS X U)
      (isEtale_chartToSpace B S hS X U)).obj F) := by
    refine (isZero_etaleModulePullback_chartToSpace_iff B S hS X U F).2 fun W g => ?_
    exact hF W ⟨a, ha, isUnit_restrict_of_isUnit a g hu⟩
  have hempty := (supportOfSheaf_eq_empty_iff_isZero B S hS (chartSpace B S hS X U) _).2 h0
  rw [supportOfSheaf_chartToSpace] at hempty
  exact (Set.eq_empty_iff_forall_notMem.mp hempty) y hx

/-- **A module supported on `Z` has no sections over a chart on which some `aᵢ` is a unit**,
when the images of such charts miss `Z`. -/
theorem subsingleton_sections_of_supportOfSheaf_subset
    (hZ : ∀ U : SmallEtale B S hS X.1, (∃ a ∈ l, IsUnit (a.1 (op U))) →
      Set.range (pointsMap B S hS _ (chartToSpace B S hS X U).hom) ∩ Z = ∅)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) ⊆ Z)
    (U : SmallEtale B S hS X.1) (hU : ∃ a ∈ l, IsUnit (a.1 (op U))) :
    Subsingleton (F.val.obj (op U)) := by
  refine (isZero_etaleModulePullback_chartToSpace_iff B S hS X U F).1 ?_ U (𝟙 U)
  refine (supportOfSheaf_eq_empty_iff_isZero B S hS (chartSpace B S hS X U) _).1 ?_
  rw [supportOfSheaf_chartToSpace]
  refine Set.eq_empty_of_forall_notMem fun y hy => ?_
  exact (Set.eq_empty_iff_forall_notMem.mp (hZ U hU)) _ ⟨⟨y, rfl⟩, hF hy⟩

end Support

/-! ### Koszul objects -/

/-- **Koszul objects lie in degrees `≤ 0`.** -/
theorem isLE_koszul : ∀ l : List (globalRing X.2), (koszul X.2 l).IsLE 0
  | [] => by
    rw [koszul_nil]
    infer_instance
  | a :: l => by
    obtain ⟨g, h, hT⟩ := exists_distTriang_koszul_cons a l
    have h₁ := isLE_koszul l
    have h₃ : ((koszul X.2 l)⟦(1 : ℤ)⟧).IsLE 0 :=
      have := DerivedCategory.TStructure.t.isLE_shift (koszul X.2 l) 0 (1 : ℤ) (-1) (by omega)
      DerivedCategory.TStructure.t.isLE_of_le _ (-1) 0 (by omega)
    exact DerivedCategory.TStructure.t.isLE₂ _ (rot_of_distTriang _ hT) 0 h₁ h₃

/-- **A Koszul object on `r` functions has no nonzero morphism into an object of `D_QCoh`
concentrated in degrees `≤ -r - 1`**, when the small étale site has a final affine chart. -/
theorem homKoszul_eq_zero_of_isLE (T : SmallEtale B S hS X.1) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS X.1 T) :
    ∀ (l : List (globalRing X.2)) (F : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)),
      QcohDerived B S hS X F → F.IsLE (-(l.length : ℤ) - 1) →
      ∀ x : koszul X.2 l ⟶ F, x = 0
  | [], F, hF, hle, x => homFromUnit_eq_zero_of_isLE T hT hTa F hF (by simpa using hle) x
  | a :: l, F, hF, hle, x => by
    obtain ⟨g, h, hT'⟩ := exists_distTriang_koszul_cons a l
    have hle' : F.IsLE (-(l.length : ℤ) - 1) := by
      have : F.IsLE (-((a :: l).length : ℤ) - 1) := hle
      exact DerivedCategory.TStructure.t.isLE_of_le _ (-((a :: l).length : ℤ) - 1) _
        (by simp only [List.length_cons]; push_cast; omega)
    have hgx : g ≫ x = 0 := homKoszul_eq_zero_of_isLE T hT hTa l F hF hle' _
    obtain ⟨z, hz⟩ := Triangle.yoneda_exact₃ _ hT' x hgx
    let e := (shiftFunctorCompIsoId (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (1 : ℤ) (-1)
      (by omega)).app (koszul X.2 l)
    have hle'' : (F⟦(-1 : ℤ)⟧).IsLE (-(l.length : ℤ) - 1) := by
      have : F.IsLE (-((a :: l).length : ℤ) - 1) := hle
      exact DerivedCategory.TStructure.t.isLE_shift F (-((a :: l).length : ℤ) - 1) (-1 : ℤ) _
        (by simp only [List.length_cons]; push_cast; omega)
    have hz0 : e.inv ≫ z⟦(-1 : ℤ)⟧' = 0 :=
      homKoszul_eq_zero_of_isLE T hT hTa l (F⟦(-1 : ℤ)⟧) (qcohDerived_shift F (-1) hF) hle'' _
    have : z⟦(-1 : ℤ)⟧' = 0 := by simpa using congrArg (e.hom ≫ ·) hz0
    have hz' : z = 0 := (shiftFunctor _ (-1 : ℤ)).map_injective (by rw [this, Functor.map_zero])
    rw [hz, hz', comp_zero]

/-- Sections over a chart are trivial for a module isomorphic to one with trivial sections. -/
private theorem subsingleton_obj_of_iso {M N : Modules.{u, u} B S hS X.1 X.2} (e : M ≅ N)
    (U : SmallEtale B S hS X.1) (h : Subsingleton (N.val.obj (op U))) :
    Subsingleton (M.val.obj (op U)) :=
  ⟨fun _ _ => (Iso.toLinearEquiv ((SheafOfModules.evaluation _ (op U)).mapIso e)).injective
    (h.elim _ _)⟩

/-- Having quasi-coherent cohomology is preserved by the truncations `τ_{≥ n}`. -/
theorem qcohDerived_truncGE (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (n : ℤ)
    (hE : QcohDerived B S hS X E) :
    QcohDerived B S hS X ((DerivedCategory.TStructure.t.truncGE n).obj E) :=
  DerivedCategoryB.derivedCategoryB_truncGE_obj _
    (WeakSerre.isWeakSerre_of_isWeakSerreClass _) n E hE

/-- **The Koszul lift** (the étale-site form of Stacks 08E3). Let the small étale site of `X` have
a final affine chart, let `l` be a list of `r` global functions, and let `F` be an object
of `D_QCoh(𝒪_X)` whose cohomology sheaves in the degrees `≥ -r + 1` vanish over every chart on
which some member of `l` is a unit. Every morphism `𝒪_X[0] ⟶ F` factors through the Koszul object
of a list of `r` functions, each a power of a member of `l`.

The morphism is first extended, one function at a time, to a morphism into `τ_{≥ -r + 1} F` from
a Koszul object, a power of each function killing the obstruction by
`AlgebraicGeometry.Space.exists_pow_smul_eq_zero_of_koszul`; it then lifts to `F` because the
Koszul object on `r` functions sees nothing in degrees `≤ -r - 1`. For the empty list there is
nothing to do. -/
theorem exists_koszul_lift (T : SmallEtale B S hS X.1) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS X.1 T) (l : List (globalRing X.2))
    (F : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hF : QcohDerived B S hS X F)
    (hvan : ∀ a ∈ l, ∀ U : SmallEtale B S hS X.1, IsUnit (a.1 (op U)) → ∀ i : ℤ,
      -(l.length : ℤ) + 1 ≤ i →
        Subsingleton (((DerivedCategory.homologyFunctor _ i).obj F).val.obj (op U)))
    (s : koszul X.2 [] ⟶ F) :
    ∃ l' : List (globalRing X.2), l'.length = l.length ∧
      (∀ U : SmallEtale B S hS X.1, (∃ a ∈ l, IsUnit (a.1 (op U))) →
        ∃ b ∈ l', IsUnit (b.1 (op U))) ∧
      ∃ (y : koszul X.2 [] ⟶ koszul X.2 l') (x : koszul X.2 l' ⟶ F), y ≫ x = s := by
  by_cases hl : l = []
  · subst hl
    exact ⟨[], rfl, fun U ⟨a, ha, _⟩ => absurd ha List.not_mem_nil, 𝟙 _, s,
      Category.id_comp s⟩
  let t := DerivedCategory.TStructure.t (C := Modules.{u, u} B S hS X.1 X.2)
  let n : ℤ := -(l.length : ℤ) + 1
  have hlen : 1 ≤ l.length := List.length_pos_iff.2 hl
  let G := (t.truncGE n).obj F
  let π : F ⟶ G := (t.truncGEπ n).app F
  let Tr := Triangle.mk ((t.truncLTι n).app F) π ((t.truncGEδLT n).app F)
  have hTr : Tr ∈ distTriang _ := t.triangleLTGE_distinguished n F
  have hG : QcohDerived B S hS X G := qcohDerived_truncGE F n hF
  have hvanG : ∀ a ∈ l, VanishesWhereUnit a G := by
    intro a ha U hU q
    by_cases hq : n ≤ q
    · have e := (DerivedCategory.truncGECompHomologyFunctorIso n q hq).app F
      exact subsingleton_obj_of_iso e.symm U (hvan a ha U hU q hq)
    · have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj G) :=
        DerivedCategory.isZero_of_isGE G n q (by omega)
      exact ModuleCat.subsingleton_of_isZero ((SheafOfModules.evaluation _ (op U)).map_isZero hz)
  -- extend into `τ_{≥ n} F`, one function at a time
  have key : ∀ l₀ : List (globalRing X.2), (∀ a ∈ l₀, a ∈ l) →
      ∃ l' : List (globalRing X.2), l'.length = l₀.length ∧
        (∀ U : SmallEtale B S hS X.1, (∃ a ∈ l₀, IsUnit (a.1 (op U))) →
          ∃ b ∈ l', IsUnit (b.1 (op U))) ∧
        ∃ (y : koszul X.2 [] ⟶ koszul X.2 l') (x : koszul X.2 l' ⟶ G), y ≫ x = s ≫ π := by
    intro l₀
    induction l₀ with
    | nil => exact fun _ => ⟨[], rfl, fun U ⟨a, ha, _⟩ => absurd ha List.not_mem_nil,
        𝟙 _, s ≫ π, Category.id_comp _⟩
    | cons a l₀ ih =>
      intro hsub
      obtain ⟨l', hlen', hunit, y, x, hyx⟩ := ih fun b hb => hsub b (List.mem_cons_of_mem a hb)
      obtain ⟨N, hN⟩ := exists_pow_smul_eq_zero_of_koszul T hT hTa a l' G hG
        (hvanG a (hsub a List.mem_cons_self)) x
      obtain ⟨g, h, hT'⟩ := exists_distTriang_koszul_cons (a ^ N) l'
      obtain ⟨x', hx'⟩ := Triangle.yoneda_exact₂ _ hT' x (by
        show (a ^ N • 𝟙 (koszul X.2 l')) ≫ x = 0
        rw [Linear.smul_comp, Category.id_comp, hN])
      refine ⟨a ^ N :: l', by simp [hlen'], fun U ⟨b, hb, hu⟩ => ?_, y ≫ g, x', ?_⟩
      · rcases List.mem_cons.1 hb with rfl | hb
        · refine ⟨b ^ N, List.mem_cons_self, ?_⟩
          rw [SubmonoidClass.coe_pow, Pi.pow_apply]
          exact hu.pow N
        · obtain ⟨c, hc, hcu⟩ := hunit U ⟨b, hb, hu⟩
          exact ⟨c, List.mem_cons_of_mem _ hc, hcu⟩
      · rw [Category.assoc, ← hyx, hx']
        rfl
  obtain ⟨l', hlen', hunit, y, x, hyx⟩ := key l fun a ha => ha
  -- lift along `F ⟶ τ_{≥ n} F`
  have hLT : ((t.truncLT n).obj F).IsLE (-(l'.length : ℤ)) :=
    t.isLE_truncLT_obj F n _ (by omega)
  have hLTqc : QcohDerived B S hS X ((t.truncLT n).obj F) :=
    DerivedCategoryB.derivedCategoryB_truncLT_obj _
      (WeakSerre.isWeakSerre_of_isWeakSerreClass _) n F hF
  have hx3 : x ≫ Tr.mor₃ = 0 :=
    homKoszul_eq_zero_of_isLE T hT hTa l' _ (qcohDerived_shift _ 1 hLTqc)
      (t.isLE_shift _ (-(l'.length : ℤ)) (1 : ℤ) _ (by omega)) _
  obtain ⟨xF, hxF⟩ : ∃ xF : koszul X.2 l' ⟶ F, x = xF ≫ π :=
    Triangle.coyoneda_exact₃ _ hTr x hx3
  refine ⟨l', hlen', hunit, y, xF, ?_⟩
  have hd : (y ≫ xF - s) ≫ π = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, ← hxF, hyx, sub_self]
  obtain ⟨z, hz⟩ : ∃ z : koszul X.2 [] ⟶ (t.truncLT n).obj F,
      y ≫ xF - s = z ≫ (t.truncLTι n).app F :=
    Triangle.coyoneda_exact₂ _ hTr (y ≫ xF - s) hd
  have hz0 : z = 0 := homFromUnit_eq_zero_of_isLE T hT hTa _ hLTqc
    (t.isLE_of_le _ (-(l'.length : ℤ)) (-1) (by rw [hlen']; omega)) z
  rwa [hz0, zero_comp, sub_eq_zero] at hz

/-! ### Morphisms out of a quasi-coherent module are determined over the final chart -/

/-- **A morphism out of a quasi-coherent module vanishing over a final affine chart vanishes**:
over every affine chart the sections of a quasi-coherent module are generated by restrictions
of sections over the final chart. -/
theorem eq_zero_of_app_terminal (T : SmallEtale B S hS X.1) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS X.1 T) {M N : Modules.{u, u} B S hS X.1 X.2}
    (hM : M.IsQuasicoherentOnSite) (g : M ⟶ N) (hg : g.val.app (op T) = 0) : g = 0 := by
  refine Modules.eq_zero_of_forall_app_isAffine_eq_zero (X := X) B S hS g fun U hU => ?_
  have hspan := (chartBaseChange_surjective_iff_span_eq_top M (hT.from U)).1
    ((isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 M hM) T U hTa hU
      (hT.from U)).2
  ext x
  have hx : x ∈ Submodule.span (chartRing B S hS X.1 X.2 U)
      (Set.range fun y : M.val.obj (op T) => chartRestrictLinear M (hT.from U) y) := by
    rw [hspan]
    trivial
  show (g.val.app (op U)).hom x = 0
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, rfl⟩ := hz
    have h : (g.val.app (op U)).hom ((M.val.map (hT.from U).op).hom y) =
        (N.val.map (hT.from U).op).hom ((g.val.app (op T)).hom y) :=
      congrArg (fun k => k.hom y) (g.val.naturality (hT.from U).op)
    have hg' : (g.val.app (op T)).hom y = 0 := by
      rw [hg]
      rfl
    show (g.val.app (op U)).hom ((M.val.map (hT.from U).op).hom y) = 0
    rw [h, hg']
    exact (N.val.map (hT.from U).op).hom.map_zero
  | zero => exact map_zero _
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul r a _ ha => rw [(g.val.app (op U)).hom.map_smul, ha, smul_zero]

/-! ### Vanishing where a function is a unit, on chart spaces -/


/-- A global function which is a unit on a chart is a unit on every chart over it. -/
theorem isUnit_globalRing_restrict (a : globalRing X.2) {U W : SmallEtale B S hS X.1} (g : W ⟶ U)
    (hu : IsUnit (a.1 (op U))) : IsUnit (a.1 (op W)) :=
  isUnit_restrict_of_isUnit a g hu

/-- **Vanishing where `a` is a unit is vanishing of the restrictions to the charts where `a` is a
unit.** -/
theorem vanishesWhereUnit_iff_isZero_restrict (a : globalRing X.2)
    (M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    VanishesWhereUnit a M ↔ ∀ U : SmallEtale B S hS X.1, IsUnit (a.1 (op U)) →
      IsZero ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U)).mapDerivedCategory.obj M) := by
  let L := fun U : SmallEtale B S hS X.1 => etaleModulePullback.{u, u} B S hS
    (chartToSpace B S hS X U) (isEtale_chartToSpace B S hS X U)
  have key : ∀ (U : SmallEtale B S hS X.1) (q : ℤ),
      IsZero ((L U).obj ((DerivedCategory.homologyFunctor _ q).obj M)) ↔
        IsZero ((DerivedCategory.homologyFunctor _ q).obj ((L U).mapDerivedCategory.obj M)) :=
    fun U q => Iso.isZero_iff (((L U).mapDerivedCategoryHomologyIso q).app M).symm
  refine ⟨fun h U hU => ?_, fun h U hU q => ?_⟩
  · rw [DerivedCategory.isZero_iff_forall_isZero_homology]
    exact fun q => (key U q).1 ((isZero_etaleModulePullback_chartToSpace_iff B S hS X U _).2
      fun W g => h W (isUnit_globalRing_restrict a g hU) q)
  · exact (isZero_etaleModulePullback_chartToSpace_iff B S hS X U _).1
      ((key U q).2 ((DerivedCategory.homologyFunctor _ q).map_isZero (h U hU))) U (𝟙 U)

/-- Vanishing where `a` is a unit passes to the middle of a distinguished triangle. -/
theorem VanishesWhereUnit.obj₂ {a : globalRing X.2}
    (T : Triangle (DerivedCategory (Modules.{u, u} B S hS X.1 X.2))) (hT : T ∈ distTriang _)
    (h₁ : VanishesWhereUnit a T.obj₁) (h₃ : VanishesWhereUnit a T.obj₃) :
    VanishesWhereUnit a T.obj₂ := by
  rw [vanishesWhereUnit_iff_isZero_restrict] at h₁ h₃ ⊢
  intro U hU
  exact Triangle.isZero₂_of_isZero₁₃ _
    ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
      (isEtale_chartToSpace B S hS X U)).mapDerivedCategory.map_distinguished _ hT)
    (h₁ U hU) (h₃ U hU)

/-- Vanishing where `a` is a unit passes to shifts. -/
theorem VanishesWhereUnit.of_iso {a : globalRing X.2}
    {M N : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)} (h : VanishesWhereUnit a M)
    (e : M ≅ N) : VanishesWhereUnit a N := fun U hU q =>
  subsingleton_obj_of_iso ((DerivedCategory.homologyFunctor _ q).mapIso e).symm U (h U hU q)

/-- Koszul objects are perfect. -/
theorem isPerfect_koszul : ∀ l : List (globalRing X.2),
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect (koszul X.2 l)
  | [] => isPerfect_unit X
  | a :: l => by
    obtain ⟨g, h, hT⟩ := exists_distTriang_koszul_cons a l
    exact RingedSite.isPerfect_obj₃_of_distinguished_general
      (smallEtaleRingedSite B S hS X.1 X.2) _ hT (isPerfect_koszul l) (isPerfect_koszul l)

/-! ### Supports through restriction to the unit charts -/

section UnitSupport

variable (l : List (globalRing X.2)) (Z : Set (points B S hS X.1))

/-- In the unit-locus description of `Z`, the support of `Hⁱ(M)` lies in `Z` exactly when `Hⁱ`
of the restriction of `M` to every chart where some member of `l` is a unit vanishes. -/
theorem supportOfSheaf_homology_subset_iff
    (hZ1 : ∀ x ∉ Z, ∃ U : SmallEtale B S hS X.1,
      x ∈ Set.range (pointsMap B S hS _ (chartToSpace B S hS X U).hom) ∧
        ∃ a ∈ l, IsUnit (a.1 (op U)))
    (hZ2 : ∀ U : SmallEtale B S hS X.1, (∃ a ∈ l, IsUnit (a.1 (op U))) →
      Set.range (pointsMap B S hS _ (chartToSpace B S hS X U).hom) ∩ Z = ∅)
    (M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (i : ℤ) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj M)) ⊆ Z ↔
      ∀ U : SmallEtale B S hS X.1, (∃ a ∈ l, IsUnit (a.1 (op U))) →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj
          ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
            (isEtale_chartToSpace B S hS X U)).mapDerivedCategory.obj M)) := by
  have key : ∀ U : SmallEtale B S hS X.1,
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U)).mapDerivedCategory.obj M)) ↔
        ∀ W : SmallEtale B S hS X.1, (W ⟶ U) →
          Subsingleton (((DerivedCategory.homologyFunctor _ i).obj M).val.obj (op W)) := fun U =>
    (Iso.isZero_iff (((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
      (isEtale_chartToSpace B S hS X U)).mapDerivedCategoryHomologyIso i).app M)).trans
      (isZero_etaleModulePullback_chartToSpace_iff B S hS X U _)
  exact ⟨fun h U ⟨a, ha, hu⟩ => (key U).2 fun W g =>
      subsingleton_sections_of_supportOfSheaf_subset l Z hZ2 _ h W
        ⟨a, ha, isUnit_globalRing_restrict a g hu⟩,
    fun h => supportOfSheaf_subset_of_unitLocus l Z hZ1 _ fun U hU => (key U).1 (h U hU) U (𝟙 U)⟩

/-- `Hⁱ` of the restriction of the middle term of a distinguished triangle to a chart vanishes
when it vanishes for the two outer terms. -/
theorem isZero_homology_res_obj₂ (U : SmallEtale B S hS X.1)
    (T : Triangle (DerivedCategory (Modules.{u, u} B S hS X.1 X.2))) (hT : T ∈ distTriang _)
    (i : ℤ)
    (h₁ : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U)).mapDerivedCategory.obj T.obj₁)))
    (h₃ : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U)).mapDerivedCategory.obj T.obj₃))) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U)).mapDerivedCategory.obj T.obj₂)) :=
  ((DerivedCategory.homologyFunctor _ 0).homologySequence_exact₂ _
    ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U)).mapDerivedCategory.map_distinguished _ hT) i).isZero_X₂
    (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

/-- `Hⁱ` of a shift, restricted to a chart. -/
theorem isZero_homology_res_shift_iff (U : SmallEtale B S hS X.1)
    (M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (a i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
        (isEtale_chartToSpace B S hS X U)).mapDerivedCategory.obj (M⟦a⟧))) ↔
      IsZero ((DerivedCategory.homologyFunctor _ (a + i)).obj
        ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U)).mapDerivedCategory.obj M)) :=
  Iso.isZero_iff ((DerivedCategory.homologyFunctor _ i).mapIso
      (((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X U)
          (isEtale_chartToSpace B S hS X U)).mapDerivedCategory.commShiftIso a).app M) ≪≫
    ((DerivedCategory.homologyFunctor _ 0).shiftIso a i (a + i) rfl).app _)

end UnitSupport

/-! ### The one-step construction -/

/-- **The one-step construction in degree zero.** Let the small étale site of `X` have a final
affine chart `T`, and let `F` be an object of `D_QCoh(𝒪_X)` with cohomology in degrees `≤ 0`,
whose `H⁰` has finitely generated sections over `T`, and whose cohomology sheaves in the degrees
`≥ -r + 1` vanish over the charts where one of `r` global functions `a₁, …, a_r` is a unit. Then
a perfect object vanishing where some `aᵢ` is a unit, with cohomology in degrees `≤ 0`, maps to
`F` surjectively on `H⁰`: generators of `H⁰(F)` over `T` are morphisms `𝒪_X[0] ⟶ F`, each of
which factors through a Koszul object, and the sum of those Koszul objects is the source. -/
theorem exists_epi_homology_zero (T : SmallEtale B S hS X.1) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS X.1 T) (l : List (globalRing X.2))
    (F : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hF : QcohDerived B S hS X F)
    (_hle : ∀ i : ℤ, 0 < i →
      IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj F))
    (hfin : Module.Finite (chartRing B S hS X.1 X.2 T)
      (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj F).val.obj
        (op T)))
    (hvan : ∀ a ∈ l, ∀ U : SmallEtale B S hS X.1, IsUnit (a.1 (op U)) → ∀ i : ℤ,
      -(l.length : ℤ) + 1 ≤ i →
        Subsingleton (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
          F).val.obj (op U))) :
    ∃ P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      ((smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P ∧ ∀ a ∈ l, VanishesWhereUnit a P) ∧
      (∀ i : ℤ, 0 < i →
        IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj P)) ∧
      ∃ γ : P ⟶ F, Epi ((DerivedCategory.homologyFunctor _ 0).map γ) := by
  classical
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := chartRing B S hS X.1 X.2 T)
    (M := ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj F).val.obj
      (op T))
  choose sj hsj using fun j : Fin k => (bijective_homFromUnitSections T hT hTa F hF).2 (g j)
  choose l' hlen hunit y x hyx using fun j : Fin k =>
    exists_koszul_lift T hT hTa l F hF hvan (sj j)
  let R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) → Prop := fun P =>
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P ∧ ∀ a ∈ l, VanishesWhereUnit a P
  have hR₀ : ∀ Z : DerivedCategory (Modules.{u, u} B S hS X.1 X.2), IsZero Z → R Z := fun Z hZ =>
    ⟨isPerfect_of_isZero B S hS hZ, fun a _ U _ q => ModuleCat.subsingleton_of_isZero
      ((SheafOfModules.evaluation _ (op U)).map_isZero
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).map_isZero hZ))⟩
  have hR₂ : ∀ T' : Triangle (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)),
      T' ∈ distTriang _ → R T'.obj₁ → R T'.obj₃ → R T'.obj₂ := fun T' hT' h₁ h₃ =>
    ⟨RingedSite.isPerfect_obj₂_of_distinguished_general (smallEtaleRingedSite B S hS X.1 X.2) T' hT'
      h₁.1 h₃.1, fun a ha => VanishesWhereUnit.obj₂ T' hT' (h₁.2 a ha) (h₃.2 a ha)⟩
  have hP : ∀ j, R (koszul X.2 (l' j)) := fun j =>
    ⟨isPerfect_koszul _, fun a ha U hU q =>
      subsingleton_homology_koszul_sections _ U (hunit j U ⟨a, ha, hU⟩) q⟩
  have hPvan : ∀ (j : Fin k) (i : ℤ), 0 < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj (koszul X.2 (l' j))) := fun j i hi =>
    have := isLE_koszul (l' j)
    DerivedCategory.isZero_of_isLE _ 0 i hi
  obtain ⟨Z, hZ, hZvan, γ, hγ⟩ :=
    DerivedCategory.exists_comp_eq_of_fin R hR₀ hR₂ 0 k _ hP hPvan x
  refine ⟨Z, hZ, hZvan, γ, ?_⟩
  obtain ⟨C, v, w, hTr⟩ := distinguished_cocone_triangle γ
  refine (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff _ hTr 0).2 ?_
  refine eq_zero_of_app_terminal T hT hTa (hF 0) _ ?_
  have hlin : (((DerivedCategory.homologyFunctor _ 0).map v).val.app (op T)).hom = 0 := by
    refine LinearMap.ext_on_range hg fun j => ?_
    have h1 := homFromUnitSections_comp T hT (sj j) v
    rw [hsj j] at h1
    refine h1.symm.trans ?_
    obtain ⟨u, hu⟩ := hγ j
    have h0' : (y j ≫ x j) ≫ v = 0 := by
      rw [← hu, Category.assoc, Category.assoc,
        show γ ≫ v = 0 from comp_distTriang_mor_zero₁₂ _ hTr, comp_zero, comp_zero]
    have h0 : sj j ≫ v = 0 := (congrArg (fun f => f ≫ v) (hyx j)).symm.trans h0'
    rw [h0, map_zero]
    rfl
  exact ModuleCat.hom_ext hlin

/-! ### Approximation -/

/-- A perfect object of `D(𝒪_X)` is `n`-pseudo-coherent for every `n`. -/
theorem isPseudoCoherentFrom_of_isPerfect {P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)}
    (hP : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P) (n : ℤ) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom P n := by
  obtain ⟨K, hK, e⟩ := RingedSite.isPseudoCoherent_of_isPerfect_general _ hP
  exact ⟨K, hK n, e⟩

/-- **Approximation on an algebraic space with a final affine chart** (the content of Stacks
08HM). Let the small étale site of the quasi-compact algebraic space `X` have a final affine
chart, let `a₁, …, a_r` be global functions and `Z ⊆ |X|` the complement of the union of the
images of the charts on which some `aᵢ` is a unit. Approximation holds for every triple
`(Z, E, m)` with `E` in `D_QCoh(𝒪_X)` `m`-pseudo-coherent and `Hⁱ(E)` supported on `Z` for
`i ≥ m - r + 1`. -/
theorem approximationHolds_of_unitLocus (T : SmallEtale B S hS X.1) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS X.1 T) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (l : List (globalRing X.2)) (Z : Set (points B S hS X.1))
    (hZ1 : ∀ x ∉ Z, ∃ U : SmallEtale B S hS X.1,
      x ∈ Set.range (pointsMap B S hS _ (chartToSpace B S hS X U).hom) ∧
        ∃ a ∈ l, IsUnit (a.1 (op U)))
    (hZ2 : ∀ U : SmallEtale B S hS X.1, (∃ a ∈ l, IsUnit (a.1 (op U))) →
      Set.range (pointsMap B S hS _ (chartToSpace B S hS X U).hom) ∩ Z = ∅)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (m : ℤ)
    (hpc : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E.obj m)
    (hsupp : ∀ i : ℤ, m - (l.length : ℤ) + 1 ≤ i →
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E.obj)) ⊆ Z) :
    ApproximationHolds B S hS X.1 X.2 Z E m := by
  let r : ℤ := l.length
  have hiff := supportOfSheaf_homology_subset_iff l Z hZ1 hZ2
  let Rc : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) → Prop := fun P =>
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P ∧ CohomologySupportedOn B S hS X.1 X.2 Z P
  let Qc : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) → Prop := fun F =>
    QcohDerived B S hS X F ∧ (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom F m ∧
      ∀ i : ℤ, m - r + 1 ≤ i → supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj F)) ⊆ Z
  have hR : ∀ (A B' D : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (f : A ⟶ B')
      (g : B' ⟶ D) (h : D ⟶ A⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang _ → Rc A → Rc D →
        Rc B' := by
    intro A B' D f g h hT' hA hD
    refine ⟨RingedSite.isPerfect_obj₂_of_distinguished_general
      (smallEtaleRingedSite B S hS X.1 X.2) _ hT' hA.1 hD.1, fun i => (hiff _ i).2 fun U hU => ?_⟩
    exact isZero_homology_res_obj₂ U _ hT' i ((hiff _ i).1 (hA.2 i) U hU)
      ((hiff _ i).1 (hD.2 i) U hU)
  have hQ : ∀ T' : Triangle (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)),
      T' ∈ distTriang _ → Rc T'.obj₁ → Qc T'.obj₂ → Qc T'.obj₃ := by
    intro T' hT' h₁ h₂
    refine ⟨(QcohDerived B S hS X).ext_of_isTriangulatedClosed₃ _ hT'
      (qcohDerived_of_isPerfect_derivedCategoryB X _ h₁.1) h₂.1,
      RingedSite.isPseudoCoherentFrom_of_distinguished_one_general _ m T' hT'
        (isPseudoCoherentFrom_of_isPerfect h₁.1 (m + 1)) h₂.2.1, fun i hi => ?_⟩
    refine (hiff _ i).2 fun U hU => ?_
    refine isZero_homology_res_obj₂ U _ (rot_of_distTriang _ hT') i
      ((hiff _ i).1 (h₂.2.2 i hi) U hU) ?_
    exact (isZero_homology_res_shift_iff U _ 1 i).2 ((hiff _ (1 + i)).1 (h₁.2 (1 + i)) U hU)
  have hstep : ∀ (E' : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)), Qc E' → ∀ t : ℤ,
      m ≤ t → (∀ i : ℤ, t < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj E')) →
      ∃ P : DerivedCategory (Modules.{u, u} B S hS X.1 X.2), Rc P ∧
        (∀ i : ℤ, t < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj P)) ∧
        ∃ α : P ⟶ E', Epi ((DerivedCategory.homologyFunctor _ t).map α) := by
    intro E' hE' t hmt hvan
    let F := E'⟦t⟧
    let eH : ∀ i : ℤ, (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj F ≅
        (DerivedCategory.homologyFunctor _ (t + i)).obj E' := fun i =>
      ((DerivedCategory.homologyFunctor _ 0).shiftIso t i (t + i) rfl).app E'
    have hFqc : QcohDerived B S hS X F := qcohDerived_shift E' t hE'.1
    have hle : ∀ i : ℤ, 0 < i →
        IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj F) :=
      fun i hi => (hvan (t + i) (by omega)).of_iso (eH i)
    have hft : SheafOfModules.IsFiniteTypeOnSite
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) t).obj E') :=
      Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType _
        (RingedSite.isFiniteType_homology_general (smallEtaleRingedSite B S hS X.1 X.2) E' t
          (RingedSite.isPseudoCoherentFrom_mono_general _ E' hE'.2.1 hmt) hvan)
    have ht : t + 0 = t := add_zero t
    let eH0 : (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj F ≅
        (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) t).obj E' :=
      eH 0 ≪≫ eqToIso (congrArg (fun k => (DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS X.1 X.2) k).obj E') ht)
    have hft0 : SheafOfModules.IsFiniteTypeOnSite
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj F) :=
      have : Epi eH0.inv := IsIso.epi_of_iso eH0.inv
      isFiniteTypeOnSite_of_epi B S hS X.1 X.2 eH0.inv hft
    have hfin := module_finite_sections_of_isFiniteTypeOnSite _ (hFqc 0) hft0 T hTa
    have hvanF : ∀ a ∈ l, ∀ U : SmallEtale B S hS X.1, IsUnit (a.1 (op U)) → ∀ i : ℤ,
        -(l.length : ℤ) + 1 ≤ i →
          Subsingleton (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
            F).val.obj (op U)) := by
      intro a ha U hU i hi
      exact subsingleton_obj_of_iso (eH i) U (subsingleton_sections_of_supportOfSheaf_subset l Z hZ2
        _ (hE'.2.2 (t + i) (by omega)) U ⟨a, ha, hU⟩)
    obtain ⟨P', ⟨hP'perf, hP'van⟩, hP'le, γ, hγ⟩ :=
      exists_epi_homology_zero T hT hTa l F hFqc hle hfin hvanF
    refine ⟨P'⟦-t⟧, ⟨RingedSite.isPerfect_shift_general _ hP'perf (-t),
      fun i => (hiff _ i).2 fun U hU => ?_⟩, fun i hi => ?_,
      γ⟦-t⟧' ≫ (shiftFunctorCompIsoId _ t (-t) (add_neg_cancel t)).hom.app E', ?_⟩
    · obtain ⟨a, ha, hu⟩ := hU
      refine (isZero_homology_res_shift_iff U _ (-t) i).2 ?_
      exact (DerivedCategory.homologyFunctor _ _).map_isZero
        ((vanishesWhereUnit_iff_isZero_restrict a P').1 (hP'van a ha) U hu)
    · exact (hP'le (-t + i) (by omega)).of_iso
        (((DerivedCategory.homologyFunctor _ 0).shiftIso (-t) i (-t + i) rfl).app P')
    · rw [Functor.map_comp]
      refine epi_comp' ?_ (IsIso.epi_of_iso _)
      exact (RingedSite.epi_map_iff_of_natIso
        ((DerivedCategory.homologyFunctor _ 0).shiftIso (-t) t 0 (by omega)) γ).2 hγ
  obtain ⟨b, hb⟩ := exists_isZero_homology_of_isPseudoCoherentFrom B S hS X hXqc E.obj m hpc
  obtain ⟨P, hP, α, hα⟩ := DerivedCategory.exists_approximatesFrom_of_step Qc Rc m hR hQ hstep
    E.obj ⟨E.property, hpc, hsupp⟩ b hb
  exact ⟨P, hP.1, hP.2, α, hα.1, hα.2⟩

/-! ### Open subspaces of an affine algebraic space as unions of unit loci -/

section UnitLocusPresentation

attribute [local instance] pointTopology

/-- The range of the map on points of the structure morphism of a chart is the range of
`AlgebraicGeometry.Space.chartPointsMap`. -/
theorem range_pointsMap_chartToSpace (U : SmallEtale B S hS X.1) :
    Set.range (pointsMap B S hS _ (chartToSpace B S hS X U).hom) = Set.range (chartPointsMap U) :=
  ((schemePointsHomeomorph B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm.surjective
    |>.range_comp _).symm

/-- **A quasi-compact open subspace of an affine algebraic space is a finite union of unit loci
of global functions**: there are finitely many global functions such that a chart lies over the
open subspace as soon as one of them is a unit on it, and every point of the open subspace lies
in the image of a chart on which one of them is a unit. -/
theorem exists_list_unitLocus_of_isOpenSubspace (hXa : IsAffineSpace B S hS X.1)
    (O : Subfunctor X.1) (hO : IsOpenSubspace B S hS O) (hOqc : IsQuasiCompact B S hS O.ι) :
    ∃ l : List (globalRing X.2),
      (∀ U : SmallEtale B S hS X.1, (∃ a ∈ l, IsUnit (a.1 (op U))) →
        Set.range (pointsMap B S hS _ (chartToSpace B S hS X U).hom) ⊆
          Set.range (pointsMap B S hS O.toFunctor O.ι)) ∧
      ∀ x ∈ Set.range (pointsMap B S hS O.toFunctor O.ι), ∃ U : SmallEtale B S hS X.1,
        x ∈ Set.range (pointsMap B S hS _ (chartToSpace B S hS X U).hom) ∧
          ∃ a ∈ l, IsUnit (a.1 (op U)) := by
  classical
  let := pointTopology B S hS X.1
  let Zc := (Set.range (pointsMap B S hS O.toFunctor O.ι))ᶜ
  obtain ⟨T₀, hT₀, ⟨i⟩⟩ := hXa
  let W₀ := chartOfIso B S hS T₀ i
  have hW₀ : IsTerminal W₀ := isTerminalChartOfIso T₀ i
  obtain ⟨I, ⟨gens, hgens⟩, hI⟩ := exists_fg_ideal_zeroLocus_eq_preimage_chartPointsMap X.2
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS O.ι hO.2).isClosed_compl
    hO (compl_compl _).symm hOqc W₀ hT₀
  let toG := globalRingOfTerminal B S hS X.2 hW₀
  let l := gens.toList.map toG
  have key : ∀ (U : SmallEtale B S hS X.1) (x : chartScheme U),
      chartPointsMap U x ∈ Set.range (pointsMap B S hS O.toFunctor O.ι) ↔
        ∃ f ∈ gens, x ∈ (chartScheme U).basicOpen ((toG f).1 (op U)) := by
    intro U x
    rw [chartPointsMap_comp (g := hW₀.from U) (x := x), ← Set.notMem_compl_iff]
    show ¬ (_ ∈ chartPointsMap W₀ ⁻¹' Zc) ↔ _
    rw [hI, ← hgens, Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
    push Not
    refine exists_congr fun f => and_congr Iff.rfl ?_
    show _ ↔ x ∈ (chartScheme U).basicOpen (((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X.1).map (hW₀.from U))).appTop f)
    exact SetLike.ext_iff.1 (Scheme.preimage_basicOpen _ f) x
  refine ⟨l, ?_, ?_⟩
  · rintro U ⟨a, ha, hu⟩
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 ha
    rw [range_pointsMap_chartToSpace]
    rintro _ ⟨x, rfl⟩
    refine (key U x).2 ⟨f, Finset.mem_toList.1 hf, ?_⟩
    rw [(chartScheme U).basicOpen_of_isUnit hu]
    trivial
  · rintro x ⟨y, rfl⟩
    have hsurj : Function.Surjective (chartPointsMap W₀) := by
      intro z
      refine ⟨schemePointsHomeomorph B S hS T₀ (pointsMap B S hS _ i.hom z), ?_⟩
      show pointsMap B S hS _ i.inv ((schemePointsHomeomorph B S hS T₀).symm
        (schemePointsHomeomorph B S hS T₀ (pointsMap B S hS _ i.hom z))) = z
      rw [Homeomorph.symm_apply_apply]
      show (pointsMap B S hS _ i.inv ∘ pointsMap B S hS _ i.hom) z = z
      rw [← pointsMap_comp, i.hom_inv_id, pointsMap_id, id]
    obtain ⟨z, hz⟩ := hsurj (pointsMap B S hS O.toFunctor O.ι y)
    obtain ⟨f, hf, hfz⟩ := (key W₀ z).1 (hz ▸ ⟨y, rfl⟩)
    let g := (toG f).1 (op W₀)
    let U := openChart B S hS X.1 W₀ ((chartScheme W₀).basicOpen g)
    let ι := openChartInclusion B S hS X.1 W₀ ((chartScheme W₀).basicOpen g)
    refine ⟨U, ?_, toG f, List.mem_map.2 ⟨f, Finset.mem_toList.2 hf, rfl⟩, ?_⟩
    · rw [range_pointsMap_chartToSpace]
      refine ⟨⟨z, hfz⟩, (chartPointsMap_comp (g := ι) (x := ⟨z, hfz⟩)).trans ?_⟩
      rw [toScheme_map_toOver_map_openChartInclusion]
      exact hz
    · rw [show (toG f).1 (op U) = chartRestrict (hF := X.2) ι g from ((toG f).2 ι.op).symm]
      exact isUnit_chartRestrict_openChartInclusion_basicOpen B S hS X.2 W₀ hT₀ g

/-- The open subspace attached to a closed subset `T` of `|X|` by Stacks 03BZ has `Tᶜ` as its set
of points. -/
theorem range_pointsMap_openSubspacesOrderIso_symm (T : Set (points B S hS X.1))
    (hT : IsClosed T) :
    Set.range (pointsMap B S hS _
      ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι) = Tᶜ := by
  rw [← openSubspacesOrderIso_apply B S hS X.1 X.2, OrderIso.apply_symm_apply]

end UnitLocusPresentation

end AlgebraicGeometry.Space

end
