module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.AffineGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietoris
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupportEtaleLocalHigher
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsSubsheaf

/-!
# The intersection of an elementary distinguished square as a unit locus

Let `(U ⊆ W, f : V ⟶ W)` be an elementary distinguished square of algebraic spaces with `V`
affine, `U` quasi-compact and `W` quasi-separated, and let `P = U ×_W V`, an open subspace of `V`.
There are finitely many global functions `a₁, …, a_r` on `V` such that an étale chart of `V` lies
over `P` as soon as one of the `aᵢ` is a unit on it, and every étale chart of `P` is covered by
charts on which one of the `aᵢ` is a unit: `P` is the union of the loci `D(aᵢ)`.

The preimage of `U` in `V` is an open subspace whose inclusion is quasi-compact, so on the
terminal affine chart of `V` its complement is the zero locus of a finitely generated ideal
(Stacks 0859, part (1)); the `aᵢ` are generators of that ideal.

## Main results

* `AlgebraicGeometry.Space.exists_list_globalRing_unitLocus`: the list of global functions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_UnitLocus :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_UnitLocus
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_UnitLocus B S hS).has_limit _

/-- The ring of global functions on an algebraic space: compatible families of sections of the
structure sheaf of its small étale site. -/
local notation "globalRing" hX:max =>
  Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (AlgebraicGeometry.RingedSite.O (smallEtaleRingedSite _ _ _ _ hX)))

/-- The global function on an algebraic space with a terminal étale chart `T` attached to a
regular function on `T`: its value on a chart is the restriction along the unique chart morphism
to `T`. -/
def globalRingOfTerminal {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {T : SmallEtale B S hS F} (hT : IsTerminal T) (x : chartRing B S hS F hF T) :
    globalRing hF :=
  ⟨fun j => chartRestrict (hF := hF) (hT.from (j.unop : SmallEtale B S hS F)) x,
    fun {j j'} g => by
    have h : (g.unop : (j'.unop : SmallEtale B S hS F) ⟶ j.unop) ≫
        hT.from (j.unop : SmallEtale B S hS F) = hT.from (j'.unop : SmallEtale B S hS F) :=
      hT.hom_ext _ _
    change chartRestrict (hF := hF) (g.unop : (j'.unop : SmallEtale B S hS F) ⟶ j.unop)
      (chartRestrict (hF := hF) (hT.from (j.unop : SmallEtale B S hS F)) x) =
      chartRestrict (hF := hF) (hT.from (j'.unop : SmallEtale B S hS F)) x
    rw [← h]
    exact (RingHom.congr_fun (chartRestrict_comp (hF := hF)
      (hT.from (j.unop : SmallEtale B S hS F))
      (g.unop : (j'.unop : SmallEtale B S hS F) ⟶ j.unop)) x).symm⟩

/-- The value of `globalRingOfTerminal` on a chart is the restriction along the morphism to the
terminal chart. -/
theorem globalRingOfTerminal_apply {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {T : SmallEtale B S hS F} (hT : IsTerminal T)
    (x : chartRing B S hS F hF T) (U : SmallEtale B S hS F) :
    (globalRingOfTerminal B S hS hF hT x).1 (op U) = chartRestrict (hF := hF) (hT.from U) x :=
  rfl

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The sieve on an étale chart `U'` of the intersection `U ×_W V` of an elementary distinguished
square of the charts over `U'` on which one of the global functions of a list on `V` is a unit. -/
def unitLocusSieve (l : List (globalRing hsq.isAlgebraicSpace))
    (U' : SmallEtale B S hS (edsInter B S hS hsq).1) : Sieve U' where
  arrows Y _ := ∃ a ∈ l, IsUnit (a.1 (op ((smallEtalePostcomp B S hS (edsSnd B S hS hsq)
    (isEtale_edsSnd B S hS hsq)).obj Y)))
  downward_closed := by
    rintro Y Z - ⟨a, ha, hu⟩ g
    refine ⟨a, ha, ?_⟩
    have h := a.2 ((smallEtalePostcomp B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)).map
      g).op
    exact h ▸ hu.map (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V
      hsq.isAlgebraicSpace).O)).obj.map ((smallEtalePostcomp B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq)).map g).op).hom

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The intersection of an elementary distinguished square is a finite union of unit loci of
global functions on the affine member.** Let `(U ⊆ W, f : V ⟶ W)` be an elementary distinguished
square with `V` affine, `U` quasi-compact and `W` quasi-separated, and `P = U ×_W V`. There is a
finite list of global functions on `V` such that
(a) an étale chart of `V` on which one of them is a unit lies over `P`, and
(b) every étale chart of `P` is covered by the charts over it on which one of them is a unit. -/
theorem exists_list_globalRing_unitLocus (hV : IsAffineSpace B S hS V)
    (hU : IsQuasiCompactSpace B S hS Uo.toFunctor)
    (hW : IsAbsolutelyQuasiSeparated B S hS hZ W.1) :
    ∃ l : List (globalRing hsq.isAlgebraicSpace),
      (∀ U : SmallEtale B S hS V, (∃ a ∈ l, IsUnit (a.1 (op U))) →
        ∃ U' : SmallEtale B S hS (edsInter B S hS hsq).1,
          Nonempty ((smallEtalePostcomp B S hS (edsSnd B S hS hsq)
            (isEtale_edsSnd B S hS hsq)).obj U' ≅ U)) ∧
      ∀ U' : SmallEtale B S hS (edsInter B S hS hsq).1,
        unitLocusSieve B S hS hsq l U' ∈
          SmallEtale.topology B S hS (edsInter B S hS hsq).1 U' := by
  classical
  have hValg := hsq.isAlgebraicSpace
  let O := Uo.preimage fV
  have hO : IsOpenSubspace B S hS O :=
    isOpenSubspace_preimage B S hS fV Uo W.2 hValg hsq.isOpenSubspace
  have hOqc : IsQuasiCompact B S hS O.ι :=
    isQuasiCompact_of_isPullback B S hS (Subfunctor.isPullback_preimage fV Uo)
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ W.2 hW hU Uo.ι)
  let T := (Set.range (pointsMap B S hS O.toFunctor O.ι))ᶜ
  have hT : IsClosed T :=
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS O.ι hO.2).isClosed_compl
  obtain ⟨T₀, hT₀, ⟨i⟩⟩ := hV
  let W₀ := chartOfIso B S hS T₀ i
  have hW₀ : IsTerminal W₀ := isTerminalChartOfIso T₀ i
  obtain ⟨I, ⟨gens, hgens⟩, hI⟩ := exists_fg_ideal_zeroLocus_eq_preimage_chartPointsMap hValg hT
    hO (compl_compl _).symm hOqc W₀ hT₀
  let toG := globalRingOfTerminal B S hS hValg hW₀
  let l := gens.toList.map toG
  have key : ∀ (U : SmallEtale B S hS V) (x : chartScheme U),
      chartPointsMap U x ∈ Set.range (pointsMap B S hS O.toFunctor O.ι) ↔
        ∃ f ∈ gens, x ∈ (chartScheme U).basicOpen ((toG f).1 (op U)) := by
    intro U x
    rw [chartPointsMap_comp (g := hW₀.from U) (x := x), ← Set.notMem_compl_iff]
    show ¬ (_ ∈ chartPointsMap W₀ ⁻¹' T) ↔ _
    rw [hI, ← hgens, Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
    push Not
    refine exists_congr fun f => and_congr Iff.rfl ?_
    show _ ↔ x ∈ (chartScheme U).basicOpen (((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS V).map (hW₀.from U))).appTop f)
    exact SetLike.ext_iff.1 (Scheme.preimage_basicOpen _ f) x
  refine ⟨l, ?_, fun U' => ?_⟩
  · rintro U ⟨a, ha, hu⟩
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 ha
    have hbo := (chartScheme U).basicOpen_of_isUnit hu
    have hpts : ∀ x, chartPointsMap U x ∈ Set.range (pointsMap B S hS O.toFunctor O.ι) :=
      fun x => (key U x).2 ⟨f, Finset.mem_toList.1 hf, by rw [hbo]; trivial⟩
    obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points B S hS hValg
      (isAlgebraicSpace_yoneda B S hS _) O hO U.1.hom).2 (by
        rintro _ ⟨y, rfl⟩
        have := hpts (schemePointsHomeomorph B S hS _ y)
        simpa [chartPointsMap] using this)
    let ψ : yoneda.obj U.1.left ⟶ (edsInter B S hS hsq).1 :=
      pullback.lift (f := (edsOpenHom B S hS hsq).hom) (g := (edsEtaleHom B S hS hsq).hom)
        (g ≫ Uo.fromPreimage fV) U.1.hom (by
          show (g ≫ Uo.fromPreimage fV) ≫ Uo.ι = U.1.hom ≫ fV
          rw [Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc, hg])
    have hψ : ψ ≫ (edsSnd B S hS hsq).hom = U.1.hom := pullback.lift_snd _ _ _
    let U' : SmallEtale B S hS (edsInter B S hS hsq).1 :=
      ⟨CostructuredArrow.mk ψ, isEtaleChart_of_comp_etale B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq) ψ (by rw [hψ]; exact U.2)⟩
    exact ⟨U', ⟨ObjectProperty.isoMk _ (CostructuredArrow.isoMk (Iso.refl _) (by
      show 𝟙 _ ≫ U.1.hom = ψ ≫ (edsSnd B S hS hsq).hom
      rw [hψ, Category.id_comp]))⟩⟩
  · let U := (smallEtalePostcomp B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)).obj U'
    let r : (edsInter B S hS hsq).1 ⟶ O.toFunctor :=
      (Subfunctor.isPullback_preimage fV Uo).lift (pullback.fst _ _) (pullback.snd _ _)
        pullback.condition
    have hr : r ≫ O.ι = pullback.snd _ _ := IsPullback.lift_snd _ _ _ _
    have hfac : (U'.1.hom ≫ r) ≫ O.ι = U.1.hom := by
      rw [Category.assoc, hr]
      rfl
    have hrange := (factorsThrough_openSubspace_iff_points B S hS hValg
      (isAlgebraicSpace_yoneda B S hS _) O hO U.1.hom).1 ⟨U'.1.hom ≫ r, hfac⟩
    let Ω : gens → (chartScheme U').Opens := fun f =>
      (chartScheme U').basicOpen ((toG f.1).1 (op U))
    have hΩ : ⨆ f, Ω f = ⊤ := by
      refine top_unique fun x _ => ?_
      obtain ⟨f, hf, hx⟩ := (key U x).1 (hrange ⟨_, rfl⟩)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hx⟩
    refine GrothendieckTopology.superset_covering _ ?_
      (ofArrows_openChartInclusion_mem_topology B S hS _ U' Ω hΩ)
    rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro f
    refine ⟨toG f.1, List.mem_map.2 ⟨f.1, Finset.mem_toList.2 f.2, rfl⟩, ?_⟩
    have hfrom : hW₀.from ((smallEtalePostcomp B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq)).obj (openChart B S hS _ U' (Ω f))) =
        (smallEtalePostcomp B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)).map
          (openChartInclusion B S hS _ U' (Ω f)) ≫ hW₀.from U := hW₀.hom_ext _ _
    show IsUnit (chartRestrict (hF := hValg) (hW₀.from ((smallEtalePostcomp B S hS
      (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)).obj (openChart B S hS _ U' (Ω f)))) f.1)
    have hc : chartRestrict (hF := hValg) ((smallEtalePostcomp B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq)).map (openChartInclusion B S hS _ U' (Ω f)) ≫ hW₀.from U)
          f.1 = chartRestrict (hF := hValg) ((smallEtalePostcomp B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq)).map (openChartInclusion B S hS _ U' (Ω f)))
          (chartRestrict (hF := hValg) (hW₀.from U) f.1) :=
      RingHom.congr_fun (chartRestrict_comp (hF := hValg) _ _) _
    rw [hfrom]
    refine (congrArg IsUnit hc).mpr ?_
    refine Scheme.isUnit_of_basicOpen_eq_top (X := (Ω f).toScheme)
      (((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map
        (openChartInclusion B S hS _ U' (Ω f)))).appTop (chartRestrict (hF := hValg)
          (hW₀.from U) f.1)) ?_
    have hι := toScheme_map_toOver_map_openChartInclusion B S hS _ U' (Ω f)
    show (Ω f).toScheme.basicOpen (((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS _).map (openChartInclusion B S hS _ U' (Ω f)))).appTop _) = ⊤
    rw [hι]
    exact basicOpen_appTop_ι_basicOpen _ _

end Square

end AlgebraicGeometry.Space

end
