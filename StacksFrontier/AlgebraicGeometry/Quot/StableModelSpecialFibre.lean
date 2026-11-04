module

public import StacksFrontier.AlgebraicGeometry.ContractionComparison.FibreFactorization
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ExceptionalContractionSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelUniqueness
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.RegularNodalModel
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.AcyclicContractionGenus
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeFunctionField
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.StableModelCharacterization
public import StacksFrontier.AlgebraicGeometry.Models.ModelHomUniqueness
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Contraction
public import StacksFrontier.AlgebraicGeometry.Quot.StableFamilySchemeFibre

/-!
# A stable model is dominated by the minimal model, compatibly with special fibres

Let `R` be a discrete valuation ring with fraction field `K` and residue field `κ`, `C` a smooth
projective curve over `K` with `H⁰(C, 𝒪_C) = K` and positive genus, `Y` its minimal model and
`X` a model of `C` which is a stable family of curves. Then there is a morphism of models
`Y ⟶ X` whose special fibre is a stable contraction of the special fibre `Yₛ` of `Y`.

## Main results

* `Stacks.Models.hasAtWorstNodalSingularities_of_isPullback_fiber`: a presentation of a fibre of
  a nodal family is a nodal curve of dimension one.
* `Stacks.Models.nonempty_of_isIso_globalSections`: a scheme with nonzero global functions is
  nonempty.
* `Stacks.Models.exists_isModelHom_isStableContraction_specialFibre`: the morphism of models
  `Y ⟶ X` and its special fibre.

## References

* [Stacks Project, Tag 0E97](https://stacks.math.columbia.edu/tag/0E97)
* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing

universe u

namespace Stacks.Models

/-- For `q` at-worst-nodal of relative dimension one and a cartesian square presenting `V` as the
fibre of `q` over `s`, a nonempty `V` has dimension one and at-worst-nodal singularities over
`κ(s)`. -/
theorem hasAtWorstNodalSingularities_of_isPullback_fiber {X S V : Scheme.{u}} {q : X ⟶ S}
    (hq : IsAtWorstNodalOfRelativeDimensionOne q) (s : S) {j : V ⟶ X}
    {g : V ⟶ Spec (.of (S.residueField s))} (sq : IsPullback j g q (S.fromSpecResidueField s))
    [Nonempty V] :
    topologicalKrullDim V = 1 ∧
      (letI : V.Over (Spec (.of (S.residueField s))) := ⟨g⟩
      Stacks.Curves.HasAtWorstNodalSingularities (S.residueField s) V) := by
  obtain ⟨-, hlfp, hfib⟩ := (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff q).mpr hq
  have : LocallyOfFinitePresentation q := hlfp
  let ι : V ≅ q.fiber s := sq.isoPullback
  have : Nonempty (q.fiber s) := ⟨ι.hom (Classical.arbitrary V)⟩
  obtain ⟨-, hdim, hnod⟩ := hfib s inferInstance
  refine ⟨(Scheme.homeoOfIso ι).isHomeomorph.topologicalKrullDim_eq.trans hdim, ?_⟩
  let f₁ : q.fiber s ⟶ Spec (.of (S.residueField s)) := q.fiberToSpecResidueField s
  have : LocallyOfFiniteType f₁ := Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField q s
  exact Stacks.Curves.hasAtWorstNodalSingularities_of_isIso f₁ g hdim ι.hom (𝟙 _) (by
      rw [Spec.map_id, Category.comp_id]
      exact sq.isoPullback_hom_snd) hnod

/-- A scheme over a nonzero ring whose global functions are that ring is nonempty. -/
theorem nonempty_of_isIso_globalSections {k : CommRingCat.{u}} [Nontrivial k] {V : Scheme.{u}}
    (g : V ⟶ Spec k) [h : IsIso ((Scheme.ΓSpecIso k).inv ≫ g.appTop)] :
    Nonempty V := by
  by_contra hV
  have : IsEmpty V := not_nonempty_iff.mp hV
  have htop : (⊤ : V.Opens) = ⊥ := by
    ext x
    exact isEmptyElim x
  have hsub : Subsingleton Γ(V, ⊤) :=
    CommRingCat.subsingleton_of_isTerminal (V.sheaf.isTerminalOfEqEmpty htop)
  exact zero_ne_one ((ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso k).inv ≫ g.appTop)).1
    (Subsingleton.elim (α := Γ(V, ⊤)) _ _))

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

attribute [local instance] genericFiberSpec_isOpenImmersion

open Stacks.Curves.StableModel in
/-- Let `C` be a smooth projective curve over `K` with `H⁰(C, 𝒪_C) = K` and positive genus, `Y`
a minimal model and `X` a model of `C` which is a stable family of curves. There is a morphism of
models `a : Y ⟶ X` with `𝒪_X = a_*𝒪_Y`; for a presentation `V` of the special fibre of `X`, the
induced `aₛ : Yₛ ⟶ V` is a stable contraction of the special fibre `Yₛ` of `Y`
([Stacks, Tag 0E7Q]); `Yₛ` is a proper curve of dimension one over `κ` with `H⁰ = κ` and genus
at least two; and `Y` is at-worst-nodal of relative dimension one ([Stacks, Tag 0CDG]). -/
theorem exists_isModelHom_isStableContraction_specialFibre (B : BigFppfSite.{u})
    (hZ : B.Contains integerBase) (hR : B.Contains (Spec (.of R))) {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] (hproj : Stacks.HProjective.IsHProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (hg : 0 < genus c)
    {Y : Scheme.{u}} {q : Y ⟶ Spec (.of R)} {eY : C ≅ pullback q (genericPointInclusion R K)}
    (hY : IsMinimalModel c q eY)
    {X : Scheme.{u}} {p : X ⟶ Spec (.of R)} {e : C ≅ pullback p (genericPointInclusion R K)}
    (hX : IsModel c p e) (hst : IsStableFamilyOfSchemes B hZ p hR) :
    ∃ a : Y ⟶ X, IsModelHom q p eY e a ∧
      IsIso (SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom) ∧
      ∃ (V : Scheme.{u}) (jX : V ⟶ X)
        (gX : V ⟶ Spec (.of ((Spec (.of R)).residueField (closedPoint R)))),
        IsPullback jX gX p ((Spec (.of R)).fromSpecResidueField (closedPoint R)) ∧
        ∃ as : q.fiber (closedPoint R) ⟶ V, as ≫ jX = q.fiberι (closedPoint R) ≫ a ∧
          IsStableContraction (q.fiberToSpecResidueField (closedPoint R) :
            q.fiber (closedPoint R) ⟶ Spec (.of ((Spec (.of R)).residueField (closedPoint R))))
            gX as ∧
          topologicalKrullDim (q.fiber (closedPoint R)) = 1 ∧
          IsIso ((Scheme.ΓSpecIso (.of ((Spec (.of R)).residueField (closedPoint R)))).inv ≫
            (q.fiberToSpecResidueField (closedPoint R) : q.fiber (closedPoint R) ⟶
              Spec (.of ((Spec (.of R)).residueField (closedPoint R)))).appTop) ∧
          2 ≤ genus (q.fiberToSpecResidueField (closedPoint R) : q.fiber (closedPoint R) ⟶
              Spec (.of ((Spec (.of R)).residueField (closedPoint R)))) ∧
          IsAtWorstNodalOfRelativeDimensionOne q := by
  set s₀ : Spec (.of R) := closedPoint R
  have hnod : IsAtWorstNodalOfRelativeDimensionOne p :=
    hst.isAtWorstNodalOfRelativeDimensionOne fun _ hF => hF.1
  have : IsProper p := hst.isProper
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : Flat p := hX.1
  have hreg : ∀ y : X, p.base y ≠ closedPoint R → IsRegularLocalRing (X.presheaf.stalk y) :=
    fun y hy => isRegularLocalRing_stalk_of_isModel c p e y
      (mem_range_genericPointInclusion_of_ne_closedPoint hy)
  have hgen : ∀ y : X, ¬ IsRegularLocalRing (X.presheaf.stalk y) → p.base y = closedPoint R :=
    fun y => not_imp_comm.1 (hreg y)
  obtain ⟨V, jX, gX, hVsq, hstabV, hH0V⟩ := hst.exists_isPullback_fiber s₀
  obtain ⟨W, h, hchain, hregW⟩ :=
    Stacks.SemistableReduction.exists_nodalBlowupChain_isRegular_of_isRegularLocalRing p hnod hreg
  obtain ⟨-, hOh, hsW⟩ := Stacks.SemistableReduction.NodalBlowupChain.specialFibre hnod hgen
    hVsq hchain
  have hnodW := hchain.isAtWorstNodalOfRelativeDimensionOne hnod
  have : IsProper h := hchain.isProper
  have : Flat (h ≫ p) := flat hnodW.1.1
  have hres : IsIso (h ∣_ (p ⁻¹ᵁ (genericPointInclusion R K).opensRange)) :=
    hchain.isIso_morphismRestrict _ fun y hy => isRegularLocalRing_stalk_of_isModel c p e y hy
  have := isIso_genericFiberMapOfHomOver_of_isIso_morphismRestrict (K := K) (h ≫ p) p h rfl hres
  obtain ⟨eW, hW, hcW⟩ := exists_isModel_isModelHom_of_isIso_source hX h
  obtain ⟨Y₁, q₁, e₁, d, hseq, hmin₁⟩ := exists_exceptionalContractionSequence_isMinimalModel c
    hproj inferInstance (h ≫ p) eW hW hregW
  have hdq : d ≫ q₁ = h ≫ p := comp_eq_of_exceptionalContractionSequence hseq
  have := hseq.isIso_genericFiberMapOfHomOver (K := K) hnodW
  have : Flat q₁ := hmin₁.isModel.1
  have : LocallyOfFiniteType q₁ := hmin₁.isModel.2.1
  have : QuasiCompact q₁ := hmin₁.isModel.2.2.1
  obtain ⟨e₁', hmod₁', hd⟩ := exists_isModel_isModelHom_of_isIso_target hW d hdq
  have hmin₁' : IsMinimalModel c q₁ e₁' :=
    ⟨hmin₁.curveProjective, hmin₁.isIso_globalSections, hmod₁', hmin₁.isProper, hmin₁.regular,
      hmin₁.not_hasExceptionalCurveOfFirstKind⟩
  obtain ⟨φ, ⟨hφq, hφc⟩, -⟩ := existsUnique_iso_of_isMinimalModel c hg q₁ q e₁' eY hmin₁' hY
  have hφ : IsModelHom q₁ q e₁' eY φ.hom := by
    refine ⟨hφq, ?_⟩
    rw [← cancel_mono (pullback.fst q (genericPointInclusion R K)), Category.assoc,
      show genericFiberMapOfHomOver (K := K) q₁ q φ.hom hφq ≫
        pullback.fst q (genericPointInclusion R K) =
          pullback.fst q₁ (genericPointInclusion R K) ≫ φ.hom from pullback.lift_fst _ _ _]
    exact hφc
  have hd' : IsModelHom (h ≫ p) q eW eY (d ≫ φ.hom) := hd.comp hφ
  have hnodY₁ := hseq.isAtWorstNodalOfRelativeDimensionOne hnodW
  have hnodY : IsAtWorstNodalOfRelativeDimensionOne q := by
    rw [show q = φ.inv ≫ q₁ by rw [← hφq, Iso.inv_hom_id_assoc]]
    have : MorphismProperty.RespectsIso
        (@IsAtWorstNodalOfRelativeDimensionOne.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@IsAtWorstNodalOfRelativeDimensionOne.{u}) φ.inv q₁).mpr hnodY₁
  obtain ⟨hg2V, htailV, hpropV, hbridgeV⟩ := hstabV
  have : IsProper gX := hpropV
  have : Nontrivial ↑(CommRingCat.of ↑((Spec (.of R)).residueField s₀)) :=
    inferInstanceAs (Nontrivial ↑((Spec (.of R)).residueField s₀))
  have : Nonempty V := nonempty_of_isIso_globalSections gX
  obtain ⟨hdimV, hnodV⟩ := hasAtWorstNodalSingularities_of_isPullback_fiber hnod _ hVsq
  have hidV : IsStableContraction gX gX (𝟙 V) :=
    (IsIteratedContractionOfRationalBridges.identity
      (k := (Spec (.of R)).residueField s₀) V gX).isStableContraction hdimV hnodV
      htailV hg2V (fun C _ => hbridgeV C)
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace gX
  have sqW := IsPullback.of_hasPullback h jX
  obtain ⟨hOc, hRc⟩ := hsW sqW
  let cs := pullback.snd h jX
  have sqWfib : IsPullback (pullback.fst h jX) (cs ≫ gX) (h ≫ p)
      ((Spec (.of R)).fromSpecResidueField s₀) := sqW.paste_vert hVsq
  have : IsProper cs := MorphismProperty.of_isPullback sqW inferInstance
  have hcs : IsStableContraction (k := (Spec (.of R)).residueField s₀) (cs ≫ gX) gX
      (cs ≫ 𝟙 V) :=
    IsStableContraction.comp cs (𝟙 V) rfl hOc hRc hidV
  let ft : pullback q ((Spec (.of R)).fromSpecResidueField s₀) ⟶
      Spec (.of ((Spec (.of R)).residueField s₀)) := pullback.snd _ _
  have sqY : IsPullback (q.fiberι s₀) ft q ((Spec (.of R)).fromSpecResidueField s₀) :=
    IsPullback.of_hasPullback _ _
  let d' := d ≫ φ.hom
  obtain ⟨ds, hds₁, hds₂⟩ :
      ∃ ds : pullback h jX ⟶ pullback q ((Spec (.of R)).fromSpecResidueField s₀),
      ds ≫ q.fiberι s₀ = pullback.fst h jX ≫ d' ∧ ds ≫ ft = cs ≫ gX :=
    ⟨sqY.lift (pullback.fst h jX ≫ d') (cs ≫ gX) (by
      rw [Category.assoc, hd'.1]
      exact sqWfib.w), sqY.lift_fst _ _ _, sqY.lift_snd _ _ _⟩
  have sqY₁ : IsPullback (q.fiberι s₀ ≫ φ.inv)
      ft q₁ ((Spec (.of R)).fromSpecResidueField s₀) :=
    IsPullback.of_iso sqY (Iso.refl _) φ.symm (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom])
      (by simp only [Iso.refl_hom]; exact (Category.comp_id ft).trans (Category.id_comp ft).symm)
      (by simp [← hφq]) (by simp)
  obtain ⟨hOd, hRd⟩ := (hseq.specialFibre hnodW).2 sqWfib sqY₁ (gs := ds)
    (by
      have := congrArg (fun t => t ≫ φ.inv) hds₁
      simp only [d', Category.assoc, Iso.hom_inv_id, Category.comp_id] at this
      exact (Category.assoc _ _ _).symm.trans this) hds₂
  have : IsProper q := hY.isProper
  have : IsProper ft := MorphismProperty.of_isPullback sqY inferInstance
  have : IsIso ((Scheme.ΓSpecIso (.of ((Spec (.of R)).residueField s₀))).inv ≫
      (cs ≫ gX).appTop) :=
    Stacks.Curves.isIso_globalSections_comp_of_isIso_unitToPushforwardObjUnit
      (k := (Spec (.of R)).residueField s₀) cs gX hOc
  have hH0Ys : IsIso ((Scheme.ΓSpecIso (.of ((Spec (.of R)).residueField s₀))).inv ≫
      ft.appTop) :=
    Stacks.Curves.isIso_globalSections_of_isIso_unitToPushforwardObjUnit
      (k := (Spec (.of R)).residueField s₀) ds hds₂ hOd
  have : Nonempty (pullback h jX : Scheme.{u}) := nonempty_of_isIso_globalSections (cs ≫ gX)
  have : Nonempty (pullback q ((Spec (.of R)).fromSpecResidueField s₀) : Scheme.{u}) :=
    nonempty_of_isIso_globalSections ft
  have : Nonempty (q.fiber s₀) :=
    (inferInstance : Nonempty (pullback q ((Spec (.of R)).fromSpecResidueField s₀) : Scheme.{u}))
  obtain ⟨hdimWs, hnodWs⟩ := hasAtWorstNodalSingularities_of_isPullback_fiber hnodW s₀ sqWfib
  obtain ⟨hdimYs, hnodYs⟩ := hasAtWorstNodalSingularities_of_isPullback_fiber hnodY s₀ sqY
  have hgW : genus gX = genus (cs ≫ gX) :=
    Stacks.Curves.genus_eq_of_isIso_unitToPushforwardObjUnit
      (k := (Spec (.of R)).residueField s₀) cs rfl hOc hRc
  have hgY : genus ft = genus (cs ≫ gX) :=
    Stacks.Curves.genus_eq_of_isIso_unitToPushforwardObjUnit
      (k := (Spec (.of R)).residueField s₀) ds hds₂ hOd hRd
  have hg2Y : 2 ≤ genus ft := by rwa [hgY, ← hgW]
  have hg2W : 2 ≤ genus (cs ≫ gX) := by rwa [← hgW]
  obtain ⟨Z, gZ, z, hz⟩ := exists_isStableContraction (k := (Spec (.of R)).residueField s₀) ft
    hdimYs hg2Y hnodYs
  have : IsProper (ds ≫ ft) := by rw [hds₂]; infer_instance
  have : IsProper ds := IsProper.of_comp ds ft
  have : CompactSpace (pullback q ((Spec (.of R)).fromSpecResidueField s₀) : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace ft
  have hdz : IsStableContraction (k := (Spec (.of R)).residueField s₀) (cs ≫ gX) gZ (ds ≫ z) :=
    IsStableContraction.comp ds z hds₂ hOd hRd hz
  obtain ⟨ε, hε, -⟩ := existsUnique_iso_of_isStableContraction
    (k := (Spec (.of R)).residueField s₀) (cs ≫ gX) hdimWs hg2W hnodWs hdz hcs
  have has : ds ≫ (z ≫ ε.hom) = cs := by
    rw [← Category.assoc, hε, Category.comp_id]
  have hasst : IsStableContraction (k := (Spec (.of R)).residueField s₀) ft gX (z ≫ ε.hom) :=
    IsStableContraction.of_comp ds (z ≫ ε.hom) hds₂ hOd hRd (by rw [has]; simpa using hcs)
  have hOd' : IsIso (SheafOfModules.unitToPushforwardObjUnit d'.toRingCatSheafHom) :=
    Stacks.SemistableReduction.isIso_unitToPushforwardObjUnit_comp_of_acyclic d φ.hom
      (hseq.specialFibre hnodW).1
      (Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_unitToPushforwardObjUnit_of_isIso _)
  have : IsProper (d' ≫ q) := by rw [hd'.1]; infer_instance
  have : IsProper d' := IsProper.of_comp d' q
  have : Surjective d' := d'.surjective_of_isIso_app fun U =>
    Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit d' hOd' U
  have : IsReduced Y := isReduced_of_isRegular hY.regular
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  have : IsIso (genericFiberMapOfHomOver (K := K) (h ≫ p) q d' hd'.1) := by
    rw [show genericFiberMapOfHomOver (K := K) (h ≫ p) q d' hd'.1 = eW.inv ≫ eY.hom by
      rw [← hd'.2, Iso.inv_hom_id_assoc]]
    infer_instance
  have hrj : Set.range jX = p ⁻¹' {s₀} := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      change p (jX v) = s₀
      rw [← Scheme.Hom.comp_apply, hVsq.w, Scheme.Hom.comp_apply,
        Scheme.fromSpecResidueField_apply]
    · intro hx
      obtain ⟨t⟩ : Nonempty (Spec ((Spec (.of R)).residueField s₀)) := inferInstance
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p)
        (g := (Spec (.of R)).fromSpecResidueField s₀) x t
        (by rw [Scheme.fromSpecResidueField_apply]; exact hx)
      exact ⟨hVsq.isoPullback.inv z, by
        rw [← Scheme.Hom.comp_apply, hVsq.isoPullback_inv_fst, hz]⟩
  have hpw : ∀ w : W, p (h w) = q (d' w) := fun w => by
    have := congrArg (fun f : W ⟶ Spec (.of R) => f w) hd'.1
    simpa only [Scheme.Hom.comp_apply, d'] using this.symm
  have hfib : ∀ y : Y, ∃ x : X, ∀ w : W, d' w = y → h w = x := by
    intro y
    by_cases hy : q y = s₀
    · obtain ⟨ys, rfl⟩ : y ∈ Set.range (q.fiberι s₀) := by
        rw [Scheme.Hom.range_fiberι]
        exact hy
      refine ⟨jX ((z ≫ ε.hom) ys), fun w hw => ?_⟩
      have hw0 : w ∈ Set.range (pullback.fst h jX) := by
        rw [Scheme.Pullback.range_fst, hrj]
        change p (h w) = s₀
        rw [hpw, hw]
        exact hy
      obtain ⟨ws, rfl⟩ := hw0
      have hdws : ds ws = ys := by
        apply (q.fiberι s₀).isEmbedding.injective
        have := congrArg (fun f => f ws) hds₁
        simp only [Scheme.Hom.comp_apply] at this
        exact this.trans hw
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← hdws]
      have := congrArg (fun f => f ws) has
      simp only [Scheme.Hom.comp_apply] at this
      exact congrArg jX this.symm
    · obtain ⟨w₀, rfl⟩ := d'.surjective y
      refine ⟨h w₀, fun w hw => ?_⟩
      have hx : (h ≫ p) w₀ ≠ s₀ := by
        rw [Scheme.Hom.comp_apply, hpw]
        exact hy
      rw [eq_of_isIso_genericFiberMapOfHomOver (K := K) hd'.1 hx hw.symm]
  obtain ⟨a, ha⟩ := Stacks.ContractionComparison.exists_comp_eq_of_forall_fiber d' h hOd' hfib
  have : IsDominant d' := ⟨d'.surjective.denseRange⟩
  have hap : a ≫ p = q := ext_of_isDominant d' (by rw [← Category.assoc, ha, hd'.1])
  have haM : IsModelHom q p eY e a := IsModelHom.of_comp_eq hd' hcW hap ha
  have hOa : IsIso (SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom) :=
    Stacks.Curves.StableModel.isIso_unitToPushforwardObjUnit_of_comp d' a hOd'
      (by rw [ha]; exact hOh)
  refine ⟨a, haM, hOa, V, jX, gX, hVsq, z ≫ ε.hom, ?_, hasst, hdimYs, hH0Ys, hg2Y, hnodY⟩
  have : IsReduced (pullback q ((Spec (.of R)).fromSpecResidueField s₀) : Scheme.{u}) :=
    Stacks.SemistableReduction.isReduced_fiber_of_isAtWorstNodal q hnodY s₀
  have : Surjective ds := ds.surjective_of_isIso_app fun U =>
    Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit ds hOd U
  have : IsDominant ds := ⟨ds.surjective.denseRange⟩
  change (z ≫ ε.hom) ≫ jX = (pullback.fst q ((Spec (.of R)).fromSpecResidueField s₀) :
    pullback q ((Spec (.of R)).fromSpecResidueField s₀) ⟶ Y) ≫ a
  refine ext_of_isDominant ds ?_
  rw [← Category.assoc, has, ← pullback.condition]
  exact (show (ds ≫ q.fiberι s₀) ≫ a = pullback.fst h jX ≫ h by
    rw [hds₁, Category.assoc, ha]).symm

end Stacks.Models

end
