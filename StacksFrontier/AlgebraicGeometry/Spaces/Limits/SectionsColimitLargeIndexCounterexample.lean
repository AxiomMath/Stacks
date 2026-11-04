module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineStageLargeIndexCounterexample
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasicoherentSectionsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf

/-!
# Stacks 07SI fails on the bounded site with no size condition

Stacks 07SI says: in Situation 084R, for a quasi-coherent `ℱ₀` on `X₀`,
`Γ(X, ℱ) = colim_{i ≥ 0} Γ(Xᵢ, ℱᵢ)`. Algebraic spaces here are presheaves on a big fppf site
whose schemes have size below a cutoff `κ`, and `AlgebraicGeometry.Space.LimitSituation` puts no
bound on its index set beyond lying in the universe of the site. **With no size condition the
statement is false**, even granting that the limit is an algebraic space, and this file proves
that it is, over the terminal base, for every big fppf site.

The witness is the system of spectra of the subrings `ℤ[T]` of a field `F` of characteristic two
with `κ ≤ #F`, indexed by the finite subsets `T` of `F`. Every stage is a countable affine scheme
and every transition morphism is affine, the limit is the presheaf of the empty scheme, and for
`ℱ₀ = 𝒪` the sections over the limit are trivial while the colimit of the sections at the stages
is not.

Stacks itself is not refuted: Section 70.2 of the source (Tag 07SD) assumes that the site is large
enough for the constructions of the chapter, and here the ring `colim ℤ[T] = F` has no spectrum in
the site. `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit` and
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_baseChangeSizeBounded` prove the
statement under two size conditions under which that convention holds.

## Main results

* `AlgebraicGeometry.Space.Refute07SI.injective_stageTransition_of_injective_rTensor`: in any
  limit situation, for a quasi-coherent `ℱ₀` and an affine étale chart surjective on points, the
  transition map `Γ(Xᵢ, ℱᵢ) → Γ(Xⱼ, ℱⱼ)` is injective as soon as the restriction of the chart
  rings tensored with `ℱ₀(V₀)` is.
* `AlgebraicGeometry.Space.Refute07SI.limitSituation`: the limit situation of the
  counterexample.
* `AlgebraicGeometry.Space.Refute07SI.not_forall_isSectionsColimit`: **the statement of Stacks
  07SI over `AlgebraicGeometry.Space.LimitSituation`, with the limit an algebraic space and no
  size condition, is false.**

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space.Refute07SI

/-! ### Injectivity of the transition maps, in any limit situation -/

section General

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X)
  {V₀ : BigAffineFppf B S hS}
  {e₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V₀) ⟶ A.system.obj (op A.base)}
  (E : AffineChartSystem B S hS (op A.base) A.system V₀ e₀)
  (he₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk e₀))
  (F₀ : Modules.{u, u} B S hS (A.stage A.base).obj (A.stage A.base).property)

/-- **A transition map is injective when the restriction of chart rings stays injective after
tensoring.**  Let `V₀ ⟶ X₀` be an affine étale chart, surjective on points,
and `ℱ₀` quasi-coherent. If the restriction of chart rings tensored with `ℱ₀(V₀)` is injective,
then so is the transition map `Γ(Xᵢ, ℱᵢ) → Γ(Xⱼ, ℱⱼ)`. -/
theorem injective_stageTransition_of_injective_rTensor (hsurj : IsSurjective B S hS e₀)
    (hF₀ : F₀.IsQuasicoherentOnSite) {i j : A.Stages} (h : i ≤ j)
    (hinj : letI := A.chartStageAlgebra E he₀ i
      letI := A.chartStageAlgebra E he₀ j
      Function.Injective ((A.chartStageRestrictLinear E he₀ h).rTensor
        (F₀.val.obj (op (A.stagesEtaleChart E he₀ A.baseStage))))) :
    Function.Injective (A.stageTransition F₀ i j h) := by
  intro σ σ' hσ
  refine moduleSections_ext_of_isSurjective (A.stageModule F₀ i)
    (A.isSurjective_stagesEtaleChart E he₀ hsurj i) ?_
  have hsec : ∀ τ : A.stageSections F₀ i, ∃ t, _ = moduleSectionValue (A.stageModule F₀ i) τ
      (op (A.stagesEtaleChart E he₀ i)) := fun τ =>
    (A.bijective_stageChartBaseChange E he₀ F₀ hF₀ i).2 _
  obtain ⟨t, ht⟩ := hsec σ
  obtain ⟨t', ht'⟩ := hsec σ'
  refine ht.symm.trans (Eq.trans (congrArg _ (hinj ?_)) ht')
  refine (A.bijective_stageChartBaseChange E he₀ F₀ hF₀ j).1 ?_
  refine (A.chartStageTransition_stageChartBaseChange E he₀ F₀ h t).symm.trans ?_
  refine Eq.trans ?_ (A.chartStageTransition_stageChartBaseChange E he₀ F₀ h t')
  refine (congrArg (A.chartStageTransition E he₀ F₀ h) ht).trans ?_
  refine Eq.trans ?_ (congrArg (A.chartStageTransition E he₀ F₀ h) ht'.symm)
  refine (A.moduleSectionValue_stageTransition E he₀ F₀ h σ).symm.trans ?_
  refine Eq.trans ?_ (A.moduleSectionValue_stageTransition E he₀ F₀ h σ')
  exact congrArg (fun s => moduleSectionValue (A.stageModule F₀ j) s
    (op (A.stagesEtaleChart E he₀ j))) hσ

/-- **The restriction of chart rings out of a field stays injective after tensoring.**  If the
chart rings `𝒪(V₀)` of the chosen stage and `𝒪(Vᵢ)` are fields and `𝒪(Vⱼ)` is a nonzero ring,
the restriction `𝒪(Vᵢ) → 𝒪(Vⱼ)` tensored with `ℱ₀(V₀)` is injective. -/
theorem injective_rTensor_of_isField {i j : A.Stages} (h : i ≤ j)
    (hfield : IsField (chartRing B S hS (A.stage A.base).obj (A.stage A.base).property
      (A.stagesEtaleChart E he₀ A.baseStage)))
    (hfieldi : IsField (chartRing B S hS (A.stage i.1).obj (A.stage i.1).property
      (A.stagesEtaleChart E he₀ i)))
    (hnt : Nontrivial (chartRing B S hS (A.stage j.1).obj (A.stage j.1).property
      (A.stagesEtaleChart E he₀ j))) :
    letI := A.chartStageAlgebra E he₀ i
    letI := A.chartStageAlgebra E he₀ j
    Function.Injective ((A.chartStageRestrictLinear E he₀ h).rTensor
      (F₀.val.obj (op (A.stagesEtaleChart E he₀ A.baseStage)))) := by
  let := A.chartStageAlgebra E he₀ i
  let := A.chartStageAlgebra E he₀ j
  have : Module.Flat (chartRing B S hS (A.stage A.base).obj (A.stage A.base).property
      (A.stagesEtaleChart E he₀ A.baseStage))
      (F₀.val.obj (op (A.stagesEtaleChart E he₀ A.baseStage))) := by
    let : Field (chartRing B S hS (A.stage A.base).obj (A.stage A.base).property
        (A.stagesEtaleChart E he₀ A.baseStage)) := hfield.toField
    exact Module.Flat.of_free
  exact Module.Flat.rTensor_preserves_injective_linearMap _
    (@RingHom.injective _ _ _ (@DivisionRing.isSimpleRing _ hfieldi.toField.toDivisionRing) _ hnt
      (chartDiagramRestrict B S hS (A.transition h) (A.stagesChartDiagram E he₀ h)))

/-- The ring of a chart of a stage is isomorphic to `R` when the chart is the spectrum of `R`. -/
private theorem nonempty_ringEquiv_chartRing_of_iso {j : A.Stages} {R : CommRingCat.{u}}
    (e : (BigFppfOver.toScheme B S hS).obj
      (E.siteDiagram.obj ((LimitSituation.stagesOverEquivalence A).functor.obj (op j))) ≅ Spec R) :
    Nonempty (chartRing B S hS (A.stage j.1).obj (A.stage j.1).property
      (A.stagesEtaleChart E he₀ j) ≃+* R) :=
  ⟨((Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv.symm).trans
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv⟩

/-- **The ring of a chart of a stage is a field** when the chart is the spectrum of a field. -/
theorem isField_chartRing_of_iso {j : A.Stages} {R : CommRingCat.{u}}
    (e : (BigFppfOver.toScheme B S hS).obj
      (E.siteDiagram.obj ((LimitSituation.stagesOverEquivalence A).functor.obj (op j))) ≅ Spec R)
    (hR : IsField R) :
    IsField (chartRing B S hS (A.stage j.1).obj (A.stage j.1).property
      (A.stagesEtaleChart E he₀ j)) :=
  (nonempty_ringEquiv_chartRing_of_iso A E he₀ e).elim fun f => MulEquiv.isField hR f.toMulEquiv

/-- **The ring of a chart of a stage is not the zero ring** when the chart is the spectrum of a
nonzero ring. -/
theorem nontrivial_chartRing_of_iso {j : A.Stages} {R : CommRingCat.{u}}
    (e : (BigFppfOver.toScheme B S hS).obj
      (E.siteDiagram.obj ((LimitSituation.stagesOverEquivalence A).functor.obj (op j))) ≅ Spec R)
    [Nontrivial R] :
    Nontrivial (chartRing B S hS (A.stage j.1).obj (A.stage j.1).property
      (A.stagesEtaleChart E he₀ j)) :=
  (nonempty_ringEquiv_chartRing_of_iso A E he₀ e).elim fun f => f.toEquiv.nontrivial

/-- **The sections at the limit are trivial when the limit has a chart with trivial ring.**  If
an étale chart `U` of the limit is surjective on points and its ring is the zero ring, then every
module on the limit has at most one global section. -/
theorem subsingleton_limitSections (hX : IsAlgebraicSpace B S hS X)
    (U : SmallEtale B S hS (A.limitSpace hX).1) (hU : IsSurjective B S hS U.1.hom)
    (hsub : Subsingleton (chartRing B S hS (A.limitSpace hX).1 (A.limitSpace hX).2 U)) :
    Subsingleton (A.limitSections F₀ hX) := by
  have hM : Subsingleton ((A.limitModule F₀ hX).val.obj (op U)) :=
    Module.subsingleton (chartRing B S hS (A.limitSpace hX).1 (A.limitSpace hX).2 U) _
  exact ⟨fun σ σ' => moduleSections_ext_of_isSurjective (A.limitModule F₀ hX) hU
    (@Subsingleton.elim _ hM _ _)⟩

/-- **The structure sheaf has two distinct global sections at the chosen stage** when the ring of
some chart there is not the zero ring. -/
theorem nontrivial_stageSections_unit (V : SmallEtale B S hS (A.stage A.base).obj)
    (hV : Nontrivial (chartRing B S hS (A.stage A.base).obj (A.stage A.base).property V)) :
    Nontrivial (A.stageSections
      (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) A.baseStage) := by
  let R := structureRingSheaf B S hS (A.stage A.base)
  have : Nontrivial (SheafOfModules.unit R).sections := by
    refine ⟨⟨(SheafOfModules.unit R).unitHomEquiv (𝟙 _),
      (SheafOfModules.unit R).unitHomEquiv 0, fun h => ?_⟩⟩
    have h1 := congrArg (fun s : (SheafOfModules.unit R).sections => s.val (op V)) h
    simp only [SheafOfModules.unitHomEquiv_apply_coe] at h1
    exact one_ne_zero (α := chartRing B S hS (A.stage A.base).obj (A.stage A.base).property V) h1
  exact (LimitSituation.stageSectionsEquivUnit B S hS A A.baseStage).nontrivial

end General

/-! ### The system of the counterexample -/

variable (F : Type u) [Field F] (B : BigFppfSite.{u})

open Refute07SQ in
/-- The spectrum of `ℤ[T]` belongs to the site. -/
theorem contains_spec_stage (T : Finset F) : B.Contains (Spec ((stageFunctor F).obj T)) := by
  show (Spec _).size < B.cutoff
  rw [Scheme.size_Spec]
  exact (max_le le_rfl Cardinal.mk_le_aleph0).trans_lt B.aleph0_lt_cutoff

open Refute07SQ in
/-- The spectrum of `ℤ[T]`, as an object of the big fppf site of the terminal scheme. -/
def specSiteObj (T : Finset F) : BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal :=
  BigFppfOver.mk B _ _ (contains_spec_stage F B T) (terminal.from _)

open Refute07SQ in
/-- The system of the spectra of the rings `ℤ[T]`, in the big fppf site of the terminal
scheme. -/
def specSiteDiagram : (Finset F)ᵒᵖ ⥤ BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal where
  obj T := specSiteObj F B T.unop
  map {_ T'} f := BigFppfOver.homMk B _ _ (contains_spec_stage F B T'.unop) (terminal.from _)
    (((stageFunctor F).op ⋙ Scheme.Spec).map f) (terminal.hom_ext _ _)
  map_id T := BigFppfOver.map_toScheme_injective B _ _
    (((stageFunctor F).op ⋙ Scheme.Spec).map_id T)
  map_comp f g := BigFppfOver.map_toScheme_injective B _ _
    (((stageFunctor F).op ⋙ Scheme.Spec).map_comp f g)

open Refute07SQ in
/-- The cone over the system with the empty scheme as vertex. -/
def emptySpecSiteCone : Cone (specSiteDiagram F B) where
  pt := emptyObj B
  π :=
    { app := fun T => BigFppfOver.homMk B _ _ (contains_spec_stage F B T.unop) (terminal.from _)
        (emptyIsInitial.to _) (terminal.hom_ext _ _)
      naturality := fun _ _ _ => hom_ext_of_isEmpty B
        (inferInstanceAs (IsEmpty (∅ : Scheme.{u}))) _ _ }

open Refute07SQ in
/-- The vertex of a cone over the system in the site is empty, as soon as `κ ≤ #F`. -/
theorem isEmpty_toScheme_specCone_pt (hF : B.cutoff ≤ #F) (s : Cone (specSiteDiagram F B)) :
    IsEmpty ((BigFppfOver.toScheme B _ _).obj s.pt) :=
  isEmpty_of_cone F hF (G := specSiteDiagram F B ⋙ BigFppfOver.toScheme B _ _)
    { app := fun _ => 𝟙 _
      naturality := fun _ _ _ => (Category.comp_id _).trans (Category.id_comp _).symm }
    ((BigFppfOver.toScheme B _ _).mapCone s) s.pt.left.2

open Refute07SQ in
/-- **The limit of the system in the site is the empty scheme**, as soon as `κ ≤ #F`. -/
def isLimitEmptySpecSiteCone (hF : B.cutoff ≤ #F) : IsLimit (emptySpecSiteCone F B) where
  lift s := BigFppfOver.homMk B _ _ (contains_empty B) (terminal.from _)
    (@IsInitial.to _ _ _ (@isInitialOfIsEmpty _ (isEmpty_toScheme_specCone_pt F B hF s)) _)
    (terminal.hom_ext _ _)
  fac s _ := hom_ext_of_isEmpty B (isEmpty_toScheme_specCone_pt F B hF s) _ _
  uniq s _ _ := hom_ext_of_isEmpty B (isEmpty_toScheme_specCone_pt F B hF s) _ _

open Refute07SQ in
/-- **The limit situation of the counterexample.** The stages are the functors of points of the
spectra of the rings `ℤ[T]`, the chosen stage is `ℤ[∅]`, and the limit is the functor of points of
the empty scheme. -/
def limitSituation [DecidableEq F] (hF : B.cutoff ≤ #F) :
    LimitSituation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal
      (yoneda.obj (emptyObj B)) where
  I := Finset F
  system := specSiteDiagram F B ⋙ yoneda
  isAlgebraicSpace _ := isAlgebraicSpace_yoneda B _ _ _
  transition_affine {T T'} _ := isAffineHom_of_presheaf
    ((presheaf_yoneda_map_iff B _ _ (P := @AlgebraicGeometry.IsAffineHom) inferInstance _).2
      (haveI : IsAffine ((BigFppfOver.toScheme B _ _).obj ((specSiteDiagram F B).obj T)) :=
        inferInstanceAs (IsAffine (Spec ((stageFunctor F).obj T.unop)))
      haveI : IsAffine ((BigFppfOver.toScheme B _ _).obj ((specSiteDiagram F B).obj T')) :=
        inferInstanceAs (IsAffine (Spec ((stageFunctor F).obj T'.unop)))
      isAffineHom_of_isAffine _))
  quasiCompact T := isQuasiCompact_yoneda_of_compact B _ _ _
    (inferInstanceAs (CompactSpace (Spec ((stageFunctor F).obj T))))
  quasiSeparated T := isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B _ _ _ _
    ⟨specSiteObj F B T, inferInstanceAs (QuasiSeparatedSpace (Spec ((stageFunctor F).obj T))),
      ⟨Functor.RepresentableBy.yoneda _⟩⟩
  π := (yoneda.mapCone (emptySpecSiteCone F B)).π
  isLimit := isLimitOfPreserves yoneda (isLimitEmptySpecSiteCone F B hF)
  base := ∅

/-- In a field in which two is zero, the subring generated by the empty set is a field. -/
theorem isField_stageFunctor_obj_empty (h2 : (2 : F) = 0) {T : Finset F} (hT : T = ∅) :
    IsField ((Refute07SQ.stageFunctor F).obj T) := by
  subst hT
  have hmem : ∀ x ∈ Subring.closure (↑(∅ : Finset F) : Set F), x = 0 ∨ x = 1 := by
    intro x hx
    rw [Finset.coe_empty, Subring.closure_empty, Subring.mem_bot] at hx
    obtain ⟨n, rfl⟩ := hx
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
    · left
      push_cast
      rw [h2, zero_mul]
    · right
      push_cast
      rw [h2, zero_mul, zero_add]
  refine ⟨exists_pair_ne _, mul_comm, fun {a} ha => ⟨1, ?_⟩⟩
  rcases hmem a.1 a.2 with h | h
  · exact absurd (Subtype.ext h) ha
  · rw [show a = 1 from Subtype.ext h, mul_one]

/-! ### The chart of the chosen stage -/

section Chart

variable [DecidableEq F] (hF : B.cutoff ≤ #F)

/-- The chosen stage `Spec ℤ[∅]`, as an affine object of the site. -/
def baseChart : BigAffineFppf B (⊤_ Scheme.{u}) B.contains_terminal :=
  ⟨specSiteObj F B ∅, inferInstanceAs (IsAffine (Spec ((Refute07SQ.stageFunctor F).obj ∅)))⟩

/-- The identity of the chosen stage, as an affine scheme-valued point of it. -/
abbrev baseChartMap :
    yoneda.obj ((BigAffineFppf.inclusion B _ _).obj (baseChart F B)) ⟶
      (limitSituation F B hF).system.obj (op (limitSituation F B hF).base) :=
  𝟙 (yoneda.obj (specSiteObj F B ∅))

/-- The chart system of the identity of the chosen stage. -/
abbrev chartSys :
    AffineChartSystem B _ _ (op (limitSituation F B hF).base) (limitSituation F B hF).system
      (baseChart F B) (baseChartMap F B hF) :=
  (limitSituation F B hF).chartSystem (baseChart F B) (baseChartMap F B hF)

/-- The identity of the chosen stage is an étale chart. -/
theorem isEtaleChart_baseChartMap :
    IsEtaleChart B _ _ ((limitSituation F B hF).system.obj (op (limitSituation F B hF).base))
      (CostructuredArrow.mk (baseChartMap F B hF)) :=
  presheaf_etale_id B _ _ (specSiteObj F B ∅)

/-- The identity of the chosen stage is surjective on points. -/
theorem isSurjective_baseChartMap : IsSurjective B _ _ (baseChartMap F B hF) :=
  fun x => ⟨x, congrFun (pointsMap_id B _ _ _) x⟩

/-- **Every chart map of the chart system of the identity is an isomorphism.** -/
theorem isIso_stageMap (k : Over (op (limitSituation F B hF).base)) :
    IsIso ((chartSys F B hF).stageMap k) :=
  have : IsIso (baseChartMap F B hF) :=
    inferInstanceAs (IsIso (𝟙 (yoneda.obj (specSiteObj F B ∅))))
  ((chartSys F B hF).isPullback k).isIso_fst_of_isIso

/-- **Every chart of the chart system of the identity is the spectrum of the ring `ℤ[T]` of its
stage.** -/
def chartSchemeIso (k : Over (op (limitSituation F B hF).base)) :
    (BigFppfOver.toScheme B _ _).obj ((chartSys F B hF).siteDiagram.obj k) ≅
      (BigFppfOver.toScheme B _ _).obj ((specSiteDiagram F B).obj k.left) :=
  (BigFppfOver.toScheme B _ _).mapIso (Yoneda.fullyFaithful.preimageIso
    (@asIso _ _ _ _ ((chartSys F B hF).stageMap k) (isIso_stageMap F B hF k) :
      yoneda.obj ((chartSys F B hF).siteDiagram.obj k) ≅
        yoneda.obj ((specSiteDiagram F B).obj k.left)))

/-- **The ring of the chart of the chosen stage is a field**, when two is zero in `F`. -/
theorem isField_chartRing_base (h2 : (2 : F) = 0) :
    IsField (chartRing B _ _ ((limitSituation F B hF).stage (limitSituation F B hF).base).obj
      ((limitSituation F B hF).stage (limitSituation F B hF).base).property
      ((limitSituation F B hF).stagesEtaleChart (chartSys F B hF)
        (isEtaleChart_baseChartMap F B hF) (limitSituation F B hF).baseStage)) :=
  isField_chartRing_of_iso (limitSituation F B hF) (chartSys F B hF)
    (isEtaleChart_baseChartMap F B hF) (j := (limitSituation F B hF).baseStage)
    (chartSchemeIso F B hF _) (isField_stageFunctor_obj_empty F h2 rfl)

/-- **The rings of the charts are not the zero ring.** -/
theorem nontrivial_chartRing (j : (limitSituation F B hF).Stages) :
    Nontrivial (chartRing B _ _ ((limitSituation F B hF).stage j.1).obj
      ((limitSituation F B hF).stage j.1).property
      ((limitSituation F B hF).stagesEtaleChart (chartSys F B hF)
        (isEtaleChart_baseChartMap F B hF) j)) :=
  nontrivial_chartRing_of_iso (limitSituation F B hF) (chartSys F B hF)
    (isEtaleChart_baseChartMap F B hF) (chartSchemeIso F B hF _)

end Chart

/-! ### A field of characteristic two of cardinality at least the cutoff -/

/-- A field in `Type u` of characteristic two and of cardinality at least the cutoff of a big
fppf site: rational functions over `ZMod 2` in a set of variables of that cardinality. -/
abbrev bigFieldTwo : Type u := FractionRing (MvPolynomial B.cutoff.out (ZMod 2))

/-- The field `bigFieldTwo B` has cardinality at least the cutoff. -/
theorem cutoff_le_mk_bigFieldTwo : B.cutoff ≤ #(bigFieldTwo B) := by
  have hinj : Function.Injective (fun i : B.cutoff.out =>
      algebraMap (MvPolynomial B.cutoff.out (ZMod 2)) (bigFieldTwo B) (MvPolynomial.X i)) :=
    (IsFractionRing.injective (MvPolynomial B.cutoff.out (ZMod 2)) (bigFieldTwo B)).comp
      MvPolynomial.X_injective
  simpa [Cardinal.mk_out] using Cardinal.mk_le_of_injective hinj

/-- Two is zero in `bigFieldTwo B`. -/
theorem two_eq_zero_bigFieldTwo : (2 : bigFieldTwo B) = 0 := by
  have h := congrArg (algebraMap (ZMod 2) (bigFieldTwo B)) (show (2 : ZMod 2) = 0 from rfl)
  rwa [map_ofNat, map_zero] at h

/-! ### The refutation -/

section Refutation

attribute [local instance] Classical.propDecidable

/-- The limit situation of the counterexample over the field `bigFieldTwo B`. -/
abbrev limitSituationTwo :
    LimitSituation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal
      (yoneda.obj (Refute07SQ.emptyObj B)) :=
  limitSituation (bigFieldTwo B) B (cutoff_le_mk_bigFieldTwo B)

/-- The structure sheaf of the chosen stage of the counterexample. -/
abbrev unitTwo : Modules.{u, u} B _ _ ((limitSituationTwo B).stage (limitSituationTwo B).base).obj
    ((limitSituationTwo B).stage (limitSituationTwo B).base).property :=
  SheafOfModules.unit (structureRingSheaf B _ _
    ((limitSituationTwo B).stage (limitSituationTwo B).base))

/-- The limit of the counterexample is an algebraic space. -/
theorem isAlgebraicSpace_limitTwo :
    IsAlgebraicSpace B (⊤_ Scheme.{u}) B.contains_terminal (yoneda.obj (Refute07SQ.emptyObj B)) :=
  isAlgebraicSpace_yoneda B _ _ _

/-- The ring of the chart of the chosen stage of the counterexample is a field. -/
theorem isField_chartRing_baseTwo :
    IsField (chartRing B _ _ ((limitSituationTwo B).stage (limitSituationTwo B).base).obj
      ((limitSituationTwo B).stage (limitSituationTwo B).base).property
      ((limitSituationTwo B).stagesEtaleChart (chartSys (bigFieldTwo B) B
        (cutoff_le_mk_bigFieldTwo B))
        (isEtaleChart_baseChartMap (bigFieldTwo B) B (cutoff_le_mk_bigFieldTwo B))
        (limitSituationTwo B).baseStage)) :=
  isField_chartRing_base (bigFieldTwo B) B (cutoff_le_mk_bigFieldTwo B)
    (two_eq_zero_bigFieldTwo B)

/-- The rings of the charts of the counterexample are not the zero ring. -/
theorem nontrivial_chartRingTwo (j : (limitSituationTwo B).Stages) :
    Nontrivial (chartRing B _ _ ((limitSituationTwo B).stage j.1).obj
      ((limitSituationTwo B).stage j.1).property
      ((limitSituationTwo B).stagesEtaleChart (chartSys (bigFieldTwo B) B
        (cutoff_le_mk_bigFieldTwo B))
        (isEtaleChart_baseChartMap (bigFieldTwo B) B (cutoff_le_mk_bigFieldTwo B)) j)) :=
  nontrivial_chartRing (bigFieldTwo B) B (cutoff_le_mk_bigFieldTwo B) j

/-- **The transition maps out of the chosen stage of the counterexample are injective** at
structure-sheaf coefficients. -/
theorem injective_stageTransitionTwo {j : (limitSituationTwo B).Stages}
    (h : (limitSituationTwo B).baseStage ≤ j) :
    Function.Injective ((limitSituationTwo B).stageTransition (unitTwo B)
      (limitSituationTwo B).baseStage j h) :=
  injective_stageTransition_of_injective_rTensor (limitSituationTwo B)
    (chartSys (bigFieldTwo B) B (cutoff_le_mk_bigFieldTwo B))
    (isEtaleChart_baseChartMap (bigFieldTwo B) B (cutoff_le_mk_bigFieldTwo B)) (unitTwo B)
    (isSurjective_baseChartMap (bigFieldTwo B) B (cutoff_le_mk_bigFieldTwo B))
    (SheafOfModules.isQuasicoherentOnSite_unit _) h
    (injective_rTensor_of_isField (limitSituationTwo B)
      (chartSys (bigFieldTwo B) B (cutoff_le_mk_bigFieldTwo B))
      (isEtaleChart_baseChartMap (bigFieldTwo B) B (cutoff_le_mk_bigFieldTwo B)) (unitTwo B) h
      (isField_chartRing_baseTwo B) (isField_chartRing_baseTwo B) (nontrivial_chartRingTwo B j))

/-- **The sections at the limit of the counterexample are trivial.** -/
theorem subsingleton_limitSectionsTwo :
    Subsingleton ((limitSituationTwo B).limitSections (unitTwo B) (isAlgebraicSpace_limitTwo B)) :=
  subsingleton_limitSections (limitSituationTwo B) (unitTwo B) (isAlgebraicSpace_limitTwo B)
    ⟨CostructuredArrow.mk (𝟙 (yoneda.obj (Refute07SQ.emptyObj B))),
      presheaf_etale_id B _ _ (Refute07SQ.emptyObj B)⟩
    (fun x => ⟨x, congrFun (pointsMap_id B _ _ _) x⟩)
    (inferInstanceAs (Subsingleton Γ((∅ : Scheme.{u}), ⊤)))

/-- **The sections at the chosen stage of the counterexample are not trivial.** -/
theorem nontrivial_stageSectionsTwo :
    Nontrivial ((limitSituationTwo B).stageSections (unitTwo B)
      (limitSituationTwo B).baseStage) :=
  nontrivial_stageSections_unit (limitSituationTwo B)
    ((limitSituationTwo B).stagesEtaleChart (chartSys (bigFieldTwo B) B
        (cutoff_le_mk_bigFieldTwo B))
      (isEtaleChart_baseChartMap (bigFieldTwo B) B (cutoff_le_mk_bigFieldTwo B))
      (limitSituationTwo B).baseStage)
    (nontrivial_chartRingTwo B (limitSituationTwo B).baseStage)

end Refutation

/-- **Stacks 07SI over `AlgebraicGeometry.Space.LimitSituation`, with the limit an algebraic space
and no size condition, is false**, for every big fppf site, over the terminal base. The
proposition refuted is the statement of
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit` with its size hypothesis on the index
set removed and the limit given as an algebraic space. -/
theorem not_forall_isSectionsColimit :
    ¬ ∀ {S : Scheme.{u}} {hS : B.Contains S} {hZ : B.Contains (⊤_ Scheme.{u})}
      {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (A : LimitSituation B S hS hZ X)
      (hX : IsAlgebraicSpace B S hS X)
      (F₀ : Modules.{u, u} B S hS (A.stage A.base).obj (A.stage A.base).property),
      F₀.IsQuasicoherentOnSite → A.IsSectionsColimit F₀ hX := by
  intro h
  have hc := h (limitSituationTwo B) (isAlgebraicSpace_limitTwo B) (unitTwo B)
    (SheafOfModules.isQuasicoherentOnSite_unit _)
  have := nontrivial_stageSectionsTwo B
  have := subsingleton_limitSectionsTwo B
  obtain ⟨σ, σ', hne⟩ := exists_pair_ne
    ((limitSituationTwo B).stageSections (unitTwo B) (limitSituationTwo B).baseStage)
  obtain ⟨j, hj, heq⟩ := hc.exists_trans_eq (limitSituationTwo B).baseStage σ σ'
    (Subsingleton.elim _ _)
  exact hne (injective_stageTransitionTwo B hj heq)

end AlgebraicGeometry.Space.Refute07SI

end
