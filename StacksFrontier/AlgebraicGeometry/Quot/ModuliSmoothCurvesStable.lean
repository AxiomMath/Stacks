module

public import StacksFrontier.AlgebraicGeometry.F6Rank136.SmoothIsNodal
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverFieldScheme
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesDense
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleChartGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.GeometricallyRegularNormal

/-!
# `Curves^{smooth} ∩ 𝓜̄_g = 𝓜_g` for `g ≥ 2` (towards Stacks 0E87)

The proof of Stacks 0E87 uses that a family of curves `f : X → S` is smooth and stable of genus
`g` exactly when it is smooth of relative dimension one with `f_*𝒪_X = 𝒪_S` universally and of
genus `g`, for `g ≥ 2`. This file proves the two halves.

* A stable family is at-worst-nodal of relative dimension one, so it has relative dimension one;
  hence a smooth stable family of genus `g` is smooth of relative dimension one, with
  `f_*𝒪_X = 𝒪_S` universally and of genus `g`. This half holds for every `g`.
* Conversely, a smooth morphism of relative dimension one is at-worst-nodal of relative
  dimension one (Stacks 0CD7, chartwise), so a family of curves which is smooth of relative
  dimension one with `f_*𝒪_X = 𝒪_S` universally is prestable. Its fibre over a field-valued point
  is a scheme (Stacks 0ADD), smooth and proper over the field with `H⁰(X_p, 𝒪) = k`, hence
  geometrically irreducible (Stacks 0FD3) and so irreducible: it has neither a rational tail nor a
  rational bridge, both of which are irreducible components with nonempty complement. Its genus is
  `g` by Stacks 0E6V, which is taken as an input here.

## Main results

* `AlgebraicGeometry.Space.hasRelativeDimension_one_of_isAtWorstNodalOfRelativeDimensionOne`:
  an at-worst-nodal morphism of relative dimension one of algebraic spaces has relative
  dimension one.
* `AlgebraicGeometry.Space.isAtWorstNodalOfRelativeDimensionOne_of_isSmooth`: a smooth morphism
  of algebraic spaces of relative dimension one is at-worst-nodal of relative dimension one.
* `AlgebraicGeometry.CurveFamily.exists_isPullback_fieldValuedPoint`: the fibre of a family of
  curves over a field-valued point of its base is a scheme.
* `AlgebraicGeometry.isSmoothH0Family_and_hasGenus_of_isStableCurveFamilyOfGenus`: a smooth
  stable family of genus `g` lies in `𝓜_g`.
* `AlgebraicGeometry.isStableCurveFamilyOfGenus_of_isSmoothH0Family`: for `g ≥ 2`, a family in
  `𝓜_g` is stable of genus `g`, given the genus of the fibres (Stacks 0E6V).
* `AlgebraicGeometry.isSmoothH0Family_and_hasGenus_iff`: the identity
  `𝓜_g = Curves^{smooth} ∩ 𝓜̄_g` on families, for `g ≥ 2`.
* `AlgebraicGeometry.isOpen_dense_pointSet_moduliSmoothOfGenus_in_stableOfGenus_of_two_le`: the
  statement of Stacks 0E87 with that identity proved.

## Implementation notes

The genus of the fibres is the input `h0E6V`: for a prestable family of curves `f : X → S` with
`R¹f_*𝒪_X` locally free of rank `g`, every fibre `X_p` over a field-valued point of `S` has genus
`g`. This is what Stacks 0E6V gives: by part (1) the classifying morphism of `X → S` factors
through `Curves^{prestable}_g`, hence so does that of `X_p`, and by part (2) `X_p` then has genus
`g`. The final statement also takes the algebraicity of
the stack of curves (`h`, Stacks 0D5A) and the openness of `𝓜̄_g` and of `𝓜_g` (`hP`, Stacks 0E78,
and `hQ`, Stacks 0E83), as
`AlgebraicGeometry.isOpen_dense_pointSet_moduliSmoothOfGenus_in_stableOfGenus` does.

## References

* [Stacks Project, Tag 0E87](https://stacks.math.columbia.edu/tag/0E87)
* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
* [Stacks Project, Tag 0CD7](https://stacks.math.columbia.edu/tag/0CD7)
* [Stacks Project, Tag 0FD3](https://stacks.math.columbia.edu/tag/0FD3)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry

/-! ### Nodal and smooth morphisms of algebraic spaces of relative dimension one -/

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **An at-worst-nodal morphism of relative dimension one has relative dimension one.** -/
theorem hasRelativeDimension_one_of_isAtWorstNodalOfRelativeDimensionOne {f : F ⟶ G}
    (hf : IsAtWorstNodalOfRelativeDimensionOne B S hS f) : HasRelativeDimension 1 B S hS f := by
  intro x c
  have hc := (hf c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm).1.2 (c.sourcePoint B S hS)
  exact (hasFiberDimensionAt_ofSchemeHom_iff _ _ _).2 (by exact_mod_cast hc)

/-- **A smooth morphism of relative dimension one is at-worst-nodal of relative dimension one.** -/
theorem isAtWorstNodalOfRelativeDimensionOne_of_isSmooth {f : F ⟶ G}
    (hs : IsSmooth B S hS f) (hd : HasRelativeDimension 1 B S hS f) :
    IsAtWorstNodalOfRelativeDimensionOne B S hS f := by
  intro U V a b h ha hb hw
  have hsm : Smooth ((BigFppfOver.toScheme B S hS).map h) := hs U V a b h ha hb hw
  have hdim : ∀ x : (BigFppfOver.toScheme B S hS).obj U,
      topologicalKrullDimAt (((BigFppfOver.toScheme B S hS).map h).fiber
          (((BigFppfOver.toScheme B S hS).map h) x))
        (((BigFppfOver.toScheme B S hS).map h).asFiber x) = ((1 : ℕ) : WithBot ℕ∞) := by
    intro x
    set p := (pointsEquivScheme B S hS U).symm x with hp
    let r : FieldValuedPoint B S hS (yoneda.obj U) := Quot.out p
    have hr : r.class B S hS (yoneda.obj U) = p := Quot.out_eq p
    let c : EtaleChartAtPoint B S hS f (pointsMap B S hS (yoneda.obj U) a p) :=
      { U := U
        V := V
        a := a
        b := b
        h := h
        a_etale := ha
        b_etale := hb
        comm := hw
        representative := r
        point := IsLocalRing.closedPoint r.carrier
        maps_to := by rw [hr] }
    have hsrc : c.sourcePoint B S hS = x := by
      show pointsToScheme B S hS U (r.class B S hS (yoneda.obj U)) = x
      rw [hr, hp]
      exact pointsToScheme_pointsEquivScheme_symm B S hS U x
    have hc := (hasFiberDimensionAt_ofSchemeHom_iff _ _ _).1 (hd _ c)
    rw [hsrc] at hc
    exact_mod_cast hc
  have := Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq _ 1 hdim
  exact isAtWorstNodalOfRelativeDimensionOne_of_smoothOfRelativeDimension _

/-- Pullback of global functions along the morphism of algebraic spaces represented by a morphism
of the site is pullback of global functions of schemes. -/
theorem globalFunctionsYonedaRingEquiv_globalFunctionsMap {T T' : BigFppfOver B S hS} (g : T ⟶ T')
    (s : globalFunctions' B S hS (yoneda.obj T')) :
    globalFunctionsYonedaRingEquiv B S hS T
        (globalFunctionsMap B S hS (schemeSpaceMap g) s) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom
        (globalFunctionsYonedaRingEquiv B S hS T' s) :=
  globalFunctionsMap_val_chart B S hS (schemeSpaceMap g) (idEtaleChart B S hS T')
    (idEtaleChart B S hS T) g
    (by change yoneda.map g ≫ 𝟙 _ = 𝟙 _ ≫ yoneda.map g; simp) s

end Space

/-! ### Irreducible curves have no rational tails and no rational bridges -/

/-- The closure of the complement of a closed subscheme supported everywhere is empty. -/
theorem isEmpty_complementaryCurve_of_support_eq_univ {X : Scheme.{u}} (C : X.IdealSheafData)
    (hC : (C.support : Set X) = Set.univ) : IsEmpty (complementaryCurve C) := by
  have : IsEmpty C.support.compl := ⟨fun y => y.2 (hC ▸ Set.mem_univ y.1)⟩
  unfold complementaryCurve Scheme.Hom.image
  rw [Scheme.ker_eq_top_of_isEmpty]
  infer_instance

/-- An irreducible scheme has no irreducible component with nonempty complementary curve. -/
private theorem false_of_mem_irreducibleComponents_of_nonempty {X : Scheme.{u}} [IrreducibleSpace X]
    (C : X.IdealSheafData) (hcomp : (C.support : Set X) ∈ irreducibleComponents X)
    (hne : Nonempty (complementaryCurve C)) : False := by
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hcomp
  exact (isEmpty_complementaryCurve_of_support_eq_univ C hcomp).false hne.some

/-- An irreducible scheme over a field has no rational tail. -/
theorem not_isRationalTail_of_irreducibleSpace (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IrreducibleSpace X] (C : X.IdealSheafData) :
    ¬ IsRationalTail k X C := by
  rintro ⟨-, hcomp, hne, -⟩
  exact false_of_mem_irreducibleComponents_of_nonempty C hcomp hne

/-- An irreducible scheme proper over a field has no rational bridge. -/
theorem not_isRationalBridge_of_irreducibleSpace (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] [IrreducibleSpace X]
    (C : X.IdealSheafData) : ¬ IsRationalBridge k X C := by
  rintro ⟨-, hcomp, hne, -⟩
  exact false_of_mem_irreducibleComponents_of_nonempty C hcomp hne

/-- A smooth proper scheme over a field `k` with `H⁰(X, 𝒪_X) = k` is irreducible. -/
theorem irreducibleSpace_of_smooth_of_isIso_appTop (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
    (hf : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)) : IrreducibleSpace X := by
  have : GeometricallyIrreducible f :=
    ((isIso_globalSections_tfae_geometricallyConnected_irreducible_integral k f
      (isGeometricallyNormal_of_smooth f)).out 1 3).1 hf
  exact GeometricallyIrreducible.irreducibleSpace_of_subsingleton f

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-! ### The fibres of a family of curves over field-valued points -/

namespace CurveFamily

/-- **The fibre of a family of curves over a field-valued point of its base is a scheme.** There
is an object `V` of the site with a morphism `v` to the spectrum of the field of the point and a
cartesian square of algebraic spaces exhibiting `V` as the fibre product of the total space with
that spectrum over the base. -/
theorem exists_isPullback_fieldValuedPoint (F : CurveFamily B hZ)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj) :
    ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject) (q : schemeSpace V ⟶ F.total),
      IsPullback q (schemeSpaceMap v) F.toBase (schemeSpaceMap p.value) := by
  obtain ⟨G, φ, hφ⟩ :=
    (curvesFiberedCategory B hZ).2.exists_lift p.value F rfl
  have hdom : (curvesFiberedCategory B hZ).1.p.obj G = p.siteObject :=
    IsHomLift.domain_eq _ p.value φ
  have hfac := IsHomLift.fac (curvesFiberedCategory B hZ).val.p p.value φ
  obtain ⟨Gbase, Gtotal, GtoBase, Gflat, Gproper, Gfp, Grel⟩ := G
  change Gbase = p.siteObject at hdom
  subst hdom
  have hcancel : ∀ {X Y : BigFppfOver B integerBase hZ} (h₁ : X = X) (h₂ : Y = Y) (k : X ⟶ Y),
      eqToHom h₁ ≫ k ≫ eqToHom h₂ = k := fun _ _ _ => by simp
  replace hfac : p.value = φ.baseMap := hfac.trans (hcancel _ _ _)
  have hspec : p.siteObject = integerSiteObject B hZ p.contained :=
    congrArg Over.mk (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))
  have hrep := isRepresentable_total_of_base_eq (K := p.carrier)
    ⟨p.siteObject, Gtotal, GtoBase, Gflat, Gproper, Gfp, Grel⟩
    (congrArg (BigFppfOver.toScheme B integerBase hZ).obj hspec)
  obtain ⟨T, ⟨e⟩⟩ : ∃ T : BigFppfOver B integerBase hZ, Nonempty (Gtotal ≅ schemeSpace T) :=
    ⟨Gtotal.1.reprX, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso Gtotal.1.reprW.symm⟩⟩
  obtain ⟨v, hv⟩ : ∃ v : T ⟶ p.siteObject, schemeSpaceMap v = e.inv ≫ GtoBase :=
    ⟨(schemeSpaceFunctorFullyFaithful _ _).preimage _,
      (schemeSpaceFunctorFullyFaithful _ _).map_preimage _⟩
  refine ⟨T, v, e.inv ≫ φ.totalMap, IsPullback.of_iso φ.cartesian e (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (by simp) ?_ (by simp) ?_⟩
  · rw [hv]
    simp
  · simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using
      congrArg schemeSpaceMap hfac.symm

variable {B hZ}

/-- The fibre over a field-valued point of a smooth family of curves is smooth over the field. -/
theorem smooth_of_isPullback_fieldValuedPoint {F : CurveFamily B hZ}
    (hF : IsSmoothFamily B hZ F)
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj}
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : schemeSpace V ⟶ F.total}
    (hsq : IsPullback q (schemeSpaceMap v) F.toBase
      (schemeSpaceMap p.value)) :
    Smooth ((BigFppfOver.toScheme B integerBase hZ).map v) :=
  have h : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B integerBase hZ⦄ (k : F ⟶ G) =>
        Space.IsSmooth B integerBase hZ k.hom) :=
    Space.isSmooth_isStableUnderBaseChange B integerBase hZ
  (Space.isSmooth_yoneda_map_iff B integerBase hZ v).1 (h.of_isPullback hsq hF)

/-- The fibre over a field-valued point of a family of curves is proper over the field. -/
theorem isProper_of_isPullback_fieldValuedPoint {F : CurveFamily B hZ}
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj}
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : schemeSpace V ⟶ F.total}
    (hsq : IsPullback q (schemeSpaceMap v) F.toBase
      (schemeSpaceMap p.value)) :
    IsProper ((BigFppfOver.toScheme B integerBase hZ).map v) := by
  have h₁ : Space.IsProper B integerBase hZ (yoneda.map v) :=
    (Space.isProper_isStableUnderBaseChange B integerBase hZ).of_isPullback hsq F.proper
  have : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B integerBase hZ)).IsStableUnderBaseChange :=
    ⟨fun hsq hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsProper)
      (hsq.map (BigFppfOver.toScheme B integerBase hZ)) hg⟩
  exact (MorphismProperty.relative_map_iff (F := yoneda)
    (P := MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B integerBase hZ))).mp
    ((Space.presheaf_isProper_iff B integerBase hZ (yoneda.map v)
      (isAlgebraicSpace_yoneda B integerBase hZ _) (isAlgebraicSpace_yoneda B integerBase hZ _)
      (Functor.relativelyRepresentable.map yoneda v)).mp h₁)

/-- The fibre `X_p` over a field-valued point `p` of a family of curves with `f_*𝒪_X = 𝒪_S`
universally has `H⁰(X_p, 𝒪) = k(p)`. -/
theorem isIso_appTop_of_isPullback_fieldValuedPoint {F : CurveFamily B hZ}
    (hF : HasUniversallyBijectiveGlobalFunctions B hZ F)
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj}
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : schemeSpace V ⟶ F.total}
    (hsq : IsPullback q (schemeSpaceMap v) F.toBase
      (schemeSpaceMap p.value)) :
    IsIso ((Scheme.ΓSpecIso (.of p.carrier)).inv ≫
      ((BigFppfOver.toScheme B integerBase hZ).map v).appTop) := by
  have hb := hF (schemeSpace p.siteObject) (schemeSpaceMap p.value)
  let e := (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ F.toBase
    (schemeSpaceMap p.value)).isoIsPullback _ _ hsq
  have he : schemeSpaceMap v = e.inv ≫ ObjectProperty.homMk (pullback.snd F.toBase.hom
      (schemeSpaceMap p.value).hom) :=
    (IsPullback.isoIsPullback_inv_snd _ _ _ _).symm
  have hbv : Function.Bijective
      (Space.globalFunctionsMap B integerBase hZ (schemeSpaceMap v)) := by
    rw [he, Space.globalFunctionsMap_comp]
    exact (globalFunctionsMap_bijective_of_iso e.symm).comp hb
  have hΓ : Function.Bijective
      (Scheme.Γ.map ((BigFppfOver.toScheme B integerBase hZ).map v).op).hom := by
    have hcomm : ⇑(Scheme.Γ.map ((BigFppfOver.toScheme B integerBase hZ).map v).op).hom ∘
          ⇑(Space.globalFunctionsYonedaRingEquiv B integerBase hZ p.siteObject) =
        ⇑(Space.globalFunctionsYonedaRingEquiv B integerBase hZ V) ∘
          ⇑(Space.globalFunctionsMap B integerBase hZ (schemeSpaceMap v)) :=
      funext fun s =>
        (Space.globalFunctionsYonedaRingEquiv_globalFunctionsMap B integerBase hZ v s).symm
    refine (Function.Bijective.of_comp_iff _
      (Space.globalFunctionsYonedaRingEquiv B integerBase hZ p.siteObject).bijective).1 ?_
    have hX := (Space.globalFunctionsYonedaRingEquiv B integerBase hZ V).bijective.comp hbv
    rwa [← hcomm] at hX
  have : IsIso ((BigFppfOver.toScheme B integerBase hZ).map v).appTop :=
    (ConcreteCategory.isIso_iff_bijective _).2 hΓ
  infer_instance

end CurveFamily

/-! ### Smooth stable families and smooth families with connected fibres -/

/-- **A smooth stable family of genus `g` lies in `𝓜_g`**: it is smooth of relative dimension one,
with `f_*𝒪_X = 𝒪_S` universally, and of genus `g`. -/
theorem isSmoothH0Family_and_hasGenus_of_isStableCurveFamilyOfGenus {g : ℕ}
    {F : CurveFamily B hZ} (hs : IsSmoothFamily B hZ F)
    (hst : IsStableCurveFamilyOfGenus B hZ g F) :
    IsSmoothH0Family B hZ F ∧ CurveFamily.HasGenus B hZ F g :=
  ⟨⟨⟨hs, Space.hasRelativeDimension_one_of_isAtWorstNodalOfRelativeDimensionOne B integerBase hZ
    hst.1.1.1⟩, hst.1.1.2⟩, hst.2⟩

/-- **For `g ≥ 2`, a family in `𝓜_g` is stable of genus `g`**, given the genus of the fibres of
prestable families of genus `g` (`h0E6V`, which is what Stacks 0E6V gives). -/
theorem isStableCurveFamilyOfGenus_of_isSmoothH0Family {g : ℕ} (hg : 2 ≤ g)
    (h0E6V : ∀ F : CurveFamily B hZ, IsPrestableCurveFamily B hZ F →
      CurveFamily.HasGenus B hZ F g →
      ∀ (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj)
        (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
        (q : yoneda.obj V ⟶ F.total.obj),
        IsPullback q (yoneda.map v) F.toBase.hom (yonedaEquiv.symm p.value) →
          genus ((BigFppfOver.toScheme B integerBase hZ).map v) = g)
    {F : CurveFamily B hZ} (hF : IsSmoothH0Family B hZ F) (hgen : CurveFamily.HasGenus B hZ F g) :
    IsStableCurveFamilyOfGenus B hZ g F := by
  have hpre : IsPrestableCurveFamily B hZ F :=
    ⟨Space.isAtWorstNodalOfRelativeDimensionOne_of_isSmooth B integerBase hZ hF.1.1 hF.1.2, hF.2⟩
  refine ⟨⟨hpre, fun p => ?_⟩, hgen⟩
  obtain ⟨V, v, q, hsq⟩ := CurveFamily.exists_isPullback_fieldValuedPoint B hZ F p
  have hsq' : IsPullback q.hom (yoneda.map v) F.toBase.hom (yonedaEquiv.symm p.value) :=
    AlgebraicSpaces.isPullback_hom B integerBase hZ hsq
  refine ⟨V, v, q.hom, hsq', ?_⟩
  have := CurveFamily.smooth_of_isPullback_fieldValuedPoint hF.1.1 hsq
  have := CurveFamily.isProper_of_isPullback_fieldValuedPoint hsq
  have := irreducibleSpace_of_smooth_of_isIso_appTop p.carrier
    ((BigFppfOver.toScheme B integerBase hZ).map v)
    (CurveFamily.isIso_appTop_of_isPullback_fieldValuedPoint hF.2 hsq)
  let : ((BigFppfOver.toScheme B integerBase hZ).obj V).Over (Spec (.of p.carrier)) :=
    ⟨(BigFppfOver.toScheme B integerBase hZ).map v⟩
  have hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).obj V ↘
    Spec (.of p.carrier)) := ‹IsProper ((BigFppfOver.toScheme B integerBase hZ).map v)›
  refine ⟨?_, not_isRationalTail_of_irreducibleSpace p.carrier _, hproper,
    not_isRationalBridge_of_irreducibleSpace p.carrier _⟩
  rwa [h0E6V F hpre hgen p V v q.hom hsq']

/-- **`𝓜_g = Curves^{smooth} ∩ 𝓜̄_g` for `g ≥ 2`**, on families of curves: a family is smooth of
relative dimension one with `f_*𝒪_X = 𝒪_S` universally and of genus `g` exactly when it is smooth
and stable of genus `g`, given the genus of the fibres (`h0E6V`, Stacks 0E6V). -/
theorem isSmoothH0Family_and_hasGenus_iff {g : ℕ} (hg : 2 ≤ g)
    (h0E6V : ∀ F : CurveFamily B hZ, IsPrestableCurveFamily B hZ F →
      CurveFamily.HasGenus B hZ F g →
      ∀ (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj)
        (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
        (q : yoneda.obj V ⟶ F.total.obj),
        IsPullback q (yoneda.map v) F.toBase.hom (yonedaEquiv.symm p.value) →
          genus ((BigFppfOver.toScheme B integerBase hZ).map v) = g)
    (F : CurveFamily B hZ) :
    IsSmoothH0Family B hZ F ∧ CurveFamily.HasGenus B hZ F g ↔
      IsSmoothFamily B hZ F ∧ IsStableCurveFamilyOfGenus B hZ g F :=
  ⟨fun hF => ⟨hF.1.1.1, isStableCurveFamilyOfGenus_of_isSmoothH0Family B hZ hg h0E6V hF.1 hF.2⟩,
    fun hF => isSmoothH0Family_and_hasGenus_of_isStableCurveFamilyOfGenus B hZ hF.1 hF.2⟩

variable (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **The statement of Stacks 0E87**, on the stack of curves `curvesAlgebraicStack B hZ h`, where
`h` is the algebraicity of the stack of curves (Stacks 0D5A). Let `g ≥ 2` and let `𝓜̄_g` and `𝓜_g`
be the open substacks cut out by being stable of genus `g` (`hP`, Stacks 0E78) and by being smooth
with `f_*𝒪_X = 𝒪_S` universally of genus `g` (`hQ`, Stacks 0E83). Then `|𝓜_g| ⊂ |𝓜̄_g|` is an
open dense subset, given the genus of the fibres (`h0E6V`, Stacks 0E6V). -/
theorem isOpen_dense_pointSet_moduliSmoothOfGenus_in_stableOfGenus_of_two_le (g : ℕ) (hg : 2 ≤ g)
    (h0E6V : ∀ F : CurveFamily B hZ, IsPrestableCurveFamily B hZ F →
      CurveFamily.HasGenus B hZ F g →
      ∀ (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj)
        (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
        (q : yoneda.obj V ⟶ F.total.obj),
        IsPullback q (yoneda.map v) F.toBase.hom (yonedaEquiv.symm p.value) →
          genus ((BigFppfOver.toScheme B integerBase hZ).map v) = g)
    (hP : IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g))
    (hQ : IsOpenCurvesLocus B hZ
      (fun X => IsSmoothH0Family B hZ X ∧ CurveFamily.HasGenus B hZ X g)) :
    letI := Stack.pointTopology B integerBase hZ (curvesAlgebraicStack B hZ h).val
    (curvesSmallOpenSubstack B hZ h hQ).pointSet B integerBase hZ ⊆
      (curvesSmallOpenSubstack B hZ h hP).pointSet B integerBase hZ ∧
    IsOpen (Subtype.val ⁻¹' (curvesSmallOpenSubstack B hZ h hQ).pointSet B integerBase hZ :
      Set ((curvesSmallOpenSubstack B hZ h hP).pointSet B integerBase hZ)) ∧
    Dense (Subtype.val ⁻¹' (curvesSmallOpenSubstack B hZ h hQ).pointSet B integerBase hZ :
      Set ((curvesSmallOpenSubstack B hZ h hP).pointSet B integerBase hZ)) :=
  isOpen_dense_pointSet_moduliSmoothOfGenus_in_stableOfGenus B hZ h g hP hQ
    (isSmoothH0Family_and_hasGenus_iff B hZ hg h0E6V)

end AlgebraicGeometry

end
