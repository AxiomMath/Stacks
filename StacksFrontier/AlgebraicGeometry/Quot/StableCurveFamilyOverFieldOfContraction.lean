module

public import StacksFrontier.AlgebraicGeometry.Quot.PrestableStabilizationStableFibres
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyContraction
public import StacksFrontier.AlgebraicGeometry.Quot.StableModelSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Quot.StableLocusOpenGlobalFunctions

/-!
# A family over a field receiving a stable contraction is stable

Let `k` be a field and `Y ⟶ Spec k` a family of curves whose total space is a scheme `G`
(the fibre of a family over a point `Spec k ⟶ S`). Suppose `a : V ⟶ G` is a morphism over `k`
from a prestable family `V ⟶ Spec k` which satisfies the three conditions of Stacks 0E7Q
(`G` proper of dimension one with at-worst-nodal singularities, `𝒪_G = a_*𝒪_V`,
`R¹a_*𝒪_V = 0`, `ω_G` ample) and `𝒪 = a'_*𝒪` after every base change. Then `Y ⟶ Spec k` is a
stable family of curves: it is at-worst-nodal of relative dimension one (Stacks 0C59 on its only
fibre), `f_*𝒪 = 𝒪` universally (from that of `V` along `a`), and over every field extension
`K/k` its fibre `G_K` receives the base change `a_K`, which satisfies the conditions of
Stacks 0E7Q over `K` (`Stacks.Curves.StableModel.IsStableContraction.baseChange`), so `G_K` has
genus at least two and neither rational tails nor rational bridges (Stacks 0E3P and its converse,
`AlgebraicGeometry.hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField`).

This is the implication (2)(c) ⟹ (2)(a) of Stacks 0E76 for the target of a contraction, used in
the proof of Stacks 0E8A: since `ω_{Y_0}` is ample, the point `u` lies in the stable locus.

## Main results

* `AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_of_hasAtWorstNodalSingularities`: a
  proper scheme over a field of dimension one with `H⁰ = k` and at-worst-nodal singularities is
  at-worst-nodal of relative dimension one over `k`.
* `AlgebraicGeometry.CurveFamily.isStableCurveFamily_ofIsPullback_of_isStableContraction`: the
  family over a field receiving a stable contraction is stable.

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
* [Stacks Project, Tag 0C59](https://stacks.math.columbia.edu/tag/0C59)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- Equidimensionality of a scheme transfers along an isomorphism of schemes. -/
private theorem equidimensional_of_iso {A G : Scheme.{u}} (ι : A ≅ G)
    (hG : TopologicalSpace.Equidimensional G) : TopologicalSpace.Equidimensional A := by
  let e := Scheme.homeoOfIso ι
  intro Z hZ W hW
  calc topologicalKrullDim Z = topologicalKrullDim (e '' Z) :=
        (e.image Z).isHomeomorph.topologicalKrullDim_eq
    _ = topologicalKrullDim (e '' W) :=
        hG _ (e.image_mem_irreducibleComponents hZ) _ (e.image_mem_irreducibleComponents hW)
    _ = topologicalKrullDim W := (e.image W).isHomeomorph.topologicalKrullDim_eq.symm

/-- **A nodal curve over a field is at-worst-nodal of relative dimension one.** A proper scheme
`G` over a field `k` of dimension one with `H⁰(G, 𝒪_G) = k` and at-worst-nodal singularities is
at-worst-nodal of relative dimension one over `k`: by Stacks 0C59 this is read on the only fibre,
which is `G`, equidimensional by Stacks 0BY5. -/
theorem isAtWorstNodalOfRelativeDimensionOne_of_hasAtWorstNodalSingularities {k : Type u}
    [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (.of k)) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim G = 1)
    (hnodal : letI : G.Over (Spec (.of k)) := ⟨f⟩
      Stacks.Curves.HasAtWorstNodalSingularities k G) :
    IsAtWorstNodalOfRelativeDimensionOne f := by
  let : G.Over (Spec (.of k)) := ⟨f⟩
  have : Flat (G ↘ Spec (.of k)) := inferInstance
  have : Flat f := inferInstanceAs (Flat (G ↘ Spec (.of k)))
  have : LocallyOfFinitePresentation f := inferInstance
  refine (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff f).1 ⟨inferInstance,
    inferInstance, fun s _ => ?_⟩
  have : IsIso ((Spec (.of k)).fromSpecResidueField s) := isIso_fromSpecResidueField_of_field k s
  have hpb := IsPullback.of_hasPullback f ((Spec (.of k)).fromSpecResidueField s)
  let ι : f.fiber s ≅ G :=
    @asIso _ _ _ _ (pullback.fst f ((Spec (.of k)).fromSpecResidueField s))
      (hpb.isIso_fst_of_isIso inferInstance)
  refine ⟨equidimensional_of_iso ι
    (equidimensional_of_isIso_globalSections_of_dimension_one k f hdim),
    (Scheme.homeoOfIso ι).isHomeomorph.topologicalKrullDim_eq.trans hdim, ?_⟩
  let φ : CommRingCat.of ((Spec (.of k)).residueField s) ⟶ CommRingCat.of k :=
    Spec.preimage (inv ((Spec (.of k)).fromSpecResidueField s))
  have hφ : Spec.map φ = inv ((Spec (.of k)).fromSpecResidueField s) := Spec.map_preimage _
  have : IsIso (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have : IsIso (Scheme.Spec.map φ.op) := inferInstanceAs (IsIso (Spec.map φ))
  have : IsIso φ.op := isIso_of_reflects_iso φ.op Scheme.Spec
  have hw : ι.hom ≫ f = f.fiberToSpecResidueField s ≫ (Spec (.of k)).fromSpecResidueField s :=
    hpb.w
  have he : ι.hom ≫ f ≫ Spec.map φ = f.fiberToSpecResidueField s := by
    rw [hφ, ← Category.assoc, hw, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  exact @Stacks.Curves.hasAtWorstNodalSingularities_of_isIso _ _ _ _ _ _ f
    (f.fiberToSpecResidueField s) _ hdim ι.hom _ φ (isIso_of_op φ) he hnodal

section StableContraction

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  {g : Y ⟶ Spec (.of k)} {c : X ⟶ Y}

/-- The target of a stable contraction out of a scheme with `H⁰ = k` has `H⁰ = k`. -/
private theorem isIso_globalSections_of_isStableContraction
    (hst : Stacks.Curves.StableModel.IsStableContraction f g c)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) := by
  have : IsIso c.appTop :=
    Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit _
      hst.isIso_unitToPushforwardObjUnit ⊤
  have : IsIso (((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) ≫ c.appTop) := by
    rw [Category.assoc, ← Scheme.Hom.comp_appTop, hst.comp_eq]
    infer_instance
  exact IsIso.of_isIso_comp_right _ c.appTop

/-- Over every field extension `K/k`, the base change of the target of a stable contraction has
genus at least two and neither rational tails nor rational bridges. -/
private theorem hasGenusTwoNoRationalTailNoRationalBridge_baseChange_of_isStableContraction
    [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hst : Stacks.Curves.StableModel.IsStableContraction f g c) (K : Type u) [Field K]
    [Algebra k K] :
    HasGenusTwoNoRationalTailNoRationalBridge K
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  have hstK := hst.baseChange K
  have := hst.isProper
  have := isIso_globalSections_of_isStableContraction hst
  have := isIso_globalSections_baseChange k K _ _ _
    (IsPullback.of_hasPullback g (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  have := hstK.isProper
  exact (hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField K _
    hstK.topologicalKrullDim_eq ((ConcreteCategory.isIso_iff_bijective _).1
      (IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of K)).inv _))
    hstK.hasAtWorstNodalSingularities).2 hstK.isAmple

end StableContraction

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

variable {F : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
  (p : Space.FieldValuedPoint B integerBase hZ F)

/-- **A family over a field receiving a stable contraction is stable.** Let `p` be a field-valued
point with field `k`, `Z` a prestable family and `Y` a family of curves, `V` and `G` presenting
their fibres over morphisms `Spec k ⟶ Z.base` and `Spec k ⟶ Y.base`, and `a : V ⟶ G` over `k`
satisfying the conditions of Stacks 0E7Q and condition (1) of Stacks 0E8A between the two fibre
families. Then the fibre family `G ⟶ Spec k` of `Y` is stable. -/
theorem isStableCurveFamily_ofIsPullback_of_isStableContraction {Z Y : CurveFamily B hZ}
    (wZ : p.siteObject ⟶ Z.base) (wY : p.siteObject ⟶ Y.base)
    {V G : BigFppfOver B integerBase hZ} (v : V ⟶ p.siteObject) (tG : G ⟶ p.siteObject)
    (qV : schemeSpace V ⟶ Z.total) (qG : schemeSpace G ⟶ Y.total)
    (sqV : IsPullback qV (schemeSpaceMap v) Z.toBase (schemeSpaceMap wZ))
    (sqG : IsPullback qG (schemeSpaceMap tG) Y.toBase (schemeSpaceMap wY))
    (hZp : IsPrestableCurveFamily B hZ Z) [IsProper ((𝒯).map v)]
    [IsIso ((Scheme.ΓSpecIso (.of p.carrier)).inv ≫ ((𝒯).map v).appTop)]
    (a : V ⟶ G) (ha : a ≫ tG = v)
    (h1 : (Z.ofIsPullback B hZ wZ qV (schemeSpaceMap v) sqV).IsUniversalStructureContraction B hZ
      (Y.ofIsPullback B hZ wY qG (schemeSpaceMap tG) sqG) rfl (schemeSpaceMap a))
    (hst : Stacks.Curves.StableModel.IsStableContraction ((𝒯).map v) ((𝒯).map tG)
      ((𝒯).map a)) :
    IsStableCurveFamily B hZ (Y.ofIsPullback B hZ wY qG (schemeSpaceMap tG) sqG) := by
  have : IsProper ((𝒯).map tG) := hst.isProper
  have := isIso_globalSections_of_isStableContraction hst
  refine ⟨⟨?_, hasUniversallyBijectiveGlobalFunctions_of_isIso_structureSharp_baseChange
    (X := Z.ofIsPullback B hZ wZ qV (schemeSpaceMap v) sqV) rfl (schemeSpaceMap a)
    ((Category.assoc _ _ _).symm.trans ((Category.comp_id _).trans
      ((schemeSpaceMap_comp a tG).symm.trans (congrArg schemeSpaceMap ha))))
    (fun T t X' Y' pX' fX' pY' fY' c' h₁ h₂ h₃ h₄ =>
      (h1 T t X' Y' pX' fX' pY' fY' c' h₁ h₂ h₃ h₄).1)
    (isPrestableCurveFamily_of_hom (Z.homOfIsPullback B hZ wZ qV _ sqV) hZp).2⟩, fun Q => ?_⟩
  · exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget tG).2
      (isAtWorstNodalOfRelativeDimensionOne_of_hasAtWorstNodalSingularities ((𝒯).map tG)
        hst.topologicalKrullDim_eq hst.hasAtWorstNodalSingularities)
  set k := p.carrier
  set K := Q.carrier
  let qv : Q.siteObject ⟶ p.siteObject := Q.value
  let t : Spec (.of K) ⟶ Spec (.of k) := (𝒯).map qv
  let : Algebra k K := (Spec.preimage t).hom.toAlgebra
  have hgK : Spec.map (CommRingCat.ofHom (algebraMap k K)) = t := Spec.map_preimage t
  set gK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let GK : BigFppfOver B integerBase hZ :=
    ofScheme (pullback ((𝒯).map tG) gK) (contains_pullback _ _ G.left.property Q.contained)
  let vGK : GK ⟶ Q.siteObject := homOfScheme (pullback.snd ((𝒯).map tG) gK)
  let jGK : GK ⟶ G := homOfScheme (pullback.fst ((𝒯).map tG) gK)
  have H : IsPullback ((𝒯).map jGK) ((𝒯).map vGK) ((𝒯).map tG) ((𝒯).map qv) := by
    show IsPullback (pullback.fst ((𝒯).map tG) gK) (pullback.snd ((𝒯).map tG) gK)
      ((𝒯).map tG) t
    rw [← hgK]
    exact IsPullback.of_hasPullback _ _
  have hsq : IsPullback jGK vGK tG qv :=
    isPullback_of_isPullback_toScheme_map
      ((BigFppfOver.fullyFaithfulToScheme B integerBase hZ specULiftZIsTerminal).map_injective
        (by
          rw [Functor.map_comp, Functor.map_comp]
          exact H.w)) H
  refine ⟨GK, vGK, yoneda.map jGK, ?_,
    hasGenusTwoNoRationalTailNoRationalBridge_baseChange_of_isStableContraction hst K⟩
  rw [yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map qv).symm]
  exact hsq.map yoneda

end CurveFamily

end AlgebraicGeometry

end
