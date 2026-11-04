module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionModificationEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleFromCompletionSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionExistence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionMorphismAffineChartFactorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleCancellationGeneral
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleRigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionLift
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubfunctorFactorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineEtaleChartTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismUniquenessAlongClosedSubset
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitSpaceDescent
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyCounterexample
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSourceFormalSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent

/-!
# Factoring the formal component through an affine étale chart, étale locally

In the proof of Stacks 0GI5 the hard case of the surjectivity begins with a reduction to an
affine formal algebraic space `W`: every point `v` of `Z ⊆ V` has an étale neighbourhood on
which the formal component `x̂ : V_{/Z} ⟶ W` factors through an affine formal algebraic space
étale over `W`.

The source obtains it from Stacks 0ARB: for an étale chart `W₀ ⟶ W` the base change
`W₀ ×_{W, x̂} V_{/Z} ⟶ V_{/Z}` is étale, hence the completion of a morphism `Ṽ ⟶ V` locally of
finite type and an isomorphism over `V ∖ Z`; that morphism is étale by Stacks 0AR4, and `x̂`
restricted to `Ṽ_{/Z}` factors through `W₀`. An affine étale chart of `Ṽ` through a point over
`v` is the neighbourhood.

## Main results

* `AlgebraicGeometry.Artin.exists_etale_affine_chart_factorization`: the statement above, for a
  locally Noetherian object `V` of the site and a locally Noetherian formal algebraic space `W`.
* `AlgebraicGeometry.Artin.exists_stage_etale_model`: an affine étale neighbourhood of a limit of
  affine objects is the base change of an affine étale neighbourhood of a stage.
* `AlgebraicGeometry.Artin.ContractionSituation.FactorsThroughAffineChart`: the property of an
  element of `F(V)` that its formal component factors through such a chart.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_factorsThroughAffineChart`: the `hfactor`
  input of
  `AlgebraicGeometry.Artin.ContractionSituation.limitPreserving_contractionFunctor_of_core`.
* `AlgebraicGeometry.Artin.ContractionSituation.limitPreserving_contractionFunctor_of_affineChart`:
  Stacks 0GI5 reduced to the elements with that property.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
* [Stacks Project, Tag 0ARB](https://stacks.math.columbia.edu/tag/0ARB)
* [Stacks Project, Tag 0AR4](https://stacks.math.columbia.edu/tag/0AR4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A section of the completion through a prescribed point of `Z`.** For a closed set `Z` of
points of an object `V` of the site and a point `v` of `V` in `Z`, the reduced closed subscheme
supported on `Z` is an object `Zo` of the site with a morphism to `V` with image in `Z` hitting
`v`. -/
theorem exists_hasImageIn_through_point {V : BigFppfOver B S hS}
    {Z : Set (Space.points B S hS (yoneda.obj V))} (hZ : IsClosed Z)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (hv : (Space.schemePointsHomeomorph B S hS V).symm v ∈ Z) :
    ∃ (Zo : BigFppfOver B S hS) (z : Zo ⟶ V),
      Space.HasImageIn B S hS (yoneda.obj V) Z Zo z ∧
        v ∈ Set.range ((BigFppfOver.toScheme B S hS).map z) := by
  classical
  let Tf := BigFppfOver.toScheme B S hS
  let X : Scheme.{u} := Tf.obj V
  let Zs : Set X := Space.pointsToScheme B S hS V '' Z
  have hZs : IsClosed Zs :=
    (Space.isClosed_pointTopology_yoneda_iff_isClosed_image B S hS V Z).1 hZ
  let Ide := Scheme.IdealSheafData.vanishingIdeal (⟨Zs, hZs⟩ : TopologicalSpace.Closeds X)
  let i : Ide.subscheme ⟶ X := Ide.subschemeι
  have hirange : Set.range i.base = Zs := by
    show Set.range Ide.subschemeι.base = Zs
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : AlgebraicGeometry.IsClosedImmersion i := by
    show AlgebraicGeometry.IsClosedImmersion Ide.subschemeι
    infer_instance
  have hZC : B.Contains Ide.subscheme := B.contains_of_mono i V.left.2
  let Zo : BigFppfOver B S hS := BigFppfOver.mk B S hS hZC (i ≫ B.inclusion.map V.hom)
  let zV : Zo ⟶ V := Over.homMk (ObjectProperty.homMk i)
    (by apply ObjectProperty.hom_ext; rfl)
  have hzV : Tf.map zV = i := rfl
  refine ⟨Zo, zV, ?_, ?_⟩
  · rw [Space.hasImageIn_iff_range_subset]
    rintro _ ⟨w, rfl⟩
    have e : yonedaEquiv.symm zV = yoneda.map zV :=
      yonedaEquiv.injective (by rw [Equiv.apply_symm_apply, yonedaEquiv_yoneda_map])
    rw [e]
    have hmem : Space.pointsToScheme B S hS V
        (Space.pointsMap B S hS _ (yoneda.map zV) w) ∈ Zs := by
      rw [Space.pointsToScheme_pointsMap_yoneda, hzV, ← hirange]
      exact ⟨_, rfl⟩
    obtain ⟨w', hw', he⟩ := hmem
    rwa [← Space.injective_pointsToScheme B S hS V he]
  · have hvZ : v ∈ Zs := ⟨_, hv, by
      rw [← Space.schemePointsHomeomorph_apply, Homeomorph.apply_symm_apply]⟩
    rwa [← hirange] at hvZ

/-- A representable étale morphism of locally Noetherian formal algebraic spaces is rig-étale:
on charts it is a representable étale morphism of Noetherian affine formal algebraic spaces. -/
theorem isRigEtale_of_isRepresentableEtale_of_isLocallyNoetherian
    {X Y : FormalSpace.FppfSheaf B S hS} (φ : X ⟶ Y)
    (hX : FormalSpace.IsLocallyNoetherian B S hS X) (hY : FormalSpace.IsLocallyNoetherian B S hS Y)
    (hφ : FormalSpace.IsRepresentableEtale B S hS φ) : FormalSpace.IsRigEtale B S hS φ := by
  intro U V hU hV a b t ha hb hae hbe hsq
  have hU' : FormalSpace.IsNoetherian B S hS U :=
    FormalSpace.isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hX a hU ⟨ha, hae⟩
  have hV' : FormalSpace.IsNoetherian B S hS V :=
    FormalSpace.isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hY b hV ⟨hb, hbe⟩
  have ht : FormalSpace.IsRepresentableEtale B S hS t :=
    FormalSpace.isRepresentableEtale_of_comp' B S hS t b ⟨hb, hbe⟩ (by
      rw [← hsq]; exact FormalSpace.IsRepresentableEtale.comp B S hS ⟨ha, hae⟩ hφ)
  have hidU := FormalSpace.isRepresentableEtale_of_isIso B S hS (𝟙 U)
  have hidV := FormalSpace.isRepresentableEtale_of_isIso B S hS (𝟙 V)
  exact FormalSpace.isRigEtale_of_isRepresentableEtale B S hS t hU' hV' ht U V hU hV (𝟙 U) (𝟙 V) t
    hidU.1 hidV.1 hidU.2 hidV.2 (by rw [Category.id_comp, Category.comp_id])

/-- A formal algebraic space with a representable étale morphism to a locally Noetherian one is
locally Noetherian. -/
private theorem isLocallyNoetherian_of_isRepresentableEtale {A C : FormalSpace.FppfSheaf B S hS}
    (g : A ⟶ C) (hA : FormalSpace.IsFormalAlgebraicSpace B S hS A)
    (hC : FormalSpace.IsLocallyNoetherian B S hS C)
    (hg : FormalSpace.IsRepresentableEtale B S hS g) :
    FormalSpace.IsLocallyNoetherian B S hS A := by
  obtain ⟨-, I, Xi, f, haff, het, hsurj⟩ := id hA
  exact ⟨hA, I, Xi, f, haff, het, hsurj, fun j =>
    FormalSpace.isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hC _
      (haff j) (FormalSpace.IsRepresentableEtale.comp B S hS (het j) hg)⟩

/-- A morphism of the site commutes with the structure morphisms to `S`. -/
private theorem map_comp_inclusion_map_hom {A A' : BigFppfOver B S hS} (f : A ⟶ A') :
    (BigFppfOver.toScheme B S hS).map f ≫ B.inclusion.map A'.hom = B.inclusion.map A.hom := by
  show B.inclusion.map f.left ≫ _ = _
  rw [← B.inclusion.map_comp]
  exact congrArg B.inclusion.map (Over.w f)

/-- Restriction of completions along `k = f ≫ g` is the composite of the restrictions. -/
private theorem completionSheafRestrict_eq_comp {F'' F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F'' ⟶ F'} {g : F' ⟶ F} {k : F'' ⟶ F} (hk : f ≫ g = k)
    {T'' : Set (Space.points B S hS F'')} {T' : Set (Space.points B S hS F')}
    {T : Set (Space.points B S hS F)} (h₁ : T'' ⊆ Space.pointsMap B S hS F'' f ⁻¹' T')
    (h₂ : T' ⊆ Space.pointsMap B S hS F' g ⁻¹' T) (h : T'' ⊆ Space.pointsMap B S hS F'' k ⁻¹' T) :
    Space.completionSheafRestrict B S hS k T'' T h =
      Space.completionSheafRestrict B S hS f T'' T' h₁ ≫
        Space.completionSheafRestrict B S hS g T' T h₂ := by
  subst hk
  exact Space.completionSheafRestrict_comp B S hS f g T'' T' T h₁ h₂ h

/-- **An étale neighbourhood on which a morphism out of a completion factors through an affine
chart** (the reduction to an affine `W` in the proof of Stacks 0GI5). Let `W` be a locally
Noetherian formal algebraic space, `V` a locally Noetherian object of the site, `Z ⊆ |V|` closed
and `x̂ : V_{/Z} ⟶ W`. Every point `v ∈ Z` lies in the image of an étale morphism `r : P ⟶ V` with
`P` affine, such that the restriction of `x̂` to `P_{/r⁻¹Z}` factors through a representable
étale morphism `ω : W₀ ⟶ W` out of a Noetherian affine formal algebraic space.

The base change `E = W₀ ×_W V_{/Z}` of a chart `ω` of the atlas of `W` through which the value of
`x̂` at `v` factors is representable étale over `V_{/Z}`, hence rig-étale and locally Noetherian;
by Stacks 0ARB it is the completion of a morphism `ν : Ṽ ⟶ V` locally of finite type and an
isomorphism over `V ∖ Z`, which is étale by Stacks 0AR4. The section of `E` through `v` gives a
point of `Ṽ` over `v`, and an affine étale chart of `Ṽ` through it is `P`. -/
theorem exists_etale_affine_chart_factorization {W : FormalSpace.FppfSheaf B S hS}
    (hW : FormalSpace.IsLocallyNoetherian B S hS W) {V : BigFppfOver B S hS}
    (hVN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V))
    {Z : Set (Space.points B S hS (yoneda.obj V))} (hZ : IsClosed Z)
    (xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ W)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (hv : (Space.schemePointsHomeomorph B S hS V).symm v ∈ Z) :
    ∃ (P : BigFppfOver B S hS) (r : P ⟶ V), Etale ((BigFppfOver.toScheme B S hS).map r) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj P) ∧
      v ∈ Set.range ((BigFppfOver.toScheme B S hS).map r) ∧
      ∃ (W₀ : FormalSpace.FppfSheaf B S hS) (ω : W₀ ⟶ W),
        FormalSpace.IsAffineFormalAlgebraicSpace B S hS W₀ ∧ FormalSpace.IsNoetherian B S hS W₀ ∧
          FormalSpace.IsRepresentableEtale B S hS ω ∧
          ∃ x₀ : Space.completionSheaf B S hS (yoneda.obj P)
              (Space.pointsMap B S hS _ (yoneda.map r) ⁻¹' Z) ⟶ W₀,
            x₀ ≫ ω = Space.completionSheafRestrict B S hS (yoneda.map r) _ Z (fun _ hz => hz) ≫
              xhat := by
  classical
  let Tf := BigFppfOver.toScheme B S hS
  let : HasColimitsOfSize.{u + 1, u + 1} (FormalSpace.FppfSheaf B S hS) :=
    Sheaf.instHasColimitsOfSize
  obtain ⟨hWf, J, Wi, f, haff, het, hsurj, hnoeth⟩ := hW
  have hWln : FormalSpace.IsLocallyNoetherian B S hS W := ⟨hWf, J, Wi, f, haff, het, hsurj, hnoeth⟩
  -- a section of `V_{/Z}` through `v`, and a chart of `W` through its value
  obtain ⟨Zo, z, hz, ⟨x, hx⟩⟩ := exists_hasImageIn_through_point hZ v hv
  let sZ : (Space.completionSheaf B S hS (yoneda.obj V) Z).obj.obj (op Zo) :=
    (FormalSpace.toCompletionSheaf B S hS (yoneda.obj V) Z).app (op Zo) ⟨ULift.up z, hz⟩
  let g : uliftYoneda.{u + 1}.obj Zo ⟶ W.obj := uliftYonedaEquiv.symm (xhat.hom.app (op Zo) sZ)
  obtain ⟨i, T, b, m, y, hm, hy⟩ :=
    FormalSpace.exists_factorization_through_point B S hS Wi f hsurj Zo g x
  -- the base change `E = W₀ ×_W V_{/Z}` as an object of the right-hand category of Stacks 0ARB
  have hVsp := isAlgebraicSpace_yoneda B S hS V
  have hVN' : Space.IsLocallyNoetherian B S hS (yoneda.obj V) :=
    Space.isLocallyNoetherian_yoneda B S hS V hVN
  have hCln := FormalSpace.isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian hVsp hVN' Z hZ
  have hCf := FormalSpace.isFormalAlgebraicSpace_completionSheaf_of_isClosed hVsp Z hZ
  have hsnd : FormalSpace.IsRepresentableEtale B S hS (pullback.snd (f i) xhat) :=
    FormalSpace.isRepresentableEtale_pullback_snd B S hS (f i) xhat (het i)
  have hEf : FormalSpace.IsFormalAlgebraicSpace B S hS (pullback (f i) xhat) :=
    FormalSpace.isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS (f i) xhat hWf
      (FormalSpace.isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (haff i)) hCf
  have hEln := isLocallyNoetherian_of_isRepresentableEtale _ hEf hCln hsnd
  have hErig : FormalSpace.IsRigEtale B S hS (pullback.snd (f i) xhat) :=
    isRigEtale_of_isRepresentableEtale_of_isLocallyNoetherian _ hEln hCln hsnd
  let Eobj : FormalSpace.RigEtaleOverCompletion B S hS (yoneda.obj V) Z :=
    ⟨Over.mk (pullback.snd (f i) xhat), hEf, hEln, hErig⟩
  have := FormalSpace.isEquivalence_completionModificationFunctor Z hZ hVsp hVN'
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (FormalSpace.completionModificationFunctor Z hZ hVsp hVN') Eobj
  -- the algebraization `ν : Ṽ ⟶ V`
  let ν : M.obj.left ⟶ yoneda.obj V := M.obj.hom
  have hVt : IsAlgebraicSpace B S hS M.obj.left := M.property.1.1
  have hνU : IsIso (pullback.snd ν (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι) :=
    M.property.1.2
  have hνft : Space.IsLocallyOfFiniteType B S hS ν := M.property.2
  let ε : Space.completionSheaf B S hS M.obj.left (Space.pointsMap B S hS _ ν ⁻¹' Z) ⟶
      pullback (f i) xhat := e.hom.hom.left
  have hε : ε ≫ pullback.snd (f i) xhat = Space.completionSheafMap B S hS ν Z := Over.w e.hom.hom
  have : IsIso ε := by
    show IsIso ((ObjectProperty.ι _ ⋙ Over.forget _).mapIso e).hom
    infer_instance
  have hνet : Space.IsEtale B S hS ν := by
    have hrep : FormalSpace.IsRepresentableEtale B S hS (Space.completionSheafMap B S hS ν Z) := by
      rw [← hε]
      exact (FormalSpace.isRepresentableEtale_of_isIso B S hS ε).comp B S hS hsnd
    exact FormalSpace.isEtale_of_isEtale_completionSheafMap_space B S hS hVt hVsp ν Z hZ
      (FormalSpace.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyNoetherian hVsp hVN')
      hνft (Space.isEtale_openComplementRestriction B S hS ν Z hνU) hrep
  -- a point of `Ṽ` over the section through `v`
  let C := Space.completionSheaf B S hS (yoneda.obj V) Z
  let sT : uliftYoneda.{u + 1}.obj T ⟶ C.obj := uliftYonedaEquiv.symm (C.obj.map b.op sZ)
  have hcomm : m ≫ (f i).hom = sT ≫ xhat.hom := by
    rw [hm]
    apply uliftYonedaEquiv.injective
    simp only [g, sT, uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
    exact (NatTrans.naturality_apply xhat.hom b.op sZ).symm
  have hpbS : IsPullback (ε ≫ pullback.fst (f i) xhat) (Space.completionSheafMap B S hS ν Z)
      (f i) xhat :=
    IsPullback.of_iso_pullback ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, hε]⟩
      (asIso ε) rfl hε
  have hpbP := hpbS.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  let t₁ : uliftYoneda.{u + 1}.obj T ⟶
      (Space.completionSheaf B S hS M.obj.left (Space.pointsMap B S hS _ ν ⁻¹' Z)).obj :=
    hpbP.lift m sT hcomm
  have ht₁ : t₁ ≫ (Space.completionSheafMap B S hS ν Z).hom = sT := hpbP.lift_snd _ _ _
  let t₂ : uliftYoneda.{u + 1}.obj T ⟶ M.obj.left ⋙ uliftFunctor.{u + 1} :=
    t₁ ≫ FormalSpace.completionToULift B S hS M.obj.left hVt.isSheaf
      (Space.pointsMap B S hS _ ν ⁻¹' Z)
  have ht₂ : t₂ ≫ Functor.whiskerRight ν uliftFunctor.{u + 1} =
      sT ≫ FormalSpace.completionToULift B S hS (yoneda.obj V) hVsp.isSheaf Z := by
    simp only [t₂, Category.assoc]
    rw [← FormalSpace.completionSheafMap_comp_completionToULift B S hS hVt.isSheaf hVsp.isSheaf,
      ← Category.assoc, ht₁]
  have hsZ : (FormalSpace.completionToULift B S hS (yoneda.obj V) hVsp.isSheaf Z).app (op Zo) sZ =
      ULift.up z :=
    congrArg (fun φ => φ.app (op Zo) ⟨ULift.up z, hz⟩)
      (FormalSpace.toSheafify_comp_completionToULift B S hS (yoneda.obj V) hVsp.isSheaf Z)
  let t₃ : yoneda.obj T ⟶ M.obj.left := yonedaEquiv.symm (uliftYonedaEquiv t₂).down
  have ht₃ : t₃ ≫ ν = yoneda.map (b ≫ z) := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
    have h := congrArg (fun φ : uliftYoneda.{u + 1}.obj T ⟶ yoneda.obj V ⋙ uliftFunctor.{u + 1} =>
      (uliftYonedaEquiv φ).down) ht₂
    simp only [uliftYonedaEquiv_comp, sT, Equiv.apply_symm_apply] at h
    refine h.trans ?_
    rw [NatTrans.naturality_apply, hsZ]
    rfl
  -- an affine étale chart of `Ṽ` through that point
  have hVtln : Space.HasEtaleLocalProperty B S hS M.obj.left
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V) :=
    Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hVt hVsp ν hνft
      (FormalSpace.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyNoetherian hVsp hVN')
  obtain ⟨P, hPaff, -, v', hv'et, Z', p, z₂, hz₂, hyr⟩ :=
    Space.exists_affine_etale_chart_through hVtln t₃ y
  let r : P ⟶ V := yoneda.preimage (v' ≫ ν)
  have hr : yoneda.map r = v' ≫ ν := yoneda.map_preimage _
  have hret : Etale (Tf.map r) := by
    have h1 : Space.IsEtale B S hS (yoneda.map r) := by
      rw [hr]
      exact Space.isEtale_comp B S hS ((Space.isEtale_iff_presheaf_of_yoneda B S hS v').2 hv'et)
        hνet
    exact (Space.presheaf_yoneda_map_iff B S hS
      AlgebraicGeometry.Etale.etale_isStableUnderBaseChange r).1
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS _).1 h1)
  have hz₂r : z₂ ≫ r = p ≫ b ≫ z := yoneda.map_injective (by
    rw [Functor.map_comp, hr, ← Category.assoc, hz₂, Category.assoc, ht₃, ← Functor.map_comp])
  refine ⟨P, r, hret, hPaff, ?_, Wi i, f i, haff i, hnoeth i, het i, ?_⟩
  · obtain ⟨z', hz'⟩ := hyr
    refine ⟨Tf.map z₂ z', ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hz₂r, Functor.map_comp, Functor.map_comp,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz']
    show Tf.map z (b.left.hom y) = v
    rw [hy, hx]
  · have h₁ : Space.pointsMap B S hS _ (yoneda.map r) ⁻¹' Z ⊆
        Space.pointsMap B S hS _ v' ⁻¹' (Space.pointsMap B S hS _ ν ⁻¹' Z) := by
      rw [hr, Space.pointsMap_comp]
      exact fun _ h => h
    refine ⟨Space.completionSheafRestrict B S hS v' _ _ h₁ ≫ ε ≫ pullback.fst (f i) xhat, ?_⟩
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc ε, hε,
      ← Space.completionSheafRestrict_self B S hS ν Z (fun _ h => h), ← Category.assoc]
    congr 1
    exact (completionSheafRestrict_eq_comp hr.symm h₁ (fun _ h => h) fun _ h => h).symm

/-- The sheafified universe lift of the presheaf represented by an object of the site is the
sheaf it represents. -/
noncomputable def sheafifiedULiftIsoYoneda (V : BigFppfOver B S hS) :
    Space.sheafifiedULift B S hS (yoneda.obj V) ≅
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V :=
  (plusPlusSheafIsoPresheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).app
    (yoneda.obj V ⋙ uliftFunctor.{u + 1})

variable (hS) in
/-- An open `O` of `S`, as an object of the site. -/
noncomputable abbrev openObj (O : S.Opens) (hO : B.Contains (O : Scheme.{u})) :
    BigFppfOver B S hS :=
  BigFppfOver.mk B S hS hO O.ι

/-- **The étale neighbourhood of `exists_etale_affine_chart_factorization` over an affine open of
`S`**: moreover `P` maps into an affine open `O` of `S`, and the chart `W₀` maps to the sheaf
represented by `O`, so that all its quotient stages lie over `O`. It is obtained by applying
`exists_etale_affine_chart_factorization` to the open subscheme `V ×_S O` of `V` and to the
open formal subspace `W ×_S O` of `W`. -/
theorem exists_etale_affine_chart_factorization_over {W : FormalSpace.FppfSheaf B S hS}
    (hW : FormalSpace.IsLocallyNoetherian B S hS W) {V : BigFppfOver B S hS}
    (hVN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V))
    {Z : Set (Space.points B S hS (yoneda.obj V))} (hZ : IsClosed Z)
    (xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ W)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (hv : (Space.schemePointsHomeomorph B S hS V).symm v ∈ Z) :
    ∃ (O : S.Opens) (_ : IsAffineOpen O) (hO : B.Contains (O : Scheme.{u}))
      (P : BigFppfOver B S hS) (r : P ⟶ V), Etale ((BigFppfOver.toScheme B S hS).map r) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj P) ∧
      v ∈ Set.range ((BigFppfOver.toScheme B S hS).map r) ∧
      Set.range (B.inclusion.map P.hom).base ⊆ (O : Set S) ∧
      ∃ (W₀ : FormalSpace.FppfSheaf B S hS) (ω : W₀ ⟶ W),
        FormalSpace.IsAffineFormalAlgebraicSpace B S hS W₀ ∧ FormalSpace.IsNoetherian B S hS W₀ ∧
          FormalSpace.IsRepresentableEtale B S hS ω ∧
          Nonempty (W₀ ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
            (openObj hS O hO)) ∧
          ∃ x₀ : Space.completionSheaf B S hS (yoneda.obj P)
              (Space.pointsMap B S hS _ (yoneda.map r) ⁻¹' Z) ⟶ W₀,
            x₀ ≫ ω = Space.completionSheafRestrict B S hS (yoneda.map r) _ Z (fun _ hz => hz) ≫
              xhat := by
  classical
  let Tf := BigFppfOver.toScheme B S hS
  let Y := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let sV : Tf.obj V ⟶ S := B.inclusion.map V.hom
  obtain ⟨O, hO, hvO, -⟩ := exists_isAffineOpen_mem_and_subset (x := sV.base v)
    (U := ⊤) trivial
  have hOC : B.Contains (O : Scheme.{u}) := B.contains_of_mono O.ι hS
  let Oobj := openObj hS O hOC
  -- the open subscheme `V ×_S O` of `V`
  let VOs : (Tf.obj V).Opens := sV ⁻¹ᵁ O
  have hVOC : B.Contains (VOs : Scheme.{u}) := B.contains_of_mono VOs.ι V.left.2
  let VO : BigFppfOver B S hS := BigFppfOver.mk B S hS hVOC (VOs.ι ≫ sV)
  let jO : VO ⟶ V := Over.homMk (ObjectProperty.homMk VOs.ι)
    (by apply ObjectProperty.hom_ext; rfl)
  have hjO : Tf.map jO = VOs.ι := rfl
  have hjOet : Etale (Tf.map jO) := by
    rw [hjO]
    exact HasRingHomProperty.of_isOpenImmersion RingHom.Etale.containsIdentities
  have hVON : IsLocallyNoetherian (Tf.obj VO) := by
    show IsLocallyNoetherian (VOs : Scheme.{u}); infer_instance
  let kO : VO ⟶ Oobj := Over.homMk (ObjectProperty.homMk (sV.resLE O VOs le_rfl)) (by
    apply ObjectProperty.hom_ext
    exact Scheme.Hom.resLE_comp_ι _ _)
  let v' : Tf.obj VO := ⟨v, hvO⟩
  have hv'v : Tf.map jO v' = v := rfl
  let ZO := Space.pointsMap B S hS _ (yoneda.map jO) ⁻¹' Z
  have hZO : IsClosed ZO := hZ.preimage (Space.continuous_pointsMap B S hS _)
  have hv' : (Space.schemePointsHomeomorph B S hS VO).symm v' ∈ ZO := by
    show Space.pointsMap B S hS _ (yoneda.map jO) _ ∈ Z
    rwa [Space.schemePointsHomeomorph_symm_naturality, hv'v]
  -- the open formal subspace `W ×_S O` of `W`
  have hOet : Etale (Tf.map (terminal.from Oobj)) := by
    have h := Space.toScheme_map_terminal_from B S hS Oobj
    have : Etale (Tf.map (terminal.from Oobj) ≫ (Space.toSchemeTerminalIso B S hS).hom) := by
      rw [h]; show Etale O.ι; infer_instance
    exact (MorphismProperty.cancel_right_of_respectsIso (P := @Etale) _ _).1 this
  let tW : W ⟶ Y.obj (⊤_ (BigFppfOver B S hS)) :=
    (FormalSpace.fppfYonedaTerminalIsTerminal B S hS).from W
  have hYO : FormalSpace.IsRepresentableEtale B S hS (Y.map (terminal.from Oobj)) :=
    FormalSpace.isRepresentableEtale_sheafifiedYoneda_map B S hS _ hOet
  let W' := pullback (Y.map (terminal.from Oobj)) tW
  have hsndW : FormalSpace.IsRepresentableEtale B S hS
      (pullback.snd (Y.map (terminal.from Oobj)) tW) :=
    FormalSpace.isRepresentableEtale_pullback_snd B S hS _ tW hYO
  have hW'f : FormalSpace.IsFormalAlgebraicSpace B S hS W' :=
    FormalSpace.isFormalAlgebraicSpace_pullback_of_isRepresentableEtale B S hS _ tW hW.1 hYO
  have hW' := isLocallyNoetherian_of_isRepresentableEtale _ hW'f hW hsndW
  -- the restriction of `x̂` to `(V ×_S O)_{/Z}`, as a morphism into `W ×_S O`
  let cmap : Space.completionSheaf B S hS (yoneda.obj VO) ZO ⟶ Y.obj VO :=
    Space.completionSheafInclusion B S hS (yoneda.obj VO) ZO ≫ (sheafifiedULiftIsoYoneda VO).hom
  let xhatO := Space.completionSheafRestrict B S hS (yoneda.map jO) ZO Z (fun _ h => h) ≫ xhat
  let xhat' : Space.completionSheaf B S hS (yoneda.obj VO) ZO ⟶ W' :=
    pullback.lift (cmap ≫ Y.map kO) xhatO
      ((FormalSpace.fppfYonedaTerminalIsTerminal B S hS).hom_ext _ _)
  obtain ⟨P, r', hret', hPaff, ⟨p₀, hp₀⟩, W₀, ω', hW₀a, hW₀n, hω', x₀, hx₀⟩ :=
    exists_etale_affine_chart_factorization hW' hVON hZO xhat' v' hv'
  refine ⟨O, hO, hOC, P, r' ≫ jO, ?_, hPaff, ⟨p₀, ?_⟩, ?_, W₀,
    ω' ≫ pullback.snd (Y.map (terminal.from Oobj)) tW, hW₀a, hW₀n, hω'.comp B S hS hsndW,
    ⟨ω' ≫ pullback.fst _ _⟩, x₀, ?_⟩
  · rw [Functor.map_comp]
    have := hret'
    infer_instance
  · rw [Functor.map_comp, Scheme.Hom.comp_apply, hp₀]
    exact hv'v
  · rintro y ⟨p, rfl⟩
    have h1 : B.inclusion.map P.hom = Tf.map r' ≫ Tf.map kO ≫ O.ι := by
      rw [← map_comp_inclusion_map_hom r',
        show B.inclusion.map VO.hom = Tf.map kO ≫ O.ι from (map_comp_inclusion_map_hom kO).symm]
    rw [h1, ← Scheme.Opens.range_ι O]
    exact ⟨(Tf.map r' ≫ Tf.map kO) p, rfl⟩
  · refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ pullback.snd (Y.map (terminal.from Oobj)) tW) hx₀).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (Space.completionSheafRestrict B S hS (yoneda.map r') _ ZO (fun _ h => h) ≫ ·)
      (pullback.lift_snd _ _ _)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (· ≫ xhat) (completionSheafRestrict_eq_comp (Functor.map_comp yoneda r' jO).symm
      (fun _ h => h) (fun _ h => h) (fun x hx => by
        rw [Set.mem_preimage, Functor.map_comp, Space.pointsMap_comp]; exact hx)).symm

/-- **An affine étale neighbourhood of the limit comes from an affine étale neighbourhood of a
stage** (Stacks 01ZM, 09ZM and 07RP). For a cofiltered limit `V = lim V_i` of affine locally
Noetherian objects of the site and an étale `r : P ⟶ V` with `P` affine there are a stage `i`, an
affine object `N` étale over `V_i` and an isomorphism `P ≅ V ×_{V_i} N` over `V`. -/
theorem exists_stage_etale_model {I : Type u} [Category.{u} I] [IsCofiltered I]
    {D : I ⥤ LocallyNoetherianOver B S hS} {κ : Cone D}
    (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
    (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i)))
    {P : BigFppfOver B S hS} (r : P ⟶ κ.pt.obj) (hr : Etale ((BigFppfOver.toScheme B S hS).map r))
    (hP : IsAffine ((BigFppfOver.toScheme B S hS).obj P)) :
    ∃ (i : I) (N : BigFppfOver B S hS) (q : N ⟶ (D.obj i).obj)
      (_ : Etale ((BigFppfOver.toScheme B S hS).map q)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj N) ∧
        ∃ θ : P ≅ pullback (κ.π.app i).hom q, θ.hom ≫ pullback.fst _ _ = r := by
  classical
  let D' := D ⋙ LocallyNoetherianOver.toScheme B S hS
  let c' := (LocallyNoetherianOver.toScheme B S hS).mapCone κ
  have : ∀ i, IsAffine (D'.obj i) := hD
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D'.map f) := fun f => inferInstance
  have : EssentiallySmall.{u} I := inferInstance
  let n : (BigFppfOver.toScheme B S hS).obj P ⟶ c'.pt := (BigFppfOver.toScheme B S hS).map r
  have : Etale n := hr
  obtain ⟨i, Ni, φ, hNia, hNif⟩ := exists_affine_over_model D' c' hκ n
  -- étaleness at a later stage
  let Y₀ : Over (D'.obj i) := Over.mk (𝟙 _)
  let f₀ : Ni ⟶ Y₀ := Over.homMk Ni.hom
  have := hNif
  have : LocallyOfFinitePresentation f₀.left := hNif
  have : Etale ((Over.pullback (c'.π.app i)).map f₀).left := by
    have h1 : ((Over.pullback (c'.π.app i)).map f₀).left ≫ pullback.snd (𝟙 _) (c'.π.app i) =
        pullback.snd Ni.hom (c'.π.app i) := by
      simp only [f₀]
      exact pullback.lift_snd _ _ _
    have h2 : φ.hom.left ≫ n = pullback.snd Ni.hom (c'.π.app i) := Over.w φ.hom
    have : Etale (((Over.pullback (c'.π.app i)).map f₀).left ≫
        pullback.snd (𝟙 _) (c'.π.app i)) := by
      rw [h1, ← h2]; infer_instance
    exact (MorphismProperty.cancel_right_of_respectsIso (P := @Etale) _ _).1 this
  have := hNia
  have : CompactSpace Y₀.left := (inferInstance : CompactSpace (D'.obj i))
  have : QuasiSeparatedSpace Y₀.left := (inferInstance : QuasiSeparatedSpace (D'.obj i))
  obtain ⟨e, he⟩ := exists_etale_pullback_of_isLimit D' c' hκ i Ni Y₀ f₀
  let j := e.left
  let Nj : Over (D'.obj j) := (Over.pullback (D'.map e.hom)).obj Ni
  have hNjet : Etale Nj.hom := by
    have h : ((Over.pullback (D'.map e.hom)).map f₀).left ≫ pullback.snd (𝟙 _) (D'.map e.hom) =
        Nj.hom := pullback.lift_snd _ _ _
    rw [← h]
    infer_instance
  have : IsAffine Nj.left := isAffine_overPullback_left D' e.hom Ni
  have := hNjet
  have : LocallyOfFinitePresentation Nj.hom := inferInstance
  have : AlgebraicGeometry.QuasiCompact Nj.hom := quasiCompact_of_compactSpace Nj.hom
  have hNc : B.Contains Nj.left :=
    Space.contains_of_locallyOfFiniteType_of_quasiCompact B S hS (Y₀ := (D.obj j).obj) Nj.hom
  let ψ : (Over.pullback (c'.π.app j)).obj Nj ≅ Over.mk n := Over.stageRebaseIso D' c' e.hom Ni ≪≫ φ
  obtain ⟨θ, hθ, -⟩ := Space.exists_iso_pullback_of_overIso (κ.π.app j).hom r Nj hNc ψ
  exact ⟨j, Space.overSiteObj Nj hNc, Space.overSiteToBase Nj hNc, hNjet, ‹IsAffine Nj.left›, θ, hθ⟩

namespace ContractionSituation

/-- **The property of an element `ξ = (Z, u', x̂)` of `F(V)` isolated by the reduction to an affine
`W` in the proof of Stacks 0GI5**: `V` maps into an affine open `O` of `S`, and its formal
component `x̂ : V_{/Z} ⟶ W` factors through a representable étale morphism `ω : W₀ ⟶ W` out of a
Noetherian affine formal algebraic space lying over `O`. -/
def FactorsThroughAffineChart (c : ContractionSituation B S hS) (V : LocallyNoetherianOver B S hS)
    (ξ : Triple c V.obj) : Prop :=
  ∃ (O : S.Opens) (_ : IsAffineOpen O) (hO : B.Contains (O : Scheme.{u})),
    Set.range (B.inclusion.map V.obj.hom).base ⊆ (O : Set S) ∧
    ∃ (W₀ : FormalSpace.FppfSheaf B S hS) (ω : W₀ ⟶ c.W),
      FormalSpace.IsAffineFormalAlgebraicSpace B S hS W₀ ∧ FormalSpace.IsNoetherian B S hS W₀ ∧
        FormalSpace.IsRepresentableEtale B S hS ω ∧
        Nonempty (W₀ ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          (openObj hS O hO)) ∧
        ∃ x₀ : Space.completionSheaf B S hS (yoneda.obj V.obj) ξ.Z ⟶ W₀, x₀ ≫ ω = ξ.xhat

/-- **The reduction to an affine `W` in the proof of Stacks 0GI5** (the `hfactor` input of
`AlgebraicGeometry.Artin.ContractionSituation.limitPreserving_contractionFunctor_of_core`). For a
cofiltered limit `V = lim V_i` of affine locally Noetherian objects, an element `ξ ∈ F(V)` and a
point `v` of `V` in `Z`, there are a stage `i` and an affine `N` étale over `V_i` such that `v`
lies in the image of `V ×_{V_i} N` and the restriction of `ξ` to `V ×_{V_i} N` has its formal
component factoring through a Noetherian affine formal algebraic space étale over `W`. -/
theorem exists_factorsThroughAffineChart (c : ContractionSituation B S hS) {J : Type u}
    [Category.{u} J] [IsCofiltered J] {D : J ⥤ LocallyNoetherianOver B S hS} {κ : Cone D}
    (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
    (hD : ∀ j, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj j)))
    (ξ : Triple c κ.pt.obj) (v : (LocallyNoetherianOver.toScheme B S hS).obj κ.pt)
    (hv : (Space.schemePointsHomeomorph B S hS κ.pt.obj).symm v ∈ ξ.Z) :
    ∃ (i : J) (N : BigFppfOver B S hS) (q : N ⟶ (D.obj i).obj)
      (hq : Etale ((BigFppfOver.toScheme B S hS).map q)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj N) ∧
      v ∈ Set.range ((BigFppfOver.toScheme B S hS).map (pullback.fst (κ.π.app i).hom q)).base ∧
      FactorsThroughAffineChart c (baseChangeCone κ q hq).pt
        (mapTriple c (pullback.fst (κ.π.app i).hom q) ξ) := by
  obtain ⟨O, hO, hOC, P, r, hret, hPaff, ⟨p₀, hp₀⟩, hPO, W₀, ω, hW₀a, hW₀n, hω, hπ, x₀, hx₀⟩ :=
    exists_etale_affine_chart_factorization_over c.isLocallyNoetherian_W κ.pt.property
      ξ.isClosed_Z ξ.xhat v hv
  obtain ⟨i, N, q, hq, hN, θ, hθ⟩ := exists_stage_etale_model hκ hD r hret hPaff
  have hfst : θ.inv ≫ r = pullback.fst (κ.π.app i).hom q := by rw [← hθ, Iso.inv_hom_id_assoc]
  refine ⟨i, N, q, hq, hN, ⟨(BigFppfOver.toScheme B S hS).map θ.hom p₀, ?_⟩, O, hO, hOC, ?_, W₀,
    ω, hW₀a, hW₀n, hω, hπ, ?_⟩
  · rwa [← Scheme.Hom.comp_apply, ← Functor.map_comp, hθ]
  · rintro _ ⟨y, rfl⟩
    show (B.inclusion.map (pullback (κ.π.app i).hom q).hom) y ∈ O
    rw [← map_comp_inclusion_map_hom θ.inv]
    exact hPO ⟨(BigFppfOver.toScheme B S hS).map θ.inv y, rfl⟩
  · have h : Space.pointsMap B S hS _ (yoneda.map (pullback.fst (κ.π.app i).hom q)) ⁻¹' ξ.Z ⊆
        Space.pointsMap B S hS _ (yoneda.map θ.inv) ⁻¹'
          (Space.pointsMap B S hS _ (yoneda.map r) ⁻¹' ξ.Z) := by
      intro x hx
      rwa [Set.mem_preimage, Set.mem_preimage, ← Function.comp_apply
        (f := Space.pointsMap B S hS _ (yoneda.map r)), ← Space.pointsMap_comp, ← Functor.map_comp,
        hfst]
    refine ⟨Space.completionSheafRestrict B S hS (yoneda.map θ.inv) _ _ h ≫ x₀, ?_⟩
    refine (Category.assoc _ _ _).trans ?_
    rw [hx₀]
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (· ≫ ξ.xhat) (completionSheafRestrict_eq_comp
      (by rw [← Functor.map_comp, hfst]) h (fun _ hz => hz) fun _ hx => hx).symm

/-- **Limit preservation of the contraction functor from the affine-chart case** (Stacks 0GI5,
with the reduction to an affine `W` done): it suffices that every element over the limit of any
system whose formal component factors through a Noetherian affine formal algebraic space étale
over `W` comes from a stage. -/
theorem limitPreserving_contractionFunctor_of_affineChart
    (c : ContractionSituation B S hS)
    (hcore : ∀ (J : Type u) [Category.{u} J] [IsCofiltered J]
      (D' : J ⥤ LocallyNoetherianOver B S hS) (κ' : Cone D'),
      IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ') →
      (∀ j, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D'.obj j))) →
      IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ'.pt) →
      ∀ ξ' : Triple c κ'.pt.obj, FactorsThroughAffineChart c κ'.pt ξ' →
        ∃ (j : J) (y : Triple c (D'.obj j).obj), mapTriple c (κ'.π.app j).hom y = ξ') :
    LimitPreserving.{u, u + 1, u, u, u + 1, u} (LocallyNoetherianOver.toScheme B S hS)
      (contractionFunctor c) :=
  limitPreserving_contractionFunctor_of_core c (FactorsThroughAffineChart c) hcore
    fun _ _ _ _ _ hκ hD _ ξ v hv => exists_factorsThroughAffineChart c hκ hD ξ v hv

end ContractionSituation

end AlgebraicGeometry.Artin

end
