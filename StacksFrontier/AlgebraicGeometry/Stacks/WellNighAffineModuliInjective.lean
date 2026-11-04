module

public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveGeometricTwoArrows
public import StacksFrontier.AlgebraicGeometry.Stacks.ClassifyingStackUniversallyInjective
public import StacksFrontier.Deformation.Artin.Infinitesimal.TwoFibreBoundary

/-!
# The moduli morphism of a well-nigh affine stack is universally injective

Let `𝒳` be a well-nigh affine algebraic stack with chart `x : U ⟶ 𝒳`, relation `s, t : R ⟶ U` and
moduli morphism `f : 𝒳 ⟶ M = Spec C` (`AlgebraicGeometry.Stack.WellNighAffineChart.moduliMap`).
This file proves that `f` is universally injective, the part of the universal-homeomorphism
assertion of Stacks 0DUP that the source reaches by base change along affine schemes and
Stacks 0DTN.

## Implementation notes

The proof goes through the geometric criterion of Stacks 0CPN, part (3)
(`AlgebraicGeometry.Stack.universallyInjective_of_liftsTwoArrowsAtGeometricPoints`): it suffices
that for an algebraically closed field `k` any two objects `x₁, x₂` of `𝒳` over `Spec k` with the
same image in `M` are isomorphic over `Spec k`. The target `M` is fibred in sets, so the condition
on 2-arrows reduces to that. An object over `Spec k` comes from a `k`-point of `U`: the chart is
surjective, flat and locally of finite presentation, so it lifts along such a cover of `Spec k`,
and that cover has a section because `k` is algebraically closed
(`AlgebraicGeometry.Stack.exists_section_of_isAlgClosed`). Two `k`-points of `U` with the same
image in `M` are joined by a `k`-point of `R`, by Stacks 03BL, part (2)
(`AlgebraicGeometry.GroupoidScheme.comp_objectsToInvariantSpectrum_eq_iff`), and the chart takes
the two ends of a point of `R` to isomorphic objects.

This replaces the source's route through base change along affine schemes, Stacks 0DTZ, 03BK,
09EF and 0DTN by Stacks 0CPN and 03BL (2), which needs no base change of the quotient stack.

## References

* [Stacks Project, Tag 0DUP](https://stacks.math.columbia.edu/tag/0DUP)
* [Stacks Project, Tag 0CPN](https://stacks.math.columbia.edu/tag/0CPN)
* [Stacks Project, Tag 03BL](https://stacks.math.columbia.edu/tag/03BL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.WellNighAffineChart

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (K : WellNighAffineChart.{u, w} B S hS 𝒳)

/-- **An object of `𝒳` over the spectrum of an algebraically closed field comes from a point of
the chart.** -/
theorem exists_chart_point_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k]
    (V : BigFppfOver B S hS) (eV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k))
    (x : 𝒳.val.val.obj) (hx : 𝒳.val.val.p.obj x = V) :
    ∃ (v : V ⟶ K.U) (φ : K.chart.hom.hom.obj (Over.mk v) ⟶ x),
      𝒳.val.val.p.IsHomLift (𝟙 V) φ := by
  obtain ⟨hrep, -⟩ := K.isFinite_chart
  obtain ⟨-, hfp⟩ := K.isRelativelyFinitePresentation_chart
  have hflatP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (spaceProperty B S hS (fun _ _ h => Space.IsFlat B S hS h)) K.chart.hom hrep :=
    (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
      (schemeStack.{u, w} B S hS K.U).property 𝒳.property K.chart.hom hrep).1 K.isFlat_chart
  have hsurjP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) K.chart.hom hrep :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS K.chart hrep).1
      K.isSurjective_chart
  obtain ⟨T', m, -, hlfp, hsurj, z, φ, hφ⟩ :=
    exists_scheme_lift_of_isSurjective_isFlat_isLocallyOfFinitePresentation B S hS K.chart.hom hrep
      (fun T y hy G hG he => ⟨hsurjP T y hy G hG he, hflatP T y hy G hG he,
        (hfp T y hy G hG he).1⟩) V ⟨x, hx⟩
  let W : BigFppfOver B S hS := Over.mk (m ≫ V.hom)
  let mW : W ⟶ V := Over.homMk m rfl
  obtain ⟨σ, hσ⟩ := exists_section_of_isAlgClosed k eV mW hlfp hsurj
  let z' : Over K.U := z
  have hzW : z'.left = W := by
    have : 𝒳.val.val.p.IsHomLift mW φ := hφ
    exact (Functor.congr_obj K.chart.hom.hom.w z).symm.trans (IsHomLift.domain_eq 𝒳.val.val.p mW φ)
  let σ' : V ⟶ z'.left := σ ≫ eqToHom hzW.symm
  let ψ := K.chart.hom.hom.toFunctor.map (Over.homMk σ' rfl : Over.mk (σ' ≫ z'.hom) ⟶ z')
  have h0 : (schemeStack.{u, w} B S hS K.U).val.val.p.IsHomLift σ'
      (Over.homMk σ' rfl : Over.mk (σ' ≫ z'.hom) ⟶ z') :=
    IsHomLift.of_fac' _ _ _ rfl rfl (by rfl)
  have hψ : 𝒳.val.val.p.IsHomLift σ' ψ :=
    Functor.isHomLift_map_of_comp_eq K.chart.hom.hom.w σ' _
  have hφ' : 𝒳.val.val.p.IsHomLift (eqToHom hzW ≫ mW) φ :=
    (IsHomLift.lift_eqToHom_comp_iff _ _ _ _).2 hφ
  have hcomp : 𝒳.val.val.p.IsHomLift (σ' ≫ eqToHom hzW ≫ mW) (ψ ≫ φ) := by
    infer_instance
  have hbase : σ' ≫ eqToHom hzW ≫ mW = 𝟙 V := by
    simp only [σ', Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, hσ]
  rw [hbase] at hcomp
  exact ⟨σ' ≫ z'.hom, ψ ≫ φ, hcomp⟩

/-- The image in `M` of the chart at a point `v : V ⟶ U` is the point `V ⟶ U ⟶ M`. -/
theorem moduliMap_obj_chart (V : BigFppfOver B S hS) (v : V ⟶ K.U) :
    K.moduliMap.hom.hom.obj (K.chart.hom.hom.obj (Over.mk v)) =
      ⟨V, Discrete.mk (v ≫ K.quotientMap)⟩ :=
  (congrArg (fun L : (schemeFibredCategory B S hS K.U).val ⥤ᵇ
      (fibredCategory B S hS K.moduliSpace.obj).val => L.obj (Over.mk v))
    K.chart_comp_moduliMap).trans
    (associatedMap_obj B S hS (yoneda.map K.quotientMap) _)

/-- **Two points of the chart over the spectrum of an algebraically closed field with the same
image in `M` are joined by a point of the relation**, by Stacks 03BL, part (2). -/
theorem exists_relation_point_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k]
    (V : BigFppfOver B S hS) (eV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k))
    (v₁ v₂ : V ⟶ K.U) (h : v₁ ≫ K.quotientMap = v₂ ≫ K.quotientMap) :
    ∃ ρ : V ⟶ K.V, ρ ≫ K.t = v₁ ∧ ρ ≫ K.s = v₂ := by
  have h' : (BigFppfOver.toScheme B S hS).map v₁ ≫
        GroupoidScheme.objectsToInvariantSpectrum K.groupoidScheme =
      (BigFppfOver.toScheme B S hS).map v₂ ≫
        GroupoidScheme.objectsToInvariantSpectrum K.groupoidScheme := by
    have := congrArg (BigFppfOver.toScheme B S hS).map h
    rwa [Functor.map_comp, Functor.map_comp, toScheme_map_quotientMap] at this
  have hsch : (eV.inv ≫ (BigFppfOver.toScheme B S hS).map v₁) ≫
        GroupoidScheme.objectsToInvariantSpectrum K.groupoidScheme =
      (eV.inv ≫ (BigFppfOver.toScheme B S hS).map v₂) ≫
        GroupoidScheme.objectsToInvariantSpectrum K.groupoidScheme :=
    (Category.assoc _ _ _).trans ((congrArg (fun g => eV.inv ≫ g) h').trans
      (Category.assoc _ _ _).symm)
  obtain ⟨r, hrt, hrs⟩ :=
    (GroupoidScheme.comp_objectsToInvariantSpectrum_eq_iff K.groupoidScheme k _ _).1 hsch
  have hover : (eV.hom ≫ r) ≫ ((Space.siteToOver B hS).obj K.V).hom =
      ((Space.siteToOver B hS).obj V).hom := by
    have ht := Over.w K.groupoidScheme.target
    have h₂ := Over.w ((Space.siteToOver B hS).map v₁)
    exact ((Category.assoc _ _ _).trans (congrArg (fun g => eV.hom ≫ r ≫ g) ht.symm)).trans
      ((congrArg (fun g => eV.hom ≫ g) ((Category.assoc _ _ _).symm.trans
        (congrArg (fun g => g ≫ K.groupoidScheme.objects.hom) hrt))).trans
        (((congrArg (fun g => eV.hom ≫ g) (Category.assoc _ _ _)).trans
          (Iso.hom_inv_id_assoc eV _)).trans h₂))
  let ρ : V ⟶ K.V := (Space.siteToOver B hS).preimage (Over.homMk (eV.hom ≫ r) hover)
  have hρ : (Space.siteToOver B hS).map ρ = Over.homMk (eV.hom ≫ r) hover :=
    Functor.map_preimage _ _
  refine ⟨ρ, ?_, ?_⟩ <;> apply (Space.siteToOver B hS).map_injective <;>
    rw [Functor.map_comp, hρ] <;> apply Over.OverMorphism.ext
  · exact (Category.assoc _ _ _).trans ((congrArg (fun g => eV.hom ≫ g) hrt).trans
      (Iso.hom_inv_id_assoc eV _))
  · exact (Category.assoc _ _ _).trans ((congrArg (fun g => eV.hom ≫ g) hrs).trans
      (Iso.hom_inv_id_assoc eV _))

/-- **The chart takes the two ends of a point of the relation to isomorphic objects**: objects
`x₁, x₂` of `𝒳` over `V` lifted from the chart at `ρ ≫ t` and `ρ ≫ s` are isomorphic over `V`. -/
private theorem exists_isHomLift_id_of_relation_point (V : BigFppfOver B S hS)
    {x₁ x₂ : 𝒳.val.val.obj} {v₁ v₂ : V ⟶ K.U} (φ₁ : K.chart.hom.hom.obj (Over.mk v₁) ⟶ x₁)
    (hφ₁ : 𝒳.val.val.p.IsHomLift (𝟙 V) φ₁) (φ₂ : K.chart.hom.hom.obj (Over.mk v₂) ⟶ x₂)
    (hφ₂ : 𝒳.val.val.p.IsHomLift (𝟙 V) φ₂) (ρ : V ⟶ K.V) (hρt : ρ ≫ K.t = v₁)
    (hρs : ρ ≫ K.s = v₂) : ∃ α : x₁ ⟶ x₂, 𝒳.val.val.p.IsHomLift (𝟙 V) α := by
  obtain ⟨ψ, hψ⟩ := K.vertical (Over.mk ρ)
  have e₁ : K.chart.hom.hom.obj (Over.mk v₁) =
      K.chart.hom.hom.obj ((schemeFibredCategoryMap B S hS K.t).hom.obj (Over.mk ρ)) :=
    congrArg (fun v => K.chart.hom.hom.obj (Over.mk v)) hρt.symm
  have e₂ : K.chart.hom.hom.obj ((schemeFibredCategoryMap B S hS K.s).hom.obj (Over.mk ρ)) =
      K.chart.hom.hom.obj (Over.mk v₂) :=
    congrArg (fun v => K.chart.hom.hom.obj (Over.mk v)) hρs
  have hψ' : 𝒳.val.val.p.IsHomLift (𝟙 V) ψ := hψ
  have := Deformation.Artin.isIso_of_isHomLift_id_fibered 𝒳.val.val.p 𝒳.val.property φ₁ hφ₁
  have := Deformation.Artin.isIso_of_isHomLift_id_fibered 𝒳.val.val.p 𝒳.val.property ψ hψ'
  have h₁' : 𝒳.val.val.p.IsHomLift (𝟙 V) (inv φ₁) :=
    IsHomLift.lift_id_inv_isIso 𝒳.val.val.p V φ₁
  have h₂' : 𝒳.val.val.p.IsHomLift (𝟙 V) (eqToHom e₁) :=
    IsHomLift.eqToHom_domain_lift_id e₁ (Functor.congr_obj K.chart.hom.hom.w (Over.mk v₁))
  have h₃' : 𝒳.val.val.p.IsHomLift (𝟙 V) (inv ψ) := IsHomLift.lift_id_inv_isIso 𝒳.val.val.p V ψ
  have h₄' : 𝒳.val.val.p.IsHomLift (𝟙 V) (eqToHom e₂) :=
    IsHomLift.eqToHom_domain_lift_id e₂ (Functor.congr_obj K.chart.hom.hom.w _)
  exact ⟨inv φ₁ ≫ eqToHom e₁ ≫ inv ψ ≫ eqToHom e₂ ≫ φ₂,
    @IsHomLift.comp_of_lift_id _ _ _ _ 𝒳.val.val.p V _ _ _ _ _ h₁'
      (@IsHomLift.comp_of_lift_id _ _ _ _ 𝒳.val.val.p V _ _ _ _ _ h₂'
        (@IsHomLift.comp_of_lift_id _ _ _ _ 𝒳.val.val.p V _ _ _ _ _ h₃'
          (@IsHomLift.comp_of_lift_id _ _ _ _ 𝒳.val.val.p V _ _ _ _ _ h₄' hφ₂)))⟩

/-- **Stacks 0DUP, universal injectivity: the moduli morphism `f : 𝒳 ⟶ M` of a well-nigh affine
algebraic stack is universally injective.** Two objects of `𝒳` over the spectrum of an
algebraically closed field with the same image in `M` come from points of the chart joined by a
point of the relation, so they are isomorphic; this is condition (3) of Stacks 0CPN. -/
theorem universallyInjective_moduliMap : UniversallyInjective B S hS K.moduliMap := by
  refine universallyInjective_of_liftsTwoArrowsAtGeometricPoints B S hS K.moduliMap ?_
  intro k _ _ V eV x₁ x₂ h₁ h₂ β hβ
  have : (fibredCategory B S hS K.moduliSpace.obj).val.p.IsFiberedInSets :=
    inferInstanceAs (PresheafOfCategories.discreteProjection K.moduliSpace.obj).IsFiberedInSets
  let G := K.moduliMap.hom.hom
  obtain ⟨v₁, φ₁, hφ₁⟩ := K.exists_chart_point_of_isAlgClosed k V eV x₁ h₁
  obtain ⟨v₂, φ₂, hφ₂⟩ := K.exists_chart_point_of_isAlgClosed k V eV x₂ h₂
  have hG : ∀ {a : (fibredCategory B S hS K.moduliSpace.obj).val.obj} {x : 𝒳.val.val.obj}
      (m : a ⟶ G.obj x), (fibredCategory B S hS K.moduliSpace.obj).val.p.IsHomLift (𝟙 V) m →
        𝒳.val.val.p.obj x = V → a = G.obj x := by
    intro a x m hm hx
    have hi : (fibredCategory B S hS K.moduliSpace.obj).val.p.IsHomLift (𝟙 V) (𝟙 (G.obj x)) :=
      IsHomLift.id (p := (fibredCategory B S hS K.moduliSpace.obj).val.p)
        ((Functor.congr_obj G.w x).trans hx)
    exact (@Functor.IsFiberedInSets.eq_of_isHomLift _ _ _ _
      (fibredCategory B S hS K.moduliSpace.obj).val.p _ _ _ (𝟙 V) _ _ _ _ _ hm hi).1
  have hGφ : ∀ {x : 𝒳.val.val.obj} {v : V ⟶ K.U} (φ : K.chart.hom.hom.obj (Over.mk v) ⟶ x),
      𝒳.val.val.p.IsHomLift (𝟙 V) φ → 𝒳.val.val.p.obj x = V →
        G.obj (K.chart.hom.hom.obj (Over.mk v)) = G.obj x :=
    fun φ hφ => hG _ (Functor.isHomLift_map_of_comp_eq G.w (𝟙 V) φ)
  have hx₁₂ : G.obj x₁ = G.obj x₂ := hG β hβ h₂
  have hv : v₁ ≫ K.quotientMap = v₂ ≫ K.quotientMap := by
    have h := ((K.moduliMap_obj_chart V v₁).symm.trans (hGφ φ₁ hφ₁ h₁)).trans
      (hx₁₂.trans ((hGφ φ₂ hφ₂ h₂).symm.trans (K.moduliMap_obj_chart V v₂)))
    injection h with _ hf
    exact Discrete.mk.inj hf
  obtain ⟨ρ, hρt, hρs⟩ := K.exists_relation_point_of_isAlgClosed k V eV v₁ v₂ hv
  obtain ⟨α, hα⟩ := K.exists_isHomLift_id_of_relation_point V φ₁ hφ₁ φ₂ hφ₂ ρ hρt hρs
  refine ⟨α, hα, ?_⟩
  have hGα : (fibredCategory B S hS K.moduliSpace.obj).val.p.IsHomLift (𝟙 V)
      (G.toFunctor.map α) := Functor.isHomLift_map_of_comp_eq G.w (𝟙 V) α
  exact @Functor.IsFiberedInSets.hom_ext_of_isHomLift _ _ _ _
    (fibredCategory B S hS K.moduliSpace.obj).val.p _ _ _ (𝟙 V) _ _ _ _ hGα hβ

end AlgebraicGeometry.Stack.WellNighAffineChart

end
