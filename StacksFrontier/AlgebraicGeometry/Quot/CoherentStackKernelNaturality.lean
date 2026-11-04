module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackKernelExtension

/-!
# Naturality of the extension class of a deformation of `Coh_{X/Y}`

Let `x` and `y` be deformations of `x₀ = (Spec k, g₀, 𝒢₀)` over `k[M]` and `k[N]` with trivial
base, and `x ⟶ y` a morphism of the predeformation category over `k[f] : k[M] ⟶ k[N]` for a
linear map `f : M ⟶ N`. The class of the extension of `y` is the class of that of `x` pushed
out along `𝒢₀ ⊗ f`. In particular the class is invariant under isomorphism of deformations.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.extensionClass_kernelExtension_comp`: the class of
  the extension of the target of a morphism of deformations over `k[f]` is the class of that of
  the source pushed out along `𝒢₀ ⊗ f`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation Deformation.Artin

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe w' u

local instance {k : Type u} [Field k] (V : FGModuleCat.{u} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

local instance {k : Type u} [Field k] (V : FGModuleCat.{u} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

namespace AlgebraicGeometry.Space

namespace CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

attribute [local instance] cohCategory predefCategory

/-! ### The charts of a morphism of test schemes over `T₀` -/

section Charts

variable {T₀ T₁ T₂ : SchemesOver D.Y} (π₁ : T₁ ⟶ T₀) (g : T₂ ⟶ T₁)

/-- The relative maps of `g` and `π₁` compose to the relative map of `g ≫ π₁`. -/
theorem relativeMap_comp_trivialBase :
    D.relativeMap g ≫ D.relativeMap π₁ = D.relativeMap (g ≫ π₁) :=
  (baseChangeMap_comp D.f g π₁).symm

/-- The transfer chart map followed by the map to `T₁` is the map to `T₂` followed by `g`. -/
theorem transferChartMap_comp_splitChartToTest (U : SmallEtale B S hS (D.space T₀).1) :
    yoneda.map (transferChartMap B S hS (D.relativeMap π₁) (D.splitRep π₁)
        (D.relativeMap (g ≫ π₁)) (D.splitRep (g ≫ π₁)) (D.relativeMap g)
        (D.relativeMap_comp_trivialBase π₁ g) U) ≫ yoneda.map (D.splitChartToTest π₁ U) =
      yoneda.map (D.splitChartToTest (g ≫ π₁) U) ≫ yoneda.map g.left := by
  rw [yoneda_map_splitChartToTest, yoneda_map_splitChartToTest]
  have hcomp : (D.relativeMap g).hom ≫ (D.projection T₁).hom =
      (D.projection T₂).hom ≫ yoneda.map g.left :=
    congrArg (fun f ↦ f.hom) (baseChangeMap_comp_inclusion D.f g)
  have hfst := transferChartMap_fst B S hS (D.relativeMap π₁) (D.splitRep π₁)
    (D.relativeMap (g ≫ π₁)) (D.splitRep (g ≫ π₁)) (D.relativeMap g)
    (D.relativeMap_comp_trivialBase π₁ g) U
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (D.projection T₁).hom) hfst).trans
    ((Category.assoc _ _ _).trans ((congrArg ((D.splitRep (g ≫ π₁)).fst U.1.hom ≫ ·) hcomp).trans
      (Category.assoc _ _ _).symm)))

/-- Pulling back a function on `T₁` to a base-changed chart and then along the transfer chart
map is pulling it back along `g` and then to the base-changed chart over `T₂`. -/
theorem chartDiagramRestrict_transferChartDiagram_siteΓ (U : SmallEtale B S hS (D.space T₀).1)
    (t : D.testRing T₁) :
    chartDiagramRestrict B S hS (D.relativeMap g)
        (transferChartDiagram B S hS (D.relativeMap π₁) (D.splitRep π₁)
          (D.relativeMap (g ≫ π₁)) (D.splitRep (g ≫ π₁)) (D.relativeMap g)
          (D.relativeMap_comp_trivialBase π₁ g) U)
        ((siteΓ (D.splitChartToTest π₁ U)).hom t) =
      (siteΓ (D.splitChartToTest (g ≫ π₁) U)).hom ((siteΓ g.left).hom t) := by
  have h : transferChartMap B S hS (D.relativeMap π₁) (D.splitRep π₁)
        (D.relativeMap (g ≫ π₁)) (D.splitRep (g ≫ π₁)) (D.relativeMap g)
        (D.relativeMap_comp_trivialBase π₁ g) U ≫ D.splitChartToTest π₁ U =
      D.splitChartToTest (g ≫ π₁) U ≫ g.left := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp]
    exact D.transferChartMap_comp_splitChartToTest π₁ g U
  have h' := congrArg (fun φ ↦ (siteΓ φ).hom t) h
  rwa [siteΓ_comp, siteΓ_comp] at h'

end Charts

/-! ### Morphisms of deformations over `k[f]` -/

section Morphism

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
  (x₀ : CoherentObject D)
  (hx₀ : D.cohQ.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  {M N : FGModuleCat.{u} k} (f : M ⟶ N)

/-- The underlying morphism of schemes of the base of a reversed arrow over `k[f]`. -/
theorem toScheme_map_morphism_squareZero (a b : DeformationObject iΛ D.cohQ x₀ hx₀)
    (ha : a.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (hb : b.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj N)
    (m : DeformationMorphism iΛ D.cohQ x₀ hx₀ a b)
    (hm : m.ringHom = eqToHom ha ≫ (squareZeroExtensionArtinian.{u, u, u} Λ k).map f ≫
      eqToHom hb.symm) :
    (BigFppfOver.toScheme B S hS).map (D.homOf m.arrow).base.left =
      eqToHom ((D.toScheme_deformationPoint iΛ x₀ hx₀ b).trans
        (congrArg (fun A : ArtinianLocalAlgCat.{u, u, u} Λ k ↦ Spec (CommRingCat.of A)) hb)) ≫
        Spec.map (CommRingCat.ofHom
          ((squareZeroExtensionArtinian.{u, u, u} Λ k).map f).hom.toRingHom) ≫
          eqToHom ((D.toScheme_deformationPoint iΛ x₀ hx₀ a).trans
            (congrArg (fun A : ArtinianLocalAlgCat.{u, u, u} Λ k ↦ Spec (CommRingCat.of A))
              ha)).symm := by
  obtain ⟨ala, pta, ara, basa, aba⟩ := a
  obtain ⟨alb, ptb, arb, basb, abb⟩ := b
  change ala = _ at ha
  change alb = _ at hb
  subst ha hb
  have hr : m.ringHom = (squareZeroExtensionArtinian.{u, u, u} Λ k).map f :=
    hm.trans (by simp)
  rw [D.toScheme_map_morphism_base iΛ x₀ hx₀ m, hr]

variable {iΛ x₀ hx₀ f}

/-- Pullback of functions along the base of a reversed arrow over `k[f]` is `k[f]`. -/
theorem siteΓ_morphismBase {a b : DeformationObject iΛ D.cohQ x₀ hx₀}
    (ha : a.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (hb : b.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj N)
    (m : DeformationMorphism iΛ D.cohQ x₀ hx₀ a b)
    (hm : m.ringHom = eqToHom ha ≫ (squareZeroExtensionArtinian.{u, u, u} Λ k).map f ≫
      eqToHom hb.symm) (z : TrivSqZeroExt k M) :
    (siteΓ (D.homOf m.arrow).base.left).hom (D.fiberRingEquiv iΛ x₀ hx₀ M a ha z) =
      D.fiberRingEquiv iΛ x₀ hx₀ N b hb (TrivSqZeroExt.map f.hom.hom z) := by
  have hg := D.toScheme_map_morphism_squareZero iΛ x₀ hx₀ f a b ha hb m hm
  have key := D.siteΓ_testRingOfSpec (D.homOf m.arrow).base.left
    (D.toScheme_defPoint iΛ x₀ hx₀ M a ha) (D.toScheme_defPoint iΛ x₀ hx₀ N b hb)
    (CommRingCat.ofHom ((squareZeroExtensionArtinian.{u, u, u} Λ k).map f).hom.toRingHom) hg
  exact congrArg (fun φ ↦ φ.hom z) key

/-- Two trivial bases `π`, `π'` of a deformation over `k[M]` are equal. -/
theorem trivialBase_unique {d : DeformationObject iΛ D.cohQ x₀ hx₀}
    (hd : d.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (π π' : d.point.T ⟶ x₀.T)
    (hπ : ∀ c, (siteΓ π.left).hom (D.residueRingEquiv iΛ x₀ hx₀ c) =
      D.fiberRingEquiv iΛ x₀ hx₀ M d hd (algebraMap k (TrivSqZeroExt k M) c))
    (hπ' : ∀ c, (siteΓ π'.left).hom (D.residueRingEquiv iΛ x₀ hx₀ c) =
      D.fiberRingEquiv iΛ x₀ hx₀ M d hd (algebraMap k (TrivSqZeroExt k M) c)) : π = π' := by
  have := D.isAffine_basePoint iΛ x₀ hx₀
  refine CostructuredArrow.hom_ext _ _ ((BigFppfOver.toScheme B S hS).map_injective
    (ext_of_isAffine ?_))
  change siteΓ π.left = siteΓ π'.left
  ext t
  obtain ⟨c, rfl⟩ := (D.residueRingEquiv iΛ x₀ hx₀).surjective t
  exact (hπ c).trans (hπ' c).symm

end Morphism

/-- Equal morphisms of `Coh_{X/Y}` have equal module comparisons, up to the identification of
the inverse images. -/
theorem _root_.AlgebraicGeometry.Space.CoherentHom.fibre_eq_of_eq {A A' : CoherentObject D}
    {m n : CoherentHom A A'} (h : m = n) :
    eqToHom (by rw [h]) ≫ m.fibre = n.fibre := by
  subst h
  simp

/-- The module comparison of a composite of `Coh_{X/Y}`, read through the comparison of
Stacks 03LU for any presentation of the composite base map. -/
theorem _root_.AlgebraicGeometry.Space.CoherentHom.fibre_eq_of_eq_comp
    {A A' A'' : CoherentObject D} (m : CoherentHom A A') (n : CoherentHom A' A'')
    (p : CoherentHom A A'') (h : p = m.comp n)
    (hih : D.relativeMap m.base ≫ D.relativeMap n.base = D.relativeMap p.base) :
    p.fibre = (modulePullbackTriangle B S hS hih).hom.app A''.F ≫
      (modulePullback B S hS (D.relativeMap m.base)).map n.fibre ≫ m.fibre := by
  subst h
  change Functor.fibreComp (D.compComparison m.base n.base) m.fibre n.fibre = _
  unfold Functor.fibreComp
  have e : D.compComparison m.base n.base = modulePullbackTriangle B S hS hih := rfl
  rw [e]
  rfl

/-- The module comparison of the arrow of the source of a reversed arrow of deformations,
through that reversed arrow. -/
theorem homOf_arrow_fibre_eq {Λ' k' : Type u} [CommRing Λ'] [Field k'] [Algebra Λ' k']
    {iΛ' : Spec (.of Λ') ⟶ S} {x₀' : CoherentObject D}
    {hx₀' : D.cohQ.obj x₀' = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k')) ≫ iΛ')}
    {a b : DeformationObject iΛ' D.cohQ x₀' hx₀'} (m : DeformationMorphism iΛ' D.cohQ x₀' hx₀' a b)
    (hih : D.relativeMap (D.homOf b.arrow).base ≫ D.relativeMap (D.homOf m.arrow).base =
      D.relativeMap (D.homOf a.arrow).base) :
    (D.homOf a.arrow).fibre = (modulePullbackTriangle B S hS hih).hom.app a.point.F ≫
      (modulePullback B S hS (D.relativeMap (D.homOf b.arrow).base)).map
        (D.homOf m.arrow).fibre ≫ (D.homOf b.arrow).fibre :=
  CoherentHom.fibre_eq_of_eq_comp D (D.homOf b.arrow) (D.homOf m.arrow) (D.homOf a.arrow)
    ((congrArg D.homOf m.triangle).symm.trans (D.categoryData.composition _ _)) hih

/-- The section of the target of a reversed arrow of deformations followed by its base is the
section of the source. -/
theorem homOf_arrow_base_comp {Λ' k' : Type u} [CommRing Λ'] [Field k'] [Algebra Λ' k']
    {iΛ' : Spec (.of Λ') ⟶ S} {x₀' : CoherentObject D}
    {hx₀' : D.cohQ.obj x₀' = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k')) ≫ iΛ')}
    {a b : DeformationObject iΛ' D.cohQ x₀' hx₀'}
    (m : DeformationMorphism iΛ' D.cohQ x₀' hx₀' a b) :
    (D.homOf b.arrow).base ≫ (D.homOf m.arrow).base = (D.homOf a.arrow).base := by
  have h := congrArg (fun n ↦ (D.homOf n).base) m.triangle
  simp only [homOf] at h
  rwa [D.categoryData.composition] at h

section Naturality

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {x₀ : CoherentObject D}
  {hx₀ : D.cohQ.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  {M N : FGModuleCat.{u} k} {f : M ⟶ N} {a b : DeformationObject iΛ D.cohQ x₀ hx₀}
  (ha : a.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
  (hb : b.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj N)
  (m : DeformationMorphism iΛ D.cohQ x₀ hx₀ a b)
  (hm : m.ringHom = eqToHom ha ≫ (squareZeroExtensionArtinian.{u, u, u} Λ k).map f ≫
      eqToHom hb.symm)

include hm in
/-- The base of a reversed arrow over `k[f]` followed by a trivial base of its source is a trivial
base of its target. -/
theorem morphismBase_comp_trivialBase (πa : a.point.T ⟶ x₀.T)
    (hπa : (BigFppfOver.toScheme B S hS).map πa.left =
      eqToHom (D.toScheme_defPoint iΛ x₀ hx₀ M a ha) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) ≫
          eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm)
    (πb : b.point.T ⟶ x₀.T)
    (hπb : (BigFppfOver.toScheme B S hS).map πb.left =
      eqToHom (D.toScheme_defPoint iΛ x₀ hx₀ N b hb) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k N))) ≫
          eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm) :
    (D.homOf m.arrow).base ≫ πa = πb := by
  refine D.trivialBase_unique hb _ _ (fun c ↦ ?_)
    (D.siteΓ_trivialBase iΛ x₀ hx₀ N b hb πb hπb)
  change (siteΓ (((D.homOf m.arrow).base).left ≫ πa.left)).hom (D.residueRingEquiv iΛ x₀ hx₀ c) = _
  rw [siteΓ_comp]
  change (siteΓ ((D.homOf m.arrow).base).left).hom ((siteΓ πa.left).hom
    (D.residueRingEquiv iΛ x₀ hx₀ c)) = _
  rw [D.siteΓ_trivialBase iΛ x₀ hx₀ M a ha πa hπa]
  exact (D.siteΓ_morphismBase ha hb m hm _).trans (congrArg _ (TrivSqZeroExt.map_inl _ _))

include hm in
/-- Along the transfer chart diagram of the base of a reversed arrow over `k[f]`, the function of
`v ∈ M` on a base-changed chart of the source restricts to the function of `f v` on the
base-changed chart of the target. -/
theorem morphismBase_transfer_functions (πa : a.point.T ⟶ x₀.T)
    (U : SmallEtale B S hS (D.space x₀.T).1) (v : ↥M) :
    chartDiagramRestrict B S hS (D.relativeMap ((D.homOf m.arrow).base))
        (transferChartDiagram B S hS (D.relativeMap πa) (D.splitRep πa)
          (D.relativeMap ((D.homOf m.arrow).base ≫ πa)) (D.splitRep ((D.homOf m.arrow).base ≫ πa))
          (D.relativeMap ((D.homOf m.arrow).base))
          (D.relativeMap_comp_trivialBase πa ((D.homOf m.arrow).base)) U)
        (((D.splitFunctions M (D.fiberFunctions iΛ x₀ hx₀ M a ha)) v).1
          (op ((smallBaseChange B S hS (D.relativeMap πa) (D.splitRep πa)).obj U))) =
      ((D.splitFunctions N (D.fiberFunctions iΛ x₀ hx₀ N b hb)) (f.hom.hom v)).1
        (op ((smallBaseChange B S hS (D.relativeMap ((D.homOf m.arrow).base ≫ πa))
          (D.splitRep ((D.homOf m.arrow).base ≫ πa))).obj U)) := by
  change chartDiagramRestrict B S hS (D.relativeMap ((D.homOf m.arrow).base))
      (transferChartDiagram B S hS (D.relativeMap πa) (D.splitRep πa)
        (D.relativeMap ((D.homOf m.arrow).base ≫ πa)) (D.splitRep ((D.homOf m.arrow).base ≫ πa))
        (D.relativeMap ((D.homOf m.arrow).base))
        (D.relativeMap_comp_trivialBase πa ((D.homOf m.arrow).base)) U)
      ((siteΓ (D.splitChartToTest πa U)).hom (D.fiberFunctions iΛ x₀ hx₀ M a ha v)) =
    (siteΓ (D.splitChartToTest ((D.homOf m.arrow).base ≫ πa) U)).hom
      (D.fiberFunctions iΛ x₀ hx₀ N b hb (f.hom.hom v))
  rw [D.chartDiagramRestrict_transferChartDiagram_siteΓ πa ((D.homOf m.arrow).base) U]
  congr 1
  change (siteΓ ((D.homOf m.arrow).base).left).hom (D.fiberRingEquiv iΛ x₀ hx₀ M a ha
    (TrivSqZeroExt.inr v)) = D.fiberRingEquiv iΛ x₀ hx₀ N b hb (TrivSqZeroExt.inr (f.hom.hom v))
  exact (D.siteΓ_morphismBase ha hb m hm _).trans (congrArg _ (TrivSqZeroExt.map_inr _ _))

variable [HasExt.{w'} (Modules.{u, u} B S hS (D.space x₀.T).1 (D.space x₀.T).2)]

include hm in
/-- Naturality of the extension class, at the trivial base of the target induced by that of
the source. -/
theorem extensionClass_kernelExtension_comp_aux (πa : a.point.T ⟶ x₀.T)
    (hπa : (BigFppfOver.toScheme B S hS).map πa.left =
      eqToHom (D.toScheme_defPoint iΛ x₀ hx₀ M a ha) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) ≫
          eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm)
    (hπb : (BigFppfOver.toScheme B S hS).map ((D.homOf m.arrow).base ≫ πa).left =
      eqToHom (D.toScheme_defPoint iΛ x₀ hx₀ N b hb) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k N))) ≫
          eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm) :
    letI := D.residueLinear iΛ x₀ hx₀
    (D.kernelExtension iΛ x₀ hx₀ M a ha πa hπa).extensionClass.comp
        (Abelian.Ext.mk₀ ((ModuleDeformation.copowerFunctor x₀.F).map f)) (add_zero 1) =
      (D.kernelExtension iΛ x₀ hx₀ N b hb ((D.homOf m.arrow).base ≫ πa) hπb).extensionClass :=
  letI := D.residueLinear iΛ x₀ hx₀
  extensionClass_retractionCopowerExtension_transfer B S hS
    (D.kernel_isSplitThickeningBy iΛ x₀ hx₀ M a ha πa hπa)
    (D.kernel_isSplitThickeningBy iΛ x₀ hx₀ N b hb ((D.homOf m.arrow).base ≫ πa) hπb)
    (D.fiberIso iΛ x₀ hx₀ a) (D.fiberIso iΛ x₀ hx₀ b) _ _ _ _ f
    (D.relativeMap ((D.homOf m.arrow).base))
    (D.relativeMap_comp_trivialBase πa ((D.homOf m.arrow).base))
    (show D.relativeMap ((D.homOf b.arrow).base) ≫
          D.relativeMap ((D.homOf m.arrow).base) = D.relativeMap ((D.homOf a.arrow).base) by
          rw [← baseChangeMap_comp, D.homOf_arrow_base_comp m])
    (D.homOf m.arrow).fibre (by
      rw [fiberIso_hom, fiberIso_hom]
      exact D.homOf_arrow_fibre_eq m _)
    (D.morphismBase_transfer_functions ha hb m hm πa)

include hm in
/-- Naturality of the extension class: for a morphism of deformations over `k[f]`, the class
of the extension of the target is the class of that of the source pushed out along `𝒢₀ ⊗ f`. -/
theorem extensionClass_kernelExtension_comp (πa : a.point.T ⟶ x₀.T)
    (hπa : (BigFppfOver.toScheme B S hS).map πa.left =
      eqToHom (D.toScheme_defPoint iΛ x₀ hx₀ M a ha) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) ≫
          eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm)
    (πb : b.point.T ⟶ x₀.T)
    (hπb : (BigFppfOver.toScheme B S hS).map πb.left =
      eqToHom (D.toScheme_defPoint iΛ x₀ hx₀ N b hb) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k N))) ≫
          eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm) :
    letI := D.residueLinear iΛ x₀ hx₀
    (D.kernelExtension iΛ x₀ hx₀ M a ha πa hπa).extensionClass.comp
        (Abelian.Ext.mk₀ ((ModuleDeformation.copowerFunctor x₀.F).map f)) (add_zero 1) =
      (D.kernelExtension iΛ x₀ hx₀ N b hb πb hπb).extensionClass := by
  obtain rfl := D.morphismBase_comp_trivialBase ha hb m hm πa hπa πb hπb
  exact D.extensionClass_kernelExtension_comp_aux ha hb m hm πa hπa hπb

end Naturality

end CoherentSituation

end AlgebraicGeometry.Space

end
