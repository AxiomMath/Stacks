module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackKernelInjective

/-!
# Deformations of `Coh_{X/Y}` with trivial base are determined by their extension classes

Let `x` and `y` be deformations of `x₀ = (Spec k, g₀, 𝒢₀)` over the same `k[M]` with trivial
base, and suppose the extensions `0 ⟶ 𝒢₀ ⊗ M ⟶ r_*ℱ ⟶ 𝒢₀ ⟶ 0` of
`AlgebraicGeometry.Space.CoherentSituation.kernelExtension` have the same class in
`Ext¹(𝒢₀, 𝒢₀ ⊗ M)`. By Stacks 06XV the middle terms are isomorphic compatibly with the two outer
terms and the square-zero functions, so by Stacks 08AI the modules of `x` and `y` are isomorphic
compatibly with the identifications with `𝒢₀`; together with the identification of the test
schemes this is a reversed arrow of `Coh_{X/Y}` from `y` to `x` over the identity of `k[M]`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.exists_morphism_of_extensionClass_eq`.

## Implementation notes

The two test schemes are equal but are not the same expression, and the comparisons of
Stacks 03LU between the inverse images along their base changes can only be computed once the
two are literally identified: the kernel does not finish comparing two inverse images of modules
along morphisms of algebraic spaces which agree only up to unfolding. So the comparison is made
in `AlgebraicGeometry.Space.CoherentSituation.exists_iso_of_extensionClass_eq_of_eq`, which takes
the two test schemes as variables with an equation between them and substitutes it away before
anything is computed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation Deformation.Artin

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe w' u

/-- A finite-dimensional `k`-vector space is a module over `kᵐᵒᵖ`, through `MulOpposite.unop`. -/
local instance {k : Type u} [Field k] (V : FGModuleCat.{u} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

/-- The actions of `k` and `kᵐᵒᵖ` on a finite-dimensional `k`-vector space agree. -/
local instance {k : Type u} [Field k] (V : FGModuleCat.{u} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

namespace AlgebraicGeometry.Space

namespace CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

attribute [local instance] cohCategory predefCategory

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
  (x₀ : CoherentObject D)
  (hx₀ : D.cohQ.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

variable {M : FGModuleCat.{u} k}

omit [CommRing Λ] [Algebra Λ k] in
/-- The square-zero functions `M ⟶ Γ(T)` of a test scheme identified with `Spec k[M]`. -/
def specFunctions (T : SchemesOver D.Y)
    (e : (BigFppfOver.toScheme B S hS).obj T.left = Spec (CommRingCat.of (TrivSqZeroExt k M))) :
    ↥M →+ D.testRing T :=
  (RingEquiv.ofBijective (D.testRingOfSpec T e).hom
    (D.bijective_testRingOfSpec T e)).toAddMonoidHom.comp (TrivSqZeroExt.inrHom k M).toAddMonoidHom

/-- The square-zero functions of a deformation over `k[M]` are the square-zero functions of its
test scheme identified with `Spec k[M]`. -/
theorem fiberFunctions_eq_specFunctions (d : DeformationObject iΛ D.cohQ x₀ hx₀)
    (hd : d.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M) :
    D.fiberFunctions iΛ x₀ hx₀ M d hd =
      D.specFunctions d.point.T (D.toScheme_defPoint iΛ x₀ hx₀ M d hd) := rfl

omit [CommRing Λ] [Algebra Λ k] in
/-- The square-zero functions of two equal test schemes agree. -/
theorem heq_splitFunctions_specFunctions {T₁ T₂ : SchemesOver D.Y} (hT : T₁ = T₂)
    (e₁ : (BigFppfOver.toScheme B S hS).obj T₁.left = Spec (CommRingCat.of (TrivSqZeroExt k M)))
    (e₂ : (BigFppfOver.toScheme B S hS).obj T₂.left = Spec (CommRingCat.of (TrivSqZeroExt k M))) :
    HEq (D.splitFunctions M (D.specFunctions T₁ e₁)) (D.splitFunctions M (D.specFunctions T₂ e₂)) := by
  subst hT
  rfl

omit [CommRing Λ] [Field k] [Algebra Λ k] in
/-- The identity law of Stacks 03LU at a module, along an endomorphism of a test scheme which is
the identity. -/
def idAppOf {T : SchemesOver D.Y} (e : T ⟶ T) (he : e = 𝟙 T)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) :
    (modulePullback B S hS (D.relativeMap e)).obj F ⟶ F := by
  subst he
  exact D.idApp T F

omit [CommRing Λ] [Field k] [Algebra Λ k] in
/-- The identity law of Stacks 03LU along an endomorphism which is the identity is an
isomorphism. -/
instance {T : SchemesOver D.Y} (e : T ⟶ T) (he : e = 𝟙 T)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) : IsIso (D.idAppOf e he F) := by
  subst he
  exact inferInstanceAs (IsIso (D.idApp T F))

omit [CommRing Λ] [Field k] [Algebra Λ k] in
/-- `AlgebraicGeometry.Space.CoherentSituation.compComparison_comp_idApp` along an endomorphism
which is the identity. -/
theorem compComparison_comp_idAppOf {T T' : SchemesOver D.Y} (h : T ⟶ T') (e : T' ⟶ T')
    (he : e = 𝟙 T') (F : Modules.{u, u} B S hS (D.space T').1 (D.space T').2) :
    (D.compComparison h e).hom.app F ≫ (modulePullback B S hS (D.relativeMap h)).map
        (D.idAppOf e he F) =
      eqToHom (congrArg (fun g => (modulePullback B S hS (D.relativeMap g)).obj F)
        ((congrArg (h ≫ ·) he).trans (Category.comp_id h))) := by
  subst he
  exact D.compComparison_comp_idApp h F

variable [HasExt.{w'} (Modules.{u, u} B S hS (D.space x₀.T).1 (D.space x₀.T).2)]

omit [CommRing Λ] [Algebra Λ k] in
/-- **Equal extension classes of two split thickenings over equal test schemes give an
identification of the modules compatible with the identifications with `𝒢₀`**, read through the
comparison of Stacks 03LU for the composite with the identification of the test schemes. -/
theorem exists_iso_of_extensionClass_eq_of_eq (ρ : k ≃+* D.testRing x₀.T)
    {T₁ T₂ : SchemesOver D.Y} (hT : T₁ = T₂) (e : T₁ ⟶ T₂) (he : e = eqToHom hT)
    (σ₁ : x₀.T ⟶ T₁) (σ₂ : x₀.T ⟶ T₂) (hσ : σ₁ ≫ e = σ₂)
    (π₁ : T₁ ⟶ x₀.T) (π₂ : T₂ ⟶ x₀.T) (hπ : π₁ = eqToHom hT ≫ π₂)
    (hi₁ : D.relativeMap σ₁ ≫ D.relativeMap π₁ = 𝟙 _)
    (hi₂ : D.relativeMap σ₂ ≫ D.relativeMap π₂ = 𝟙 _)
    {ι₁ : ↥M →+ Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (D.space T₁).1
        (D.space T₁).2).O)}
    {ι₂ : ↥M →+ Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (D.space T₂).1
        (D.space T₂).2).O)} (hι : HEq ι₁ ι₂)
    (hs₁ : IsSplitThickeningBy B S hS (D.relativeMap π₁) (D.splitRep π₁) (D.relativeMap σ₁) hi₁ M
      (D.splitScalars₀ ρ.toRingHom) (D.splitScalars₁ π₁ ρ.toRingHom) ι₁)
    (hs₂ : IsSplitThickeningBy B S hS (D.relativeMap π₂) (D.splitRep π₂) (D.relativeMap σ₂) hi₂ M
      (D.splitScalars₀ ρ.toRingHom) (D.splitScalars₁ π₂ ρ.toRingHom) ι₂)
    (F₁ : Modules.{u, u} B S hS (D.space T₁).1 (D.space T₁).2)
    (F₂ : Modules.{u, u} B S hS (D.space T₂).1 (D.space T₂).2)
    (ψ₁ : (modulePullback B S hS (D.relativeMap σ₁)).obj F₁ ≅ x₀.F)
    (ψ₂ : (modulePullback B S hS (D.relativeMap σ₂)).obj F₂ ≅ x₀.F)
    (hF₁ : F₁.IsQuasicoherentOnSite) (hF₂ : F₂.IsQuasicoherentOnSite)
    (hflat₁ : ∀ U : SmallEtale B S hS (D.space x₀.T).1,
      IsAffine ((SmallEtale.toOver B S hS (D.space x₀.T).1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
      ∀ n : Fin (Module.finrank k M) → F₁.val.obj (op (retractionChartDiagram B S hS
        (D.relativeMap π₁) (D.splitRep π₁) (D.relativeMap σ₁) hi₁ U).V),
        ∑ j, (ι₁ (ModuleDeformation.stdBasis M j)).1
            (op (retractionChartDiagram B S hS (D.relativeMap π₁) (D.splitRep π₁)
              (D.relativeMap σ₁) hi₁ U).V) • n j = 0 →
          ∀ j, n j ∈ (RingHom.ker (chartDiagramRestrict B S hS (D.relativeMap σ₁)
            (retractionChartDiagram B S hS (D.relativeMap π₁) (D.splitRep π₁)
              (D.relativeMap σ₁) hi₁ U))) •
              (⊤ : Submodule (chartRing B S hS (D.space T₁).1 (D.space T₁).2
                  (retractionChartDiagram B S hS (D.relativeMap π₁) (D.splitRep π₁)
                    (D.relativeMap σ₁) hi₁ U).V)
                (F₁.val.obj (op (retractionChartDiagram B S hS (D.relativeMap π₁) (D.splitRep π₁)
                  (D.relativeMap σ₁) hi₁ U).V))))
    (hflat₂ : ∀ U : SmallEtale B S hS (D.space x₀.T).1,
      IsAffine ((SmallEtale.toOver B S hS (D.space x₀.T).1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
      ∀ n : Fin (Module.finrank k M) → F₂.val.obj (op (retractionChartDiagram B S hS
        (D.relativeMap π₂) (D.splitRep π₂) (D.relativeMap σ₂) hi₂ U).V),
        ∑ j, (ι₂ (ModuleDeformation.stdBasis M j)).1
            (op (retractionChartDiagram B S hS (D.relativeMap π₂) (D.splitRep π₂)
              (D.relativeMap σ₂) hi₂ U).V) • n j = 0 →
          ∀ j, n j ∈ (RingHom.ker (chartDiagramRestrict B S hS (D.relativeMap σ₂)
            (retractionChartDiagram B S hS (D.relativeMap π₂) (D.splitRep π₂)
              (D.relativeMap σ₂) hi₂ U))) •
              (⊤ : Submodule (chartRing B S hS (D.space T₂).1 (D.space T₂).2
                  (retractionChartDiagram B S hS (D.relativeMap π₂) (D.splitRep π₂)
                    (D.relativeMap σ₂) hi₂ U).V)
                (F₂.val.obj (op (retractionChartDiagram B S hS (D.relativeMap π₂) (D.splitRep π₂)
                  (D.relativeMap σ₂) hi₂ U).V))))
    (hr : IsAffineHom B S hS (D.relativeMap π₂).hom)
    (h : letI := retractionLinear B S hS (X₀ := D.space x₀.T) (D.splitScalars₀ ρ.toRingHom)
      (retractionCopowerExtension B S hS F₂ x₀.F ψ₂ hF₂ hs₂ hflat₂).extensionClass =
        (retractionCopowerExtension B S hS F₁ x₀.F ψ₁ hF₁ hs₁ hflat₁).extensionClass) :
    ∃ θ : (modulePullback B S hS (D.relativeMap e)).obj F₂ ≅ F₁,
      eqToHom (congrArg (fun g => (modulePullback B S hS (D.relativeMap g)).obj F₂) hσ.symm) ≫
        (D.compComparison σ₁ e).hom.app F₂ ≫
          (modulePullback B S hS (D.relativeMap σ₁)).map θ.hom ≫ ψ₁.hom = ψ₂.hom := by
  subst hT
  rw [eqToHom_refl, Category.id_comp] at hπ
  subst hπ
  obtain rfl := eq_of_heq hι
  rw [eqToHom_refl] at he
  have hσ' : σ₁ = σ₂ := (Category.comp_id σ₁).symm.trans ((congrArg (σ₁ ≫ ·) he.symm).trans hσ)
  subst hσ'
  obtain ⟨θ₀, hθ₀⟩ := exists_iso_of_extensionClass_retractionCopowerExtension_eq B S hS
    (D.relativeMap π₁) hs₂ hs₁ ψ₂ ψ₁ hF₂ hF₁ hflat₂ hflat₁ hr rfl rfl h
  rw [eqToHom_refl, Category.id_comp] at hθ₀
  refine ⟨asIso (D.idAppOf e he F₂) ≪≫ θ₀, ?_⟩
  rw [Iso.trans_hom, asIso_hom, Functor.map_comp, Category.assoc,
    reassoc_of% (D.compComparison_comp_idAppOf σ₁ e he F₂),
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, hθ₀]

/-- The trivial bases of two deformations over the same `k[M]` agree through the identification of
their test schemes. -/
theorem trivialBase_eq_eqToHom_comp (a b : DeformationObject iΛ D.cohQ x₀ hx₀)
    (ha : a.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (hb : b.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (πa : a.point.T ⟶ x₀.T)
    (hπa : (BigFppfOver.toScheme B S hS).map πa.left =
      eqToHom (D.toScheme_defPoint iΛ x₀ hx₀ M a ha) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) ≫
          eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm)
    (πb : b.point.T ⟶ x₀.T)
    (hπb : (BigFppfOver.toScheme B S hS).map πb.left =
      eqToHom (D.toScheme_defPoint iΛ x₀ hx₀ M b hb) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) ≫
          eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm)
    (hT : b.point.T = a.point.T) : πb = eqToHom hT ≫ πa := by
  refine CostructuredArrow.hom_ext _ _ ((BigFppfOver.toScheme B S hS).map_injective ?_)
  rw [CostructuredArrow.comp_left, CategoryTheory.Functor.map_comp, hπb, hπa,
    CostructuredArrow.eqToHom_left, eqToHom_map, eqToHom_trans_assoc]

/-- **Two deformations over `k[M]` with trivial base whose extensions have the same class are
related by a reversed arrow over the identity of `k[M]`.** -/
theorem exists_morphism_of_extensionClass_eq (a b : DeformationObject iΛ D.cohQ x₀ hx₀)
    (ha : a.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (hb : b.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (πa : a.point.T ⟶ x₀.T)
    (hπa : (BigFppfOver.toScheme B S hS).map πa.left =
      eqToHom (D.toScheme_defPoint iΛ x₀ hx₀ M a ha) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) ≫
          eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm)
    (πb : b.point.T ⟶ x₀.T)
    (hπb : (BigFppfOver.toScheme B S hS).map πb.left =
      eqToHom (D.toScheme_defPoint iΛ x₀ hx₀ M b hb) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) ≫
          eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm)
    (h : letI := D.residueLinear iΛ x₀ hx₀
      (D.kernelExtension iΛ x₀ hx₀ M a ha πa hπa).extensionClass =
        (D.kernelExtension iΛ x₀ hx₀ M b hb πb hπb).extensionClass) :
    ∃ m : DeformationMorphism iΛ D.cohQ x₀ hx₀ a b, m.ringHom = eqToHom (ha.trans hb.symm) := by
  have hT := (D.point_T_eq iΛ x₀ hx₀ a b ha hb πa hπa πb hπb).symm
  have hβ : (D.homOf b.arrow).base ≫ eqToHom hT = (D.homOf a.arrow).base := by
    rw [D.homOf_arrow_base_eq iΛ x₀ hx₀ a b ha hb hT, Category.assoc, eqToHom_trans,
      eqToHom_refl, Category.comp_id]
  haveI := D.isAffine_basePoint iΛ x₀ hx₀
  haveI := D.isAffine_fiberPoint iΛ x₀ hx₀ M a ha
  obtain ⟨θ, hθ⟩ := D.exists_iso_of_extensionClass_eq_of_eq x₀ (D.residueRingEquiv iΛ x₀ hx₀) hT
    (eqToHom hT) rfl (D.homOf b.arrow).base (D.homOf a.arrow).base hβ πb πa
    (D.trivialBase_eq_eqToHom_comp iΛ x₀ hx₀ a b ha hb πa hπa πb hπb hT) _ _
    (D.heq_splitFunctions_specFunctions hT _ _)
    (D.kernel_isSplitThickeningBy iΛ x₀ hx₀ M b hb πb hπb)
    (D.kernel_isSplitThickeningBy iΛ x₀ hx₀ M a ha πa hπa) b.point.F a.point.F
    (D.fiberIso iΛ x₀ hx₀ b) (D.fiberIso iΛ x₀ hx₀ a) b.point.quasicoherent a.point.quasicoherent
    (D.kernel_flat iΛ x₀ hx₀ M b hb πb hπb) (D.kernel_flat iΛ x₀ hx₀ M a ha πa hπa)
    (D.isAffineHom_relativeMap πa) h
  rw [fiberIso_hom, fiberIso_hom] at hθ
  let cm : CoherentHom b.point a.point := ⟨eqToHom hT, θ.hom, inferInstance⟩
  let arrow : b.point ⟶ a.point := (Equiv.cast (D.categoryData.hom_type _ _)).symm cm
  have harrow : D.homOf arrow = cm := Equiv.apply_symm_apply _ _
  have hleft : (D.cohQ.map arrow).left = eqToHom (congrArg (fun T : SchemesOver D.Y =>
      (BigFppfOver.toScheme B S hS).obj T.left) hT) := by
    change (BigFppfOver.toScheme B S hS).map (D.homOf arrow).base.left = _
    rw [harrow]
    change (BigFppfOver.toScheme B S hS).map (eqToHom hT).left = _
    rw [CostructuredArrow.eqToHom_left, eqToHom_map]
  have htri : b.arrow ≫ arrow = a.arrow := by
    apply (Equiv.cast (D.categoryData.hom_type _ _)).injective
    change D.homOf (b.arrow ≫ arrow) = D.homOf a.arrow
    rw [show D.homOf (b.arrow ≫ arrow) = (D.homOf b.arrow).comp (D.homOf arrow) from
      D.categoryData.composition _ _, harrow]
    exact D.comp_mk_eq (D.homOf b.arrow) (eqToHom hT) θ.hom (D.homOf a.arrow) hβ hθ
  refine ⟨⟨eqToHom (ha.trans hb.symm), arrow, htri, ?_⟩, rfl⟩
  rw [hleft, spec_map_eqToHom]
  exact eqToHom_comp_eqToHom_comp_eqToHom_eq _ _ _ _

end CoherentSituation

end AlgebraicGeometry.Space

end
