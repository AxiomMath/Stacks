module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DerivedTwistComposition

/-!
# Transport of a twisted endomorphism along the outer pair of functors

Let `P : 𝒞 ⥤ 𝒞` be an additive functor preserving injective objects, and let
`F₁ : 𝒞 ⥤ 𝒟`, `F₂ : 𝒟 ⥤ ℰ` and `G₁ : 𝒞 ⥤ 𝒟'`, `G₂ : 𝒟' ⥤ ℰ` be two pairs of additive functors
with `F₁` and `G₁` preserving injective objects, together with comparisons
`θ : P ⋙ F₁ ≅ F₁`, `θ' : P ⋙ G₁ ≅ G₁` and an isomorphism `ν : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂` of the
composites. A twist `τ : K ⟶ P(K)` of a bounded below complex induces an endomorphism of
`RF₂(RF₁(K))` and one of `RG₂(RG₁(K))`
(`CategoryTheory.Functor.derivedTwistEndo`). If `ν` is compatible with `θ` and `θ'`, the natural
isomorphism `RF₂ ∘ RF₁ ≅ R(F₂ ∘ F₁) ≅ R(G₂ ∘ G₁) ≅ RG₂ ∘ RG₁` attached to `ν` intertwines them.

## Main definitions

* `CategoryTheory.Functor.outerTwistIso`: the natural isomorphism `RF₂ ∘ RF₁ ≅ RG₂ ∘ RG₁`.

## Main results

* `CategoryTheory.Functor.twistComparison_comp_outerTwistIso_hom`: its chain model.
* `CategoryTheory.Functor.derivedTwistEndo_outerTwistIso`: it intertwines the twisted
  endomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁

namespace CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard

section Outer

variable {C D D' E : Type u₁} [Category.{v₁} C] [Category.{v₁} D] [Category.{v₁} D']
  [Category.{v₁} E] [Abelian C] [Abelian D] [Abelian D'] [Abelian E] [EnoughInjectives C]
  [EnoughInjectives D] [EnoughInjectives D']
  (P : C ⥤ C) (F₁ : C ⥤ D) (F₂ : D ⥤ E) (G₁ : C ⥤ D') (G₂ : D' ⥤ E) [P.Additive]
  [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive] [P.PreservesInjectiveObjects]
  [F₁.PreservesInjectiveObjects] [G₁.PreservesInjectiveObjects]
  (ν : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)

/-- **The natural isomorphism `RF₂ ∘ RF₁ ≅ RG₂ ∘ RG₁` attached to `ν : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂`**:
the composition comparisons of [Stacks, Tag 05T2] on both sides, and the invariance of right
derivation under the isomorphism `ν`. -/
public def outerTwistIso :
    F₁.rightDerivedFunctorPlus ⋙ F₂.rightDerivedFunctorPlus ≅
      G₁.rightDerivedFunctorPlus ⋙ G₂.rightDerivedFunctorPlus :=
  (rightDerivedFunctorPlusCompIso F₁ F₂).symm ≪≫
    Stacks.EtaleCohomology.rightDerivedFunctorPlusIsoOfCompIso F₁ F₂ (G₁ ⋙ G₂) ν ≪≫
      rightDerivedFunctorPlusCompIso G₁ G₂

/-- The componentwise `ν : F₂(F₁(K)) ≅ G₂(G₁(K))`, as a morphism of bounded below complexes. -/
public abbrev outerCompMap (K : CochainComplex.Plus C) :
    F₂.mapCochainComplexPlus.obj (F₁.mapCochainComplexPlus.obj K) ⟶
      G₂.mapCochainComplexPlus.obj (G₁.mapCochainComplexPlus.obj K) :=
  ObjectProperty.homMk ((NatTrans.mapHomologicalComplex ν.hom _).app K.obj)

/-- **Chain model of the outer transport isomorphism.**  The comparison
`F₂(F₁(K)) ⟶ RF₂(RF₁(K))` followed by the isomorphism is the componentwise `ν` followed by the
comparison `G₂(G₁(K)) ⟶ RG₂(RG₁(K))`. -/
public lemma twistComparison_comp_outerTwistIso_hom (K : CochainComplex.Plus C) :
    twistComparison F₁ F₂ K ≫ (outerTwistIso F₁ F₂ G₁ G₂ ν).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map (outerCompMap F₁ F₂ G₁ G₂ ν K) ≫ twistComparison G₁ G₂ K := by
  have hF := mapCochainComplexPlusDerivedUnit_comp F₁ F₂ (rightDerivedFunctorPlusComp F₁ F₂)
    (rightDerivedFunctorPlusComp_fac F₁ F₂) K
  have hG := mapCochainComplexPlusDerivedUnit_comp G₁ G₂ (rightDerivedFunctorPlusComp G₁ G₂)
    (rightDerivedFunctorPlusComp_fac G₁ G₂) K
  have hν := mapCochainComplexPlusDerivedUnit_app_comp_rightDerivedFunctorPlusIsoOfCompIso_hom
    F₁ F₂ (G₁ ⋙ G₂) ν K
  have hcΘ : (rightDerivedFunctorPlusCompIso F₁ F₂).hom.app (DerivedCategory.Plus.Q.obj K) ≫
      (outerTwistIso F₁ F₂ G₁ G₂ ν).hom.app (DerivedCategory.Plus.Q.obj K) =
      (Stacks.EtaleCohomology.rightDerivedFunctorPlusIsoOfCompIso F₁ F₂ (G₁ ⋙ G₂) ν).hom.app
          (DerivedCategory.Plus.Q.obj K) ≫
        (rightDerivedFunctorPlusCompIso G₁ G₂).hom.app (DerivedCategory.Plus.Q.obj K) :=
    Iso.hom_inv_id_app_assoc _ _ _
  rw [show twistComparison F₁ F₂ K = _ from hF.symm, show twistComparison G₁ G₂ K = _ from hG.symm]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hcΘ).trans ((reassoc_of% hν) _))

/-- **The outer transport isomorphism against the resolution comparisons.**  For a
quasi-isomorphism `ψ : K ⟶ T` into a bounded below complex of injectives, the isomorphism is read
on `T` off the componentwise `ν`. -/
public lemma outerTwistIso_hom_comp_twistResolutionIso {K T : CochainComplex.Plus C} (ψ : K ⟶ T)
    [QuasiIso ψ.hom] (hT : ∀ n, Injective (T.obj.X n)) :
    DerivedCategory.Plus.ι.map ((outerTwistIso F₁ F₂ G₁ G₂ ν).hom.app
        (DerivedCategory.Plus.Q.obj K)) ≫ (twistResolutionIso G₁ G₂ ψ hT).hom =
      (twistResolutionIso F₁ F₂ ψ hT).hom ≫
        DerivedCategory.Q.map (outerCompMap F₁ F₂ G₁ G₂ ν T).hom := by
  have := isIso_twistComparison F₁ F₂ T hT
  have := isIso_twistComparison G₁ G₂ T hT
  have hn := (outerTwistIso F₁ F₂ G₁ G₂ ν).hom.naturality (DerivedCategory.Plus.Q.map ψ)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  have hc := twistComparison_comp_outerTwistIso_hom F₁ F₂ G₁ G₂ ν T
  have hc' : (outerTwistIso F₁ F₂ G₁ G₂ ν).hom.app (DerivedCategory.Plus.Q.obj T) ≫
      CategoryTheory.inv (twistComparison G₁ G₂ T) =
      CategoryTheory.inv (twistComparison F₁ F₂ T) ≫
        DerivedCategory.Plus.Q.map (outerCompMap F₁ F₂ G₁ G₂ ν T) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, hc, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  change DerivedCategory.Plus.ι.map _ ≫ DerivedCategory.Plus.ι.map _ =
    DerivedCategory.Plus.ι.map _ ≫ DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Q.map (outerCompMap F₁ F₂ G₁ G₂ ν T))
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  change (outerTwistIso F₁ F₂ G₁ G₂ ν).hom.app (DerivedCategory.Plus.Q.obj K) ≫
      (G₂.rightDerivedFunctorPlus.map
        (G₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ)) ≫
        CategoryTheory.inv (twistComparison G₁ G₂ T)) =
    (F₂.rightDerivedFunctorPlus.map
      (F₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ)) ≫
        CategoryTheory.inv (twistComparison F₁ F₂ T)) ≫
      DerivedCategory.Plus.Q.map (outerCompMap F₁ F₂ G₁ G₂ ν T)
  rw [← Category.assoc, ← hn, Category.assoc, hc', Category.assoc]

variable (θ : P ⋙ F₁ ≅ F₁) (θ' : P ⋙ G₁ ≅ G₁)

/-- **Transport of a twisted endomorphism along the outer pair.**  If
`F₂(θ) ≫ ν = ν ≫ G₂(θ')`, the outer transport isomorphism intertwines the endomorphism of
`RF₂(RF₁(K))` induced by a twist `τ` with the endomorphism of `RG₂(RG₁(K))` induced by `τ`. -/
public theorem derivedTwistEndo_outerTwistIso
    (hν : ∀ X : C, F₂.map (θ.hom.app X) ≫ ν.hom.app X =
      ν.hom.app (P.obj X) ≫ G₂.map (θ'.hom.app X))
    (K : CochainComplex.Plus C) (τ : K ⟶ P.mapCochainComplexPlus.obj K) :
    derivedTwistEndo P F₁ F₂ θ K τ ≫
        (outerTwistIso F₁ F₂ G₁ G₂ ν).hom.app (DerivedCategory.Plus.Q.obj K) =
      (outerTwistIso F₁ F₂ G₁ G₂ ν).hom.app (DerivedCategory.Plus.Q.obj K) ≫
        derivedTwistEndo P G₁ G₂ θ' K τ := by
  obtain ⟨a, ha⟩ := K.property
  have : K.obj.IsStrictlyGE a := ha
  have : K.obj.IsGE a := inferInstance
  obtain ⟨R, -, -⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a K.obj
  let T : CochainComplex.Plus C := ⟨R.cocomplex, R.boundedBelow⟩
  let ψ : K ⟶ T := ObjectProperty.homMk R.ι
  have : QuasiIso ψ.hom := R.quasiIso
  have hT : ∀ n, Injective (T.obj.X n) := R.injective
  obtain ⟨g, hg⟩ := exists_twist_lift P ψ hT τ
  have e₁ := twistResolutionIso_hom_comp P F₁ F₂ θ ψ hT τ g hg
  have e₂ := twistResolutionIso_hom_comp P G₁ G₂ θ' ψ hT τ g hg
  have e₃ := outerTwistIso_hom_comp_twistResolutionIso F₁ F₂ G₁ G₂ ν ψ hT
  have hch : twistChainEndo P F₁ F₂ θ T g ≫ outerCompMap F₁ F₂ G₁ G₂ ν T =
      outerCompMap F₁ F₂ G₁ G₂ ν T ≫ twistChainEndo P G₁ G₂ θ' T g := by
    ext n : 2
    have hνn : F₂.map (F₁.map (g.hom.f n)) ≫ ν.hom.app (P.obj (T.obj.X n)) =
        ν.hom.app (T.obj.X n) ≫ G₂.map (G₁.map (g.hom.f n)) :=
      ν.hom.naturality (g.hom.f n)
    change F₂.map (F₁.map (g.hom.f n) ≫ θ.hom.app (T.obj.X n)) ≫ ν.hom.app (T.obj.X n) =
      ν.hom.app (T.obj.X n) ≫ G₂.map (G₁.map (g.hom.f n) ≫ θ'.hom.app (T.obj.X n))
    erw [F₂.map_comp, G₂.map_comp, Category.assoc]
    exact (congrArg (_ ≫ ·) (hν (T.obj.X n))).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) hνn).trans (Category.assoc _ _ _)))
  refine DerivedCategory.Plus.ι.map_injective ?_
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    ← cancel_mono (twistResolutionIso G₁ G₂ ψ hT).hom,
    Category.assoc, Category.assoc, e₂, e₃, reassoc_of% e₁, reassoc_of% e₃]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← ObjectProperty.FullSubcategory.comp_hom,
    ← ObjectProperty.FullSubcategory.comp_hom, hch]

end Outer

end CategoryTheory.Functor

end
