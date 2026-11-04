module

public import StacksFrontier.Algebra.Homology.RightDerivedEdge

/-!
# Compatibilities of the edge morphism of a composite of right derived functors

Let `P : A ⥤ B` preserve injective objects and let `Q : B ⥤ D` be additive.  The edge morphism
`Stacks.Cohomology.RightDerivedEdge.edge P Q n : Rⁿ Q ∘ P ⟶ Rⁿ (Q ∘ P)` is characterised by
`Stacks.Cohomology.RightDerivedEdge.edge_app_eq`: any comparison of injective resolutions that
preserves the augmentation computes it.  This file derives from that characterisation the two
compatibilities of the edge morphism which a functoriality argument along a change of site
needs.

* **Naturality in the second functor.**  A natural transformation `τ : Q ⟶ Q'` commutes with
  the edge morphisms of `(P, Q)` and `(P, Q')`.
* **Pasting along a transformation of the first functor.**  Let `G₁ : A ⥤ B₁`,
  `G₂ : A ⥤ B₂` and `K : B₂ ⥤ B₁` preserve injective objects, let `α : G₁ ⟶ G₂ ⋙ K` and let
  `T : B₁ ⥤ D` be additive.  Then the map `Rⁿ(G₁ ⋙ T) ⟶ Rⁿ(G₂ ⋙ K ⋙ T)` induced by `α`,
  preceded by the edge morphism of `(G₁, T)`, is the map `Rⁿ T (G₁ X) ⟶ Rⁿ T (K (G₂ X))`
  induced by `α`, followed by the edge morphisms of `(K, T)` and of `(G₂, K ⋙ T)`.

In the geometric case `G₁ = (u₁)_*`, `G₂ = (u₂)_*` are restrictions of sheaves along two
functors of sites into a site `𝒞`, `K = f_*` is a direct image and `T = Γ(-)`, the second
statement says that the restriction map `Hⁿ(u₁ U₁, F) ⟶ Hⁿ(u₂ U₂, F)` of cohomology on `𝒞` is,
under the collapse isomorphisms with the two smaller sites, the pullback map along `f` composed
with the map induced by `α`.

## Main results

* `Stacks.Cohomology.RightDerivedEdge.edge_app_comp_rightDerived_whiskerLeft`: naturality of
  the edge morphism in the second functor.
* `Stacks.Cohomology.RightDerivedEdge.edge_app_comp_rightDerived_whiskerRight`: the pasting
  law.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 01FA](https://stacks.math.columbia.edu/tag/01FA)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Stacks.Cohomology.RightDerivedEdge

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasInjectiveResolutions A]
  {B₁ : Type u₂} [Category.{v₂} B₁] [Abelian B₁] [HasInjectiveResolutions B₁]
  {B₂ : Type u₄} [Category.{v₄} B₂] [Abelian B₂] [HasInjectiveResolutions B₂]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]

/-- **The edge morphism is natural in the second functor.**  For `τ : Q ⟶ Q'` the square formed
by the edge morphisms of `(P, Q)` and `(P, Q')` and the maps of right derived functors induced by
`τ` commutes. -/
theorem edge_app_comp_rightDerived_whiskerLeft (P : A ⥤ B₁) [P.Additive]
    [P.PreservesInjectiveObjects] {Q Q' : B₁ ⥤ D} [Q.Additive] [Q'.Additive] (τ : Q ⟶ Q')
    (n : ℕ) (X : A) :
    (edge P Q n).app X ≫ (NatTrans.rightDerived (Functor.whiskerLeft P τ) n).app X =
      (NatTrans.rightDerived τ n).app (P.obj X) ≫ (edge P Q' n).app X := by
  let I := injectiveResolution X
  let J := injectiveResolution (P.obj X)
  have e₁ := edge_app_eq P Q n I J (resolutionComparison P X)
    (ι_f_zero_comp_resolutionComparison P X)
  have e₂ := edge_app_eq P Q' n I J (resolutionComparison P X)
    (ι_f_zero_comp_resolutionComparison P X)
  change _ = _ ≫ (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map _ ≫
    (isoRightDerivedObjComp P Q I n).inv at e₁
  change _ = _ ≫ (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map _ ≫
    (isoRightDerivedObjComp P Q' I n).inv at e₂
  have r₁ : (NatTrans.rightDerived (Functor.whiskerLeft P τ) n).app X =
      (isoRightDerivedObjComp P Q I n).hom ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℕ)).app
            ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) ≫
        (isoRightDerivedObjComp P Q' I n).inv :=
    InjectiveResolution.rightDerived_app_eq _ I n
  rw [e₁, e₂, r₁, InjectiveResolution.rightDerived_app_eq τ J n]
  simp only [assoc, Iso.inv_hom_id_assoc]
  refine congrArg (fun t => (J.isoRightDerivedObj Q n).hom ≫ t) ?_
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  refine congrArg (fun t => (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map t ≫
    (isoRightDerivedObjComp P Q' I n).inv) ?_
  ext k
  exact τ.naturality ((resolutionComparison P X).f k)

omit [Abelian B₁] [HasInjectiveResolutions B₁] [Abelian B₂] [HasInjectiveResolutions B₂] in
/-- The augmentation chase behind `edge_app_comp_rightDerived_whiskerRight`, stated over variable
objects: at the data of interest the sources are degree-zero terms of single complexes, across
which the rewriting tactics cannot see. -/
private theorem aug_chase (K : B₂ ⥤ B₁) {W V₁ V₂ T₁ : B₁} {P₀ P₁ P₂ : B₂}
    (i : W ⟶ V₁) (φ : V₁ ⟶ V₂) (a : V₂ ⟶ K.obj P₂) (d : V₁ ⟶ T₁) (ψ : T₁ ⟶ K.obj P₁)
    (χ : P₁ ⟶ P₂) (j : K.obj P₀ ⟶ T₁) (m : P₀ ⟶ P₁) (b : W ⟶ K.obj P₀) (g : W ⟶ V₂) (g' : P₀ ⟶ P₂)
    (h₁ : i ≫ φ = g) (h₄ : i ≫ d = b ≫ j) (h₂ : j ≫ ψ = K.map m) (h₃ : m ≫ χ = g')
    (hn : g ≫ a = b ≫ K.map g') :
    i ≫ φ ≫ a = i ≫ d ≫ ψ ≫ K.map χ := by
  rw [reassoc_of% h₁, hn, reassoc_of% h₄, reassoc_of% h₂, ← K.map_comp, h₃]

/-- **The pasting law for edge morphisms.**  Let `G₁ : A ⥤ B₁`, `G₂ : A ⥤ B₂` and
`K : B₂ ⥤ B₁` preserve injective objects, let `α : G₁ ⟶ G₂ ⋙ K` and let `T : B₁ ⥤ D` be
additive.  Then, at every object `X` and in every degree,

  `edge(G₁, T) ≫ Rⁿ(α ▷ T) = Rⁿ T (α_X) ≫ edge(K, T) ≫ edge(G₂, K ⋙ T)`

as maps `Rⁿ T (G₁ X) ⟶ Rⁿ (G₂ ⋙ K ⋙ T) X`. -/
theorem edge_app_comp_rightDerived_whiskerRight (G₁ : A ⥤ B₁) (G₂ : A ⥤ B₂) (K : B₂ ⥤ B₁)
    [G₁.Additive] [G₂.Additive] [K.Additive] [G₁.PreservesInjectiveObjects]
    [G₂.PreservesInjectiveObjects] [K.PreservesInjectiveObjects] (α : G₁ ⟶ G₂ ⋙ K)
    (T : B₁ ⥤ D) [T.Additive] (n : ℕ) (X : A) :
    (edge G₁ T n).app X ≫
        (NatTrans.rightDerived (Functor.whiskerRight α T ≫ (Functor.associator _ _ _).hom)
          n).app X =
      (T.rightDerived n).map (α.app X) ≫ (edge K T n).app (G₂.obj X) ≫
        (edge G₂ (K ⋙ T) n).app X := by
  let I := injectiveResolution X
  let L := injectiveResolution (G₁.obj X)
  let M := injectiveResolution (G₂.obj X)
  let N := injectiveResolution (K.obj (G₂.obj X))
  let c := ComplexShape.up ℕ
  let H := HomologicalComplex.homologyFunctor D c n
  -- `Rⁿ(G₂ ⋙ K ⋙ T)` computed on `I`, with the complex spelled `T (K (G₂ I))`.
  let e : ((G₂ ⋙ K ⋙ T).rightDerived n).obj X ≅
      H.obj ((T.mapHomologicalComplex c).obj ((K.mapHomologicalComplex c).obj
        ((G₂.mapHomologicalComplex c).obj I.cocomplex))) :=
    I.isoRightDerivedObj (G₂ ⋙ K ⋙ T) n
  have e₁ := edge_app_eq G₁ T n I L (resolutionComparison G₁ X)
    (ι_f_zero_comp_resolutionComparison G₁ X)
  change _ = _ ≫ H.map ((T.mapHomologicalComplex c).map (resolutionComparison G₁ X)) ≫
    (isoRightDerivedObjComp G₁ T I n).inv at e₁
  have e₂ := edge_app_eq K T n M N (resolutionComparison K (G₂.obj X))
    (ι_f_zero_comp_resolutionComparison K (G₂.obj X))
  change _ = _ ≫ H.map ((T.mapHomologicalComplex c).map (resolutionComparison K (G₂.obj X))) ≫
    (isoRightDerivedObjComp K T M n).inv at e₂
  have e₃ := edge_app_eq G₂ (K ⋙ T) n I M (resolutionComparison G₂ X)
    (ι_f_zero_comp_resolutionComparison G₂ X)
  change _ = (isoRightDerivedObjComp K T M n).hom ≫
    H.map ((T.mapHomologicalComplex c).map ((K.mapHomologicalComplex c).map
      (resolutionComparison G₂ X))) ≫ e.inv at e₃
  have hα : (NatTrans.mapHomologicalComplex (Functor.whiskerRight α T ≫
      (Functor.associator _ _ _).hom) c).app I.cocomplex =
      (T.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex α c).app I.cocomplex) := by
    ext k
    exact Category.comp_id _
  have r₁ : (NatTrans.rightDerived (Functor.whiskerRight α T ≫
      (Functor.associator _ _ _).hom) n).app X =
      (isoRightDerivedObjComp G₁ T I n).hom ≫
        H.map ((T.mapHomologicalComplex c).map
          ((NatTrans.mapHomologicalComplex α c).app I.cocomplex)) ≫ e.inv := by
    rw [InjectiveResolution.rightDerived_app_eq _ I n, hα]
    rfl
  have r₂ := InjectiveResolution.isoRightDerivedObj_hom_naturality (α.app X) L N
    (InjectiveResolution.desc (α.app X) N L) (InjectiveResolution.desc_commutes_zero _ _ _) T n
  rw [e₁, r₁, e₂, e₃, ← cancel_epi (L.isoRightDerivedObj T n).inv]
  rw [← Iso.eq_comp_inv] at r₂
  rw [r₂]
  simp only [assoc, Iso.inv_hom_id_assoc]
  have hinj : ∀ k, Injective (((K.mapHomologicalComplex c).obj
      ((G₂.mapHomologicalComplex c).obj I.cocomplex)).X k) := fun k =>
    K.injective_obj_of_injective (G₂.injective_obj_of_injective (I.injective k))
  have w : L.ι.f 0 ≫ (resolutionComparison G₁ X ≫
      (NatTrans.mapHomologicalComplex α c).app I.cocomplex).f 0 =
      L.ι.f 0 ≫ (InjectiveResolution.desc (α.app X) N L ≫ resolutionComparison K (G₂.obj X) ≫
        (K.mapHomologicalComplex c).map (resolutionComparison G₂ X)).f 0 := by
    have h₁ := ι_f_zero_comp_resolutionComparison G₁ X
    have h₂ := ι_f_zero_comp_resolutionComparison K (G₂.obj X)
    have h₃ := ι_f_zero_comp_resolutionComparison G₂ X
    have h₄ := InjectiveResolution.desc_commutes_zero (α.app X) N L
    exact aug_chase K (L.ι.f 0) ((resolutionComparison G₁ X).f 0) (α.app _)
      ((InjectiveResolution.desc (α.app X) N L).f 0) ((resolutionComparison K (G₂.obj X)).f 0)
      ((resolutionComparison G₂ X).f 0) (N.ι.f 0) (M.ι.f 0) (α.app X)
      (G₁.map (I.ι.f 0)) (G₂.map (I.ι.f 0)) h₁ h₄ h₂ h₃ (α.naturality (I.ι.f 0))
  have key := homologyMap_map_eq_of_aug T L hinj _ _ w n
  simp only [Functor.map_comp, HomologicalComplex.homologyMap_comp] at key
  exact (reassoc_of% key) e.inv

end Stacks.Cohomology.RightDerivedEdge
