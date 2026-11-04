module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictBridgeCocycle
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModulePushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.TwoIsoCoherenceOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransitionCoherence

/-!
# The squares of the strict components paste

Let `X` be a simplicial algebraic space and `(C_n, 𝒪_n)` the component ringed topoi of the
strict components of `X`. The 2-isomorphisms
`strictComponentTransitionTwoIso X φ : f_φ ∘ realize_n ≅ realize_m ∘ X(φ)_{étale}` of
`AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictComponentTransitionTwoIso` are
pseudonatural: for `ψ : l ⟶ m` and `φ : m ⟶ n` the square of `ψ ≫ φ`, preceded by the canonical
2-isomorphism `f_ψ ∘ f_φ ≅ f_{ψ ≫ φ}` of Stacks 09WE, is the pasting of the squares of `φ` and of
`ψ`, followed by the 2-isomorphism `X(ψ ≫ φ)_{étale} ≅ X(ψ)_{étale} ∘ X(φ)_{étale}` of Stacks
0DE7 (`strictComponentTransitionTwoIso_pasting`). On direct images it is restriction along the
corresponding identity of the comparisons of iterated base changes of Stacks 03G2
(`componentStrictTransitionRealizeIso_inv_comp`), which is checked on the two projections of a
fibre product.

Nothing here is registered.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : SimplicialObject (AlgebraicSpaces B S hS))

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- The strict composite `u_ψ ⋙ u_φ = u_{ψ ≫ φ}` of the transition functors of the strict
components, as an isomorphism with identity components. -/
def componentStrictTransitionCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    componentStrictTransition X ψ ⋙ componentStrictTransition X φ ≅
      componentStrictTransition X (ψ ≫ φ) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun g ↦
    (Category.comp_id _).trans ((strictTransition_map_comp ψ φ g).symm.trans
      (Category.id_comp _).symm))

/-- The direct-image compositor `f_{φ*} ⋙ f_{ψ*} ≅ f_{(ψ ≫ φ)*}` of Stacks 09WE of the strict
components is restriction along `componentStrictTransitionCompIso`. -/
theorem strictSituation_pushforwardCompSymm_eq {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (strictSituation X).pushforwardCompSymm ψ φ =
      Functor.sheafPushforwardContinuousComp' (componentStrictTransitionCompIso X ψ φ)
        (Type (u + 1)) ((strictSituation X).componentTopology l)
        ((strictSituation X).componentTopology m) ((strictSituation X).componentTopology n) := by
  apply Iso.ext
  ext P c x
  refine (congrArg (fun f ↦ f x)
    (SimplicialSiteSituation.pushforwardCompSymm_inl_hom_app_hom_app (strictSimplicialSite X)
      ψ φ P c)).trans ?_
  simp only [eqToIso.inv, eqToHom_app]
  rfl

/-- The transport between the direct images along two equal morphisms of algebraic spaces acts on
sections as restriction along the transport of the base changes. -/
theorem spacesBaseChange_sheafPushforward_eqToHom_app_hom_app {Y Z : AlgebraicSpaces B S hS}
    {f g : Y ⟶ Z} (e : f = g) (M : Sheaf (SpacesEtale.topology B S hS Y) (Type (u + 1)))
    (V : (SpacesEtale B S hS Z)ᵒᵖ) :
    ((eqToHom (congrArg (fun k ↦ (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous
        (Type (u + 1)) (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS Y)) e)).app
        M).hom.app V =
      M.obj.map (eqToHom (congrArg (fun k ↦ (spacesBaseChange B S hS k).functor.obj V.unop)
        e.symm)).op := by
  subst e
  exact (M.obj.map_id _).symm

/-- A chase through four squares, over an arbitrary category. -/
private theorem comp_comp_comp_comp_eq_of_fst {𝒞 : Type*} [Category 𝒞]
    {P₀ P₁ P₂ P₃ P₄ Q₂ Q₃ W V : 𝒞} (A : P₀ ⟶ P₁) (B' : P₁ ⟶ P₂) (C : P₂ ⟶ P₃) (D : P₃ ⟶ P₄)
    (f₄ : P₄ ⟶ V) (f₃ : P₃ ⟶ Q₃) (f₃' : Q₃ ⟶ V) (f₂ : P₂ ⟶ Q₂) (g : Q₂ ⟶ Q₃) (f₂' : Q₂ ⟶ W)
    (fW : W ⟶ V) (h₁ : P₁ ⟶ W) (h₀ : P₀ ⟶ W)
    (hD : D ≫ f₄ = f₃ ≫ f₃') (hC : C ≫ f₃ = f₂ ≫ g) (hg : g ≫ f₃' = f₂' ≫ fW)
    (hB : B' ≫ f₂ ≫ f₂' = h₁) (hA : A ≫ h₁ = h₀) :
    (A ≫ B' ≫ C ≫ D) ≫ f₄ = h₀ ≫ fW := by
  rw [← hA, ← hB]
  simp only [Category.assoc, hD, reassoc_of% hC, hg]

/-- **The comparisons of iterated base changes of the strict components are pseudonatural.** The
comparison `realize_l ⋙ (-)×X(ψ ≫ φ) ⟶ u_{ψ ≫ φ} ⋙ realize_n` is the transport along
`X(φ) ≫ X(ψ) = X(ψ ≫ φ)`, the composition isomorphism of base changes, the base change of the
comparison of `ψ` and the comparison of `φ`. Both sides are maps into a fibre product, compared
on its two projections. -/
theorem componentStrictTransitionRealizeIso_inv_comp {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) (hk : X.map φ.op ≫ X.map ψ.op = X.map (ψ ≫ φ).op)
    (c : (strictSituation X).component l) :
    (componentStrictTransitionRealizeIso X (ψ ≫ φ)).inv.app c =
      eqToHom (congrArg (fun k ↦ (spacesBaseChange B S hS k).functor.obj
          ((componentRealize X l).obj c)) hk.symm) ≫
        (spacesBaseChange_comp B S hS (X.map φ.op) (X.map ψ.op)).inv.app
          ((componentRealize X l).obj c) ≫
        (spacesBaseChange B S hS (X.map φ.op)).functor.map
          ((componentStrictTransitionRealizeIso X ψ).inv.app c) ≫
        (componentStrictTransitionRealizeIso X φ).inv.app
          ((componentStrictTransition X ψ).obj c) := by
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (pullback.hom_ext ?_ ?_))
  · exact (StrictObj.transitionRealizeInv_fst (ψ ≫ φ) c).trans
      (comp_comp_comp_comp_eq_of_fst _ _ _ _ _ _ _ _ _ _ _ _ _
        (StrictObj.transitionRealizeInv_fst φ ((componentStrictTransition X ψ).obj c))
        (spacesBaseChange_map_fst (X.map φ.op)
          ((componentStrictTransitionRealizeIso X ψ).inv.app c))
        (StrictObj.transitionRealizeInv_fst ψ c)
        (spacesBaseChange_comp_inv_app_hom_left_fst_fst (X.map φ.op) (X.map ψ.op)
          ((componentRealize X l).obj c))
        (spacesBaseChange_eqToHom_hom_left_fst hk.symm ((componentRealize X l).obj c))).symm
  · exact (Over.w _).trans (Over.w _).symm

/-- A presheaf of types applied to the opposite of a fourfold composite. -/
private theorem map_comp_comp_comp_op_apply {𝒞 : Type*} [Category 𝒞] (F : 𝒞ᵒᵖ ⥤ Type*)
    {A₀ A₁ A₂ A₃ A₄ : 𝒞} (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₄)
    (x : F.obj (op A₄)) :
    F.map (a ≫ b ≫ c ≫ d).op x = F.map a.op (F.map b.op (F.map c.op (F.map d.op x))) := by
  simp only [op_comp, FunctorToTypes.map_comp_apply]

/-- **The squares of the strict components paste, on direct images.** The identity of
`strictComponentTransitionTwoIso_pasting` on the underlying isomorphisms of direct images of
sheaves of sets, spelled through the direct images along the site functors. -/
theorem componentStrictTransitionPushforwardIso_pasting {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) (hk : X.map φ.op ≫ X.map ψ.op = X.map (ψ ≫ φ).op) :
    haveI := Functor.isContinuous_comp (spacesBaseChange B S hS (X.map ψ.op)).functor
      (spacesBaseChange B S hS (X.map φ.op)).functor (SpacesEtale.topology B S hS (X.obj (op l)))
        (SpacesEtale.topology B S hS (X.obj (op m))) (SpacesEtale.topology B S hS (X.obj (op n)))
    Functor.associator ((componentRealize X n).sheafPushforwardContinuous (Type (u + 1))
      ((strictSituation X).componentTopology n) (SpacesEtale.topology B S hS (X.obj (op n))))
      ((componentStrictTransition X φ).sheafPushforwardContinuous (Type (u + 1))
      ((strictSituation X).componentTopology m) ((strictSituation X).componentTopology n))
      ((componentStrictTransition X ψ).sheafPushforwardContinuous (Type (u + 1))
      ((strictSituation X).componentTopology l) ((strictSituation X).componentTopology m)) ≪≫
      Functor.isoWhiskerLeft ((componentRealize X n).sheafPushforwardContinuous (Type (u + 1))
        ((strictSituation X).componentTopology n) (SpacesEtale.topology B S hS (X.obj (op n))))
        (Functor.sheafPushforwardContinuousComp'
        (componentStrictTransitionCompIso X ψ φ)
        (Type (u + 1)) ((strictSituation X).componentTopology l)
          ((strictSituation X).componentTopology m) ((strictSituation X).componentTopology n)) ≪≫
      (Functor.sheafPushforwardContinuousComp (componentStrictTransition X (ψ ≫ φ))
        (componentRealize X n) (Type (u + 1)) ((strictSituation X).componentTopology l)
        ((strictSituation X).componentTopology n) (SpacesEtale.topology B S hS (X.obj (op n))) ≪≫
      Functor.sheafPushforwardContinuousIso (componentStrictTransitionRealizeIso X (ψ ≫ φ))
        (Type (u + 1)) ((strictSituation X).componentTopology l)
        (SpacesEtale.topology B S hS (X.obj (op n))) ≪≫
      (Functor.sheafPushforwardContinuousComp (componentRealize X l)
        (spacesBaseChange B S hS (X.map ((ψ ≫ φ)).op)).functor (Type (u + 1))
        ((strictSituation X).componentTopology l) (SpacesEtale.topology B S hS (X.obj (op l)))
        (SpacesEtale.topology B S hS (X.obj (op n)))).symm) =
    Functor.isoWhiskerRight (Functor.sheafPushforwardContinuousComp (componentStrictTransition X φ)
      (componentRealize X n) (Type (u + 1)) ((strictSituation X).componentTopology m)
      ((strictSituation X).componentTopology n) (SpacesEtale.topology B S hS (X.obj (op n))) ≪≫
      Functor.sheafPushforwardContinuousIso (componentStrictTransitionRealizeIso X φ) (Type (u + 1))
        ((strictSituation X).componentTopology m) (SpacesEtale.topology B S hS (X.obj (op n))) ≪≫
      (Functor.sheafPushforwardContinuousComp (componentRealize X m)
        (spacesBaseChange B S hS (X.map (φ).op)).functor (Type (u + 1))
        ((strictSituation X).componentTopology m) (SpacesEtale.topology B S hS (X.obj (op m)))
        (SpacesEtale.topology B S hS (X.obj (op n)))).symm)
        ((componentStrictTransition X ψ).sheafPushforwardContinuous (Type (u + 1))
        ((strictSituation X).componentTopology l) ((strictSituation X).componentTopology m)) ≪≫
      Functor.associator ((spacesBaseChange B S hS (X.map φ.op)).functor.sheafPushforwardContinuous
        (Type (u + 1)) (SpacesEtale.topology B S hS (X.obj (op m)))
        (SpacesEtale.topology B S hS (X.obj (op n))))
        ((componentRealize X m).sheafPushforwardContinuous (Type (u + 1))
        ((strictSituation X).componentTopology m) (SpacesEtale.topology B S hS (X.obj (op m))))
        ((componentStrictTransition X ψ).sheafPushforwardContinuous (Type (u + 1))
        ((strictSituation X).componentTopology l) ((strictSituation X).componentTopology m)) ≪≫
      Functor.isoWhiskerLeft
        ((spacesBaseChange B S hS (X.map φ.op)).functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS (X.obj (op m))) (SpacesEtale.topology B S hS (X.obj (op n))))
        (Functor.sheafPushforwardContinuousComp (componentStrictTransition X ψ)
        (componentRealize X m) (Type (u + 1)) ((strictSituation X).componentTopology l)
        ((strictSituation X).componentTopology m) (SpacesEtale.topology B S hS (X.obj (op m))) ≪≫
      Functor.sheafPushforwardContinuousIso (componentStrictTransitionRealizeIso X ψ) (Type (u + 1))
        ((strictSituation X).componentTopology l) (SpacesEtale.topology B S hS (X.obj (op m))) ≪≫
      (Functor.sheafPushforwardContinuousComp (componentRealize X l)
        (spacesBaseChange B S hS (X.map (ψ).op)).functor (Type (u + 1))
        ((strictSituation X).componentTopology l) (SpacesEtale.topology B S hS (X.obj (op l)))
        (SpacesEtale.topology B S hS (X.obj (op m)))).symm) ≪≫
      (Functor.associator ((spacesBaseChange B S hS (X.map φ.op)).functor.sheafPushforwardContinuous
        (Type (u + 1)) (SpacesEtale.topology B S hS (X.obj (op m)))
        (SpacesEtale.topology B S hS (X.obj (op n))))
        ((spacesBaseChange B S hS (X.map ψ.op)).functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS (X.obj (op l))) (SpacesEtale.topology B S hS (X.obj (op m))))
        ((componentRealize X l).sheafPushforwardContinuous (Type (u + 1))
        ((strictSituation X).componentTopology l)
        (SpacesEtale.topology B S hS (X.obj (op l))))).symm ≪≫
      Functor.isoWhiskerRight
        (eqToIso (congrArg
        (fun k => ((spacesBaseChange B S hS k).functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS (X.obj (op l))) (SpacesEtale.topology B S hS (X.obj (op n)))))
        hk.symm) ≪≫
        ((Functor.sheafPushforwardContinuousIso (spacesBaseChange_comp B S hS (X.map φ.op)
          (X.map ψ.op)) (Type (u + 1)) (SpacesEtale.topology B S hS (X.obj (op l)))
          (SpacesEtale.topology B S hS (X.obj (op n)))).symm ≪≫
      (Functor.sheafPushforwardContinuousComp (spacesBaseChange B S hS (X.map ψ.op)).functor
        (spacesBaseChange B S hS (X.map φ.op)).functor (Type (u + 1))
        (SpacesEtale.topology B S hS (X.obj (op l))) (SpacesEtale.topology B S hS (X.obj (op m)))
        (SpacesEtale.topology B S hS (X.obj (op n)))).symm)).symm
        ((componentRealize X l).sheafPushforwardContinuous (Type (u + 1))
        ((strictSituation X).componentTopology l) (SpacesEtale.topology B S hS (X.obj (op l)))) :=
        by
  apply Iso.ext
  ext P c x
  show P.obj.map ((componentStrictTransitionRealizeIso X (ψ ≫ φ)).inv.app c.unop).op
      (P.obj.map (𝟙 (op ((componentRealize X n).obj ((componentStrictTransition X (ψ ≫ φ)).obj
        c.unop)))) x) =
    ((eqToHom (congrArg (fun k ↦ (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous
        (Type (u + 1)) (SpacesEtale.topology B S hS (X.obj (op l)))
        (SpacesEtale.topology B S hS (X.obj (op n)))) hk)).app P).hom.app
        (op ((componentRealize X l).obj c.unop))
      (P.obj.map ((spacesBaseChange_comp B S hS (X.map φ.op) (X.map ψ.op)).inv.app
          ((componentRealize X l).obj c.unop)).op
        (P.obj.map ((spacesBaseChange B S hS (X.map φ.op)).functor.map
            ((componentStrictTransitionRealizeIso X ψ).inv.app c.unop)).op
          (P.obj.map ((componentStrictTransitionRealizeIso X φ).inv.app
            ((componentStrictTransition X ψ).obj c.unop)).op x)))
  refine (congrArg (fun y ↦ P.obj.map ((componentStrictTransitionRealizeIso X (ψ ≫ φ)).inv.app
    c.unop).op y) (FunctorToTypes.map_id_apply P.obj x)).trans ?_
  refine (congrArg (fun z ↦ P.obj.map z.op x)
    (componentStrictTransitionRealizeIso_inv_comp X ψ φ hk c.unop)).trans ?_
  refine (map_comp_comp_comp_op_apply P.obj _ _ _ _ x).trans ?_
  exact (ConcreteCategory.congr_hom
    (spacesBaseChange_sheafPushforward_eqToHom_app_hom_app hk P _) _).symm

/-- **The squares of the strict components paste** (Stacks 04IC). The 2-isomorphism
`f_{ψ ≫ φ} ∘ realize_n ≅ realize_l ∘ X(ψ ≫ φ)`, preceded by `f_ψ ∘ f_φ ≅ f_{ψ ≫ φ}`, is the
pasting of the 2-isomorphisms of `φ` and of `ψ`, followed by
`X(ψ ≫ φ) ≅ X(ψ) ∘ X(φ)` of Stacks 0DE7 read through `X(φ) ≫ X(ψ) = X(ψ ≫ φ)`. This is the
hypothesis of `derivedPullbackTwoIsoSquare_pasting` for the strict components. -/
theorem strictComponentTransitionTwoIso_pasting {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (hk : X.map φ.op ≫ X.map ψ.op = X.map (ψ ≫ φ).op) :
    (RingedToposHom.TwoIso.associator (strictComponentRingedToposHom X n)
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) ψ)).trans
      ((((strictSituation X).transitionRingedToposHomCompTwoIso (strictStructureSheaf X)
          ψ φ).whiskerLeft (strictComponentRingedToposHom X n)).trans
        (strictComponentTransitionTwoIso X (ψ ≫ φ))) =
    ((strictComponentTransitionTwoIso X φ).whiskerRight
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) ψ)).trans
      ((RingedToposHom.TwoIso.associator (spacesEtaleRingedToposHom (X.map φ.op))
          (strictComponentRingedToposHom X m)
          ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) ψ)).trans
        (((strictComponentTransitionTwoIso X ψ).whiskerLeft
            (spacesEtaleRingedToposHom (X.map φ.op))).trans
          ((RingedToposHom.TwoIso.associator (spacesEtaleRingedToposHom (X.map φ.op))
              (spacesEtaleRingedToposHom (X.map ψ.op))
              (strictComponentRingedToposHom X l)).symm.trans
            (((RingedToposHom.TwoIso.ofEq (congrArg spacesEtaleRingedToposHom hk.symm)).trans
              (spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp (X.map φ.op)
                (X.map ψ.op))).symm.whiskerRight (strictComponentRingedToposHom X l))))) := by
  apply RingedToposHom.TwoIso.ext
  dsimp only [RingedToposHom.TwoIso.trans, RingedToposHom.TwoIso.symm,
    RingedToposHom.TwoIso.whiskerLeft, RingedToposHom.TwoIso.whiskerRight,
    RingedToposHom.TwoIso.associator]
  simp only [RingedToposHom.TwoIso.ofEq_e]
  have h := componentStrictTransitionPushforwardIso_pasting X ψ φ hk
  rw [← strictSituation_pushforwardCompSymm_eq] at h
  exact h

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
