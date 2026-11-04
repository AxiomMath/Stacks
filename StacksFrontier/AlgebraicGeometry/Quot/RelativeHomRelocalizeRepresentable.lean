module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRelocalizeSituation
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomAffineLocal

/-!
# Representability of the relative Hom functor across relocalization

Let `h : W ⟶ S` be a morphism of a big fppf site and `Z` a scheme over `W`, viewed as the scheme
`j Z` over `S`.  A scheme `V'` over `j Z` is a scheme `V` over `Z`, and the points of `V` over
`Z` on the test schemes over `Z` are the points of `V'` over `j Z` on the test schemes coming from
`Z`.  With the identification of relative Hom functors of
`AlgebraicGeometry.Space.HomSituation.homFunctorRelocalizeIso`, a representation of the relative
Hom functor of a relocalized situation over `S` by a scheme over `j Z` gives a representation
over `W`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

section Points

variable {B W S hW hS} (Z : BigFppfOver B W hW)

/-- A test scheme over the scheme `Z` over `W` as a test scheme over the scheme `j Z` over `S`. -/
def relocalizeSchemeTests :
    SchemesOver ((schemeSpaceFunctor B W hW).obj Z) ⥤
      SchemesOver ((schemeSpaceFunctor B S hS).obj ((Over.map h).obj Z)) where
  obj T := CostructuredArrow.mk (Y := (Over.map h).obj T.left)
    ((schemeSpaceFunctor B S hS).map ((Over.map h).map (testPoint T : T.left ⟶ Z)))
  map {T T'} g := CostructuredArrow.homMk ((Over.map h).map g.left) (by
    have hw : g.left ≫ (testPoint T' : T'.left ⟶ Z) = testPoint T := testPoint_naturality g
    change (schemeSpaceFunctor B S hS).map ((Over.map h).map g.left) ≫
        (schemeSpaceFunctor B S hS).map ((Over.map h).map (testPoint T' : T'.left ⟶ Z)) =
      (schemeSpaceFunctor B S hS).map ((Over.map h).map (testPoint T : T.left ⟶ Z))
    exact ((schemeSpaceFunctor B S hS).map_comp _ _).symm.trans
      (congrArg (schemeSpaceFunctor B S hS).map (((Over.map h).map_comp _ _).symm.trans
        (congrArg (Over.map h).map hw))))
  map_id T := CostructuredArrow.hom_ext _ _ ((Over.map h).map_id _)
  map_comp f g := CostructuredArrow.hom_ext _ _ ((Over.map h).map_comp _ _)

variable {Z} {V' : BigFppfOver B S hS} (w' : V' ⟶ (Over.map h).obj Z)

/-- A scheme over `j Z` read as a scheme over `W`, through `Z`. -/
abbrev relocalizeDescend : BigFppfOver B W hW :=
  Over.mk (w'.left ≫ Z.hom)

/-- A scheme over `j Z` read as a scheme over `Z`. -/
abbrev relocalizeDescendHom : relocalizeDescend h w' ⟶ Z :=
  Over.homMk w'.left

/-- The section of `j Z` that the test scheme `relocalizeSchemeTests T` is: the image of the
section of `Z` that `T` is. -/
theorem testPoint_relocalizeSchemeTests (T : SchemesOver ((schemeSpaceFunctor B W hW).obj Z)) :
    (testPoint ((relocalizeSchemeTests h Z).obj T) : (Over.map h).obj T.left ⟶ (Over.map h).obj Z) =
      (Over.map h).map (testPoint T : T.left ⟶ Z) :=
  yonedaEquiv_yoneda_map _

/-- **The points of `V` over `Z` are the points of `V'` over `j Z`**, at one test scheme. -/
def relocalizeDescendPointsEquiv (T : SchemesOver ((schemeSpaceFunctor B W hW).obj Z)) :
    spacePointsOverObj ((schemeSpaceFunctor B W hW).map (relocalizeDescendHom h w')) T ≃
      spacePointsOverObj ((schemeSpaceFunctor B S hS).map w')
        ((relocalizeSchemeTests h Z).obj T) where
  toFun x := ⟨Over.homMk (x.1 : T.left ⟶ relocalizeDescend h w').left (by
      have e := Over.w (x.1 : T.left ⟶ relocalizeDescend h w')
      change (x.1 : T.left ⟶ relocalizeDescend h w').left ≫ V'.hom = T.left.hom ≫ h
      rw [← Over.w w', ← Category.assoc, ← e]
      rfl), by
      have hx : (x.1 : T.left ⟶ relocalizeDescend h w') ≫ relocalizeDescendHom h w' =
          (testPoint T : T.left ⟶ Z) := x.2
      have hl : (x.1 : T.left ⟶ relocalizeDescend h w').left ≫ w'.left =
          (testPoint T : T.left ⟶ Z).left :=
        congrArg (fun k : T.left ⟶ Z => k.left) hx
      refine Eq.trans ?_ (testPoint_relocalizeSchemeTests h T).symm
      exact Over.OverMorphism.ext hl⟩
  invFun y := ⟨Over.homMk (y.1 : (Over.map h).obj T.left ⟶ V').left (by
      have hy : (y.1 : (Over.map h).obj T.left ⟶ V') ≫ w' =
          (Over.map h).map (testPoint T : T.left ⟶ Z) :=
        y.2.trans (testPoint_relocalizeSchemeTests h T)
      have hl : (y.1 : (Over.map h).obj T.left ⟶ V').left ≫ w'.left =
          (testPoint T : T.left ⟶ Z).left :=
        congrArg (fun k : (Over.map h).obj T.left ⟶ (Over.map h).obj Z => k.left) hy
      change (y.1 : (Over.map h).obj T.left ⟶ V').left ≫ w'.left ≫ Z.hom = T.left.hom
      rw [← Category.assoc, hl]
      exact Over.w (testPoint T : T.left ⟶ Z)), by
      have hy : (y.1 : (Over.map h).obj T.left ⟶ V') ≫ w' =
          (Over.map h).map (testPoint T : T.left ⟶ Z) :=
        y.2.trans (testPoint_relocalizeSchemeTests h T)
      have hl : (y.1 : (Over.map h).obj T.left ⟶ V').left ≫ w'.left =
          (testPoint T : T.left ⟶ Z).left :=
        congrArg (fun k : (Over.map h).obj T.left ⟶ (Over.map h).obj Z => k.left) hy
      exact Over.OverMorphism.ext hl⟩
  left_inv x := Subtype.ext (Over.OverMorphism.ext rfl)
  right_inv y := Subtype.ext (Over.OverMorphism.ext rfl)

/-- **The points of `V` over `Z` are the points of `V'` over `j Z`**, naturally in the test
scheme over `Z`. -/
def relocalizeDescendPointsIso :
    spacePointsOver ((schemeSpaceFunctor B W hW).map (relocalizeDescendHom h w')) ≅
      (relocalizeSchemeTests h Z).op ⋙ spacePointsOver ((schemeSpaceFunctor B S hS).map w') :=
  NatIso.ofComponents (fun T => (relocalizeDescendPointsEquiv h w' T.unop).toIso)
    (fun _ => ConcreteCategory.hom_ext _ _ fun _ => Subtype.ext (Over.OverMorphism.ext rfl))

end Points

/-- The test schemes over `Z` read over `j Z` and then over `Λ h_Z` are the test schemes of
`AlgebraicGeometry.Space.relocalizeSchemesOver`. -/
def relocalizeSchemeTestsMapIso (Z : BigFppfOver B W hW) :
    relocalizeSchemeTests h Z ⋙ CostructuredArrow.map (relocalizeSchemeSpaceHom B W S hW hS h Z) ≅
      relocalizeSchemesOver B W S hW hS h ((schemeSpaceFunctor B W hW).obj Z) :=
  NatIso.ofComponents (fun T => CostructuredArrow.isoMk (Iso.refl _) (by
      have hT : T.hom = (schemeSpaceFunctor B W hW).map (testPoint T : T.left ⟶ Z) :=
        ObjectProperty.hom_ext _ (yonedaEquiv_symm_testPoint T).symm
      change 𝟙 _ ≫ relocalizeSchemeSpaceHom B W S hW hS h T.left ≫
          relocalizeHomSE B W S hW hS h T.hom =
        (schemeSpaceFunctor B S hS).map ((Over.map h).map (testPoint T : T.left ⟶ Z)) ≫
          relocalizeSchemeSpaceHom B W S hW hS h Z
      rw [Category.id_comp, hT]
      exact (relocalizeSchemeSpaceHom_naturality B W S hW hS h (testPoint T : T.left ⟶ Z)).symm))
    (fun g => CostructuredArrow.hom_ext _ _ ((Category.comp_id _).trans (Category.id_comp _).symm))

namespace HomSituation

variable {B W S hW hS}

/-- **Representability of the relative Hom functor descends along relocalization**, over an
affine test scheme.  Let `s` be a situation of Stacks 08JT over `W` and `p : h_Z ⟶ base` with `Z`
a scheme over `W`.  If the relative Hom functor of the relocalized base-changed situation, read
over `j Z`, is represented by a scheme `V'` affine and locally of finite presentation over
`j Z`, then the relative Hom functor of the base-changed situation over `W` is represented by
`V'` viewed as a scheme over `Z`. -/
theorem exists_baseChange_representation_of_relocalize (s : HomSituation B W hW)
    (Z : BigFppfOver B W hW) (p : (schemeSpaceFunctor B W hW).obj Z ⟶ s.base)
    {V' : BigFppfOver B S hS} (w' : V' ⟶ (Over.map h).obj Z)
    (θ : spacePointsOver ((schemeSpaceFunctor B S hS).map w') ⋙ uliftFunctor.{u + 1, u} ≅
      (((s.baseChangedSituation p).relocalize h).baseChangedSituation
        (relocalizeSchemeSpaceHom B W S hW hS h Z)).homFunctor
          (modulePushforwardCoherence B S hS)) :
    Nonempty (spacePointsOver ((schemeSpaceFunctor B W hW).map (relocalizeDescendHom h w')) ⋙
        uliftFunctor.{u + 1, u} ≅
      (s.baseChangedSituation p).homFunctor (modulePushforwardCoherence B W hW)) :=
  ⟨Functor.isoWhiskerRight (relocalizeDescendPointsIso h w') uliftFunctor.{u + 1, u} ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (relocalizeSchemeTests h Z).op θ ≪≫
    Functor.isoWhiskerLeft (relocalizeSchemeTests h Z).op
      (((s.baseChangedSituation p).relocalize h).homFunctorBaseChange
        (relocalizeSchemeSpaceHom B W S hW hS h Z)) ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (NatIso.op (relocalizeSchemeTestsMapIso B W S hW hS h Z)).symm _ ≪≫
    ((s.baseChangedSituation p).homFunctorRelocalizeIso h
      (modulePushforwardCoherence B W hW) (modulePushforwardCoherence B S hS)).symm⟩

/-- **The relative Hom functor is affine and of finite presentation over the base once its
relocalizations over every affine base change are.**  This reduces Stacks 08K6 over an arbitrary
base scheme `W` to the case of situations over `S`, for instance over `Spec ℤ`, where the
Noetherian approximation of the source applies. -/
theorem isAffineFinitePresentationAlgebraicSpaceOverBase_of_relocalize (s : HomSituation B W hW)
    (hc : ModulePushforwardCoherence B W hW)
    (hrel : ∀ (Z : BigFppfOver B W hW), IsAffine ((BigFppfOver.toScheme B W hW).obj Z) →
      ∀ p : (schemeSpaceFunctor B W hW).obj Z ⟶ s.base,
        ∃ (V' : BigFppfOver B S hS) (w' : V' ⟶ (Over.map h).obj Z),
          _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map w') ∧
            LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map w') ∧
              Nonempty (spacePointsOver ((schemeSpaceFunctor B S hS).map w') ⋙
                  uliftFunctor.{u + 1, u} ≅
                (((s.baseChangedSituation p).relocalize h).baseChangedSituation
                  (relocalizeSchemeSpaceHom B W S hW hS h Z)).homFunctor
                    (modulePushforwardCoherence B S hS))) :
    s.IsAffineFinitePresentationAlgebraicSpaceOverBase hc :=
  s.isAffineFinitePresentationAlgebraicSpaceOverBase_of_baseChange hc fun Z hZ p => by
    obtain ⟨V', w', hw, hwfp, ⟨θ⟩⟩ := hrel Z hZ p
    exact ⟨relocalizeDescend h w', relocalizeDescendHom h w', hw, hwfp,
      s.exists_baseChange_representation_of_relocalize h Z p w' θ⟩

end HomSituation

end AlgebraicGeometry.Space

end
