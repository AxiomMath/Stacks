module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleSquare
public import StacksFrontier.CategoryTheory.Sites.Localization.AndMorphismsTwoSquare

/-!
# The degrees of the spaces-étale ringed topos of a simplicial algebraic space

Let `X` be a simplicial algebraic space. The inclusion of the objects of degree `n` into
`X_{spaces,étale}` is continuous and cocontinuous, so it gives a morphism of ringed topoi
`d_n : (Sh((X_n)_{spaces,étale}), 𝒪_{X_n}) ⟶ (Sh(X_{spaces,étale}), 𝒪_X)` whose inverse image is
restriction to the degree. The morphisms of ringed topoi of Stacks 0DE7 restrict degreewise: for
`h : X ⟶ Y`, `h ∘ d_n ≅ d_n ∘ h_n`, and for an augmentation `a : X → Z`, `a ∘ d_n ≅ a_n`.

## Main definitions

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.degreeRingedToposHom`: the morphism `d_n`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.degreeExchangeTwoIso`: `h ∘ d_n ≅ d_n ∘ h_n`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.augmentationDegreeTwoIso`: `a ∘ d_n ≅ a_n`.

## Main results

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.degreeExchangeSquare_guitartExact`: the square
  of the degree inclusions and base change is Guitart exact.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.ranBaseChange_unit_comp_eq`: structure maps
  paste across the base change of right Kan extensions of a 2-square.

## References

* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 0FN1](https://stacks.math.columbia.edu/tag/0FN1)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits AlgebraicGeometry.RingedToposHom

universe u

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : SimplicialObject (AlgebraicSpaces B S hS)}

section Generic

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {A : Type u₅} [Category.{v₅} A]
  {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {D₁ : Type u₃} [Category.{v₃} D₁] {D₂ : Type u₄} [Category.{v₄} D₂]
  {uc : C₂ ⥤ C₁} {uf : D₂ ⥤ D₁} {q₁ : C₁ ⥤ D₁} {q₂ : C₂ ⥤ D₂}
  [∀ F : C₁ᵒᵖ ⥤ A, q₁.op.HasPointwiseRightKanExtension F]
  [∀ F : C₂ᵒᵖ ⥤ A, q₂.op.HasPointwiseRightKanExtension F]
  (w : TwoSquare uc q₂ q₁ uf)

/-- **Structure maps paste across the base change of right Kan extensions.** For a 2-square `w` of
functors `uc ⋙ q₁ ⟶ q₂ ⋙ uf`, maps `φf : P₂ ⟶ uf^p P₁`, `χ` and `ψ` agreeing after restriction to
`C₂`, the unit of `q₁`, the base change of `w` and `χ` compose to the unit of `q₂` followed by `ψ`.
-/
theorem ranBaseChange_unit_comp_eq {P₁ : D₁ᵒᵖ ⥤ A} {P₂ : D₂ᵒᵖ ⥤ A} {R : C₂ᵒᵖ ⥤ A}
    (φf : P₂ ⟶ uf.op ⋙ P₁) (χ : uc.op ⋙ q₁.op ⋙ P₁ ⟶ R) (ψ : q₂.op ⋙ P₂ ⟶ R)
    (H : ∀ U : C₂ᵒᵖ, φf.app (q₂.op.obj U) ≫ P₁.map (w.app U.unop).op ≫ χ.app U = ψ.app U) :
    φf ≫ Functor.whiskerLeft uf.op ((q₁.op.ranAdjunction A).unit.app P₁) ≫
        w.op.ranBaseChange.app (q₁.op ⋙ P₁) ≫ q₂.op.ran.map χ =
      (q₂.op.ranAdjunction A).unit.app P₂ ≫ q₂.op.ran.map ψ := by
  refine Functor.hom_ext_of_isRightKanExtension _ (q₂.op.ranCounit.app _) _ _ ?_
  ext U
  have fac := Stacks.SheafOfModules.ranBaseChange_fac w.op (q₁.op ⋙ P₁) U
  have u₁ := ((q₁.op.ranAdjunction A).unit.app P₁).naturality (w.op.app U)
  dsimp only [Functor.id_obj, Functor.comp_obj, Functor.whiskeringLeft_obj_obj] at u₁
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc,
    ran_map_app_ranCounit_app]
  simp only [Functor.whiskeringLeft_obj_obj]
  simp only [Functor.ranCounit_app_app_ranAdjunction_unit_app_app_assoc, reassoc_of% fac,
    ← reassoc_of% u₁, Functor.comp_obj]
  exact H U

end Generic

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pointwise right Kan extensions of presheaves along the degree
-- inclusion is deep
variable (X) in
/-- Right Kan extensions along the inclusion of a degree exist. -/
instance hasPointwiseRightKanExtension_degreeInclusion (n : SimplexCategory)
    (G : (SpacesEtale B S hS (X.obj (op n)))ᵒᵖ ⥤ Type (u + 1)) :
    (degreeInclusion X n).op.HasPointwiseRightKanExtension G := inferInstance

variable (X) in
/-- The morphism of topoi `d_n : Sh((X_n)_{spaces,étale}) ⟶ Sh(X_{spaces,étale})` of the inclusion
of the degree-`n` objects, which is continuous and cocontinuous: its inverse image is restriction
to the degree. -/
def degreeToposHom (n : SimplexCategory) :
    MorphismOfTopoi (Sheaf (SpacesEtale.topology B S hS (X.obj (op n))) (Type (u + 1)))
      (Sheaf (topology X) (Type (u + 1))) :=
  haveI := hasPointwiseRightKanExtension_degreeInclusion X n
  Functor.morphismOfTopoiOfCocontinuous.{u + 1, u + 1, u + 1, u + 1, u + 1} (degreeInclusion X n)
    (SpacesEtale.topology B S hS (X.obj (op n))) (topology X)

variable (X) in
/-- **The inclusion of a degree as a morphism of ringed topoi**
`d_n : (Sh((X_n)_{spaces,étale}), 𝒪_{X_n}) ⟶ (Sh(X_{spaces,étale}), 𝒪_X)`: the structure sheaf of
`X` restricts to that of `X_n`. -/
def degreeRingedToposHom (n : SimplexCategory) :
    RingedToposHom (spacesEtaleRingedTopos B S hS (X.obj (op n))) (ringedTopos X) :=
  RingedToposHom.ofInverseImageIso (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
    (Y := ringedTopos X) (degreeToposHom X n)
    (Stacks.Sheaves.ToposPullback.restrictionCommRingIso
      (SpacesEtale.topology B S hS (X.obj (op n))) (topology X) (degreeInclusion X n)
      (structureSheaf X))

variable (X) in
/-- The structure map of `d_n`, on underlying sheaves of sets, is the unit of `d_n⁻¹ ⊣ d_{n,*}`. -/
theorem forgetFSharp_degreeRingedToposHom (n : SimplexCategory) :
    forgetFSharp (degreeRingedToposHom X n) =
      (degreeToposHom X n).adj.unit.app ((ringedTopos X).forgetRing.obj (structureSheaf X)) := by
  refine (Stacks.Sheaves.ToposPushforward.forget_map_commRingImageAdjunction_homEquiv
    (degreeToposHom X n) _ _ _).trans ?_
  exact (congrArg ((degreeToposHom X n).adj.homEquiv _ _)
      (Stacks.Sheaves.ToposPullback.restrictionCommRingIso_hom_forget
        (SpacesEtale.topology B S hS (X.obj (op n))) (topology X) (degreeInclusion X n)
        (structureSheaf X))).trans
    (((degreeToposHom X n).adj.homEquiv_unit _ _ _).trans
      ((whisker_eq _ ((degreeToposHom X n).pushforward.map_id _)).trans (Category.comp_id _)))

variable (h : X ⟶ Y)

/-- The degree-`n` base change is continuous. -/
instance degreePullback_isContinuous (n : SimplexCategory) :
    (degreePullback h n).IsContinuous (SpacesEtale.topology B S hS (Y.obj (op n)))
      (SpacesEtale.topology B S hS (X.obj (op n))) :=
  Functor.isContinuous_of_iso (spacesBaseChangeIso h n) _ _

/-- The commutative square of the degree-`n` inclusions and base change along `h`. -/
abbrev degreeExchangeSquare (n : SimplexCategory) :
    TwoSquare (degreePullback h n) (degreeInclusion Y n) (degreeInclusion X n)
      (pullbackFunctor h) :=
  𝟙 (degreeInclusion Y n ⋙ pullbackFunctor h)

/-- The downwards structured arrows of the degree square are the arrows of degree `n`. -/
def degreeExchangeStructuredArrowIso (n : SimplexCategory)
    (W : SpacesEtale B S hS (X.obj (op n))) :
    structuredArrowInclusion h ((degreeInclusion X n).obj W) ≅
      (degreeExchangeSquare h n).structuredArrowDownwards W :=
  NatIso.ofComponents (fun c ↦ StructuredArrow.isoMk (Iso.refl _) (by
    refine ((congrArg _ ((pullbackFunctor h).map_id _)).trans (Category.comp_id _)).trans ?_
    exact (Category.comp_id _).symm)) (fun {c c'} x ↦ by
      ext
      exact (Category.comp_id ((degreeInclusion Y n).map x.right)).trans
        (Category.id_comp ((degreeInclusion Y n).map x.right)).symm)

/-- **The degree square of base change is Guitart exact.** -/
instance degreeExchangeSquare_guitartExact (n : SimplexCategory) :
    (degreeExchangeSquare h n).GuitartExact := by
  rw [TwoSquare.guitartExact_iff_initial]
  intro W
  exact @Functor.initial_of_natIso _ _ _ _ _ _
    (structuredArrowInclusion_initial h ((degreeInclusion X n).obj W))
    (degreeExchangeStructuredArrowIso h n W)

/-- **Base change along a morphism of simplicial algebraic spaces restricts degreewise**
(Stacks 0DE7): `h ∘ d_n ≅ d_n ∘ h_n` as morphisms of ringed topoi
`(Sh((X_n)_{spaces,étale}), 𝒪_{X_n}) ⟶ (Sh(Y_{spaces,étale}), 𝒪_Y)`. -/
def degreeExchangeTwoIso (n : SimplexCategory) :
    TwoIso (A := spacesEtaleRingedTopos B S hS (X.obj (op n))) (B := ringedTopos Y)
      (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := ringedTopos X) (Z := ringedTopos Y) (ringedToposHom h) (degreeRingedToposHom X n))
      (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS (Y.obj (op n))) (Z := ringedTopos Y)
        (degreeRingedToposHom Y n) (spacesEtaleRingedToposHom (h.app (op n)))) where
  e := (Stacks.Sites.CocontinuousExchange.sheafIsoOfTwoSquareAndMorphismsTwoSquare (Type (u + 1))
    (SpacesEtale.topology B S hS (Y.obj (op n))) (SpacesEtale.topology B S hS (X.obj (op n)))
    (topology Y) (topology X) (degreeExchangeSquare h n)).symm ≪≫
    Functor.isoWhiskerRight (Functor.sheafPushforwardContinuousIso (spacesBaseChangeIso h n).symm
      (Type (u + 1)) (SpacesEtale.topology B S hS (Y.obj (op n)))
      (SpacesEtale.topology B S hS (X.obj (op n)))) _
  commutes := by
    refine (eq_whisker (forgetFSharp_comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1,
      u + 1} (ringedToposHom h) (degreeRingedToposHom X n)) _).trans
      (Eq.trans ?_ (forgetFSharp_comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1,
        u + 1} (degreeRingedToposHom Y n) (spacesEtaleRingedToposHom (h.app (op n)))).symm)
    rw [forgetFSharp_degreeRingedToposHom, forgetFSharp_degreeRingedToposHom]
    refine ObjectProperty.hom_ext _ ?_
    have key := ranBaseChange_unit_comp_eq (A := Type (u + 1)) (degreeExchangeSquare h n)
      (forgetFSharp (ringedToposHom h)).hom
      ((Functor.sheafPushforwardContinuousIso (spacesBaseChangeIso h n).symm (Type (u + 1))
        (SpacesEtale.topology B S hS (Y.obj (op n)))
        (SpacesEtale.topology B S hS (X.obj (op n)))).hom.app
          ((spacesEtaleRingedTopos B S hS (X.obj (op n))).forgetRing.obj
            (SpacesEtale.structureSheaf B S hS (X.obj (op n))))).hom
      (forgetFSharp (spacesEtaleRingedToposHom (h.app (op n)))).hom (fun U ↦ by
        rw [forgetFSharp_ringedToposHom_app, forgetFSharp_spacesEtaleRingedToposHom_app]
        simp only [Functor.op_obj, Functor.comp_obj, pullbackFunctorProjection_app, NatTrans.id_app,
          spacesBaseChangeIso, Functor.sheafPushforwardContinuousIso_hom, Iso.symm_inv,
          Functor.sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj,
          Functor.whiskerRight_app, NatTrans.op_app, Over.forget_obj]
        have e1 := ((sheafToPresheaf (topology X) (Type (u + 1))).obj
          ((ringedTopos X).forgetRing.obj (ringedTopos X).O)).map_id
            (op ((pullbackFunctor h).obj ((degreeInclusion Y n).obj (unop U))))
        have e2 := ((spacesEtaleRingedTopos B S hS (X.obj (op n))).forgetRing.obj
          (SpacesEtale.structureSheaf B S hS (X.obj (op n)))).obj.map_id
            (op ((spacesBaseChange B S hS (h.app (op n))).functor.obj (unop U)))
        exact (congrArg (_ ≫ ·) ((congrArg (· ≫ _) e1).trans ((Category.id_comp _).trans e2))).trans
          (Category.comp_id _))
    change (forgetFSharp (ringedToposHom h)).hom ≫ Functor.whiskerLeft (pullbackFunctor h).op
        (((degreeInclusion X n).sheafAdjunctionCocontinuous (Type (u + 1))
          (SpacesEtale.topology B S hS (X.obj (op n))) (topology X)).unit.app
            ((ringedTopos X).forgetRing.obj (structureSheaf X))).hom ≫
        ((Stacks.Sites.CocontinuousExchange.sheafIsoOfTwoSquareAndMorphismsTwoSquare (Type (u + 1))
            (SpacesEtale.topology B S hS (Y.obj (op n)))
            (SpacesEtale.topology B S hS (X.obj (op n))) (topology Y) (topology X)
            (degreeExchangeSquare h n)).inv.app
              ((spacesEtaleRingedTopos B S hS (X.obj (op n))).forgetRing.obj
                (SpacesEtale.structureSheaf B S hS (X.obj (op n))))).hom ≫
          (((degreeInclusion Y n).sheafPushforwardCocontinuous (Type (u + 1))
            (SpacesEtale.topology B S hS (Y.obj (op n))) (topology Y)).map
            ((Functor.sheafPushforwardContinuousIso (spacesBaseChangeIso h n).symm (Type (u + 1))
              (SpacesEtale.topology B S hS (Y.obj (op n)))
              (SpacesEtale.topology B S hS (X.obj (op n)))).hom.app
                ((spacesEtaleRingedTopos B S hS (X.obj (op n))).forgetRing.obj
                  (SpacesEtale.structureSheaf B S hS (X.obj (op n)))))).hom =
      (((degreeInclusion Y n).sheafAdjunctionCocontinuous (Type (u + 1))
          (SpacesEtale.topology B S hS (Y.obj (op n))) (topology Y)).unit.app
            ((ringedTopos Y).forgetRing.obj (structureSheaf Y))).hom ≫
        (((degreeInclusion Y n).sheafPushforwardCocontinuous (Type (u + 1))
          (SpacesEtale.topology B S hS (Y.obj (op n))) (topology Y)).map
          (forgetFSharp (spacesEtaleRingedToposHom (h.app (op n))))).hom
    have hX : (((degreeInclusion X n).sheafAdjunctionCocontinuous (Type (u + 1))
          (SpacesEtale.topology B S hS (X.obj (op n))) (topology X)).unit.app
            ((ringedTopos X).forgetRing.obj (structureSheaf X))).hom =
        ((degreeInclusion X n).op.ranAdjunction (Type (u + 1))).unit.app
          ((ringedTopos X).forgetRing.obj (structureSheaf X)).obj :=
      Functor.sheafAdjunctionCocontinuous_unit_app_hom _ _ _ _ _
    have hY : (((degreeInclusion Y n).sheafAdjunctionCocontinuous (Type (u + 1))
          (SpacesEtale.topology B S hS (Y.obj (op n))) (topology Y)).unit.app
            ((ringedTopos Y).forgetRing.obj (structureSheaf Y))).hom =
        ((degreeInclusion Y n).op.ranAdjunction (Type (u + 1))).unit.app
          ((ringedTopos Y).forgetRing.obj (structureSheaf Y)).obj :=
      Functor.sheafAdjunctionCocontinuous_unit_app_hom _ _ _ _ _
    rw [hX, hY,
      Stacks.Sites.CocontinuousExchange.sheafIsoOfTwoSquare_inv_app_hom_andMorphismsTwoSquare]
    exact key

variable (Z : AlgebraicSpaces B S hS)

/-- The adjunction `d_n⁻¹ ∘ ε⁻¹ ⊣ ε_* ∘ d_{n,*}` of forgetting the degree after including it. -/
def constDegreeAdj (n : SimplexCategory) :
    (constToposHom Z).inverseImage ⋙ (degreeToposHom ((Functor.const _).obj Z) n).inverseImage ⊣
      (degreeToposHom ((Functor.const _).obj Z) n).pushforward ⋙ (constToposHom Z).pushforward :=
  (constToposHom Z).adj.comp (degreeToposHom ((Functor.const _).obj Z) n).adj

/-- Including a degree of `const(Z)` and forgetting it is the identity, on direct images. -/
def constDegreePushforwardIso (n : SimplexCategory) :
    (degreeToposHom ((Functor.const _).obj Z) n).pushforward ⋙ (constToposHom Z).pushforward ≅
      𝟭 _ :=
  conjugateIsoEquiv (constDegreeAdj Z n) Adjunction.id
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp in
/-- The structure map of `ε ∘ d_n` is carried to the identity by `constDegreePushforwardIso`. -/
theorem forgetFSharp_constDegree_comp_hom (n : SimplexCategory) :
    forgetFSharp (RingedToposHom.comp
        (X := spacesEtaleRingedTopos B S hS (((Functor.const _).obj Z).obj (op n)))
        (Y := ringedTopos ((Functor.const _).obj Z)) (Z := spacesEtaleRingedTopos B S hS Z)
        (constRingedToposHom Z) (degreeRingedToposHom ((Functor.const _).obj Z) n)) ≫
      (constDegreePushforwardIso Z n).hom.app
        ((spacesEtaleRingedTopos B S hS Z).forgetRing.obj (SpacesEtale.structureSheaf B S hS Z)) =
      𝟙 _ := by
  refine (eq_whisker (forgetFSharp_comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1,
    u + 1} (constRingedToposHom Z) (degreeRingedToposHom ((Functor.const _).obj Z) n)) _).trans ?_
  rw [forgetFSharp_constRingedToposHom, forgetFSharp_degreeRingedToposHom]
  have key := unit_conjugateEquiv (constDegreeAdj Z n) Adjunction.id
    (NatIso.ofComponents (fun F ↦ Iso.refl _) (fun _ ↦ rfl) :
      𝟭 _ ≅ (constToposHom Z).inverseImage ⋙
        (degreeToposHom ((Functor.const _).obj Z) n).inverseImage).hom
    ((spacesEtaleRingedTopos B S hS Z).forgetRing.obj (SpacesEtale.structureSheaf B S hS Z))
  rw [constDegreeAdj, Adjunction.comp_unit_app] at key
  refine key.trans ?_
  simp only [Adjunction.id, Functor.id_map]
  rfl

variable {Z} in
attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp in
/-- `(ε ∘ d_n) ∘ f_{étale} ≅ f_{étale}` for a morphism `f` into a degree of `const(Z)`. -/
def constDegreeCompTwoIso {n : SimplexCategory} {V : AlgebraicSpaces B S hS}
    (f : V ⟶ ((Functor.const _).obj Z).obj (op n)) :
    TwoIso (A := spacesEtaleRingedTopos B S hS V) (B := spacesEtaleRingedTopos B S hS Z)
      (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS V)
        (Y := spacesEtaleRingedTopos B S hS (((Functor.const _).obj Z).obj (op n)))
        (Z := spacesEtaleRingedTopos B S hS Z)
        (RingedToposHom.comp
          (X := spacesEtaleRingedTopos B S hS (((Functor.const _).obj Z).obj (op n)))
          (Y := ringedTopos ((Functor.const _).obj Z)) (Z := spacesEtaleRingedTopos B S hS Z)
          (constRingedToposHom Z) (degreeRingedToposHom ((Functor.const _).obj Z) n))
        (spacesEtaleRingedToposHom f))
      (spacesEtaleRingedToposHom (Z₂ := Z) f) where
  e := Functor.isoWhiskerLeft (spacesEtaleRingedToposHom f).toToposHom.pushforward
      (constDegreePushforwardIso Z n) ≪≫ Functor.rightUnitor _
  commutes := by
    refine (eq_whisker (forgetFSharp_comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1,
      u + 1} _ (spacesEtaleRingedToposHom f)) _).trans ?_
    have nat := (constDegreePushforwardIso Z n).hom.naturality
      (forgetFSharp (spacesEtaleRingedToposHom f))
    have u := forgetFSharp_constDegree_comp_hom Z n
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
      ((Category.comp_id _).trans nat))).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) u).trans (Category.id_comp _))

variable {Z} in
/-- **The augmentation restricted to a degree is the augmentation of that degree**:
`a ∘ d_n ≅ a_n` as morphisms `(Sh((X_n)_{spaces,étale}), 𝒪_{X_n}) ⟶ (Sh(Z_{spaces,étale}), 𝒪_Z)`.
-/
def augmentationDegreeTwoIso (a : X ⟶ (Functor.const _).obj Z) (n : SimplexCategory) :
    TwoIso (A := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (B := spacesEtaleRingedTopos B S hS Z)
      (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := ringedTopos X) (Z := spacesEtaleRingedTopos B S hS Z)
        (augmentationRingedToposHom a) (degreeRingedToposHom X n))
      (spacesEtaleRingedToposHom (Z₂ := Z) (a.app (op n))) :=
  (TwoIso.associator (degreeRingedToposHom X n) (ringedToposHom a)
      (constRingedToposHom Z)).symm.trans
    ((TwoIso.whiskerRight (degreeExchangeTwoIso a n) (constRingedToposHom Z)).trans
      ((TwoIso.associator (spacesEtaleRingedToposHom (a.app (op n)))
          (degreeRingedToposHom ((Functor.const _).obj Z) n) (constRingedToposHom Z)).trans
        (constDegreeCompTwoIso (a.app (op n)))))

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
