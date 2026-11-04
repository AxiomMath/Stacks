module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Cartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentInclusion
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardExact

/-!
# Cartesian abelian sheaves form a weak Serre subcategory

Let `S` be a simplicial-site situation. The cartesian abelian sheaves on its total site form a weak
Serre subcategory of all abelian sheaves there: the zero sheaf is cartesian, and the middle term of
a five term exact sequence whose other four terms are cartesian is cartesian. A colimit of
cartesian abelian sheaves is cartesian.

## Main results

* `CategoryTheory.SimplicialSiteSituation.isCartesianAbSheaf_isWeakSerreClass`: the weak Serre
  property.
* `CategoryTheory.SimplicialSiteSituation.isCartesianAbSheaf_isClosedUnderColimitsOfShape`:
  colimits of cartesian abelian sheaves are cartesian.
* `CategoryTheory.SimplicialSiteSituation.isCartesianAbSheaf_weakSerre_colimits`:
  **Stacks 0D7J (1)**, the two together.
* `CategoryTheory.SimplicialSiteSituation.abelianFiberTransition`: the transition of Stacks 09WF on
  abelian sheaves, whose invertibility is cartesianness, together with
  `abelianFiberTransition_isIso_iff` identifying its invertibility with that of the transition of
  the underlying sheaf of sets.

## Implementation notes

Cartesianness of an abelian sheaf is a condition on the transitions of its underlying sheaf of sets
(`CategoryTheory.SimplicialSiteSituation.IsCartesianAbSheaf`). `abelianFiberTransition` reads it as
invertibility of a natural transformation between *exact* functors on abelian sheaves: it is the
transition of Stacks 09WF transported through the equivalence
`CategoryTheory.Sites.AbelianSheaf.equivalence` between abelian sheaves and commutative group
objects in the topos, under which `CategoryTheory.Sites.abelianInverseImage` becomes
`CategoryTheory.Functor.mapCommGrp` of the geometric inverse image. The two readings agree by
`abelianFiberTransition_isIso_iff`.

The weak Serre property is taken in the closure-condition form
`CategoryTheory.ObjectProperty.IsWeakSerreClass`, which Stacks 0754 shows equivalent to the five
term exact sequence form of Stacks 02MO (2); that equivalence is
`CategoryTheory.ObjectProperty.isWeakSerreClass_iff_prop_obj₂_of_exact`.

The component inverse image is the inverse image of the morphism of topoi
`CategoryTheory.SimplicialSiteSituation.componentMorphism`, which is sheafified restriction; Stacks
00XR (1) identifies it with plain restriction, which is what the transition of Stacks 09WF is
stated for.

## References

* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sites
open scoped ZeroObject

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] CategoryTheory.sheafTypeCartesian CategoryTheory.sheafTypeBraided

/-- The restriction to a simplicial degree is braided. -/
noncomputable local instance restrict_braided (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) : (S.restrict.{u, u} n).Braided :=
  .ofChosenFiniteProducts _

/-- The inverse image along a transition morphism preserves finite limits. -/
noncomputable local instance transition_inverseImage_preservesFiniteLimits
    (S : SimplicialSiteSituation.{u}) {m n : SimplexCategory} (φ : m ⟶ n) :
    PreservesFiniteLimits (S.transitionMorphism φ).inverseImage :=
  (S.transitionMorphism φ).preservesFiniteLimits

/-- The inverse image along a transition morphism is braided. -/
noncomputable local instance transition_inverseImage_braided
    (S : SimplicialSiteSituation.{u}) {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionMorphism φ).inverseImage.Braided :=
  .ofChosenFiniteProducts _

/-- The pushforward along a transition morphism preserves finite limits. -/
noncomputable local instance transition_pushforward_preservesFiniteLimits
    (S : SimplicialSiteSituation.{u}) {m n : SimplexCategory} (φ : m ⟶ n) :
    PreservesFiniteLimits (S.transitionMorphism φ).pushforward := by
  let : (S.transitionMorphism φ).pushforward.IsRightAdjoint :=
    (S.transitionMorphism φ).adj.isRightAdjoint
  infer_instance

/-- The pushforward along a transition morphism is braided. -/
noncomputable local instance transition_pushforward_braided
    (S : SimplicialSiteSituation.{u}) {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionMorphism φ).pushforward.Braided :=
  .ofChosenFiniteProducts _

/-- The transition of Stacks 09WF read on commutative group objects of the topoi: the mate of
`restrictTransition` for the adjunction of Stacks 00XO lifted to group objects. -/
noncomputable def groupFiberTransition (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.restrict.{u, u} m).mapCommGrp ⋙
        (S.transitionMorphism φ).inverseImage.mapCommGrp ⟶
      (S.restrict.{u, u} n).mapCommGrp :=
  letI β := Functor.mapCommGrpNatTrans (S.restrictTransition φ) ≫
    (Functor.mapCommGrpCompIso (F := S.restrict.{u, u} n)
      (G := (S.transitionMorphism φ).pushforward)).hom
  Functor.whiskerRight β (S.transitionMorphism φ).inverseImage.mapCommGrp ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (S.restrict.{u, u} n).mapCommGrp
      (Adjunction.mapCommGrp (S.transitionMorphism φ).adj).counit ≫
    (Functor.rightUnitor _).hom

/-- Forgetting the group structure turns `groupFiberTransition` into the transition of Stacks 09WF
on the underlying sheaves of sets. -/
theorem groupFiberTransition_forget_app (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (F : CommGrp (Sheaf S.totalTopology (Type u))) :
    (CommGrp.forget₂Grp _ ⋙ Grp.forget _).map ((groupFiberTransition S φ).app F) =
      (fiberTransition S φ).app F.X := by
  ext V x
  dsimp [groupFiberTransition, Adjunction.mapCommGrp, Functor.mapCommGrpNatTrans,
    Functor.mapCommGrpCompIso, Functor.mapCommGrpIdIso, Functor.mapGrpNatTrans,
    Functor.mapMonNatTrans, fiberTransition]
  rfl

/-- An exact functor sends an exact sequence of composable arrows to an exact sequence. -/
theorem exact_mapComposableArrows {C D : Type*} [Category C] [Category D]
    [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
    {n : ℕ} {T : ComposableArrows C n} (hT : T.Exact) (F : C ⥤ D)
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    ((F.mapComposableArrows n).obj T).Exact := by
  refine ⟨⟨?_⟩, ?_⟩
  · intro i hi
    show F.map (T.map' i (i + 1)) ≫ F.map (T.map' (i + 1) (i + 2)) = 0
    rw [← Functor.map_comp, hT.toIsComplex.zero' i (i + 1) (i + 2)]
    simp
  · intro i hi
    show ((T.sc hT.toIsComplex i).map F).Exact
    exact (hT.exact i hi).map F

/-- **The four lemma for a natural transformation.** If a natural transformation between exact
functors is epi, invertible, invertible and mono at the four outer terms of a five term exact
sequence, then it is invertible at the middle term. -/
theorem isIso_app_obj'_two_of_exact {C D : Type*} [Category C] [HasZeroObject C]
    [Preadditive C] [Category D] [Abelian D] (F G : C ⥤ D)
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (η : F ⟶ G) (T : ComposableArrows C 4) (hT : T.Exact)
    (h₀ : Epi (η.app (T.obj' 0))) (h₁ : IsIso (η.app (T.obj' 1)))
    (h₃ : IsIso (η.app (T.obj' 3))) (h₄ : Mono (η.app (T.obj' 4))) :
    IsIso (η.app (T.obj' 2)) := by
  let τ := ((Functor.whiskeringRight (Fin 5) C D).map η).app T
  have hτ₀ : Epi (ComposableArrows.app' τ 0) := by simpa [τ] using h₀
  have hτ₁ : IsIso (ComposableArrows.app' τ 1) := by simpa [τ] using h₁
  have hτ₃ : IsIso (ComposableArrows.app' τ 3) := by simpa [τ] using h₃
  have hτ₄ : Mono (ComposableArrows.app' τ 4) := by simpa [τ] using h₄
  have hmid := Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
    (exact_mapComposableArrows hT F) (exact_mapComposableArrows hT G) τ hτ₀ hτ₁ hτ₃ hτ₄
  simpa [τ] using hmid

section AbelianTransition

variable (S : SimplicialSiteSituation.{u}) {m n : SimplexCategory} (φ : m ⟶ n)

/-- The inverse image along a component morphism preserves finite limits. -/
noncomputable local instance componentMorphism_inverseImage_preservesFiniteLimits
    (k : SimplexCategory) : PreservesFiniteLimits (componentMorphism S k).inverseImage :=
  (componentMorphism S k).preservesFiniteLimits

/-- The inverse image along a component morphism is braided. -/
noncomputable local instance componentMorphism_inverseImage_braided (k : SimplexCategory) :
    (componentMorphism S k).inverseImage.Braided := .ofChosenFiniteProducts _

/-- **Stacks 00XR (1).** The inverse image of the component morphism of topoi is plain restriction,
with no sheafification. -/
noncomputable def componentMorphismInverseImageIso (k : SimplexCategory) :
    (componentMorphism S k).inverseImage ≅ S.restrict.{u, u} k :=
  (S.inclusion k).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    (Type u) (S.componentTopology k) S.totalTopology

/-- **Stacks 00XR (1).** The abelian inverse image along the component inclusion, read through the
equivalence with commutative group objects, is `mapCommGrp` of plain restriction. -/
noncomputable def abelianComponentIso (k : SimplexCategory) :
    abelianInverseImage (componentMorphism S k) ≅
      ((AbelianSheaf.equivalence S.totalTopology).functor ⋙
          (S.restrict.{u, u} k).mapCommGrp) ⋙
        (AbelianSheaf.equivalence (S.componentTopology k)).inverse :=
  Functor.isoWhiskerLeft (AbelianSheaf.equivalence S.totalTopology).functor
    (Functor.isoWhiskerRight
      (Functor.mapCommGrpNatIso (componentMorphismInverseImageIso S k))
      (AbelianSheaf.equivalence (S.componentTopology k)).inverse)

/-- The composite of two abelian inverse images, read through the equivalence with commutative
group objects: the middle equivalence cancels. -/
noncomputable def abelianComponentCompIso :
    abelianInverseImage (componentMorphism S m) ⋙
        abelianInverseImage (S.transitionMorphism φ) ≅
      (((AbelianSheaf.equivalence S.totalTopology).functor ⋙
            (S.restrict.{u, u} m).mapCommGrp) ⋙
          (S.transitionMorphism φ).inverseImage.mapCommGrp) ⋙
        (AbelianSheaf.equivalence (S.componentTopology n)).inverse :=
  letI I := (AbelianSheaf.equivalence S.totalTopology).functor
  letI EN := (AbelianSheaf.equivalence (S.componentTopology n)).inverse
  letI EM := (AbelianSheaf.equivalence (S.componentTopology m)).inverse
  letI IM := (AbelianSheaf.equivalence (S.componentTopology m)).functor
  letI vGrp := (S.transitionMorphism φ).inverseImage.mapCommGrp
  letI pM := (componentMorphism S m).inverseImage.mapCommGrp
  Functor.associator (I ⋙ pM) EM (IM ⋙ (vGrp ⋙ EN)) ≪≫
    Functor.isoWhiskerLeft (I ⋙ pM)
      (Functor.isoWhiskerLeft EM (Functor.associator IM vGrp EN) ≪≫
        (Functor.associator EM IM (vGrp ⋙ EN)).symm ≪≫
        Functor.isoWhiskerRight
          (AbelianSheaf.equivalence (S.componentTopology m)).counitIso (vGrp ⋙ EN) ≪≫
        Functor.leftUnitor (vGrp ⋙ EN)) ≪≫
    (Functor.associator (I ⋙ pM) vGrp EN).symm ≪≫
    Functor.isoWhiskerLeft I
      (Functor.isoWhiskerRight
        (Functor.mapCommGrpNatIso (componentMorphismInverseImageIso S m))
        (vGrp ⋙ EN)) ≪≫
    Functor.associator (I ⋙ (S.restrict.{u, u} m).mapCommGrp) vGrp EN

/-- `groupFiberTransition`, transported into the categories of abelian sheaves. -/
noncomputable def abelianFiberTransitionAux :
    (((AbelianSheaf.equivalence S.totalTopology).functor ⋙
          (S.restrict.{u, u} m).mapCommGrp) ⋙
        (S.transitionMorphism φ).inverseImage.mapCommGrp) ⋙
      (AbelianSheaf.equivalence (S.componentTopology n)).inverse ⟶
    ((AbelianSheaf.equivalence S.totalTopology).functor ⋙
        (S.restrict.{u, u} n).mapCommGrp) ⋙
      (AbelianSheaf.equivalence (S.componentTopology n)).inverse :=
  Functor.whiskerRight
    (Functor.whiskerLeft (AbelianSheaf.equivalence S.totalTopology).functor
      (groupFiberTransition S φ))
    (AbelianSheaf.equivalence (S.componentTopology n)).inverse

/-- **Stacks 09WF** on abelian sheaves: the transition comparing the abelian inverse images of a
total-site abelian sheaf in two simplicial degrees. -/
noncomputable def abelianFiberTransition :
    abelianInverseImage (componentMorphism S m) ⋙
        abelianInverseImage (S.transitionMorphism φ) ⟶
      abelianInverseImage (componentMorphism S n) :=
  (abelianComponentCompIso S φ).hom ≫ abelianFiberTransitionAux S φ ≫
    (abelianComponentIso S n).inv

/-- The abelian transition of Stacks 09WF is invertible exactly when the transition of the
underlying sheaf of sets is. -/
theorem abelianFiberTransition_isIso_iff (F : Sheaf S.totalTopology Ab.{u}) :
    IsIso ((abelianFiberTransition S φ).app F) ↔
      IsIso ((fiberTransition S φ).app
        ((sheafCompose S.totalTopology (forget Ab.{u})).obj F)) := by
  let I := (AbelianSheaf.equivalence S.totalTopology).functor
  let EN := (AbelianSheaf.equivalence (S.componentTopology n)).inverse
  let : EN.FullyFaithful :=
    (AbelianSheaf.equivalence (S.componentTopology n)).fullyFaithfulInverse
  let g := (groupFiberTransition S φ).app (I.obj F)
  have hstep : IsIso ((abelianFiberTransition S φ).app F) ↔ IsIso (EN.map g) := by
    have hEq : (abelianFiberTransition S φ).app F =
        (abelianComponentCompIso S φ).hom.app F ≫ EN.map g ≫
          (abelianComponentIso S n).inv.app F := by
      dsimp only [abelianFiberTransition, abelianFiberTransitionAux, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rw [hEq, isIso_comp_left_iff, isIso_comp_right_iff]
  rw [hstep, isIso_iff_of_reflects_iso g EN]
  let : (Grp.forget (Sheaf (S.componentTopology n) (Type u))).ReflectsIsomorphisms := by
    show (Grp.forget₂Mon _ ⋙ Mon.forget _).ReflectsIsomorphisms
    infer_instance
  rw [← isIso_iff_of_reflects_iso g (CommGrp.forget₂Grp _ ⋙ Grp.forget _),
    groupFiberTransition_forget_app]
  rfl

end AbelianTransition

/-- The cartesian abelian sheaves on the total site of a simplicial site form a weak Serre
subcategory of all abelian sheaves there. -/
instance isCartesianAbSheaf_isWeakSerreClass (S : SimplicialSiteSituation.{u}) :
    ObjectProperty.IsWeakSerreClass (IsCartesianAbSheaf S) := by
  refine (ObjectProperty.isWeakSerreClass_iff_prop_obj₂_of_exact (IsCartesianAbSheaf S)).2 ?_
  constructor
  · refine ⟨(0 : Sheaf S.totalTopology Ab.{u}), fun m n φ => ?_⟩
    exact (abelianFiberTransition_isIso_iff S φ 0).1 (IsZero.isIso
      ((abelianInverseImage (componentMorphism S m) ⋙
        abelianInverseImage (S.transitionMorphism φ)).map_isZero (isZero_zero _))
      ((abelianInverseImage (componentMorphism S n)).map_isZero (isZero_zero _)) _)
  · intro T hT h₀ h₁ h₃ h₄
    change IsCartesianSheaf S
      ((sheafCompose S.totalTopology (forget Ab.{u})).obj (T.obj' 2))
    intro m n φ
    refine (abelianFiberTransition_isIso_iff S φ (T.obj' 2)).1 ?_
    exact isIso_app_obj'_two_of_exact _ _ (abelianFiberTransition S φ) T hT
      (by let := (abelianFiberTransition_isIso_iff S φ (T.obj' 0)).2 (h₀ φ); infer_instance)
      ((abelianFiberTransition_isIso_iff S φ (T.obj' 1)).2 (h₁ φ))
      ((abelianFiberTransition_isIso_iff S φ (T.obj' 3)).2 (h₃ φ))
      (by let := (abelianFiberTransition_isIso_iff S φ (T.obj' 4)).2 (h₄ φ); infer_instance)

/-- A natural transformation between two functors that preserve the colimit of a diagram is
invertible at the colimit as soon as it is invertible at every term of the diagram. -/
theorem isIso_app_of_isColimit {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (η : F ⟶ G) {J : Type*} [Category* J] {K : J ⥤ C} {c : Cocone K} (hc : IsColimit c)
    [PreservesColimit K F] [PreservesColimit K G] (h : ∀ j, IsIso (η.app (K.obj j))) :
    IsIso (η.app c.pt) := by
  have : IsIso (Functor.whiskerLeft K η) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (Functor.whiskerLeft K η) h
  have e : η.app c.pt = (IsColimit.coconePointsIsoOfNatIso (isColimitOfPreserves F hc)
      (isColimitOfPreserves G hc) (asIso (Functor.whiskerLeft K η))).hom := by
    refine (isColimitOfPreserves F hc).hom_ext fun j => ?_
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    simp
  rw [e]
  infer_instance

/-- The abelian inverse image along a morphism of topoi preserves colimits of every shape, being a
left adjoint. -/
private theorem abelianInverseImage_preservesColimitsOfShape {C D : Type u} [SmallCategory C]
    [SmallCategory D] {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    (J : Type*) [Category* J] (f : MorphismOfTopoi (Sheaf K (Type u)) (Sheaf L (Type u))) :
    PreservesColimitsOfShape J (abelianInverseImage f) :=
  (Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward _ f
    ).leftAdjoint_preservesColimits.preservesColimitsOfShape

/-- Colimits of cartesian abelian sheaves on the total site of a simplicial site are cartesian, for
diagrams of every shape. -/
theorem isCartesianAbSheaf_isClosedUnderColimitsOfShape (S : SimplicialSiteSituation.{u})
    (J : Type*) [Category* J] :
    ObjectProperty.IsClosedUnderColimitsOfShape (IsCartesianAbSheaf S) J := by
  constructor
  rintro X ⟨p⟩ m n φ
  let F := abelianInverseImage (componentMorphism S m) ⋙
    abelianInverseImage (S.transitionMorphism φ)
  let G := abelianInverseImage (componentMorphism S n)
  have hF : PreservesColimit p.diag F :=
    have := abelianInverseImage_preservesColimitsOfShape J (componentMorphism S m)
    have := abelianInverseImage_preservesColimitsOfShape J (S.transitionMorphism φ)
    inferInstance
  have hG : PreservesColimit p.diag G :=
    have := abelianInverseImage_preservesColimitsOfShape J (componentMorphism S n)
    inferInstance
  have hterm : ∀ j, IsIso ((abelianFiberTransition S φ).app (p.diag.obj j)) := fun j =>
    (abelianFiberTransition_isIso_iff S φ (p.diag.obj j)).2 (p.prop_diag_obj j φ)
  have hX : IsIso ((abelianFiberTransition S φ).app X) :=
    @isIso_app_of_isColimit _ _ _ _ F G (abelianFiberTransition S φ) J _ p.diag
      (Cocone.mk X p.ι) p.isColimit hF hG hterm
  exact (abelianFiberTransition_isIso_iff S φ X).1 hX

/-- **Stacks 0D7J (1).** The cartesian abelian sheaves on the total site of a simplicial site form
a weak Serre subcategory of all abelian sheaves there, and colimits of systems of cartesian abelian
sheaves are cartesian. -/
@[stacks 0D7J "part (1)"]
theorem isCartesianAbSheaf_weakSerre_colimits (S : SimplicialSiteSituation.{u}) :
    ObjectProperty.IsWeakSerreClass (IsCartesianAbSheaf S) ∧
      ∀ (J : Type*) [Category* J],
        ObjectProperty.IsClosedUnderColimitsOfShape (IsCartesianAbSheaf S) J :=
  ⟨inferInstance, fun J _ => isCartesianAbSheaf_isClosedUnderColimitsOfShape S J⟩

end CategoryTheory.SimplicialSiteSituation

end
