module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.CommRingModuleData
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.Basic

/-!
# Pushforward of a graded algebra: transported addition

The addition morphism `M ⨯ M ⟶ M` of a sheaf of modules, its transport along a functor
preserving the product `M ⨯ M`, and the comparison of the transported additions for the direct
image of sheaves of modules along a morphism of ringed topoi.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open AlgebraicGeometry Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.GradedAlgebraPushforward

universe u u' v v' w w' x x'

/-- Two sheaves of sets on a site have a binary product. -/
instance hasBinaryProductSheafType {C : Type u} [Category.{v, u} C]
    {J : GrothendieckTopology C} (M N : Sheaf J (Type w)) : HasLimit (pair M N) :=
  inferInstance

private lemma pushforwardModules_additive
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y) :
    Functor.Additive
      (f.pushforwardModules) := by
  have : (f.pushforwardModules).IsRightAdjoint :=
    (f.pullbackAdjPushforwardModulesViaComparison).isRightAdjoint
  exact Functor.additive_of_preserves_binary_products _

/-- The addition morphism `M ⨯ M ⟶ M` of a sheaf of modules, the sum of the two projections. -/
noncomputable def modulePlusHom
    {C : Type u} [Category.{v, u} C] {J : GrothendieckTopology C}
    {O : Sheaf J RingCat.{w}} (M : SheafOfModules.{x} O) :
    M ⨯ M ⟶ M :=
  (Limits.prod.fst : M ⨯ M ⟶ M) + Limits.prod.snd

lemma underlyingAdditiveSheafPreservesFiniteLimits
    {C : Type u} [Category.{v, u} C] {J : GrothendieckTopology C} :
    PreservesFiniteLimits (sheafCompose J (forget AddCommGrpCat.{u})) := by
  have : PreservesFiniteLimits
      (sheafCompose J (forget AddCommGrpCat.{u}) ⋙ sheafToPresheaf J (Type u)) := by
    change PreservesFiniteLimits
      (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{u} (Type u)).obj
          (forget AddCommGrpCat.{u}))
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J _)

attribute [local instance] underlyingAdditiveSheafPreservesFiniteLimits

/-- The product comparison maps of two naturally isomorphic functors are intertwined by the
natural isomorphism. -/
lemma naturalIso_prodComparison_coherence
    {C : Type u} [Category.{v, u} C] {D : Type u'} [Category.{v', u'} D]
    (F G : C ⥤ D) (α : F ≅ G) (X Y : C)
    [HasBinaryProduct X Y]
    [HasBinaryProduct (F.obj X) (F.obj Y)]
    [HasBinaryProduct (G.obj X) (G.obj Y)] :
    prodComparison F X Y ≫ prod.map (α.hom.app X) (α.hom.app Y) =
      α.hom.app (X ⨯ Y) ≫ prodComparison G X Y := by
  apply Limits.prod.hom_ext
  · calc
      (prodComparison F X Y ≫ prod.map (α.hom.app X) (α.hom.app Y)) ≫ prod.fst =
          F.map prod.fst ≫ α.hom.app X := by simp
      _ = α.hom.app (X ⨯ Y) ≫ G.map prod.fst := α.hom.naturality _
      _ = (α.hom.app (X ⨯ Y) ≫ prodComparison G X Y) ≫ prod.fst := by simp
  · calc
      (prodComparison F X Y ≫ prod.map (α.hom.app X) (α.hom.app Y)) ≫ prod.snd =
          F.map prod.snd ≫ α.hom.app Y := by simp
      _ = α.hom.app (X ⨯ Y) ≫ G.map prod.snd := α.hom.naturality _
      _ = (α.hom.app (X ⨯ Y) ≫ prodComparison G X Y) ≫ prod.snd := by simp

/-- The addition of a sheaf of modules `M` transported along a functor `F` preserving the product
`M ⨯ M`: the morphism `F M ⨯ F M ⟶ F M` obtained from `F` applied to the addition of `M`. -/
noncomputable def transportedModuleAddition
    {C : Type u} [Category.{v, u} C] {D : Type u'} [Category.{v', u'} D]
    {J : GrothendieckTopology C} {O : Sheaf J RingCat.{w}}
    (F : SheafOfModules.{x} O ⥤ D) (M : SheafOfModules.{x} O)
    [HasBinaryProduct (F.obj M) (F.obj M)]
    [IsIso (prodComparison F M M)] : F.obj M ⨯ F.obj M ⟶ F.obj M :=
  inv (prodComparison F M M) ≫ F.map (modulePlusHom M)

/-- A natural isomorphism of functors intertwines the transported additions. -/
lemma naturalIso_transportedModuleAddition
    {C : Type u} [Category.{v, u} C] {D : Type u'} [Category.{v', u'} D]
    {J : GrothendieckTopology C} {O : Sheaf J RingCat.{w}}
    (F G : SheafOfModules.{x} O ⥤ D) (α : F ≅ G)
    (M : SheafOfModules.{x} O)
    [HasBinaryProduct (F.obj M) (F.obj M)] [IsIso (prodComparison F M M)]
    [HasBinaryProduct (G.obj M) (G.obj M)] [IsIso (prodComparison G M M)] :
    transportedModuleAddition F M ≫ α.hom.app M =
      prod.map (α.hom.app M) (α.hom.app M) ≫ transportedModuleAddition G M := by
  have hc := naturalIso_prodComparison_coherence F G α M M
  have hci : inv (prodComparison F M M) ≫ α.hom.app (M ⨯ M) =
      prod.map (α.hom.app M) (α.hom.app M) ≫ inv (prodComparison G M M) := by
    have hh := congrArg (fun q => inv (prodComparison F M M) ≫ q ≫
      inv (prodComparison G M M)) hc
    simpa [Category.assoc] using hh.symm
  change (inv (prodComparison F M M) ≫ F.map (modulePlusHom M)) ≫ α.hom.app M =
    prod.map (α.hom.app M) (α.hom.app M) ≫
      (inv (prodComparison G M M) ≫ G.map (modulePlusHom M))
  calc
    (inv (prodComparison F M M) ≫ F.map (modulePlusHom M)) ≫ α.hom.app M =
        (inv (prodComparison F M M) ≫ α.hom.app (M ⨯ M)) ≫ G.map (modulePlusHom M) := by
      calc
        (inv (prodComparison F M M) ≫ F.map (modulePlusHom M)) ≫ α.hom.app M =
            inv (prodComparison F M M) ≫
              (F.map (modulePlusHom M) ≫ α.hom.app M) := by simp [Category.assoc]
        _ = inv (prodComparison F M M) ≫
              (α.hom.app (M ⨯ M) ≫ G.map (modulePlusHom M)) := by
          rw [α.hom.naturality]
        _ = (inv (prodComparison F M M) ≫ α.hom.app (M ⨯ M)) ≫
              G.map (modulePlusHom M) := by simp [Category.assoc]
    _ = prod.map (α.hom.app M) (α.hom.app M) ≫
          (inv (prodComparison G M M) ≫ G.map (modulePlusHom M)) := by
      rw [hci]
      exact Category.assoc _ _ _

/-- An additive functor between sheaves of modules carries the addition of `M` to the addition of
its image, up to the product comparison. -/
lemma map_modulePlusHom
    {C : Type u} [Category.{v, u} C] {D : Type u'} [Category.{v', u'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {O : Sheaf J RingCat.{w}} {O' : Sheaf K RingCat.{w'}}
    (F : SheafOfModules.{x} O ⥤ SheafOfModules.{x'} O') [F.Additive]
    (M : SheafOfModules.{x} O) :
    prodComparison F M M ≫ modulePlusHom (F.obj M) = F.map (modulePlusHom M) := by
  simp [modulePlusHom, Functor.map_add]

lemma transportedModuleAddition_apply
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {O : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} O)
    [IsIso (prodComparison (Sheaf.moduleSheafFunctor O) M M)]
    (U : Cᵒᵖ)
    (element : ((Stacks.underlyingModuleSheaf J M) ⨯
      (Stacks.underlyingModuleSheaf J M)).obj.obj U) :
    (transportedModuleAddition (Sheaf.moduleSheafFunctor O) M).hom.app U
        element =
      (show M.val.obj U from (prod.fst : Stacks.underlyingModuleSheaf J M ⨯
        Stacks.underlyingModuleSheaf J M ⟶ _).hom.app U element) +
      (show M.val.obj U from (prod.snd : Stacks.underlyingModuleSheaf J M ⨯
        Stacks.underlyingModuleSheaf J M ⟶ _).hom.app U element) := by
  let H := Sheaf.moduleSheafFunctor O
  have h₁ : inv (prodComparison H M M) ≫ H.map prod.fst = prod.fst := by
    rw [← prodComparison_fst, IsIso.inv_hom_id_assoc]
  have h₂ : inv (prodComparison H M M) ≫ H.map prod.snd = prod.snd := by
    rw [← prodComparison_snd, IsIso.inv_hom_id_assoc]
  change (show M.val.obj U from (H.map prod.fst).hom.app U
      ((inv (prodComparison H M M)).hom.app U element)) +
    (show M.val.obj U from (H.map prod.snd).hom.app U
      ((inv (prodComparison H M M)).hom.app U element)) = _
  exact congrArg₂ (fun (left right : M.val.obj U) => left + right)
    (congrArg (fun g => g.hom.app U element) h₁) (congrArg (fun g => g.hom.app U element) h₂)

private lemma transportedModuleAddition_comp
    {C : Type u} [Category.{v, u} C] {D : Type u'} [Category.{v', u'} D]
    {E : Type w'} [Category.{v', w'} E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology E}
    {O : Sheaf J RingCat.{w}} {O' : Sheaf K RingCat.{w'}}
    (F : SheafOfModules.{x} O ⥤ SheafOfModules.{x'} O')
    (G : SheafOfModules.{x'} O' ⥤ D)
    (M : SheafOfModules.{x} O) [F.Additive]
    [HasBinaryProduct (F.obj M) (F.obj M)]
    [HasBinaryProduct ((F ⋙ G).obj M) ((F ⋙ G).obj M)]
    [HasBinaryProduct (G.obj (F.obj M)) (G.obj (F.obj M))]
    [IsIso (prodComparison F M M)]
    [IsIso (prodComparison (F ⋙ G) M M)]
    [IsIso (prodComparison G (F.obj M) (F.obj M))] :
    transportedModuleAddition (F ⋙ G) M =
      transportedModuleAddition G (F.obj M) := by
  simp only [transportedModuleAddition, prodComparison_comp, Functor.comp_map]
  rw [← map_modulePlusHom F M]
  simp [Functor.map_comp, Category.assoc]

/-- The image of `prod.lift f g` under a functor, followed by the product comparison, is
`prod.lift (F.map f) (F.map g)`. -/
lemma map_prod_lift
    {C : Type u} [Category.{v, u} C] {D : Type u'} [Category.{v', u'} D]
    (F : C ⥤ D) {X A B : C}
    [HasBinaryProduct A B] [HasBinaryProduct (F.obj A) (F.obj B)]
    (f : X ⟶ A) (g : X ⟶ B) :
    F.map (Limits.prod.lift f g) ≫ prodComparison F A B =
      Limits.prod.lift (F.map f) (F.map g) := by
  apply Limits.prod.hom_ext
  · rw [Category.assoc, prodComparison_fst, ← F.map_comp]
    simp
  · rw [Category.assoc, prodComparison_snd, ← F.map_comp]
    simp

/-- A morphism `X ⨯ Y ⟶ Z` transported along a functor `F` preserving the product `X ⨯ Y`: the
morphism `F X ⨯ F Y ⟶ F Z` given by the inverse product comparison followed by `F.map m`. -/
noncomputable def transportedBinaryMap
    {C : Type u} [Category.{v, u} C] {D : Type u'} [Category.{v', u'} D]
    (F : C ⥤ D) (X Y Z : C) [HasBinaryProduct X Y]
    [HasBinaryProduct (F.obj X) (F.obj Y)]
    [IsIso (prodComparison F X Y)] (m : X ⨯ Y ⟶ Z) :
    F.obj X ⨯ F.obj Y ⟶ F.obj Z :=
  inv (prodComparison F X Y) ≫ F.map m

/-- The sections over `U` of a binary product of sheaves of sets are the binary product of the
sections over `U`. -/
noncomputable def sheafProductSectionsIso
    {C : Type u} [Category.{v, u} C] {J : GrothendieckTopology C}
    (M N : Sheaf J (Type x)) (U : Cᵒᵖ) :
    (M ⨯ N).obj.obj U ≅ M.obj.obj U ⨯ N.obj.obj U := by
  let F := sheafToPresheaf J (Type x) ⋙
    (CategoryTheory.evaluation (Cᵒᵖ) (Type x)).obj U
  change F.obj (M ⨯ N) ≅ F.obj M ⨯ F.obj N
  exact asIso (Limits.prodComparison F M N)

/-- The element of the categorical product `α ⨯ β` of types corresponding to the pair `(x, y)`. -/
noncomputable def typeProductElement {α β : Type u'} (x : α) (y : β) : α ⨯ β :=
  (Limits.Concrete.prodEquiv α β).symm (x, y)

/-- If a morphism `m : X ⨯ Y ⟶ Z` is additive in its second argument with respect to binary
operations `plusY` and `plusZ`, then so is its transport along `F`, with respect to the transported
operations. -/
lemma transportedBinaryMap_add_right
    {C : Type u} [Category.{v, u} C] {D : Type u'} [Category.{v', u'} D]
    (F : C ⥤ D) (X Y Z : C)
    [HasBinaryProduct X Y] [HasBinaryProduct Y Y] [HasBinaryProduct Z Z]
    [HasBinaryProduct (Y ⨯ Y) X] [HasBinaryProduct X (Y ⨯ Y)]
    [HasBinaryProduct (F.obj X) (F.obj Y)]
    [HasBinaryProduct (F.obj Y) (F.obj Y)]
    [HasBinaryProduct (F.obj Z) (F.obj Z)]
    [HasBinaryProduct (F.obj X) (F.obj Y ⨯ F.obj Y)]
    [HasBinaryProduct (F.obj X) (F.obj (Y ⨯ Y))]
    [HasBinaryProduct (F.obj X ⨯ F.obj Y) (F.obj X ⨯ F.obj Y)]
    [IsIso (prodComparison F X Y)]
    [IsIso (prodComparison F Y Y)]
    [IsIso (prodComparison F Z Z)]
    [IsIso (prodComparison F X (Y ⨯ Y))]
    (plusY : Y ⨯ Y ⟶ Y) (plusZ : Z ⨯ Z ⟶ Z) (m : X ⨯ Y ⟶ Z)
    (h : (Limits.prod.lift Limits.prod.fst
        (Limits.prod.snd ≫ plusY)) ≫ m =
      Limits.prod.lift
        ((Limits.prod.lift Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.fst)) ≫ m)
        ((Limits.prod.lift Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.snd)) ≫ m) ≫ plusZ) :
    (Limits.prod.lift Limits.prod.fst
        (Limits.prod.snd ≫ transportedBinaryMap F Y Y Y plusY)) ≫
        transportedBinaryMap F X Y Z m =
      Limits.prod.lift
        ((Limits.prod.lift Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.fst) ≫
          transportedBinaryMap F X Y Z m))
        ((Limits.prod.lift Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.snd) ≫
          transportedBinaryMap F X Y Z m)) ≫
        transportedBinaryMap F Z Z Z plusZ := by
  let e := prodComparison F X (Y ⨯ Y) ≫
    prod.map (𝟙 (F.obj X)) (prodComparison F Y Y)
  have he : IsIso e := by dsimp [e]; infer_instance
  have key : ∀ (q : Y ⨯ Y ⟶ Y) (q' : F.obj Y ⨯ F.obj Y ⟶ F.obj Y),
      prodComparison F Y Y ≫ q' = F.map q →
      e ≫ Limits.prod.lift Limits.prod.fst (Limits.prod.snd ≫ q') =
        F.map (Limits.prod.lift Limits.prod.fst (Limits.prod.snd ≫ q)) ≫
          prodComparison F X Y := by
    intro q q' hq
    apply Limits.prod.hom_ext
    · simp [e, Category.assoc, ← Functor.map_comp]
    · simp [e, Category.assoc, hq, ← Functor.map_comp]
  have hplus := key plusY (transportedBinaryMap F Y Y Y plusY) (by simp [transportedBinaryMap])
  have hfst := key Limits.prod.fst Limits.prod.fst (prodComparison_fst F Y Y)
  have hsnd := key Limits.prod.snd Limits.prod.snd (prodComparison_snd F Y Y)
  have hrhs : e ≫
      (Limits.prod.lift
        ((Limits.prod.lift Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.fst) ≫
          transportedBinaryMap F X Y Z m))
        ((Limits.prod.lift Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.snd) ≫
          transportedBinaryMap F X Y Z m)) ≫
        transportedBinaryMap F Z Z Z plusZ) =
      F.map (Limits.prod.lift
        ((Limits.prod.lift Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.fst) ≫ m))
        ((Limits.prod.lift Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.snd) ≫ m)) ≫ plusZ) := by
    let p₁ : X ⨯ (Y ⨯ Y) ⟶ X ⨯ Y :=
      Limits.prod.lift Limits.prod.fst
        (Limits.prod.snd ≫ (Limits.prod.fst : Y ⨯ Y ⟶ Y))
    let p₂ : X ⨯ (Y ⨯ Y) ⟶ X ⨯ Y :=
      Limits.prod.lift Limits.prod.fst
        (Limits.prod.snd ≫ (Limits.prod.snd : Y ⨯ Y ⟶ Y))
    have hprod : e ≫ Limits.prod.lift
        (Limits.prod.lift Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.fst) ≫
          transportedBinaryMap F X Y Z m)
        (Limits.prod.lift Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.snd) ≫
          transportedBinaryMap F X Y Z m) =
        Limits.prod.lift (F.map (p₁ ≫ m)) (F.map (p₂ ≫ m)) := by
      apply Limits.prod.hom_ext
      · simp only [Category.assoc, Limits.prod.lift_fst]
        rw [← Category.assoc, hfst]
        simp [Category.assoc, transportedBinaryMap, p₁]
      · simp only [Category.assoc, Limits.prod.lift_snd]
        rw [← Category.assoc, hsnd]
        simp [Category.assoc, transportedBinaryMap, p₂]
    rw [← Category.assoc, hprod]
    change Limits.prod.lift (F.map (p₁ ≫ m)) (F.map (p₂ ≫ m)) ≫
        (inv (prodComparison F Z Z) ≫ F.map plusZ) =
      F.map (Limits.prod.lift (p₁ ≫ m) (p₂ ≫ m) ≫ plusZ)
    rw [← map_prod_lift F (p₁ ≫ m) (p₂ ≫ m)]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, Functor.map_comp]
  apply (cancel_epi e).1
  calc
    e ≫ (Limits.prod.lift Limits.prod.fst
        (Limits.prod.snd ≫ transportedBinaryMap F Y Y Y plusY) ≫
        transportedBinaryMap F X Y Z m) =
      F.map (Limits.prod.lift Limits.prod.fst (Limits.prod.snd ≫ plusY) ≫ m) := by
        rw [← Category.assoc, hplus]
        simp [transportedBinaryMap, Category.assoc]
    _ = F.map (Limits.prod.lift
          ((Limits.prod.lift Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.fst) ≫ m))
          ((Limits.prod.lift Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.snd) ≫ m)) ≫ plusZ) :=
        congrArg F.map h
    _ = e ≫
        (Limits.prod.lift
          ((Limits.prod.lift Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.fst) ≫
            transportedBinaryMap F X Y Z m))
          ((Limits.prod.lift Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.snd) ≫
            transportedBinaryMap F X Y Z m)) ≫
          transportedBinaryMap F Z Z Z plusZ) := hrhs.symm

/-- The comparison between the underlying sheaf of a direct image of modules and the direct image
of the underlying sheaf intertwines the two additions. -/
lemma pushforwardModulesUnderlyingIso_addition
    {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
    (f : RingedToposHom X Y)
    (M : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
    [IsIso (prodComparison
      (f.pushforwardModules ⋙
        Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) M M)]
    [IsIso (prodComparison
      (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
        f.toToposHom.pushforward) M M)] :
    transportedModuleAddition
        (f.pushforwardModules ⋙
          Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) M ≫
      f.pushforwardModulesUnderlyingIso.hom.app M =
    prod.map
        (f.pushforwardModulesUnderlyingIso.hom.app M)
        (f.pushforwardModulesUnderlyingIso.hom.app M) ≫
      transportedModuleAddition
        (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
          f.toToposHom.pushforward) M :=
  naturalIso_transportedModuleAddition _ _ f.pushforwardModulesUnderlyingIso M

lemma pushforwardModules_underlying_plus_naturality
    {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{u', u', u'}}
    (f : RingedToposHom X Y)
    (M : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
    [IsIso (prodComparison
      (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
        f.toToposHom.pushforward) M M)] :
    transportedModuleAddition
        (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
        (f.pushforwardModules.obj M) ≫
      f.pushforwardModulesUnderlyingIso.hom.app M =
      prod.map
        (f.pushforwardModulesUnderlyingIso.hom.app M)
        (f.pushforwardModulesUnderlyingIso.hom.app M) ≫
      transportedModuleAddition
        (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
          f.toToposHom.pushforward) M := by
  let P := f.pushforwardModules
  let H := Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)
  let H₀ := Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)
  let G := H₀ ⋙ f.toToposHom.pushforward
  let α := f.pushforwardModulesUnderlyingIso
  have : P.IsRightAdjoint := (f.pullbackAdjPushforwardModulesViaComparison).isRightAdjoint
  have : f.toToposHom.pushforward.IsRightAdjoint := f.toToposHom.adj.isRightAdjoint
  have : P.Additive := pushforwardModules_additive f
  have : PreservesFiniteLimits H := by
    dsimp [H, Sheaf.moduleSheafFunctor]
    exact comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits H₀ := by
    dsimp [H₀, Sheaf.moduleSheafFunctor]
    exact comp_preservesFiniteLimits _ _
  have : IsIso (prodComparison P M M) := by infer_instance
  have : IsIso (prodComparison H (P.obj M) (P.obj M)) := by infer_instance
  have : IsIso (prodComparison (P ⋙ H) M M) := by infer_instance
  have : IsIso (prodComparison G M M) := by infer_instance
  have hcomp : transportedModuleAddition (P ⋙ H) M =
      transportedModuleAddition H (P.obj M) :=
    transportedModuleAddition_comp P H M
  have hadd := pushforwardModulesUnderlyingIso_addition f M
  rw [hcomp] at hadd
  simpa [P, H, H₀, G, α] using hadd

end Stacks.Sheaves.GradedAlgebraPushforward
