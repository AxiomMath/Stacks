module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushforwardEssentiallySmall.Specification

/-!
# Pushforward of a graded algebra at unrelated universes: the multiplication on local sections

The multiplication of the direct image of a graded algebra, read on local sections through
`pushedSectionEquiv`, is `transposedMultiplicationAt`. This file shows that it is additive and
linear in each variable, and packages it as the bilinear map `pushforwardBilinearMap`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open AlgebraicGeometry Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sites.SheafSection
open scoped Stacks.Sites.SheafSection.OfEssentiallySmall

namespace Stacks.Sheaves.GradedAlgebraEssentiallySmall

open Stacks.Sheaves.GradedAlgebraPushforward

universe u u' u₂ v v' v₂ w w' x x' u₁ u₁'

private lemma pushforwardModules_additive
    {X : RingedTopos.{v, u₁, w}}
    {Y : RingedTopos.{v', u₁', w'}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (f : RingedToposHom X Y) :
    Functor.Additive
      (f.pushforwardModules) := by
  have : (f.pushforwardModules).IsRightAdjoint :=
    (f.pullbackAdjPushforwardModulesViaComparison).isRightAdjoint
  exact Functor.additive_of_preserves_binary_products _

private lemma underlyingAdditiveSheafPreservesFiniteLimits
    {C : Type u} [Category.{v, u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget AddCommGrpCat.{w})] :
    PreservesFiniteLimits (sheafCompose J (forget AddCommGrpCat.{w})) := by
  have : PreservesFiniteLimits
      (sheafCompose J (forget AddCommGrpCat.{w}) ⋙ sheafToPresheaf J (Type w)) := by
    change PreservesFiniteLimits
      (sheafToPresheaf J AddCommGrpCat.{w} ⋙
        (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{w} (Type w)).obj
          (forget AddCommGrpCat.{w}))
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J _)

attribute [local instance] underlyingAdditiveSheafPreservesFiniteLimits

private lemma transportedModuleAddition_apply
    {C : Type u} [Category.{v, u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    {O : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} O)
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
  have first : inv (prodComparison H M M) ≫ H.map prod.fst = prod.fst := by
    rw [← prodComparison_fst, IsIso.inv_hom_id_assoc]
  have second : inv (prodComparison H M M) ≫ H.map prod.snd = prod.snd := by
    rw [← prodComparison_snd, IsIso.inv_hom_id_assoc]
  change (H.map (modulePlusHom M)).hom.app U
    ((inv (prodComparison H M M)).hom.app U element) = _
  change (show M.val.obj U from (H.map prod.fst).hom.app U
      ((inv (prodComparison H M M)).hom.app U element)) +
    (show M.val.obj U from (H.map prod.snd).hom.app U
      ((inv (prodComparison H M M)).hom.app U element)) = _
  exact congrArg₂ (fun (left right : M.val.obj U) => left + right)
    (congrArg (fun morphism => morphism.hom.app U element) first)
    (congrArg (fun morphism => morphism.hom.app U element) second)

private lemma transportedModuleAddition_comp
    {C : Type u} [Category.{v, u} C] {D : Type u'} [Category.{v', u'} D]
    {E : Type u₂} [Category.{v₂, u₂} E]
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

/-- Two local sections of a direct image are equal if their transposes agree on all elements. -/
private lemma pushedSectionEquiv_ext
    {X : RingedTopos.{v, u₁, w}} {Y : RingedTopos.{v', u₁', w'}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] [EssentiallySmall.{w'} Y.C]
    {f : RingedToposHom X Y}
    {M : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)} {U : Y.Cᵒᵖ}
    {a b : (f.pushforwardModules.obj M).val.obj U}
    (h : ∀ (V : X.Cᵒᵖ)
      (element : (f.toToposHom.inverseImage.obj
        ((presheafToSheaf Y.J (Type w')).obj (smallYoneda.{w'} U.unop))).obj.obj V),
      (pushedSectionEquiv f M U a).hom.app V element =
        (pushedSectionEquiv f M U b).hom.app V element) :
    a = b := by
  apply (pushedSectionEquiv f M U).injective
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  exact h V

variable {X : RingedTopos.{v, u₁, w}} {Y : RingedTopos.{v', u₁', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [EssentiallySmall.{w} X.C] [EssentiallySmall.{w'} Y.C]

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] [EssentiallySmall.{w'} Y.C] in
private lemma pushforwardModules_underlying_plus_naturality
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
  have := f.pullbackAdjPushforwardModulesViaComparison
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
      transportedModuleAddition H (P.obj M) := transportedModuleAddition_comp P H M
  have hadd := pushforwardModulesUnderlyingIso_addition f M
  rw [hcomp] at hadd
  simpa [P, H, H₀, G, α] using hadd

/-- **The multiplication of the direct image of a graded algebra, on local sections.** Two
sections of direct-image pieces over `U` are transposed to morphisms out of the inverse image
of the sheafified Yoneda object of `U`, paired, multiplied in the source algebra, and transposed
back. -/
public noncomputable def transposedMultiplicationAt
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (i j : ℤ) (U : Y.Cᵒᵖ)
    (left : (f.pushforwardModules.obj
      (A.piece i)).val.obj U)
    (right : (f.pushforwardModules.obj
      (A.piece j)).val.obj U) :
    (f.pushforwardModules.obj
      (A.piece (i + j))).val.obj U :=
  (pushedSectionEquiv f (A.piece (i + j)) U).symm
    (prod.lift (pushedSectionEquiv f (A.piece i) U left)
      (pushedSectionEquiv f (A.piece j) U right) ≫ multiplicationSheafMap A i j)

private noncomputable def sheafPair
    {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} [EssentiallySmall.{w} C]
    (M N : Sheaf J (Type w)) (U : Cᵒᵖ) (left : M.obj.obj U) (right : N.obj.obj U) :
    (M ⨯ N).obj.obj U :=
  (sectionEquivSmall J U (M ⨯ N)).symm
    (prod.lift (sectionEquivSmall J U M left) (sectionEquivSmall J U N right))

private lemma sheafPair_fst
    {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} [EssentiallySmall.{w} C]
    (M N : Sheaf J (Type w)) (U : Cᵒᵖ) (left : M.obj.obj U) (right : N.obj.obj U) :
    (prod.fst : M ⨯ N ⟶ M).hom.app U (sheafPair M N U left right) = left := by
  apply (sectionEquivSmall J U M).injective
  rw [sectionEquivSmall_comp]
  simp [sheafPair]

private lemma sheafPair_snd
    {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} [EssentiallySmall.{w} C]
    (M N : Sheaf J (Type w)) (U : Cᵒᵖ) (left : M.obj.obj U) (right : N.obj.obj U) :
    (prod.snd : M ⨯ N ⟶ N).hom.app U (sheafPair M N U left right) = right := by
  apply (sectionEquivSmall J U N).injective
  rw [sectionEquivSmall_comp]
  simp [sheafPair]

private lemma sheafPair_eta
    {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} [EssentiallySmall.{w} C]
    (M N : Sheaf J (Type w)) (U : Cᵒᵖ) (element : (M ⨯ N).obj.obj U) :
    sheafPair M N U ((prod.fst : M ⨯ N ⟶ M).hom.app U element)
      ((prod.snd : M ⨯ N ⟶ N).hom.app U element) = element := by
  apply (sectionEquivSmall J U (M ⨯ N)).injective
  simp only [sheafPair, Equiv.apply_symm_apply, sectionEquivSmall_comp]
  apply prod.hom_ext <;> simp

private lemma sheafPair_map
    {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} [EssentiallySmall.{w} C]
    {M N P Q : Sheaf J (Type w)} (leftMap : M ⟶ P) (rightMap : N ⟶ Q)
    (U : Cᵒᵖ) (left : M.obj.obj U) (right : N.obj.obj U) :
    (prod.map leftMap rightMap).hom.app U (sheafPair M N U left right) =
      sheafPair P Q U (leftMap.hom.app U left) (rightMap.hom.app U right) := by
  apply (sectionEquivSmall J U (P ⨯ Q)).injective
  simp only [sectionEquivSmall_comp, sheafPair, Equiv.apply_symm_apply]
  apply prod.hom_ext <;> simp

private lemma sheafPair_prodMap_fst
    {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} [EssentiallySmall.{w} C]
    {M N P Q : Sheaf J (Type w)} (leftMap : M ⟶ P) (rightMap : N ⟶ Q)
    (U : Cᵒᵖ) (left : M.obj.obj U) (right : N.obj.obj U) :
    (prod.fst : P ⨯ Q ⟶ P).hom.app U
        ((prod.map leftMap rightMap).hom.app U (sheafPair M N U left right)) =
      leftMap.hom.app U left := by
  rw [sheafPair_map, sheafPair_fst]

private lemma sheafPair_prodMap_snd
    {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} [EssentiallySmall.{w} C]
    {M N P Q : Sheaf J (Type w)} (leftMap : M ⟶ P) (rightMap : N ⟶ Q)
    (U : Cᵒᵖ) (left : M.obj.obj U) (right : N.obj.obj U) :
    (prod.snd : P ⨯ Q ⟶ Q).hom.app U
        ((prod.map leftMap rightMap).hom.app U (sheafPair M N U left right)) =
      rightMap.hom.app U right := by
  rw [sheafPair_map, sheafPair_snd]

private lemma sheafPair_restrict_fst
    {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} [EssentiallySmall.{w} C]
    (M N : Sheaf J (Type w)) {U V : Cᵒᵖ} (morphism : U ⟶ V)
    (left : M.obj.obj U) (right : N.obj.obj U) :
    (prod.fst : M ⨯ N ⟶ M).hom.app V
        ((M ⨯ N).obj.map morphism (sheafPair M N U left right)) =
      M.obj.map morphism left := by
  have naturality := congrArg (fun component => component (sheafPair M N U left right))
    ((prod.fst : M ⨯ N ⟶ M).hom.naturality morphism)
  simp only [CategoryTheory.comp_apply] at naturality
  rw [naturality, sheafPair_fst]

private lemma sheafPair_restrict_snd
    {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} [EssentiallySmall.{w} C]
    (M N : Sheaf J (Type w)) {U V : Cᵒᵖ} (morphism : U ⟶ V)
    (left : M.obj.obj U) (right : N.obj.obj U) :
    (prod.snd : M ⨯ N ⟶ N).hom.app V
        ((M ⨯ N).obj.map morphism (sheafPair M N U left right)) =
      N.obj.map morphism right := by
  have naturality := congrArg (fun component => component (sheafPair M N U left right))
    ((prod.snd : M ⨯ N ⟶ N).hom.naturality morphism)
  simp only [CategoryTheory.comp_apply] at naturality
  rw [naturality, sheafPair_snd]

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] in
private lemma pushedSectionEquiv_add
    (f : RingedToposHom X Y)
    (M : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) (U : Y.Cᵒᵖ)
    (left right : (f.pushforwardModules.obj
      M).val.obj U) :
    pushedSectionEquiv f M U (left + right) =
      prod.lift (pushedSectionEquiv f M U left) (pushedSectionEquiv f M U right) ≫
        transportedModuleAddition
          (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
          M := by
  let H := Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)
  let H' := Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)
  let P := f.pushforwardModules
  let alpha := pushedPieceUnderlyingIso f M
  let element := sheafPair (H'.obj (P.obj M)) (H'.obj (P.obj M)) U left right
  have : f.toToposHom.pushforward.IsRightAdjoint := f.toToposHom.adj.isRightAdjoint
  have : PreservesFiniteLimits H := by
    dsimp [H, Sheaf.moduleSheafFunctor]
    exact comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits H' := by
    dsimp [H', Sheaf.moduleSheafFunctor]
    exact comp_preservesFiniteLimits _ _
  have equality := pushforwardModules_underlying_plus_naturality f M
  have addition : (transportedModuleAddition H' (P.obj M)).hom.app U element =
      left + right := by
    rw [transportedModuleAddition_apply (M := P.obj M)]
    exact congrArg₂ (fun (a b : (P.obj M).val.obj U) => a + b)
      (sheafPair_fst _ _ _ _ _) (sheafPair_snd _ _ _ _ _)
  change transposedSectionEquiv f U _ (alpha.hom.hom.app U (left + right)) = _
  rw [← addition]
  have applied := congrArg (fun morphism => morphism.hom.app U element) equality
  change alpha.hom.hom.app U ((transportedModuleAddition H' (P.obj M)).hom.app U element) =
    (transportedModuleAddition (H ⋙ f.toToposHom.pushforward) M).hom.app U
      ((prod.map alpha.hom alpha.hom).hom.app U element) at applied
  have transport : transportedModuleAddition (H ⋙ f.toToposHom.pushforward) M =
      (pushforwardProductIso f (H.obj M) (H.obj M)).inv ≫
        f.toToposHom.pushforward.map (transportedModuleAddition H M) := by
    simp [transportedModuleAddition, prodComparison_comp, pushforwardProductIso,
      Functor.map_comp, Category.assoc]
  rw [applied, transport]
  rw [transposedSectionEquiv_binary f U (H.obj M) (H.obj M)
    (Stacks.underlyingModuleSheaf X.J M)]
  have componentLeft : (prod.fst : f.toToposHom.pushforward.obj (H.obj M) ⨯
        f.toToposHom.pushforward.obj (H.obj M) ⟶ _).hom.app U
        ((prod.map alpha.hom alpha.hom).hom.app U element) =
      alpha.hom.hom.app U left :=
    sheafPair_prodMap_fst alpha.hom alpha.hom U left right
  have componentRight : (prod.snd : f.toToposHom.pushforward.obj (H.obj M) ⨯
        f.toToposHom.pushforward.obj (H.obj M) ⟶ _).hom.app U
        ((prod.map alpha.hom alpha.hom).hom.app U element) =
      alpha.hom.hom.app U right :=
    sheafPair_prodMap_snd alpha.hom alpha.hom U left right
  rw [componentLeft, componentRight]
  rfl

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] in
private lemma pushedSectionEquiv_add_apply
    (f : RingedToposHom X Y)
    (M : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) (U : Y.Cᵒᵖ)
    (left right : (f.pushforwardModules.obj
      M).val.obj U) (V : X.Cᵒᵖ)
    (element : (f.toToposHom.inverseImage.obj
      ((presheafToSheaf Y.J (Type w')).obj (smallYoneda.{w'} U.unop))).obj.obj V) :
    (pushedSectionEquiv f M U (left + right)).hom.app V element =
      (show M.val.obj V from (pushedSectionEquiv f M U left).hom.app V element) +
      (show M.val.obj V from (pushedSectionEquiv f M U right).hom.app V element) := by
  rw [pushedSectionEquiv_add, sheaf_comp_apply,
    transportedModuleAddition_apply (M := M), sheaf_lift_fst_apply, sheaf_lift_snd_apply]

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] in
/-- **The multiplication of the direct image of a graded algebra is pointwise multiplication in
the source algebra**, read through the transposed description of its local sections. -/
public lemma transposedMultiplicationAt_apply
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (i j : ℤ) (U : Y.Cᵒᵖ)
    (left : (f.pushforwardModules.obj
      (A.piece i)).val.obj U)
    (right : (f.pushforwardModules.obj
      (A.piece j)).val.obj U) (V : X.Cᵒᵖ)
    (element : (f.toToposHom.inverseImage.obj
      ((presheafToSheaf Y.J (Type w')).obj (smallYoneda.{w'} U.unop))).obj.obj V) :
    (pushedSectionEquiv f (A.piece (i + j)) U
      (transposedMultiplicationAt f A i j U left right)).hom.app V element =
      (A.mul i j).app V
        ((pushedSectionEquiv f (A.piece i) U left).hom.app V element)
        ((pushedSectionEquiv f (A.piece j) U right).hom.app V element) := by
  simp only [transposedMultiplicationAt, Equiv.apply_symm_apply, sheaf_comp_apply]
  change (A.mul i j).app V _ _ = _
  rw [sheaf_lift_fst_apply, sheaf_lift_snd_apply]

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] in
private lemma pushedSectionEquiv_transposedMultiplicationAt
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (i j : ℤ) (U : Y.Cᵒᵖ)
    (left : (f.pushforwardModules.obj (A.piece i)).val.obj U)
    (right : (f.pushforwardModules.obj (A.piece j)).val.obj U) :
    pushedSectionEquiv f (A.piece (i + j)) U
        (transposedMultiplicationAt f A i j U left right) =
      prod.lift (pushedSectionEquiv f (A.piece i) U left)
          (pushedSectionEquiv f (A.piece j) U right) ≫
        multiplicationSheafMap A i j :=
  (pushedSectionEquiv f (A.piece (i + j)) U).apply_symm_apply _

attribute [local irreducible] transposedMultiplicationAt

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] in
private lemma transposedMultiplicationAt_add_left
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (i j : ℤ) (U : Y.Cᵒᵖ)
    (left₁ left₂ : (f.pushforwardModules.obj
      (A.piece i)).val.obj U)
    (right : (f.pushforwardModules.obj
      (A.piece j)).val.obj U) :
    transposedMultiplicationAt f A i j U (left₁ + left₂) right =
      transposedMultiplicationAt f A i j U left₁ right +
        transposedMultiplicationAt f A i j U left₂ right := by
  apply pushedSectionEquiv_ext
  intro V element
  change (pushedSectionEquiv f (A.piece (i + j)) U
    (transposedMultiplicationAt f A i j U (left₁ + left₂) right)).hom.app V element = _
  rw [pushedSectionEquiv_add_apply f (A.piece (i + j))]
  rw [transposedMultiplicationAt_apply, transposedMultiplicationAt_apply,
    transposedMultiplicationAt_apply, pushedSectionEquiv_add_apply f (A.piece i)]
  change ((A.mul i j).app V (_ + _)) _ = _
  rw [map_add]
  rfl

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] in
/-- The multiplication of the direct image of a graded algebra is additive on the right. -/
public lemma transposedMultiplicationAt_add_right
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (i j : ℤ) (U : Y.Cᵒᵖ)
    (left : (f.pushforwardModules.obj
      (A.piece i)).val.obj U)
    (right₁ right₂ : (f.pushforwardModules.obj
      (A.piece j)).val.obj U) :
    transposedMultiplicationAt f A i j U left (right₁ + right₂) =
      transposedMultiplicationAt f A i j U left right₁ +
        transposedMultiplicationAt f A i j U left right₂ := by
  apply pushedSectionEquiv_ext
  intro V element
  change (pushedSectionEquiv f (A.piece (i + j)) U
    (transposedMultiplicationAt f A i j U left (right₁ + right₂))).hom.app V element = _
  rw [pushedSectionEquiv_add_apply f (A.piece (i + j))]
  rw [transposedMultiplicationAt_apply, transposedMultiplicationAt_apply,
    transposedMultiplicationAt_apply, pushedSectionEquiv_add_apply f (A.piece j)]
  exact ((A.mul i j).app V _).map_add _ _

private noncomputable def pushedScalarSection
    (f : RingedToposHom X Y) (U : Y.Cᵒᵖ)
    (scalar : ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O).obj.obj U) :
    f.toToposHom.inverseImage.obj
      ((presheafToSheaf Y.J (Type w')).obj (smallYoneda.{w'} U.unop)) ⟶
        Stacks.underlyingRingSheaf X.J X.O :=
  transposedSectionEquiv f U _
    (((sheafCompose Y.J (forget CommRingCat)).map f.fSharp ≫
      (pushforwardCommRingForgetIso f.toToposHom).hom.app X.O).hom.app U scalar)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] in
private lemma pushedSectionEquiv_smul_apply
    (f : RingedToposHom X Y)
    (M : SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) (U : Y.Cᵒᵖ)
    (scalar : ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O).obj.obj U)
    (value : (f.pushforwardModules.obj
      M).val.obj U) (V : X.Cᵒᵖ)
    (element : (f.toToposHom.inverseImage.obj
      ((presheafToSheaf Y.J (Type w')).obj (smallYoneda.{w'} U.unop))).obj.obj V) :
    (pushedSectionEquiv f M U (scalar • value)).hom.app V element =
      (show ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O).obj.obj V from
        (pushedScalarSection f U scalar).hom.app V element) •
      (show M.val.obj V from (pushedSectionEquiv f M U value).hom.app V element) := by
  let P := pushforwardCommRingModule X.J Y.J f.toToposHom X.O
  let structureMap := (Stacks.forgetCommRingSheaf Y.J).map
    (f.fSharp ≫ P.ringIso.inv)
  let ringMap := (sheafCompose Y.J (forget CommRingCat)).map
    (f.fSharp ≫ P.ringIso.inv)
  let targetScalar : ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) P.ring).obj.obj U :=
    structureMap.hom.app U scalar
  let targetValue : (P.moduleFunctor.obj M).val.obj U := value
  let pair := sheafPair (Stacks.underlyingRingSheaf Y.J P.ring)
    (Stacks.underlyingModuleSheaf Y.J (P.moduleFunctor.obj M)) U
      targetScalar targetValue
  have scalarComponent : @Eq
      (((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) P.ring).obj.obj U)
      ((prod.fst : _ ⨯ _ ⟶ Stacks.underlyingRingSheaf Y.J P.ring).hom.app U pair)
      targetScalar :=
    sheafPair_fst _ _ U targetScalar targetValue
  have valueComponent : @Eq ((P.moduleFunctor.obj M).val.obj U)
      ((prod.snd : _ ⨯ _ ⟶
        Stacks.underlyingModuleSheaf Y.J (P.moduleFunctor.obj M)).hom.app U pair)
      targetValue :=
    sheafPair_snd _ _ U targetScalar targetValue
  have action : (P.action M).hom.app U pair = targetScalar • targetValue :=
    (P.action_apply M U pair).trans
      (congrArg₂ (fun (r : ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) P.ring).obj.obj U)
          (m : (P.moduleFunctor.obj M).val.obj U) => r • m)
        scalarComponent valueComponent)
  have equality := P.action_eq M
  have applied := congrArg (fun morphism => morphism.hom.app U pair) equality
  have comparison : P.productIso M = pushforwardProductIso f
      (Stacks.underlyingRingSheaf X.J X.O)
      (Stacks.underlyingModuleSheaf X.J M) := by
    apply Iso.ext
    apply prod.hom_ext
    · rw [P.productIso_hom_fst, pushforwardProductIso_hom_fst]
    · rw [P.productIso_hom_snd, pushforwardProductIso_hom_snd]
  rw [comparison] at applied
  have factor : ringMap = (sheafCompose Y.J (forget CommRingCat)).map f.fSharp := by
    dsimp only [ringMap]
    congr 1
  have comparison' : P.underlyingRingIso.hom =
      (pushforwardCommRingForgetIso f.toToposHom).hom.app X.O := by
    change ((sheafCompose Y.J (forget CommRingCat.{w'})).mapIso (Iso.refl _) ≪≫
      (pushforwardCommRingForgetIso f.toToposHom).app X.O).hom = _
    rw [Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.app_hom]
  have ringCoherence : ringMap ≫ P.underlyingRingIso.hom =
      (sheafCompose Y.J (forget CommRingCat)).map f.fSharp ≫
        (pushforwardCommRingForgetIso f.toToposHom).hom.app X.O := by
    rw [factor, comparison']
    rfl
  change (transposedSectionEquiv f U _
    (P.moduleIso.hom.app M |>.hom.app U (targetScalar • targetValue))).hom.app V element = _
  rw [← action, applied]
  have cancel := P.moduleIso.inv_hom_id_app M
  have cancelApplied := congrArg (fun morphism => morphism.hom.app U
    (((prod.map P.underlyingRingIso.hom (P.moduleIso.hom.app M) ≫
      (pushforwardProductIso f _ _).inv ≫ f.toToposHom.pushforward.map
        (P.sourceAction M)).hom.app U pair))) cancel
  change (transposedSectionEquiv f U _
    (((prod.map P.underlyingRingIso.hom (P.moduleIso.hom.app M) ≫
      (pushforwardProductIso f _ _).inv ≫ f.toToposHom.pushforward.map
        (P.sourceAction M) ≫ P.moduleIso.inv.app M ≫ P.moduleIso.hom.app M).hom.app U
          pair))).hom.app V element = _
  simp only [Iso.inv_hom_id_app]
  change (transposedSectionEquiv f U _
    ((((pushforwardProductIso f _ _).inv ≫ f.toToposHom.pushforward.map
      (P.sourceAction M)).hom.app U)
        ((prod.map P.underlyingRingIso.hom (P.moduleIso.hom.app M)).hom.app U pair))).hom.app V
          element = _
  have mapped : (prod.map P.underlyingRingIso.hom (P.moduleIso.hom.app M)).hom.app U pair =
      sheafPair (f.toToposHom.pushforward.obj (Stacks.underlyingRingSheaf X.J X.O))
        (f.toToposHom.pushforward.obj (Stacks.underlyingModuleSheaf X.J M)) U
        (P.underlyingRingIso.hom.hom.app U targetScalar)
        ((P.moduleIso.hom.app M).hom.app U targetValue) :=
    sheafPair_map _ _ U targetScalar targetValue
  rw [mapped, transposedSectionEquiv_binary, sheafPair_fst, sheafPair_snd]
  rw [sheaf_comp_apply, P.sourceAction_apply,
    sheaf_lift_fst_apply, sheaf_lift_snd_apply]
  apply congrArg₂
    (fun (scalar : ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O).obj.obj V)
    (value : M.val.obj V) => scalar • value)
  swap
  · rfl
  dsimp [targetScalar, structureMap]
  have ringApplied := congrArg (fun morphism => morphism.hom.app U scalar) ringCoherence
  change ((transposedSectionEquiv f U _
    (P.underlyingRingIso.hom.hom.app U (ringMap.hom.app U scalar))).hom.app V element) = _
  have composed : @Eq ((f.toToposHom.pushforward.obj
        (Stacks.underlyingRingSheaf X.J X.O)).obj.obj U)
      (P.underlyingRingIso.hom.hom.app U (ringMap.hom.app U scalar))
      ((ringMap ≫ P.underlyingRingIso.hom).hom.app U scalar) :=
    (sheaf_comp_apply ringMap P.underlyingRingIso.hom U scalar).symm
  rw [composed, ringCoherence]
  rfl

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] in
/-- The multiplication of the direct image of a graded algebra is linear on the left. -/
public lemma transposedMultiplicationAt_smul_left
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (i j : ℤ) (U : Y.Cᵒᵖ)
    (scalar : ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O).obj.obj U)
    (left : (f.pushforwardModules.obj
      (A.piece i)).val.obj U)
    (right : (f.pushforwardModules.obj
      (A.piece j)).val.obj U) :
    transposedMultiplicationAt f A i j U (scalar • left) right =
      scalar • transposedMultiplicationAt f A i j U left right := by
  apply pushedSectionEquiv_ext
  intro V element
  change (pushedSectionEquiv f (A.piece (i + j)) U
    (transposedMultiplicationAt f A i j U (scalar • left) right)).hom.app V element = _
  rw [transposedMultiplicationAt_apply, pushedSectionEquiv_smul_apply,
    pushedSectionEquiv_smul_apply, transposedMultiplicationAt_apply]
  exact (A.mul i j).map_smul_left V _ _ _

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] in
/-- The multiplication of the direct image of a graded algebra is linear on the right. -/
public lemma transposedMultiplicationAt_smul_right
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (i j : ℤ) (U : Y.Cᵒᵖ)
    (scalar : ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O).obj.obj U)
    (left : (f.pushforwardModules.obj
      (A.piece i)).val.obj U)
    (right : (f.pushforwardModules.obj
      (A.piece j)).val.obj U) :
    transposedMultiplicationAt f A i j U left (scalar • right) =
      scalar • transposedMultiplicationAt f A i j U left right := by
  apply pushedSectionEquiv_ext
  intro V element
  change (pushedSectionEquiv f (A.piece (i + j)) U
    (transposedMultiplicationAt f A i j U left (scalar • right))).hom.app V element = _
  rw [transposedMultiplicationAt_apply, pushedSectionEquiv_smul_apply,
    pushedSectionEquiv_smul_apply, transposedMultiplicationAt_apply]
  exact (A.mul i j).map_smul_right V _ _ _

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [EssentiallySmall.{w} X.C] in
lemma pushedMultiplicationSheafMap_apply
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (i j : ℤ) (U : Y.Cᵒᵖ)
    (element : (Stacks.underlyingModuleSheaf Y.J
        (f.pushforwardModules.obj
          (A.piece i)) ⨯ Stacks.underlyingModuleSheaf Y.J
        (f.pushforwardModules.obj
          (A.piece j))).obj.obj U) :
    (pushedMultiplicationSheafMap f A i j).hom.app U element =
      transposedMultiplicationAt f A i j U
        ((prod.fst : _ ⨯ _ ⟶ Stacks.underlyingModuleSheaf Y.J
          (f.pushforwardModules.obj
            (A.piece i))).hom.app U element)
        ((prod.snd : _ ⨯ _ ⟶ Stacks.underlyingModuleSheaf Y.J
          (f.pushforwardModules.obj
            (A.piece j))).hom.app U element) := by
  apply (pushedSectionEquiv f (A.piece (i + j)) U).injective
  change transposedSectionEquiv f U _
    ((pushedPieceUnderlyingIso f (A.piece (i + j))).hom.hom.app U
      ((pushedMultiplicationSheafMap f A i j).hom.app U element)) = _
  rw [← sheaf_comp_apply]
  dsimp only [pushedMultiplicationSheafMap]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change transposedSectionEquiv f U _
    ((pushforwardMultiplicationMap f A i j).hom.app U
      ((prod.map (pushedPieceUnderlyingIso f (A.piece i)).hom
        (pushedPieceUnderlyingIso f (A.piece j)).hom).hom.app U element)) = _
  rw [pushforwardMultiplicationMap, transposedSectionEquiv_binary]
  have target : pushedSectionEquiv f (A.piece (i + j)) U
        (transposedMultiplicationAt f A i j U
          ((prod.fst : _ ⨯ _ ⟶ Stacks.underlyingModuleSheaf Y.J
            (f.pushforwardModules.obj (A.piece i))).hom.app U element)
          ((prod.snd : _ ⨯ _ ⟶ Stacks.underlyingModuleSheaf Y.J
            (f.pushforwardModules.obj (A.piece j))).hom.app U element)) =
      prod.lift
          (pushedSectionEquiv f (A.piece i) U
            ((prod.fst : _ ⨯ _ ⟶ Stacks.underlyingModuleSheaf Y.J
              (f.pushforwardModules.obj (A.piece i))).hom.app U element))
          (pushedSectionEquiv f (A.piece j) U
            ((prod.snd : _ ⨯ _ ⟶ Stacks.underlyingModuleSheaf Y.J
              (f.pushforwardModules.obj (A.piece j))).hom.app U element)) ≫
        multiplicationSheafMap A i j :=
    pushedSectionEquiv_transposedMultiplicationAt f A i j U _ _
  rw [target, prodMap_fst_apply, prodMap_snd_apply]
  rfl

/-- **The multiplication of the direct image of a graded algebra**, as a bilinear map of
sheaves of modules. Its value on local sections is `transposedMultiplicationAt`. -/
public noncomputable def pushforwardBilinearMap
    (f : RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))
    (i j : ℤ) :
    SheafOfModules.BilinearMap
      (f.pushforwardModules.obj
        (A.piece i))
      (f.pushforwardModules.obj
        (A.piece j))
      (f.pushforwardModules.obj
        (A.piece (i + j))) where
  app U := AddMonoidHom.mk'
    (fun left => AddMonoidHom.mk' (transposedMultiplicationAt f A i j U left)
      (transposedMultiplicationAt_add_right f A i j U left))
    (fun left₁ left₂ => by
      ext right
      exact transposedMultiplicationAt_add_left f A i j U left₁ left₂ right)
  map_smul_left := transposedMultiplicationAt_smul_left f A i j
  map_smul_right := transposedMultiplicationAt_smul_right f A i j
  naturality {U V} morphism left right := by
    let element := sheafPair
      (Stacks.underlyingModuleSheaf Y.J
        (f.pushforwardModules.obj
          (A.piece i)))
      (Stacks.underlyingModuleSheaf Y.J
        (f.pushforwardModules.obj
          (A.piece j))) U left right
    have equality := congrArg (fun component => component element)
      ((pushedMultiplicationSheafMap f A i j).hom.naturality morphism)
    simp only [CategoryTheory.comp_apply] at equality
    rw [pushedMultiplicationSheafMap_apply, pushedMultiplicationSheafMap_apply] at equality
    have sourceLeft : @Eq ((f.pushforwardModules.obj (A.piece i)).val.obj U)
        ((prod.fst : _ ⨯ _ ⟶ Stacks.underlyingModuleSheaf Y.J
          (f.pushforwardModules.obj (A.piece i))).hom.app U element) left :=
      sheafPair_fst _ _ U left right
    have sourceRight : @Eq ((f.pushforwardModules.obj (A.piece j)).val.obj U)
        ((prod.snd : _ ⨯ _ ⟶ Stacks.underlyingModuleSheaf Y.J
          (f.pushforwardModules.obj (A.piece j))).hom.app U element) right :=
      sheafPair_snd _ _ U left right
    have targetLeft : @Eq ((f.pushforwardModules.obj (A.piece i)).val.obj V)
        ((prod.fst : _ ⨯ _ ⟶ Stacks.underlyingModuleSheaf Y.J
            (f.pushforwardModules.obj (A.piece i))).hom.app V
          ((Stacks.underlyingModuleSheaf Y.J (f.pushforwardModules.obj (A.piece i)) ⨯
            Stacks.underlyingModuleSheaf Y.J
              (f.pushforwardModules.obj (A.piece j))).obj.map morphism element))
        ((f.pushforwardModules.obj (A.piece i)).val.map morphism left) :=
      sheafPair_restrict_fst _ _ morphism left right
    have targetRight : @Eq ((f.pushforwardModules.obj (A.piece j)).val.obj V)
        ((prod.snd : _ ⨯ _ ⟶ Stacks.underlyingModuleSheaf Y.J
            (f.pushforwardModules.obj (A.piece j))).hom.app V
          ((Stacks.underlyingModuleSheaf Y.J (f.pushforwardModules.obj (A.piece i)) ⨯
            Stacks.underlyingModuleSheaf Y.J
              (f.pushforwardModules.obj (A.piece j))).obj.map morphism element))
        ((f.pushforwardModules.obj (A.piece j)).val.map morphism right) :=
      sheafPair_restrict_snd _ _ morphism left right
    rw [sourceLeft, sourceRight, targetLeft, targetRight] at equality
    exact equality.symm

end Stacks.Sheaves.GradedAlgebraEssentiallySmall

end
