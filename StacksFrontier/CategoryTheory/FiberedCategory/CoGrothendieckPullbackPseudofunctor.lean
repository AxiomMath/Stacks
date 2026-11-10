module

public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import StacksFrontier.CategoryTheory.FiberedCategory.PullbackPseudofunctor
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso
public import StacksFrontier.CategoryTheory.Sites.Descent.StrongTransDescentData
public import StacksFrontier.CategoryTheory.Sites.Stack.DescentDataEquivalence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pullback pseudofunctor of a Grothendieck construction

Let `F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat` be a pseudofunctor and `p : ∫ᶜ F ⥤ 𝒮` the projection of its
Grothendieck construction. The pullback pseudofunctor of the fibred category `p`, built from
chosen strongly cartesian lifts, is related to `F` by a strong transformation whose components
are the inclusions of `F(U)` as the fibres of `p`, all equivalences of categories. Consequently
`p` is a stack exactly when `F` is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor Opposite Bicategory

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] (F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{max v₁ v₂, max u₁ u₂})

/-- The cartesian lifts of the Grothendieck construction are natural in the object. -/
lemma cartesianLift_naturality {V W : 𝒮} (f : W ⟶ V) {X Y : F.obj ⟨op V⟩} (α : X ⟶ Y) :
    (ι F W).map ((F.map f.op.toLoc).toFunctor.map α) ≫ cartesianLift Y f =
      cartesianLift X f ≫ (ι F V).map α := by
  ext
  · change 𝟙 W ≫ f = f ≫ 𝟙 V
    exact (Category.id_comp f).trans (Category.comp_id f).symm
  · simp only [ι, categoryStruct_comp_base, op_comp, Quiver.Hom.comp_toLoc,
      categoryStruct_comp_fiber, op_id, Quiver.Hom.id_toLoc, Cat.Hom.id_toFunctor,
      Category.assoc, Functor.map_comp]
    rw [F.whiskerRight_mapId_inv_app, F.whiskerLeft_mapId_inv_app]
    simp only [Strict.rightUnitor_eqToIso, eqToIso.inv, PrelaxFunctor.map₂_eqToHom,
      Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, map_id, Category.id_comp, Category.assoc,
      Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id, Strict.leftUnitor_eqToIso]
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    exact congrArg _ (eqToHom_trans _ _).symm

/-- The cartesian lift of an identity is the unit constraint of `F`. -/
lemma cartesianLift_id {U : 𝒮} (a : F.obj ⟨op U⟩) :
    cartesianLift a (𝟙 U) = (ι F U).map ((F.mapId ⟨op U⟩).hom.toNatTrans.app a) := by
  ext
  · rfl
  · simp only [ι_map_fiber]
    exact (Cat.Hom.hom_inv_id_toNatTrans_app (F.mapId ⟨op U⟩) a).symm.trans
      (Category.comp_id _).symm

/-- The cartesian lifts of a composite are the composites of the cartesian lifts, up to the
composition constraint of `F`. -/
lemma cartesianLift_comp {V W Z : 𝒮} (φ : W ⟶ V) (ψ : Z ⟶ W) (a : F.obj ⟨op V⟩) :
    cartesianLift a (ψ ≫ φ) =
      (ι F Z).map ((F.mapComp φ.op.toLoc ψ.op.toLoc).hom.toNatTrans.app a) ≫
        cartesianLift ((F.map φ.op.toLoc).toFunctor.obj a) ψ ≫ cartesianLift a φ := by
  ext
  · change ψ ≫ φ = 𝟙 Z ≫ ψ ≫ φ
    simp
  · simp only [ι, categoryStruct_comp_base, op_comp, Quiver.Hom.comp_toLoc,
      categoryStruct_comp_fiber, op_id, Quiver.Hom.id_toLoc, Cat.Hom.id_toFunctor,
      Category.assoc, Functor.map_comp, Functor.map_id, Category.id_comp]
    rw [F.mapComp_id_right_inv_app]
    simp [Strict.rightUnitor_eqToIso, PrelaxFunctor.map₂_eqToHom]

/-- The inclusion of `F(U)` as the fibre of the projection over `U`. -/
abbrev fiberι (U : 𝒮) : F.obj ⟨op U⟩ ⥤ (forget F).Fiber U :=
  Fiber.inducedFunctor (comp_const F U)

/-- The cartesian lift of `φ` at `a`, and the chosen cartesian lift of the projection at the image
of `a`, have canonically isomorphic sources. -/
def pullbackIso {U V : 𝒮} (φ : V ⟶ U) (a : F.obj ⟨op U⟩) :
    (fiberι F V).obj ((F.map φ.op.toLoc).toFunctor.obj a) ≅
      (IsFibered.fiberPullback (p := forget F) φ).obj ((fiberι F U).obj a) :=
  have := isStronglyCartesian_homCartesianLift a φ
  Functor.fiberIsoOfCartesian (z := (fiberι F V).obj ((F.map φ.op.toLoc).toFunctor.obj a))
    (z' := (IsFibered.fiberPullback (p := forget F) φ).obj ((fiberι F U).obj a)) φ
    (cartesianLift a φ) (IsPreFibered.pullbackMap ((fiberι F U).obj a).2 φ)
    (IsStronglyCartesian.isCartesian_of_isStronglyCartesian (forget F) φ (cartesianLift a φ))
    (IsPreFibered.pullbackMap.IsCartesian ((fiberι F U).obj a).2 φ)

/-- The isomorphism `pullbackIso F φ a`, followed by the chosen cartesian lift, is the cartesian
lift of `φ` at `a`. -/
@[reassoc (attr := simp)]
lemma pullbackIso_hom_fac {U V : 𝒮} (φ : V ⟶ U) (a : F.obj ⟨op U⟩) :
    Fiber.fiberInclusion.map (pullbackIso F φ a).hom ≫
      IsPreFibered.pullbackMap ((fiberι F U).obj a).2 φ = cartesianLift a φ := by
  have := isStronglyCartesian_homCartesianLift a φ
  exact Functor.fiberIsoOfCartesian_hom_fac _ _ _
    (IsStronglyCartesian.isCartesian_of_isStronglyCartesian (forget F) φ (cartesianLift a φ))
    (IsPreFibered.pullbackMap.IsCartesian ((fiberι F U).obj a).2 φ)

/-- The naturality isomorphism of the comparison of `F` with the pullback pseudofunctor. -/
def pullbackNatIso {U V : 𝒮} (φ : V ⟶ U) :
    (F.map φ.op.toLoc).toFunctor ⋙ fiberι F V ≅
      fiberι F U ⋙ IsFibered.fiberPullback (p := forget F) φ :=
  NatIso.ofComponents (pullbackIso F φ) fun {a b} ψ ↦ by
    apply Functor.fiber_hom_ext_of_cartesian φ
      (IsPreFibered.pullbackMap ((fiberι F U).obj b).2 φ)
      (IsPreFibered.pullbackMap.IsCartesian ((fiberι F U).obj b).2 φ)
    simp only [Functor.comp_map, Functor.map_comp]
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullbackIso_hom_fac F φ b)).trans
      ((cartesianLift_naturality F φ ψ).trans ?_))
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_
      (congrArg (_ ≫ ·) (IsFibered.fiberPullbackMap_comm φ ((fiberι F U).map ψ)).symm)
    exact (congrArg (· ≫ _) (pullbackIso_hom_fac F φ a).symm).trans (Category.assoc _ _ _)

/-- **The comparison of `F` with the pullback pseudofunctor of its Grothendieck construction.**
Its component at `U` is the inclusion of `F(U)` as the fibre over `U`, and its naturality
isomorphisms identify the cartesian lifts of the construction with the chosen ones. -/
@[sga "4 VI 7.1.4" "partial"]
def toPullbackStrongTrans :
    F.StrongTrans (IsFibered.pullbackPseudofunctor (forget F)) where
  app U := Cat.Hom.ofFunctor (fiberι F U.as.unop)
  naturality f := Cat.Hom.isoMk (pullbackNatIso F f.as.unop)
  naturality_naturality := by
    intro a b f g η
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 _ := Subsingleton.elim _ _
    simp
  naturality_id := by
    intro a
    ext x
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app, eqToHom_refl, Category.comp_id]
    apply Fiber.fiberInclusion.map_injective
    have h2 : Fiber.fiberInclusion.map
        (((IsFibered.pullbackPseudofunctor (forget F)).mapId a).hom.toNatTrans.app
          ((fiberι F a.as.unop).obj x)) =
        IsPreFibered.pullbackMap ((fiberι F a.as.unop).obj x).2 (𝟙 _) :=
      (IsFibered.pbMapId_hom_app _ a _).trans (IsFibered.cmpUnderlying_cartPullback_cartId _ _)
    refine (Functor.map_comp _ _ _).trans ((congrArg (_ ≫ ·) h2).trans ?_)
    exact (pullbackIso_hom_fac F (𝟙 _) x).trans (cartesianLift_id F x)
  naturality_comp := by
    intro a b c f g
    ext x
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.associator_hom_app, Cat.associator_inv_app, eqToHom_refl, Category.comp_id,
      Category.id_comp]
    have hcart := (IsFibered.cartComp (p := forget F) f.as.unop g.as.unop).isCart
      ((fiberι F a.as.unop).obj x)
    apply Functor.fiber_hom_ext_of_cartesian (g.as.unop ≫ f.as.unop)
      ((IsFibered.cartComp f.as.unop g.as.unop).proj ((fiberι F a.as.unop).obj x))
      (IsStronglyCartesian.isCartesian_of_isStronglyCartesian (forget F) (g.as.unop ≫ f.as.unop)
        ((IsFibered.cartComp f.as.unop g.as.unop).proj ((fiberι F a.as.unop).obj x)))
    refine ((congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans (Category.assoc _ _ _)).trans ?_
    refine (congrArg (_ ≫ ·) (IsFibered.pullbackPseudofunctor_mapComp_compatible (forget F) f g
      ((fiberι F a.as.unop).obj x))).trans ?_
    refine (pullbackIso_hom_fac F (f ≫ g).as.unop x).trans
      ((cartesianLift_comp F f.as.unop g.as.unop x).trans ?_)
    symm
    refine (congrArg (fun t ↦ t ≫ (IsFibered.cartComp f.as.unop g.as.unop).proj
      ((fiberι F a.as.unop).obj x)) ((Fiber.fiberInclusion.map_comp _ _).trans
        (congrArg (_ ≫ ·) (Fiber.fiberInclusion.map_comp _ _)))).trans ?_
    refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (fun t ↦ _ ≫ (t ≫ _))
      (IsFibered.fiberPullbackMap_comm g.as.unop (pullbackIso F f.as.unop x).hom)).trans ?_
    refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (pullbackIso_hom_fac F f.as.unop x)))).trans ?_
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) (pullbackIso_hom_fac F g.as.unop ((F.map f).toFunctor.obj x)))

/-- Every component of `toPullbackStrongTrans F` is an equivalence of categories. -/
lemma isEquivalence_toPullbackStrongTrans_app (U : LocallyDiscrete 𝒮ᵒᵖ) :
    ((toPullbackStrongTrans F).app U).toFunctor.IsEquivalence :=
  inferInstanceAs (Fiber.inducedFunctor (comp_const F U.as.unop)).IsEquivalence

/-- **The Grothendieck construction of a stack is a stack.** If `F` is a stack for a
Grothendieck topology `J`, then the projection `∫ᶜ F ⥤ 𝒮` is a stack in the sense of
Stacks 026F. -/
public theorem isStack_forget_of_isStack {J : GrothendieckTopology 𝒮} [F.IsStack J] :
    (forget F).IsStack J := by
  rw [← Functor.isStack_pullbackPseudofunctor_iff]
  refine Pseudofunctor.IsStack.of_isStackFor (fun S R hR ↦ ?_)
  exact ((toPullbackStrongTrans F).isStackFor_iff_of_app_isEquivalence
    (isEquivalence_toPullbackStrongTrans_app F) R.arrows).mp (F.isStackFor' R hR)

end CategoryTheory.Pseudofunctor.CoGrothendieck

end
