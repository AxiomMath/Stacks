module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSite
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint

/-!
# The morphism from a ringed site with a final object to its ringed point of global sections

Let `(C, O)` be a ringed site with a final object `T`, and let `A = O(T)` be the ring of global
sections. The *ringed point of global sections* is the site of the point with the trivial topology,
ringed by `A`, and the functor `pt ↦ T` defines a morphism of ringed sites

`p : (C, O) ⟶ (pt, A)`

whose direct image on modules is `F ↦ Γ(C, F) = F(T)`.

## Main definitions

* `AlgebraicGeometry.RingedSite.globalPointFunctor`: the functor `pt ↦ T`.
* `AlgebraicGeometry.RingedSite.globalPoint`: the ringed point `(pt, O(T))`.
* `AlgebraicGeometry.RingedSite.toGlobalPoint`: the morphism of ringed sites `(C, O) ⟶ (pt, O(T))`.
* `AlgebraicGeometry.RingedSite.globalPointEvaluation`: modules on the ringed point as modules over
  `O(T)`, by evaluation at the point.
* `AlgebraicGeometry.RingedSite.toGlobalPointPushforwardIso`: the direct image along the morphism,
  read at the point, is evaluation at `T`.

## Main results

* `AlgebraicGeometry.RingedSite.globalPointFunctor_isMorphismOfSites`: `pt ↦ T` defines a morphism
  of sites (Stacks 00X5: the comma categories have an initial object).
* `AlgebraicGeometry.RingedSite.globalPointEvaluationFullyFaithful`: evaluation at the point is
  fully faithful.
* `AlgebraicGeometry.RingedSite.toGlobalPointPullbackIso`: if `Φ` is a fully faithful left adjoint
  of evaluation at `T`, then evaluation at the point is an equivalence and the pullback along the
  morphism is `Φ` after evaluation at the point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.RingedPoint

universe u

namespace AlgebraicGeometry.RingedSite

/-! ### The site of the point -/

/-- The object of the site of the point. -/
abbrev globalPointObj : PointSite.{u, u} := ULiftHom.objUp ⟨⟨PUnit.unit⟩⟩

/-- The site of the point has exactly one object. -/
theorem globalPoint_obj_eq (x : PointSite.{u, u}) : x = globalPointObj := by
  rcases x with ⟨⟨⟨⟩⟩⟩
  rfl

/-- Between two objects of the site of the point there is exactly one morphism. -/
instance globalPoint_unique_hom (x y : PointSite.{u, u}) : Unique (x ⟶ y) where
  default := pointSiteEquiv.fullyFaithfulFunctor.preimage (eqToHom (Subsingleton.elim _ _))
  uniq _ := pointSiteEquiv.fullyFaithfulFunctor.map_injective (Subsingleton.elim _ _)

/-- Between two objects of the opposite of the site of the point there is exactly one
morphism. -/
instance globalPoint_unique_hom_op (x y : PointSite.{u, u}ᵒᵖ) : Unique (x ⟶ y) where
  default := (default : y.unop ⟶ x.unop).op
  uniq _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

variable (X : RingedSite.{u, u, u}) (T : X.C)

/-- **The functor `pt ↦ T`** from the site of the point to the site of `X`. -/
abbrev globalPointFunctor : PointSite.{u, u} ⥤ X.C := (Functor.const _).obj T

/-- The functor `pt ↦ T` is continuous for the trivial topology on the site of the point. -/
instance globalPointFunctor_isContinuous :
    (globalPointFunctor X T).IsContinuous (⊥ : GrothendieckTopology PointSite.{u, u}) X.J :=
  ⟨fun _ ↦ Presieve.isSheaf_bot⟩

variable {X T}

/-- When `T` is final, the arrow `V ⟶ T` is an initial object of the comma category of `V`. -/
def globalPointStructuredArrowIsInitial (hT : IsTerminal T) (V : X.C) :
    IsInitial (StructuredArrow.mk (Y := globalPointObj) (hT.from V) :
      StructuredArrow V (globalPointFunctor X T)) :=
  IsInitial.ofUniqueHom
    (fun _ ↦ StructuredArrow.homMk default (hT.hom_ext _ _))
    (fun _ _ ↦ StructuredArrow.ext _ _ (Subsingleton.elim _ _))

/-- When `T` is final, `pt ↦ T` is representably flat: each comma category has an initial
object. -/
theorem representablyFlat_globalPointFunctor (hT : IsTerminal T) :
    RepresentablyFlat (globalPointFunctor X T) :=
  ⟨fun V ↦ IsCofiltered.of_isInitial _ (globalPointStructuredArrowIsInitial hT V)⟩

/-- **When `T` is final, `pt ↦ T` defines a morphism of sites `(C, J) ⟶ pt`** (Stacks 00X5). -/
theorem globalPointFunctor_isMorphismOfSites (hT : IsTerminal T) :
    (globalPointFunctor X T).IsMorphismOfSites (⊥ : GrothendieckTopology PointSite.{u, u}) X.J :=
  have := representablyFlat_globalPointFunctor hT
  Functor.isMorphismOfSites_of_representablyFlat _ _ _

variable (X T)

/-- **The ringed point of global sections**: the site of the point with the trivial topology,
ringed by the sections of the structure sheaf over `T`, which is the direct image of the
structure sheaf along `pt ↦ T`. -/
abbrev globalPoint : RingedSite.{u, u, u} where
  C := PointSite.{u, u}
  J := ⊥
  O := ((globalPointFunctor X T).sheafPushforwardContinuous CommRingCat.{u} ⊥ X.J).obj X.O

variable {X T}

/-- **The morphism of ringed sites `(C, O) ⟶ (pt, O(T))`**, for a final object `T`. -/
def toGlobalPoint (hT : IsTerminal T) : RingedSite.Hom X (globalPoint X T) where
  u := globalPointFunctor X T
  isMorphismOfSites := globalPointFunctor_isMorphismOfSites hT
  fsharp := 𝟙 _

/-! ### Modules on the ringed point -/

variable (X T)

/-- **Evaluation at the point**: a module on the ringed point of global sections is a module
over the ring of sections over `T`. -/
abbrev globalPointEvaluation :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (globalPoint X T).O) ⥤
      ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T)) :=
  SheafOfModules.evaluation _ (op globalPointObj)

/-- **Evaluation at the point is faithful.** -/
instance globalPointEvaluation_faithful : (globalPointEvaluation X T).Faithful where
  map_injective {M N} f g h := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun x ↦ ?_))
    obtain ⟨x⟩ := x
    obtain rfl := globalPoint_obj_eq x
    exact h

/-- **Evaluation at the point is full.** -/
instance globalPointEvaluation_full : (globalPointEvaluation X T).Full where
  map_surjective {M N} φ := by
    let app : ∀ x : PointSite.{u, u}ᵒᵖ, M.val.obj x ⟶ N.val.obj x := fun x ↦ by
      obtain ⟨x⟩ := x
      obtain rfl := globalPoint_obj_eq x
      exact φ
    refine ⟨⟨{ app := app, naturality := ?_ }⟩, ?_⟩
    · intro x y f
      obtain ⟨x⟩ := x
      obtain ⟨y⟩ := y
      obtain rfl := globalPoint_obj_eq x
      obtain rfl := globalPoint_obj_eq y
      obtain rfl : f = 𝟙 _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
      ext m
      simp [app]
      rfl
    · rfl

/-- Evaluation at the point is fully faithful. -/
def globalPointEvaluationFullyFaithful : (globalPointEvaluation X T).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

variable {X T}

/-- **The direct image along `(C, O) ⟶ (pt, O(T))`, read at the point, is evaluation at `T`.** -/
def toGlobalPointPushforwardIso (hT : IsTerminal T) :
    (toGlobalPoint hT).toRingedToposSiteHom.pushforwardTopos ⋙ globalPointEvaluation X T ≅
      SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op T) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-! ### The pullback along the morphism to the ringed point -/

section Pullback

/-- The unit of an adjunction whose left adjoint is fully faithful is an isomorphism. -/
private theorem isIso_unit_of_fullyFaithful {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (hL : L.FullyFaithful) : IsIso adj.unit := by
  have := hL.full
  have := hL.faithful
  infer_instance

variable (hT : IsTerminal T)
  {Φ : ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T)) ⥤
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  (adj : Φ ⊣ SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op T))
  (hΦ : Φ.FullyFaithful)

include hT adj hΦ in
/-- If evaluation at `T` has a fully faithful left adjoint, evaluation at the point is
essentially surjective: the module `Φ M` on `X` pushes forward to a module whose value at the
point is `Γ(T, Φ M) ≅ M`. -/
theorem globalPointEvaluation_essSurj : (globalPointEvaluation X T).EssSurj where
  mem_essImage M := by
    have := isIso_unit_of_fullyFaithful adj hΦ
    exact ⟨(toGlobalPoint hT).toRingedToposSiteHom.pushforwardTopos.obj (Φ.obj M),
      ⟨(toGlobalPointPushforwardIso hT).app (Φ.obj M) ≪≫ (asIso (adj.unit.app M)).symm⟩⟩

/-- **Evaluation at the point as an equivalence**, when evaluation at `T` has a fully faithful left
adjoint. -/
def globalPointEvaluationEquivalence :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (globalPoint X T).O) ≌
      ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T)) :=
  haveI := globalPointEvaluation_essSurj hT adj hΦ
  haveI : (globalPointEvaluation X T).IsEquivalence := { }
  (globalPointEvaluation X T).asEquivalence

/-- The functor of `globalPointEvaluationEquivalence` is evaluation at the point. -/
theorem globalPointEvaluationEquivalence_functor :
    (globalPointEvaluationEquivalence hT adj hΦ).functor = globalPointEvaluation X T :=
  rfl

/-- `Φ` after evaluation at the point is left adjoint to the direct image along the morphism to
the ringed point. -/
def globalPointEvaluationCompAdjunction :
    globalPointEvaluation X T ⋙ Φ ⊣ (toGlobalPoint hT).toRingedToposSiteHom.pushforwardTopos :=
  ((globalPointEvaluationEquivalence hT adj hΦ).toAdjunction.comp adj).ofNatIsoRight
    (Functor.isoWhiskerRight (toGlobalPointPushforwardIso hT).symm
        (globalPointEvaluationEquivalence hT adj hΦ).inverse ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (globalPointEvaluationEquivalence hT adj hΦ).unitIso.symm ≪≫
      Functor.rightUnitor _)

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

variable [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The pullback along `(C, O) ⟶ (pt, O(T))` is `Φ` after evaluation at the point**, for a fully
faithful left adjoint `Φ` of evaluation at `T`: both are left adjoint to the direct image. -/
def toGlobalPointPullbackIso :
    (toGlobalPoint hT).toRingedToposSiteHom.pullbackTopos ≅ globalPointEvaluation X T ⋙ Φ :=
  ((toGlobalPoint hT).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos).leftAdjointUniq
    (globalPointEvaluationCompAdjunction hT adj hΦ)

/-- The pullback along the morphism to the ringed point is fully faithful. -/
def toGlobalPointPullbackFullyFaithful :
    (toGlobalPoint hT).toRingedToposSiteHom.pullbackTopos.FullyFaithful :=
  (((globalPointEvaluationEquivalence hT adj hΦ).fullyFaithfulFunctor.comp hΦ)).ofIso
    (toGlobalPointPullbackIso hT adj hΦ).symm

include adj hΦ in
/-- The unit of pullback and direct image along the morphism to the ringed point is an
isomorphism. -/
theorem isIso_toGlobalPoint_unit :
    IsIso ((toGlobalPoint hT).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit) :=
  isIso_unit_of_fullyFaithful _ (toGlobalPointPullbackFullyFaithful hT adj hΦ)

include adj hΦ in
/-- **The counit of pullback and direct image along the morphism to the ringed point is an
isomorphism at every module isomorphic to some `Φ M`.** -/
theorem isIso_toGlobalPoint_counit_app_of_iso
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (M : ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op T)))
    (e : N ≅ Φ.obj M) :
    IsIso ((toGlobalPoint hT).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.counit.app
      N) := by
  have := (toGlobalPointPullbackFullyFaithful hT adj hΦ).full
  have := (toGlobalPointPullbackFullyFaithful hT adj hΦ).faithful
  let E := globalPointEvaluationEquivalence hT adj hΦ
  exact (toGlobalPoint hT).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
    |>.isIso_counit_app_of_iso (e ≪≫ (Φ.mapIso (E.counitIso.app M)).symm ≪≫
      ((toGlobalPointPullbackIso hT adj hΦ).app _).symm)

end Pullback

end AlgebraicGeometry.RingedSite

end
