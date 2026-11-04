module

public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import Mathlib.RingTheory.Flat.CategoryTheory
import StacksCore.Tactic.StacksAttribute

/-!
# Objectwise flatness implies flatness of a presheaf of modules

Let `O` be a presheaf of commutative rings on a category and `F` a presheaf of `O`-modules. If
`F(U)` is a flat `O(U)`-module for every object `U`, then `F` is a flat presheaf of modules,
that is, tensoring on the right with `F` is an exact endofunctor of presheaves of modules
(Stacks 03ER(1)).

The proof is the one in the source: limits and colimits of presheaves of modules are computed
objectwise, so the evaluation functors jointly reflect them, and objectwise the tensor functor
is the tensor functor of a module, which is exact precisely because that module is flat.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.PresheafOfModules.sectionTensorRight`: tensoring modules
  over a fixed ring with a fixed module, with the ring and module carriers in independent
  universes.

## Main results

* `AlgebraicGeometry.SheafOfModules.PresheafOfModules.isFlat_of_objectwise_flat`: a presheaf of
  modules whose module of sections over every object is flat is a flat presheaf of modules.

## Implementation notes

Flatness is `AlgebraicGeometry.SheafOfModules.PresheafOfModules.IsFlat`, the exactness of
tensoring on the right of Stacks 03ER(1), and the ring and module universes are independent,
which is the form the Stacks 03EV, 03EW and 03EZ arguments use.

`sectionTensorRight` is built here rather than taken from Mathlib's monoidal structure on
`ModuleCat` because the module carriers and the ring carrier are allowed to lie in independent
universes, which is what the presheaf-level statement needs.

## References

* [Stacks Project, Tag 03ES](https://stacks.math.columbia.edu/tag/03ES)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe v u w z

namespace AlgebraicGeometry.SheafOfModules.PresheafOfModules

variable {C : Type u} [Category.{v} C]

/-- Tensoring modules over a fixed commutative ring with a fixed module, with independent
universes for the ring and the module carriers. -/
noncomputable def sectionTensorRight (R : Type w) [CommRing R] (M : ModuleCat.{z} R) :
    ModuleCat.{z} R ⥤ ModuleCat.{z} R where
  obj N := ModuleCat.of R (N ⊗[R] M)
  map f := ModuleCat.ofHom (f.hom.rTensor M)
  map_id N := by ext x y; rfl
  map_comp f g := by ext x y; rfl

private lemma sectionTensorRight_additive (R : Type w) [CommRing R] (M : ModuleCat.{z} R) :
    (sectionTensorRight R M).Additive :=
  ⟨ModuleCat.hom_ext (LinearMap.rTensor_add M _ _)⟩

private lemma sectionTensorRight_exact (R : Type w) [CommRing R] (M : ModuleCat.{z} R)
    [Module.Flat R M] :
    PreservesFiniteLimits (sectionTensorRight R M) ∧
      PreservesFiniteColimits (sectionTensorRight R M) := by
  have := sectionTensorRight_additive R M
  refine ((Functor.exact_tfae (sectionTensorRight R M)).out 2 4).mp fun S hS => ?_
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.rTensor_exact M hS

/-- Tensoring presheaves of modules on the right with `F` is, objectwise, tensoring modules
with the sections of `F`. -/
private noncomputable def evaluationTensorRightIso (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (F : _root_.PresheafOfModules.{z} (ringPresheaf O)) (U : Cᵒᵖ) :
    tensorRight F ⋙ _root_.PresheafOfModules.evaluation _ U ≅
      _root_.PresheafOfModules.evaluation _ U ⋙ sectionTensorRight (O.obj U) (F.obj U) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- **A presheaf of modules whose sections over every object are flat is flat.** Finite limits
and finite colimits of presheaves of modules are computed objectwise, so exactness of the
objectwise tensor endofunctor is an objectwise condition, and over each object it is exactness
of tensoring modules by the sections there. -/
@[stacks 03ES]
theorem isFlat_of_objectwise_flat {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (F : _root_.PresheafOfModules.{z} (ringPresheaf O))
    (hF : ∀ U : Cᵒᵖ, Module.Flat ((ringPresheaf O).obj U) (F.obj U)) :
    IsFlat F := by
  have key (U : Cᵒᵖ) :
      PreservesFiniteLimits (tensorRight F ⋙ _root_.PresheafOfModules.evaluation _ U) ∧
        PreservesFiniteColimits (tensorRight F ⋙ _root_.PresheafOfModules.evaluation _ U) := by
    have : Module.Flat (O.obj U) (F.obj U) := hF U
    obtain ⟨h₁, h₂⟩ := sectionTensorRight_exact (O.obj U) (F.obj U)
    exact ⟨preservesFiniteLimits_of_natIso (evaluationTensorRightIso O F U).symm,
      preservesFiniteColimits_of_natIso (evaluationTensorRightIso O F U).symm⟩
  rw [IsFlat, exactFunctor_iff]
  refine ⟨⟨fun J _ _ => ⟨fun {K} => ?_⟩⟩, ⟨fun J _ _ => ⟨fun {K} => ?_⟩⟩⟩
  · apply preservesLimit_of_preserves_limit_cone (limit.isLimit K)
    apply _root_.PresheafOfModules.evaluationJointlyReflectsLimits
    intro U
    have := (key U).1
    exact (isLimitOfPreserves _ (limit.isLimit K)).ofIsoLimit
      (Functor.mapConeMapCone (limit.cone K)).symm
  · apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K)
    apply _root_.PresheafOfModules.evaluationJointlyReflectsColimits
    intro U
    have := (key U).2
    exact (isColimitOfPreserves _ (colimit.isColimit K)).ofIsoColimit
      (Functor.mapCoconeMapCocone (colimit.cocone K)).symm

end AlgebraicGeometry.SheafOfModules.PresheafOfModules

end
