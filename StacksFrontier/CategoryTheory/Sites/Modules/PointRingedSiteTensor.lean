module

public import StacksFrontier.CategoryTheory.Sites.Modules.PointRingedSiteModulesEquiv
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifyUnitIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatTwoOutOfThree

/-!
# The tensor product of sheaves of modules on the one-point ringed site

On the one-point ringed site of a commutative ring `A` (one object, the chaotic topology), every
presheaf of modules is a sheaf, so the sheafified tensor product of two sheaves of modules has
as sections over the point the tensor product of their sections. This file records that
identification, naturally in both variables.

## Main definitions

* `Stacks.PointRingedSite.evSheafTensorIso`: `Γ(pt, M ⊗ N) ≅ Γ(pt, M) ⊗ Γ(pt, N)`.
* `Stacks.PointRingedSite.evSheafTensorNatIso`: the same, as an isomorphism of bifunctors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace Stacks.PointRingedSite

universe u

variable (A : Type u) [CommRing A]

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

/-- The sections over the point of the sheafification of a presheaf of modules on the point are
its sections over the point: on the chaotic site every presheaf is a sheaf. -/
def evSheafificationIso
    (P : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (site A).O).obj) :
    (ev A).obj ((PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (site A).O).obj)).obj P) ≅ P.obj (op (pt A)) :=
  (LinearEquiv.toModuleIso (PresheafOfModules.unitAppEquiv
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (site A).O).obj) P
    (Presheaf.isSheaf_bot _) (op (pt A)))).symm

/-- `Stacks.PointRingedSite.evSheafificationIso` is natural in the presheaf of modules. -/
@[reassoc]
theorem evSheafificationIso_hom_naturality
    {P P' : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (site A).O).obj}
    (f : P ⟶ P') :
    (ev A).map ((PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (site A).O).obj)).map f) ≫
        (evSheafificationIso A P').hom =
      (evSheafificationIso A P).hom ≫ f.app (op (pt A)) := by
  rw [← cancel_epi (evSheafificationIso A P).inv, Iso.inv_hom_id_assoc,
    ← cancel_mono (evSheafificationIso A P').inv, Category.assoc, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  exact (congrArg (fun g => PresheafOfModules.Hom.app g (op (pt A)))
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (site A).O).obj)).unit.naturality f)).symm

/-- **The sections over the point of a tensor product are the tensor product of the sections**:
`Γ(pt, M ⊗ N) ≅ Γ(pt, M) ⊗ Γ(pt, N)`, the sheafification being invisible on the point. -/
def evSheafTensorIso
    (M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (site A).O)) :
    (ev A).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (site A).O).obj M).obj N) ≅
      (ev A).obj M ⊗ (ev A).obj N :=
  evSheafificationIso A _

/-- `Stacks.PointRingedSite.evSheafTensorIso` is natural in the first variable. -/
@[reassoc]
theorem evSheafTensorIso_hom_naturality_left
    {M M' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (site A).O)} (g : M ⟶ M')
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (site A).O)) :
    (ev A).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (site A).O).map g).app N) ≫
        (evSheafTensorIso A M' N).hom =
      (evSheafTensorIso A M N).hom ≫ (ev A).map g ▷ (ev A).obj N := by
  refine (evSheafificationIso_hom_naturality A _).trans ?_
  congr 1

/-- `Stacks.PointRingedSite.evSheafTensorIso` is natural in the second variable. -/
@[reassoc]
theorem evSheafTensorIso_hom_naturality_right
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (site A).O))
    {N N' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (site A).O)} (g : N ⟶ N') :
    (ev A).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (site A).O).obj M).map g) ≫
        (evSheafTensorIso A M N').hom =
      (evSheafTensorIso A M N).hom ≫ (ev A).obj M ◁ (ev A).map g := by
  refine (evSheafificationIso_hom_naturality A _).trans ?_
  congr 1

/-- **`Γ(pt, - ⊗ -) ≅ Γ(pt, -) ⊗ Γ(pt, -)` as an isomorphism of bifunctors.** -/
def evSheafTensorNatIso :
    Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (site A).O ⋙
        (Functor.whiskeringRight _ _ _).obj (ev A) ≅
      ev A ⋙ curriedTensor _ ⋙ (Functor.whiskeringLeft _ _ _).obj (ev A) :=
  NatIso.ofComponents
    (fun M => NatIso.ofComponents (fun N => evSheafTensorIso A M N)
      (fun g => evSheafTensorIso_hom_naturality_right A M g))
    (fun g => NatTrans.ext (funext fun N => evSheafTensorIso_hom_naturality_left A g N))

/-- **A sheaf of modules on the point whose sections form a flat module is flat.** Tensoring with
it is, on sections over the point, tensoring with a flat module
(`Stacks.PointRingedSite.evSheafTensorIso`), which preserves injections. -/
theorem isFlat_of_flat_ev
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (site A).O))
    (hM : Module.Flat (ptRing A) ((ev A).obj M)) :
    AlgebraicGeometry.SheafOfModules.IsFlat (O := (site A).O) M := by
  refine Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_of_mono_sheafTensor_map _ M ?_
  intro N N' ι hι
  refine (ev A).mono_of_mono_map ?_
  have hinj : Function.Injective ((ev A).map ι).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hw : Mono ((ev A).obj M ◁ (ev A).map ι) :=
    (ModuleCat.mono_iff_injective _).2 (Module.Flat.lTensor_preserves_injective_linearMap _ hinj)
  have := evSheafTensorIso_hom_naturality_right A M ι
  rw [← Iso.eq_comp_inv] at this
  rw [this]
  infer_instance

end Stacks.PointRingedSite

end
