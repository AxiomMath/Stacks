module

public import StacksFrontier.CategoryTheory.Sites.Modules.PointRingedSite

/-!
# Sheaves of modules on the one-point ringed site are modules

On the one-point ringed site `Stacks.PointRingedSite.site A` (one object, the trivial topology,
the constant structure sheaf `A`) every presheaf of modules is a sheaf, and a presheaf of modules
is determined by its module of sections over the point, all restriction maps being identities. So
taking sections over the point is an equivalence from sheaves of modules to `A`-modules.

## Main definitions

* `Stacks.PointRingedSite.constModule`: the sheaf of modules with sections `M` over the point.
* `Stacks.PointRingedSite.modulesEquiv`: the equivalence `ev A`, with inverse `constModule A`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace Stacks.PointRingedSite

variable (A : Type u) [CommRing A]

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

/-- The ring of sections of the structure sheaf over the point. -/
abbrev ptRing : RingCat.{u} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (site A).O).obj.obj (op (pt A))

/-- The presheaf of modules on the point with sections `M`, every restriction map being the
identity. -/
def constPresheafModule (M : ModuleCat.{u} (ptRing A)) :
    PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (site A).O).obj where
  obj _ := M
  map f := (ModuleCat.restrictScalarsId' _ (RingHom.ext fun _ => rfl)).inv.app M
  map_id _ := rfl
  map_comp _ _ := by
    ext x
    rfl

/-- **The sheaf of modules on the point with sections `M`.** -/
def constModule : ModuleCat.{u} (ptRing A) ⥤
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (site A).O) where
  obj M := ⟨constPresheafModule A M, Presheaf.isSheaf_bot _⟩
  map g := ⟨{
    app := fun _ => g
    naturality := fun _ => by
      ext x
      rfl }⟩

/-- The comparison of a sheaf of modules on the point with the constant sheaf of modules on its
sections over the point. -/
def constModuleEvIso (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (site A).O)) :
    M ≅ (constModule A).obj ((ev A).obj M) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (fun {U V} f => by
      rcases U with ⟨⟨⟨⟩⟩⟩
      rcases V with ⟨⟨⟨⟩⟩⟩
      obtain rfl : f = 𝟙 _ := Quiver.Hom.unop_inj
        (@Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _)
      ext x
      exact congrArg (fun g => g.hom x) (M.val.map_id _)))

/-- **Sheaves of modules on the one-point ringed site are `A`-modules**: sections over the point,
with inverse the constant sheaf of modules. -/
def modulesEquiv :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (site A).O) ≌
      ModuleCat.{u} (ptRing A) where
  functor := ev A
  inverse := constModule A
  unitIso := NatIso.ofComponents (constModuleEvIso A) (fun f => by
      refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
      rcases U with ⟨⟨⟨⟩⟩⟩
      rfl)
  counitIso := Iso.refl _
  functor_unitIso_comp M := by
    ext x
    rfl

end Stacks.PointRingedSite

end
