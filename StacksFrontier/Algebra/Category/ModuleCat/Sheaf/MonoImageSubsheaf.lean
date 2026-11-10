module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleEssentiallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleFactorThru

/-!
# A monomorphism of sheaves of modules is an isomorphism onto its image subsheaf

Let `J` be a Grothendieck topology on a category `C`, let `R : Sheaf J RingCat` be a sheaf of
rings, and let `f : M ⟶ N` be a morphism of sheaves of `R`-modules.  Its image subsheaf
`Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule f ⊆ N` consists of the sections of `N` which
*locally* lie in the range of `f`, and `f` factors through it.  When `f` is a monomorphism that
factorisation is an isomorphism: the local condition collapses, so a section of `N` lying
locally in the range of `f` lies in the range of `f`.

This identifies a submodule of `N` with `M` itself, which is what lets a monomorphism into the
structure sheaf be read as a sheaf of ideals with a prescribed isomorphism type.

## Main definitions

* `Stacks.SheafOfModules.ImageSubsheaf.toImage` is the factorisation `M ⟶ Im f` of `f` through
  its image subsheaf.
* `Stacks.SheafOfModules.ImageSubsheaf.imageIso` is that factorisation as an isomorphism
  `M ≅ Im f`, for `f` a monomorphism.

## Main results

* `Stacks.SheafOfModules.ImageSubsheaf.exists_app_eq_of_mem_imageSubmodule`: for a monomorphism
  `f`, a section of `N` which lies locally in the range of `f` is in the range of `f`.
* `Stacks.SheafOfModules.ImageSubsheaf.mem_imageSubmodule_obj_iff_of_mono`: so for a
  monomorphism the image subsheaf is, over every object, exactly the range on sections.
* `Stacks.SheafOfModules.ImageSubsheaf.bijective_toImage_app`: consequently the factorisation is
  bijective on sections over every object.
* `Stacks.SheafOfModules.ImageSubsheaf.isIso_toImage`: and is therefore an isomorphism.

## Implementation notes

The collapse of the local condition is the sheaf axiom for `M`, used through the underlying
type-valued presheaf.  A monomorphism of sheaves of modules is injective on sections, so the
local preimages of a section of `N` are *unique*; uniqueness turns them into a compatible family
on the covering sieve, the sheaf condition for `M` amalgamates that family, and the separatedness
of `N` identifies the image of the amalgamation with the original section.

Isomorphy is read off from bijectivity on sections through the two functors
`SheafOfModules.toSheaf` and `sheafToPresheaf`, both of which reflect isomorphisms; this avoids
assuming that the category of sheaves of modules is abelian, which the parallel argument for an
epimorphism in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf` needs in order to
invoke balancedness.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u t

namespace Stacks.SheafOfModules.ImageSubsheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {M N : SheafOfModules.{t} R}

/-- The factorisation of a morphism of sheaves of modules through its image subsheaf. -/
noncomputable def toImage (f : M ⟶ N) : M ⟶ (imageSubmodule f).toSheafOfModules :=
  (imageSubmodule f).factorThru f (fun _ m => apply_mem_imageSubmodule f m)

/-- The factorisation through the image subsheaf, followed by the inclusion of the image, is the
original morphism. -/
lemma toImage_ι (f : M ⟶ N) : toImage f ≫ (imageSubmodule f).ι = f :=
  _root_.SheafOfModules.Submodule.factorThru_ι _ _ _

/-- On sections, the factorisation through the image subsheaf is the original morphism. -/
lemma toImage_app_coe (f : M ⟶ N) (X : Cᵒᵖ) (m : M.val.obj X) :
    (((toImage f).val.app X m).1 : N.val.obj X) = f.val.app X m :=
  _root_.PresheafOfModules.Submodule.factorThru_app_val _ _ _ _ _

/-- **A section lying locally in the range of a monomorphism lies in its range.**  The local
preimages are unique, hence form a compatible family, hence glue; the glued section has the
right image because the target is separated. -/
theorem exists_app_eq_of_mem_imageSubmodule (f : M ⟶ N) [Mono f] {X : Cᵒᵖ}
    (x : N.val.obj X) (hx : x ∈ (imageSubmodule f).obj X) :
    ∃ m : M.val.obj X, f.val.app X m = x := by
  set P := M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{t}
  set Q := N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{t}
  have hS : (rangeSubmodule f).toSubfunctor.sieveOfSection x ∈ J X.unop :=
    (mem_localImageObj_iff f x).1 hx
  set S : Sieve X.unop := (rangeSubmodule f).toSubfunctor.sieveOfSection x
  have hpre : ∀ ⦃Y : C⦄ (g : Y ⟶ X.unop), S.arrows g →
      ∃ m : M.val.obj (op Y), f.val.app (op Y) m = Q.map g.op x :=
    fun _ g hg => (sieveOfSection_rangeSubmodule_apply f x g).1 hg
  let fam : Presieve.FamilyOfElements P (S : Presieve X.unop) := fun Y g hg => (hpre g hg).choose
  have hfam : ∀ ⦃Y : C⦄ (g : Y ⟶ X.unop) (hg : S.arrows g),
      f.val.app (op Y) (fam g hg) = Q.map g.op x := fun Y g hg => (hpre g hg).choose_spec
  have hnat : ∀ {Y Z : Cᵒᵖ} (g : Y ⟶ Z) (y : M.val.obj Y),
      f.val.app Z (P.map g y) = Q.map g (f.val.app Y y) := fun g y =>
    PresheafOfModules.naturality_apply f.val g y
  have hcomp : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Y Z g h hg
    refine PresheafOfModules.injective_of_mono (f := f.val) (op Z) ?_
    rw [hfam (h ≫ g) (S.downward_closed hg h), hnat h.op (fam g hg), hfam g hg]
    exact Functor.map_comp_apply Q g.op h.op x
  obtain ⟨m, hm, -⟩ := (isSheaf_forget M S hS) fam hcomp
  refine ⟨m, (isSheaf_forget N S hS).isSeparatedFor.ext fun {Y} g hg => ?_⟩
  change Q.map g.op (f.val.app X m) = Q.map g.op x
  rw [← hnat g.op m, show P.map g.op m = fam g hg from hm g hg, hfam g hg]

/-- **For a monomorphism of sheaves of modules the image subsheaf is the sectionwise range.**
Over every object, a section of `N` lies in the image subsheaf of `f` exactly when it is the
image of a section of `M`: one direction is
`Stacks.SheafOfModules.ImageSubsheaf.exists_app_eq_of_mem_imageSubmodule`, the other holds for
any morphism.

This is the form in which the image subsheaf is compared with a submodule prescribed
chartwise: the local condition defining `imageSubmodule` never has to be unfolded. -/
theorem mem_imageSubmodule_obj_iff_of_mono (f : M ⟶ N) [Mono f] {X : Cᵒᵖ} (x : N.val.obj X) :
    x ∈ (imageSubmodule f).obj X ↔ ∃ m : M.val.obj X, f.val.app X m = x :=
  ⟨exists_app_eq_of_mem_imageSubmodule f x,
    fun ⟨m, hm⟩ => hm ▸ apply_mem_imageSubmodule f m⟩

/-- For a monomorphism of sheaves of modules, the factorisation through the image subsheaf is
bijective on sections over every object. -/
theorem bijective_toImage_app (f : M ⟶ N) [Mono f] (X : Cᵒᵖ) :
    Function.Bijective ((toImage f).val.app X) := by
  constructor
  · intro a b hab
    refine PresheafOfModules.injective_of_mono (f := f.val) X ?_
    rw [← toImage_app_coe f X a, ← toImage_app_coe f X b, hab]
  · rintro ⟨x, hx⟩
    obtain ⟨m, hm⟩ := exists_app_eq_of_mem_imageSubmodule f x hx
    exact ⟨m, Subtype.ext ((toImage_app_coe f X m).trans hm)⟩

/-- **A monomorphism of sheaves of modules factors isomorphically through its image
subsheaf.** -/
instance isIso_toImage (f : M ⟶ N) [Mono f] : IsIso (toImage f) := by
  rw [← isIso_iff_of_reflects_iso _ (_root_.SheafOfModules.toSheaf.{t} R),
    ← isIso_iff_of_reflects_iso _ (sheafToPresheaf J AddCommGrpCat.{t}),
    NatTrans.isIso_iff_isIso_app]
  intro X
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_toImage_app f X

/-- The source of a monomorphism of sheaves of modules, identified with its image subsheaf. -/
noncomputable def imageIso (f : M ⟶ N) [Mono f] : M ≅ (imageSubmodule f).toSheafOfModules :=
  asIso (toImage f)

end Stacks.SheafOfModules.ImageSubsheaf

end
