module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleLocalSummand
public import StacksFrontier.AlgebraicGeometry.CardinalGeneration.Basic

/-!
# From a subobject of a module on a scheme to a concrete submodule

Let `X` be a scheme and `F` an `𝒪_X`-module. Mathlib has two notions of "submodule of `F`" and
nothing relating them:

* the categorical one, `CategoryTheory.Subobject F`, an isomorphism class of monomorphisms into
  `F`;
* the concrete one, `SheafOfModules.Submodule F`, a family of `Γ(X, U)`-submodules of `Γ(F, U)`,
  one for each open `U`, stable under restriction and local.

For a morphism `f : A ⟶ F` of `𝒪_X`-modules, the sections of `F` that locally lie in the image of
`f` form a concrete submodule `ofHom f`. When `f` is a monomorphism, its sheaf of modules is
isomorphic to `A` over `F`, and its sections over `U` are exactly the image of `Γ(A, U)`. Hence
every subobject of `F` is the subobject defined by a concrete submodule.

## Main definitions

* `ofHom f`: the submodule of sections locally in the image of `f`, for an arbitrary morphism.
* `imageModule f` and `imageModuleι f`: the `𝒪_X`-module of `ofHom f` and its inclusion into `F`.
* `toImageModule f`: the factorization of `f` through `imageModuleι f`.
* `imageIso f`: the isomorphism `A ≅ imageModule f`, for `f` a monomorphism.
* `ofSubobject P`: the concrete submodule attached to a subobject `P` of `F`.

## Main results

* `isIso_toImageModule`: for `f` a monomorphism, `toImageModule f` is an isomorphism.
* `obj_ofHom_of_mono`: for `f` a monomorphism, the sections of `ofHom f` over `U` are the range
  of `f` on sections over `U`.
* `imageIso_hom_imageModuleι`: the isomorphism `imageIso f` carries the inclusion to `f`.
* `subobjectMk_imageModuleι`: the subobject defined by the inclusion of `ofSubobject P` is `P`.
* `exists_submodule_of_mono` and `exists_submodule_of_subobject`: every monomorphism into `F`,
  and every subobject of `F`, is isomorphic over `F` to the inclusion of a concrete submodule.

## Why this is needed

[Stacks, Tag 01PE] is formalized in this tree only in the `Subobject` spelling:
`AlgebraicGeometry.exists_quasicoherentSubobject_restrict`
(`StacksFrontier/AlgebraicGeometry/ResolutionsAndBounds/QuasiCoherentExtension.lean`) extends a
quasi-coherent `Subobject (F.restrict j)` to a quasi-coherent `Subobject F`. The glueing step of
[Stacks, Tag 01PF] (`Stacks.AlgebraicGeometry.SubmoduleGlueOpens.glue` and
`Stacks.AlgebraicGeometry.SubmoduleGlueLocality.restrictTo_glue_of_le`) and its affine case
`Stacks.AlgebraicGeometry.Tag01PFAffineSubsheaf.exists_isFiniteType_submodule_eq_top_on` are
stated for concrete submodules. Without a map between the two notions the extension step is
unreachable from the side the rest of the induction is written on; this file is that map.
Since `imageIso f` is an isomorphism of sheaves of modules, and `SheafOfModules.IsQuasicoherent`,
`IsFiniteType` and `IsCoherent` are closed under isomorphism, these properties transport from the
subobject to `(ofHom f).toSheafOfModules`.

## Implementation notes

The submodule `ofHom f` is `Stacks.SheafOfModules.localImage` of the underlying morphism of
presheaves of modules. The isomorphism with `A` is obtained from
`Stacks.AlgebraicGeometry.CardinalGeneration.isIso_of_mono_of_locallySurjective`.

The objects and morphisms are named at the `AlgebraicGeometry.Scheme.Modules` spelling
(`imageModule`, `imageModuleι`, `toImageModule`), since `AlgebraicGeometry.Scheme.Modules` is a
`def` with its own `Category` instance, and at that spelling neither `Mono N.ι` (for
`N : F.Submodule`) nor `CompleteLattice F.Submodule` is synthesized. Monicity of
`toImageModule f` is obtained from `CategoryTheory.mono_of_mono_fac`.

## What this does not do, and no stacks attribute

No stacks attribute is attached: nothing here asserts [Stacks, Tag 01PE], [Stacks, Tag 01PF] or
any other tag. This file is one of the three primitives the affine induction of Tag 01PF is built
from, a change of spelling between two existing statements.

Nothing is proved about `N ↦ Subobject.mk N.ι` being injective: `subobjectMk_imageModuleι` gives
only that it is surjective, which is what the induction consumes.

## References

* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.SubmodulePrimitives

variable {X : Scheme.{u}} {F : X.Modules}

/-! ### The submodule of sections locally in the image -/

/-- The submodule of `F` of sections that locally lie in the image of a morphism `f : A ⟶ F` of
`𝒪_X`-modules. -/
def ofHom {A : X.Modules} (f : A ⟶ F) : F.Submodule :=
  Stacks.SheafOfModules.localImage f.val

/-- The `𝒪_X`-module of `ofHom f`. -/
def imageModule {A : X.Modules} (f : A ⟶ F) : X.Modules :=
  (ofHom f).toSheafOfModules

/-- The inclusion of `imageModule f` into `F`, as a morphism of `𝒪_X`-modules. -/
def imageModuleι {A : X.Modules} (f : A ⟶ F) : imageModule f ⟶ F :=
  (ofHom f).ι

/-- The factorization of `f` through the submodule of sections locally in its image. -/
def toImageModule {A : X.Modules} (f : A ⟶ F) : A ⟶ imageModule f :=
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimage
    (Stacks.SheafOfModules.toLocalImage f.val)

/-- The factorization `toImageModule f` composed with the inclusion `imageModuleι f` is `f`. -/
@[simp]
theorem toImageModule_imageModuleι {A : X.Modules} (f : A ⟶ F) :
    toImageModule f ≫ imageModuleι f = f :=
  SheafOfModules.hom_ext (Stacks.SheafOfModules.toLocalImage_ι f.val)

/-- The inclusion `imageModuleι f` is the inclusion `SheafOfModules.Submodule.ι` of `ofHom f`.
The two spellings differ only in which `Category` instance their `⟶` carries, and no instance
about either crosses to the other, so both names are needed. -/
theorem imageModuleι_eq_ι {A : X.Modules} (f : A ⟶ F) :
    imageModuleι f = ((ofHom f).ι : imageModule f ⟶ F) :=
  rfl

/-- On sections over `U`, the underlying section of `F` of `(toImageModule f).app U x` is
`f.app U x`. -/
theorem imageModuleι_app_toImageModule_app {A : X.Modules} (f : A ⟶ F) (U : X.Opens)
    (x : Γ(A, U)) :
    (imageModuleι f).app U ((toImageModule f).app U x) = f.app U x :=
  rfl

/-- A section of `F` lies in `ofHom f` exactly when it locally lies in the image of `f`. -/
theorem mem_ofHom_iff {A : X.Modules} (f : A ⟶ F) {U : X.Opens} (s : Γ(F, U)) :
    s ∈ (ofHom f).obj (op U) ↔
      ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
        ∃ t : Γ(A, V), f.app V t = F.presheaf.map (homOfLE hVU).op s := by
  refine ⟨fun hs x hx => ?_, fun h x hx => ?_⟩
  · obtain ⟨V, i, ⟨t, ht⟩, hxV⟩ := hs x hx
    exact ⟨V, i.le, hxV, t, ht⟩
  · obtain ⟨V, hVU, hxV, t, ht⟩ := h x hx
    exact ⟨V, homOfLE hVU, ⟨t, ht⟩, hxV⟩

/-- The range of `f` on sections over `U` is contained in the sections of `ofHom f` over `U`. -/
theorem le_obj_ofHom {A : X.Modules} (f : A ⟶ F) (U : X.Opens) :
    LinearMap.range (f.val.app (op U)).hom ≤ (ofHom f).obj (op U) := by
  rintro s ⟨t, rfl⟩ x hx
  exact ⟨U, homOfLE le_rfl, ⟨A.val.map (homOfLE le_rfl).op t,
    PresheafOfModules.naturality_apply f.val (homOfLE (le_rfl : U ≤ U)).op t⟩, hx⟩

/-! ### The comparison with the source, for a monomorphism -/

/-- For `f` a monomorphism, `toImageModule f` is a monomorphism. -/
instance mono_toImageModule {A : X.Modules} (f : A ⟶ F) [Mono f] : Mono (toImageModule f) :=
  mono_of_mono_fac (toImageModule_imageModuleι f)

/-- For `f` a monomorphism, the factorization `toImageModule f` is an isomorphism. -/
instance isIso_toImageModule {A : X.Modules} (f : A ⟶ F) [Mono f] :
    IsIso (toImageModule f) := by
  refine CardinalGeneration.isIso_of_mono_of_locallySurjective (toImageModule f)
    fun U s x hx => ?_
  obtain ⟨V, i, ⟨t, ht⟩, hxV⟩ := s.2 x hx
  exact ⟨V, i.le, hxV, t, Subtype.ext ht⟩

/-- For `f : A ⟶ F` a monomorphism, the isomorphism of `A` with the module of the submodule of
sections locally in the image of `f`. -/
def imageIso {A : X.Modules} (f : A ⟶ F) [Mono f] : A ≅ imageModule f :=
  asIso (toImageModule f)

/-- The forward map of `imageIso f` is `toImageModule f`. -/
@[simp]
theorem imageIso_hom {A : X.Modules} (f : A ⟶ F) [Mono f] :
    (imageIso f).hom = toImageModule f :=
  rfl

/-- The isomorphism `imageIso f` carries the inclusion of the submodule to `f`. -/
@[reassoc (attr := simp)]
theorem imageIso_hom_imageModuleι {A : X.Modules} (f : A ⟶ F) [Mono f] :
    (imageIso f).hom ≫ imageModuleι f = f :=
  toImageModule_imageModuleι f

/-- The inverse of `imageIso f` composed with `f` is the inclusion `imageModuleι f`. -/
@[reassoc (attr := simp)]
theorem imageIso_inv_comp {A : X.Modules} (f : A ⟶ F) [Mono f] :
    (imageIso f).inv ≫ f = imageModuleι f :=
  (Iso.inv_comp_eq _).2 (imageIso_hom_imageModuleι f).symm

/-- For `f` a monomorphism, the inclusion `imageModuleι f` is a monomorphism. -/
instance mono_imageModuleι {A : X.Modules} (f : A ⟶ F) [Mono f] : Mono (imageModuleι f) := by
  rw [← imageIso_inv_comp f]
  infer_instance

/-- For `f` a monomorphism, the sections of `ofHom f` over `U` are the range of `f` on sections
over `U`. -/
theorem obj_ofHom_of_mono {A : X.Modules} (f : A ⟶ F) [Mono f] (U : X.Opens) :
    (ofHom f).obj (op U) = LinearMap.range (f.val.app (op U)).hom := by
  refine le_antisymm (fun s hs => ?_) (le_obj_ofHom f U)
  have hbij := (ConcreteCategory.isIso_iff_bijective ((toImageModule f).app U)).1
    (Scheme.Modules.Hom.isIso_iff_isIso_app.1 (isIso_toImageModule f) U)
  obtain ⟨t, ht⟩ := hbij.2 (⟨s, hs⟩ : Γ(imageModule f, U))
  exact ⟨t, congrArg ((imageModuleι f).app U) ht⟩

/-! ### The subobject spelling -/

/-- The concrete submodule attached to a subobject of `F`: the sections locally lying in the image
of its monomorphism. -/
def ofSubobject (P : Subobject F) : F.Submodule :=
  ofHom P.arrow

/-- The module of `ofSubobject P` is isomorphic to the underlying module of `P`. -/
def ofSubobjectIso (P : Subobject F) : (P : X.Modules) ≅ imageModule P.arrow :=
  imageIso P.arrow

/-- The subobject defined by the inclusion of `ofSubobject P` is `P`. -/
theorem subobjectMk_imageModuleι (P : Subobject F) :
    Subobject.mk (imageModuleι P.arrow) = P :=
  (Subobject.mk_eq_mk_of_comm _ _ (ofSubobjectIso P).symm
    (imageIso_inv_comp P.arrow)).trans (Subobject.mk_arrow P)

/-! ### The two statements in existential form -/

/-- Every monomorphism into `F` is, up to isomorphism over `F`, the inclusion of a concrete
submodule. -/
theorem exists_submodule_of_mono {A : X.Modules} (f : A ⟶ F) [Mono f] :
    ∃ (N : F.Submodule) (ι : (N.toSheafOfModules : X.Modules) ⟶ F)
      (e : A ≅ (N.toSheafOfModules : X.Modules)), ι = N.ι ∧ e.hom ≫ ι = f :=
  ⟨ofHom f, imageModuleι f, imageIso f, rfl, imageIso_hom_imageModuleι f⟩

/-- Every subobject of `F` is, up to isomorphism over `F`, the inclusion of a concrete
submodule. -/
theorem exists_submodule_of_subobject (P : Subobject F) :
    ∃ (N : F.Submodule) (ι : (N.toSheafOfModules : X.Modules) ⟶ F)
      (e : (P : X.Modules) ≅ (N.toSheafOfModules : X.Modules)), ι = N.ι ∧ e.hom ≫ ι = P.arrow :=
  exists_submodule_of_mono P.arrow

end Stacks.AlgebraicGeometry.SubmodulePrimitives

end
