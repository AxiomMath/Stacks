module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.Topology.Sheaves.Stalks
public import StacksFrontier.Topology.Sheaves.Modules.SupportSection
import StacksCore.Tactic.StacksAttribute

/-!
# Support of a sheaf of modules and of a section

For a sheaf of modules on a ringed space, the support of the sheaf is the set of points at
which its stalk is nonzero, and the support of a section over an open set is the set of points
of that open set at which the germ of the section is nonzero. Both notions are already
available, as `AlgebraicGeometry.RingedSpace.ModuleSheaf.supp` and
`AlgebraicGeometry.RingedSpace.ModuleSheaf.suppSection`, the latter in the general form for a
section over an arbitrary open subset; specializing to the top open recovers the global form.

Fixing a subset `Z` of the space, the local sections of an abelian sheaf `F` whose support is
contained in `Z` form an abelian subsheaf of `F`. Closedness of `Z` is not needed for this.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.supportedSections`: the additive subgroup of the sections
  over `U` whose germs vanish outside `Z`.
* `AlgebraicGeometry.SheafOfModules.supportedSectionsSheaf`: those subgroups assembled into an
  abelian sheaf.
* `AlgebraicGeometry.SheafOfModules.supportedSectionsSubsheaf`: that sheaf presented as an
  abelian subsheaf of `F`, i.e. as an object of `MonoOver F`.
* `AlgebraicGeometry.SheafOfModules.moduleSheafOfModules`: a categorical sheaf of modules over
  the structure sheaf of a ringed space, repackaged as a `ModuleSheaf`.

## Main results

* `AlgebraicGeometry.SheafOfModules.mem_range_supportedSectionsSubsheaf_iff` identifies the
  sections of the subsheaf inside the sections of `F`.
* `AlgebraicGeometry.SheafOfModules.mem_supportedSections_moduleSheaf_iff` identifies the
  defining condition with containment of the support of the section in `Z`.

## Implementation notes

An abelian subsheaf is represented by its canonical monomorphism into `F`. Its source is built
sectionwise out of additive subgroups, so the displayed monomorphism realizes the subsets of
the definition literally, rather than only up to isomorphism. The section subgroups and the
inclusion maps are exposed, so that their elements and restriction maps are directly available
to dependent constructions.

The defining condition is vanishing of germs outside `Z`, and it is stated for an arbitrary
abelian sheaf, with no module structure chosen. Its comparison with the support of a section of
a sheaf of modules is therefore a separate lemma, which also fixes the ringed space to live in
`Type`, as the section-support API it compares against does.

## References

* [Stacks Project, Definition 17.5.1 (Tag 01AT)](https://stacks.math.columbia.edu/tag/01AT)
* [Stacks Project, Remark 17.5.4 (Tag 01AY)](https://stacks.math.columbia.edu/tag/01AY)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace TopCat

add_to_stacks 01AT "parts (1) and (2): sheaf support"
  AlgebraicGeometry.RingedSpace.ModuleSheaf.supp
add_to_stacks 01AT "part (3): section support"
  AlgebraicGeometry.RingedSpace.ModuleSheaf.suppSection

namespace AlgebraicGeometry.SheafOfModules

universe u

variable {X : TopCat.{u}}

/-- The additive subgroup of sections over `U` supported on `Z ∩ U`. -/
public def supportedSections (Z : Set X) (F : X.Sheaf AddCommGrpCat.{u})
    (U : (Opens X)ᵒᵖ) : AddSubgroup (F.presheaf.obj U) where
  carrier := {s | ∀ (x : X) (hx : x ∈ unop U), x ∉ Z →
    F.presheaf.germ (unop U) x hx s = 0}
  zero_mem' := by
    intro x hx _
    exact map_zero (F.presheaf.germ (unop U) x hx).hom
  add_mem' := by
    intro s t hs ht x hx hxZ
    simp only [map_add, hs x hx hxZ, ht x hx hxZ, add_zero]
  neg_mem' := by
    intro s hs x hx hxZ
    simp only [map_neg, hs x hx hxZ, neg_zero]

/-- Membership is exactly vanishing of every germ outside `Z`. -/
@[simp]
public lemma mem_supportedSections_iff (Z : Set X) (F : X.Sheaf AddCommGrpCat.{u})
    (U : (Opens X)ᵒᵖ) (s : F.presheaf.obj U) :
    s ∈ supportedSections Z F U ↔
      ∀ (x : X) (hx : x ∈ unop U), x ∉ Z → F.presheaf.germ (unop U) x hx s = 0 :=
  Iff.rfl

/-- Restriction takes a supported section to a supported section. -/
public lemma supportedSections_map {Z : Set X} {F : X.Sheaf AddCommGrpCat.{u}}
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) {s : F.presheaf.obj U}
    (hs : s ∈ supportedSections Z F U) :
    F.presheaf.map i s ∈ supportedSections Z F V := by
  intro x hxV hxZ
  simpa only [F.presheaf.germ_res_apply' i x hxV] using hs x (i.unop.le hxV) hxZ

/-- The presheaf whose sections are the sections of `F` supported on `Z`. -/
@[implicit_reducible]
public noncomputable def supportedSectionsPresheaf (Z : Set X)
    (F : X.Sheaf AddCommGrpCat.{u}) : X.Presheaf AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (supportedSections Z F U)
  map {U V} i := AddCommGrpCat.ofHom
    { toFun := fun s ↦ ⟨F.presheaf.map i s.1, supportedSections_map i s.2⟩
      map_zero' := by simp
      map_add' := by simp }
  map_id U := by ext; simp
  map_comp i j := by ext; simp

/-- The inclusion of the presheaf of supported sections into `F`. -/
@[implicit_reducible]
public noncomputable def supportedSectionsPresheafι (Z : Set X)
    (F : X.Sheaf AddCommGrpCat.{u}) : supportedSectionsPresheaf Z F ⟶ F.presheaf where
  app U := AddCommGrpCat.ofHom (supportedSections Z F U).subtype
  naturality _ _ i := by ext; rfl

instance (Z : Set X) (F : X.Sheaf AddCommGrpCat.{u}) :
    Mono (supportedSectionsPresheafι Z F) := by
  apply +allowSynthFailures NatTrans.mono_of_mono_app
  intro U; rw [AddCommGrpCat.mono_iff_injective]; exact Subtype.val_injective

/-- The underlying type-valued subfunctor of supported sections. -/
private def supportedSectionsSubfunctor (Z : Set X)
    (F : X.Sheaf AddCommGrpCat.{u}) :
    Subfunctor (F.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}) where
  obj U := {s : (F.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}).obj U |
    s ∈ supportedSections Z F U}
  map i _ hs := supportedSections_map i hs

/-- Membership in the supported-sections condition is local. -/
private lemma supportedSectionsSubfunctor_isSheaf (Z : Set X)
    (F : X.Sheaf AddCommGrpCat.{u}) :
    Presieve.IsSheaf (Opens.grothendieckTopology X)
      (supportedSectionsSubfunctor Z F).toFunctor := by
  rw [(supportedSectionsSubfunctor Z F).isSheaf_iff
    ((isSheaf_iff_isSheaf_of_type _ _).mp
      (GrothendieckTopology.HasSheafCompose.isSheaf F.presheaf F.2))]
  intro U s hs
  change s ∈ supportedSections Z F U
  intro x hx hxZ
  rw [Opens.mem_grothendieckTopology] at hs
  obtain ⟨W, g, hg, hxW⟩ := hs x hx
  simpa only [F.presheaf.germ_res_apply g x hxW] using
    (show F.presheaf.map g.op s ∈ supportedSections Z F (op W) from hg) x hxW hxZ

/-- The abelian sheaf of sections of `F` supported on `Z`. -/
public noncomputable def supportedSectionsSheaf (Z : Set X)
    (F : X.Sheaf AddCommGrpCat.{u}) : X.Sheaf AddCommGrpCat.{u} :=
  ⟨supportedSectionsPresheaf Z F, by
    apply Presheaf.isSheaf_of_isSheaf_comp (Opens.grothendieckTopology X)
      (s := CategoryTheory.forget AddCommGrpCat.{u})
    apply (isSheaf_iff_isSheaf_of_type _ _).mpr
    change Presieve.IsSheaf (Opens.grothendieckTopology X)
      (supportedSectionsSubfunctor Z F).toFunctor
    exact supportedSectionsSubfunctor_isSheaf Z F⟩

/-- The inclusion of the abelian sheaf of supported sections into `F`. -/
@[implicit_reducible]
public noncomputable def supportedSectionsSheafι (Z : Set X)
    (F : X.Sheaf AddCommGrpCat.{u}) : supportedSectionsSheaf Z F ⟶ F :=
  ⟨supportedSectionsPresheafι Z F⟩

/-- On sections, the canonical inclusion is the subgroup inclusion. -/
@[simp]
public lemma supportedSectionsSheafι_app (Z : Set X) (F : X.Sheaf AddCommGrpCat.{u})
    (U : (Opens X)ᵒᵖ) (s : (supportedSectionsSheaf Z F).presheaf.obj U) :
    (supportedSectionsSheafι Z F).hom.app U s = s.val :=
  rfl

/-- Restriction of a supported section is its restriction in the ambient sheaf. -/
@[simp]
public lemma supportedSectionsSheaf_map_val (Z : Set X) (F : X.Sheaf AddCommGrpCat.{u})
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (s : (supportedSectionsSheaf Z F).presheaf.obj U) :
    ((supportedSectionsSheaf Z F).presheaf.map i s).val = F.presheaf.map i s.val :=
  rfl

instance (Z : Set X) (F : X.Sheaf AddCommGrpCat.{u}) :
    Mono (supportedSectionsSheafι Z F) := by
  have : Mono (supportedSectionsSheafι Z F).hom :=
    show Mono (supportedSectionsPresheafι Z F) from inferInstance
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _

/-- The abelian subsheaf of `F` consisting of the local sections supported on
`Z`. It is bundled together with its canonical inclusion into `F`. -/
@[implicit_reducible, stacks 01AY "supported_sections_subsheaf", sga "2 XIV 1.0" "sheaf Γ_Y(F)"]
public noncomputable def supportedSectionsSubsheaf (Z : Set X)
    (F : X.Sheaf AddCommGrpCat.{u}) : MonoOver F :=
  MonoOver.mk (supportedSectionsSheafι Z F)

/-- A section of `F` lies in the supported-sections subsheaf over `U` exactly
when its support is contained in `Z ∩ U`. -/
@[simp]
public lemma mem_range_supportedSectionsSubsheaf_iff (Z : Set X)
    (F : X.Sheaf AddCommGrpCat.{u}) (U : (Opens X)ᵒᵖ) (s : F.presheaf.obj U) :
    s ∈ Set.range ((supportedSectionsSubsheaf Z F).arrow.hom.app U) ↔
      s ∈ supportedSections Z F U := by
  constructor
  · rintro ⟨t, rfl⟩; exact t.2
  · exact fun hs ↦ ⟨⟨s, hs⟩, rfl⟩

/-- A sheaf of modules over the structure sheaf of a ringed space, in the categorical sense of
`SheafOfModules`, repackaged as a `ModuleSheaf`: the underlying presheaf of modules is the same,
and the sheaf condition transfers verbatim. -/
public noncomputable def moduleSheafOfModules {Y : RingedSpace.{u, u}}
    (F : _root_.SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.sheaf)) :
    RingedSpace.ModuleSheaf Y where
  toPresheaf := F.val
  isSheaf := F.isSheaf

/-- For the abelian sheaf underlying a sheaf of modules, the sectionwise condition is exactly
containment of the support of the section in `Z`. -/
public lemma mem_supportedSections_moduleSheaf_iff {Y : RingedSpace}
    (F : RingedSpace.ModuleSheaf Y) (Z : Set Y.carrier)
    (U : Opens Y.carrier) (s : F.toPresheaf.obj (op U)) :
    s ∈ supportedSections Z ⟨F.toPresheaf.presheaf, F.isSheaf⟩ (op U) ↔
      F.suppSection U s ⊆ Z ∩ (U : Set Y.carrier) := by
  constructor
  · intro hs x ⟨hxU, hne⟩
    exact ⟨by_contra fun hxZ ↦ hne (hs x hxU hxZ), hxU⟩
  · intro hs x hxU hxZ
    by_contra hne
    exact hxZ (hs ⟨hxU, hne⟩).1

end AlgebraicGeometry.SheafOfModules
