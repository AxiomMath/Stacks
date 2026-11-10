module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Modules.Support
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf of modules of sections supported on a subset

Let `F` be a sheaf of modules on a ringed space `X` and let `Z ⊆ X` be a subset. The sections
of `F` over an open `U` whose support is contained in `Z ∩ U` form a submodule, and these
submodules form a sheaf of modules, a subsheaf of `F`. It is supported on `Z`, and it is the
largest such subsheaf: every morphism into `F` out of a sheaf of modules supported on `Z`
factors through it. No closedness assumption on `Z` is needed.

Stacks 01AT already builds the corresponding subsheaf of *abelian* groups,
`AlgebraicGeometry.SheafOfModules.supportedSectionsSheaf`. What is added here is the module
structure: supported sections are stable under multiplication by sections of the structure
sheaf, because the support of `a • s` is contained in the support of `s`, so the abelian
subsheaf is in fact a subsheaf of modules.

## Main definitions

* `Stacks.SheafOfModules.SupportedSections.supportedSubmodule`: the presheaf submodule of
  sections supported on `Z`.
* `Stacks.SheafOfModules.SupportedSections.supportedModuleSheaf`: that submodule together with
  its sheaf condition.
* `Stacks.SheafOfModules.SupportedSections.supportedSectionsSheaf`: the sheaf of sections
  supported on `Z` as an object of `SheafOfModules`, bundled with its inclusion into `F` and
  with the specification of that inclusion.

## Main results

* `AlgebraicGeometry.RingedSpace.ModuleSheaf.sectionGerm_eq_zero_iff`: a germ of a section
  vanishes exactly when the section already vanishes on a neighbourhood of the point.
* `Stacks.SheafOfModules.SupportedSections.mem_supportedSectionsSheafι_range_iff`: on every
  open set, the range of the inclusion of the supported-sections sheaf is precisely the set of
  sections whose support is contained in `Z ∩ U`.
* `Stacks.SheafOfModules.SupportedSections.supportedSectionsSheafι_mono`: that inclusion is a
  monomorphism, so the supported sections really are a submodule sheaf of `F`.
* `Stacks.SheafOfModules.SupportedSections.supportedSectionsSheaf_supp_subset`: the
  supported-sections sheaf is itself supported on `Z`.
* `Stacks.SheafOfModules.SupportedSections.hom_to_supportedSectionsSheaf_of_supp_subset`:
  maximality — any morphism into `F` from a sheaf of modules supported on `Z` factors through
  the supported-sections subsheaf.
* `AlgebraicGeometry.RingedSpace.ModuleSheaf.suppSection_subset_map_of_injective`: a morphism
  injective on sections does not shrink the support of a section, the converse of Stacks
  01AU(5).

## Implementation notes

The specification of the construction is carried by the bundled inclusion rather than by a
separate normal form: the inclusion is injective on sections and its range on every open set
is identified with the intended subset of `F(U)`, which pins the subsheaf down up to unique
isomorphism. It is returned together with the sheaf so that this identification is available
to any construction built on top of it.

Section support is read through the ringed-space presentation
`AlgebraicGeometry.RingedSpace.ModuleSheaf` of a sheaf of modules, which is where the
section-support API of Stacks 01AT/01AU lives; the repackaging is Stacks 01AT's
`AlgebraicGeometry.SheafOfModules.moduleSheafOfModules`. Because `ModuleSheaf` is indexed by a
ringed space whose carrier, structure sheaf and module sections all live in one universe, all
universes here are identified as well.

## References

* [Stacks Project, Definition 17.5.1 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Definition 17.5.1 (Tag 01AT)](https://stacks.math.columbia.edu/tag/01AT)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleSheaf

/-- A germ of a section vanishes exactly when the section vanishes on some neighbourhood of
the point. -/
theorem sectionGerm_eq_zero_iff {X : RingedSpace} (F : ModuleSheaf X)
    (U : Opens X.carrier) (x : X.carrier) (hx : x ∈ U) (s : F.toPresheaf.obj (op U)) :
    F.sectionGerm U x hx s = 0 ↔
      ∃ (W : Opens X.carrier) (_ : x ∈ W) (j : W ⟶ U), F.toPresheaf.map j.op s = 0 := by
  constructor
  · intro h
    have h0 : F.abPresheaf.germ U x hx s = F.abPresheaf.germ U x hx 0 := by
      rw [map_zero]
      exact h
    obtain ⟨W, hxW, iU, _, e⟩ := F.abPresheaf.germ_eq x hx hx s 0 h0
    refine ⟨W, hxW, iU, ?_⟩
    change F.abPresheaf.map iU.op s = 0
    rw [e, map_zero]
  · rintro ⟨W, hxW, j, hj⟩
    have h1 : F.abPresheaf.map j.op s = (0 : F.abPresheaf.obj (op W)) := hj
    change F.abPresheaf.germ U x hx s = 0
    rw [← F.abPresheaf.germ_res_apply j x hxW s, h1, map_zero]

/-- Converse of `AlgebraicGeometry.RingedSpace.ModuleSheaf.suppSection_map_subset` for a
morphism which is injective on sections: the support of a section is then contained in the
support of its image. -/
theorem suppSection_subset_map_of_injective {X : RingedSpace} {F G : ModuleSheaf X}
    (φ : PresheafOfModules.Hom F.toPresheaf G.toPresheaf)
    (hinj : ∀ U : Opens X.carrier, Function.Injective (φ.app (op U)))
    (U : Opens X.carrier) (s : F.toPresheaf.obj (op U)) :
    F.suppSection U s ⊆ G.suppSection U (φ.app (op U) s) := by
  rintro x ⟨hxU, hne⟩
  refine ⟨hxU, fun hz => hne ?_⟩
  obtain ⟨V, hxV, j, hj⟩ := (G.sectionGerm_eq_zero_iff U x hxU (φ.app (op U) s)).mp hz
  refine (F.sectionGerm_eq_zero_iff U x hxU s).mpr ⟨V, hxV, j, hinj V ?_⟩
  rw [PresheafOfModules.naturality_apply φ j.op s, hj]
  exact (map_zero _).symm

end AlgebraicGeometry.RingedSpace.ModuleSheaf

namespace Stacks.SheafOfModules.SupportedSections

open AlgebraicGeometry RingedSpaceModuleAdjunction

/-- Restricting a section does not change where its germ vanishes: the germ of a restricted
section vanishes at a point of the smaller open set exactly when the germ of the original
section does. -/
theorem sectionGerm_map_eq_zero_iff {X : RingedSpace}
    (F : RingedSpace.ModuleSheaf X)
    {U V : (Opens X.carrier)ᵒᵖ} (i : U ⟶ V)
    (x : X.carrier) (hx : x ∈ unop V) (s : F.toPresheaf.obj U) :
    F.sectionGerm (unop V) x hx (F.toPresheaf.map i s) = 0 ↔
      F.sectionGerm (unop U) x (i.unop.le hx) s = 0 := by
  constructor
  · intro h
    obtain ⟨W, hxW, j, hj⟩ :=
      (F.sectionGerm_eq_zero_iff (unop V) x hx (F.toPresheaf.map i s)).mp h
    apply (F.sectionGerm_eq_zero_iff (unop U) x (i.unop.le hx) s).mpr
    refine ⟨W, hxW, j ≫ i.unop, ?_⟩
    change F.toPresheaf.map (i ≫ j.op) s = 0
    rwa [F.toPresheaf.map_comp_apply]
  · intro h
    obtain ⟨W, hxW, j, hj⟩ :=
      (F.sectionGerm_eq_zero_iff (unop U) x (i.unop.le hx) s).mp h
    let T := W ⊓ unop V
    let a : T ⟶ W := homOfLE inf_le_left
    let b : T ⟶ unop V := homOfLE inf_le_right
    apply (F.sectionGerm_eq_zero_iff (unop V) x hx (F.toPresheaf.map i s)).mpr
    refine ⟨T, ⟨hxW, hx⟩, b, ?_⟩
    have heq : i ≫ b.op = j.op ≫ a.op := Subsingleton.elim _ _
    rw [← F.toPresheaf.map_comp_apply i b.op, heq, F.toPresheaf.map_comp_apply j.op a.op, hj]
    exact map_zero (F.toPresheaf.map a.op).hom

/-- The presheaf submodule of sections supported on `Z`. -/
noncomputable def supportedSubmodule {X : RingedSpace} (Z : Set X.carrier)
    (F : RingedSpace.ModuleSheaf X) :
    F.toPresheaf.Submodule where
  obj U :=
    { carrier := {s | F.suppSection (unop U) s ⊆ Z ∩ (unop U : Opens X.carrier)}
      zero_mem' := by
        intro x ⟨hx, hne⟩
        exact False.elim (hne ((F.sectionGerm_eq_zero_iff (unop U) x hx 0).mpr
          ⟨unop U, hx, 𝟙 _, map_zero (F.toPresheaf.map (𝟙 U)).hom⟩))
      add_mem' := by
        intro s s' hs hs' x hx
        exact (F.suppSection_add_subset (unop U) s s' hx).elim (hs ·) (hs' ·)
      smul_mem' := by
        intro a s hs x hx
        exact hs (F.suppSection_smul_subset (unop U) a s hx).2 }
  map := by
    intro U V i s hs
    change F.suppSection (unop V) (F.toPresheaf.map i s) ⊆ Z ∩ (unop V : Opens X.carrier)
    intro x ⟨hx, hne⟩
    exact ⟨(hs ⟨i.unop.le hx,
      fun h ↦ hne ((sectionGerm_map_eq_zero_iff F i x hx s).mpr h)⟩).1, hx⟩

/-- The sheaf of modules whose local sections are those supported on `Z`. -/
noncomputable def supportedModuleSheaf {X : RingedSpace.{u, u}} (Z : Set X.carrier)
    (F : RingedSpace.ModuleSheaf X) :
    RingedSpace.ModuleSheaf X where
  toPresheaf := (supportedSubmodule Z F).toPresheafOfModules
  isSheaf := by
    apply Presheaf.isSheaf_of_isSheaf_comp (Opens.grothendieckTopology X.carrier)
      (s := forget AddCommGrpCat)
    apply (isSheaf_iff_isSheaf_of_type _ _).mpr
    change Presieve.IsSheaf (Opens.grothendieckTopology X.carrier)
      (supportedSubmodule Z F).toSubfunctor.toFunctor
    have hF : Presieve.IsSheaf (Opens.grothendieckTopology X.carrier)
        (F.abPresheaf ⋙ forget AddCommGrpCat) :=
      (isSheaf_iff_isSheaf_of_type _ _).mp
        (GrothendieckTopology.HasSheafCompose.isSheaf F.abPresheaf F.isSheaf)
    rw [(supportedSubmodule Z F).toSubfunctor.isSheaf_iff hF]
    intro U s hs
    change F.suppSection (unop U) s ⊆ Z ∩ (unop U : Opens X.carrier)
    intro x ⟨hx, hne⟩
    rw [Opens.mem_grothendieckTopology] at hs
    obtain ⟨W, g, hg, hxW⟩ := hs x hx
    have hmem : F.toPresheaf.map g.op s ∈ (supportedSubmodule Z F).obj (op W) := hg
    exact ⟨(hmem ⟨hxW,
      fun h ↦ hne ((sectionGerm_map_eq_zero_iff F g.op x hxW s).mp h)⟩).1, hx⟩

/-- The sheaf of sections of `F` supported on `Z`, equipped with its canonical inclusion into
`F`. On each open set the inclusion is injective and its range is precisely the set of
sections whose support is contained in `Z ∩ U`. -/
@[stacks 0G6N "the sheaf of sections supported on Z"]
noncomputable def supportedSectionsSheaf {X : RingedSpace.{u, u}}
    (Z : Set X.carrier) (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    Σ G : _root_.SheafOfModules.{u} (structureSheafRing X),
      {ι : G ⟶ F //
        (∀ U, Function.Injective (ι.val.app U)) ∧
          ∀ (U : (Opens X.carrier)ᵒᵖ) (s : F.val.obj U),
            s ∈ Set.range (ι.val.app U) ↔
              (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).suppSection (unop U) s ⊆
                Z ∩ ((unop U : Opens X.carrier) : Set X.carrier)} :=
  ⟨⟨(supportedModuleSheaf Z
        (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F)).toPresheaf,
      (supportedModuleSheaf Z
        (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F)).isSheaf⟩,
    ⟨(supportedSubmodule Z (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F)).ι⟩,
    ⟨fun _ _ _ h => Subtype.val_injective h,
    fun U s => by
      change s ∈ Set.range ((supportedSubmodule Z
        (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F)).ι.app U) ↔ _
      refine ⟨?_, fun hs => ⟨⟨s, hs⟩, rfl⟩⟩
      rintro ⟨t, rfl⟩
      exact t.2⟩⟩

/-- The canonical inclusion of the supported-sections sheaf into the original sheaf. -/
noncomputable def supportedSectionsSheafι {X : RingedSpace.{u, u}}
    (Z : Set X.carrier) (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (supportedSectionsSheaf Z F).1 ⟶ F :=
  (supportedSectionsSheaf Z F).2.1

/-- On sections, the inclusion of the supported-sections sheaf is the inclusion of a
submodule. -/
@[simp]
theorem supportedSectionsSheafι_app {X : RingedSpace.{u, u}}
    (Z : Set X.carrier) (F : _root_.SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ)
    (s : (supportedSectionsSheaf Z F).1.val.obj U) :
    ((supportedSectionsSheafι Z F).val.app U) s = s.1 :=
  rfl

/-- A section of `F` over `U` lies in the range of the inclusion exactly when its support is
contained in `Z ∩ U`. -/
theorem mem_supportedSectionsSheafι_range_iff {X : RingedSpace.{u, u}}
    (Z : Set X.carrier) (F : _root_.SheafOfModules.{u} (structureSheafRing X))
    (U : (Opens X.carrier)ᵒᵖ) (s : F.val.obj U) :
    s ∈ Set.range ((supportedSectionsSheafι Z F).val.app U) ↔
      (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).suppSection (unop U) s ⊆
        Z ∩ ((unop U : Opens X.carrier) : Set X.carrier) :=
  (supportedSectionsSheaf Z F).2.2.2 U s

/-- **Stacks 0G6N.** The sections supported on `Z` form a *submodule* sheaf of `F`: their
inclusion is a monomorphism of sheaves of modules. -/
@[stacks 0G6N "the supported sections form a submodule sheaf"]
instance supportedSectionsSheafι_mono {X : RingedSpace.{u, u}}
    (Z : Set X.carrier) (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    Mono (supportedSectionsSheafι Z F) := by
  refine ⟨fun {_} g h hgh => ?_⟩
  ext U s
  exact Subtype.ext (congrArg (fun k => k.val.app U s) hgh)

/-- **Stacks 0G6N.** The sheaf of sections supported on `Z` is itself supported on `Z`. -/
@[stacks 0G6N "the subsheaf is supported on Z"]
theorem supportedSectionsSheaf_supp_subset {X : RingedSpace.{u, u}}
    (Z : Set X.carrier) (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
      (supportedSectionsSheaf Z F).1).supp ⊆ Z := by
  intro x hx
  obtain ⟨U, s, hs⟩ := (RingedSpace.ModuleSheaf.mem_supp_iff _ x).mp hx
  have h := RingedSpace.ModuleSheaf.suppSection_subset_map_of_injective
    (F := AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
      (supportedSectionsSheaf Z F).1)
    (G := AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F)
    (supportedSectionsSheafι Z F).val (fun V => (supportedSectionsSheaf Z F).2.2.1 (op V)) U s hs
  exact ((mem_supportedSectionsSheafι_range_iff Z F (op U)
    ((supportedSectionsSheafι Z F).val.app (op U) s)).mp ⟨s, rfl⟩ h).1

/-- **Stacks 0G6N.** Maximality of the subsheaf of sections supported on `Z`: any morphism
into `F` from a sheaf of modules which is supported on `Z` factors through it. The
factorisation is unique because `supportedSectionsSheafι` is a monomorphism. -/
@[stacks 0G6N "maximality of the subsheaf among subsheaves supported on Z"]
theorem hom_to_supportedSectionsSheaf_of_supp_subset {X : RingedSpace.{u, u}}
    (Z : Set X.carrier) (F G : _root_.SheafOfModules.{u} (structureSheafRing X)) (i : G ⟶ F)
    (hG : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules G).supp ⊆ Z) :
    ∃ j : G ⟶ (supportedSectionsSheaf Z F).1,
      j ≫ supportedSectionsSheafι Z F = i := by
  have bound (U : (Opens X.carrier)ᵒᵖ) (s : G.val.obj U) :
      i.val.app U s ∈ (supportedSubmodule Z
        (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F)).obj U := by
    intro x hx
    refine ⟨hG ((RingedSpace.ModuleSheaf.mem_supp_iff _ x).2 ⟨unop U, s, ?_⟩), hx.1⟩
    exact RingedSpace.ModuleSheaf.suppSection_map_subset
      (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules G)
      (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F) i.val (unop U) s hx
  let φ : G.val.presheaf ⟶ (supportedSubmodule Z
      (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F)).toPresheafOfModules.presheaf :=
    { app := fun U => AddCommGrpCat.ofHom <| AddMonoidHom.mk'
        (fun s => ⟨i.val.app U s, bound U s⟩)
        (fun s t => Subtype.ext ((i.val.app U).hom.map_add s t))
      naturality := fun U V f => by
        ext s
        exact Subtype.ext (PresheafOfModules.naturality_apply i.val f s) }
  refine ⟨⟨PresheafOfModules.homMk φ
    (fun U r s => Subtype.ext ((i.val.app U).hom.map_smul r s))⟩, ?_⟩
  apply SheafOfModules.hom_ext
  ext U s
  rfl

end Stacks.SheafOfModules.SupportedSections

end
