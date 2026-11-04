module

public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.ModuleValuedAlternatingComplex

/-!
# The slice-site scalar action on sections is restriction of scalars along an inclusion

Let `X` be a topological space carrying a sheaf of rings `R`, let `V` be an open subset and let
`I` be a sheaf of `R`-modules. For `W ≤ V`, `Stacks.Cohomology.CechSheaf.sectionsModuleOfLE`
makes the sections of `I` over `W` a module over `R(V)` by taking the module structure that the
presheaf of modules on the slice site over `V` carries at the object `Over.mk (homOfLE h)`. That
structure is a restriction of scalars along the ring map `R(V) ⟶ R(W)` induced by the *unique*
morphism out of the terminal slice object, and this map is the restriction map
`R.obj.map (homOfLE h).op` of the structure sheaf. Consequently the `R(V)`-action on sections over
`W` is the `R(W)`-action with the scalar restricted from `V` to `W`.

## Main definitions

* `Stacks.Cohomology.CechSheaf.topSliceHom`: the unique morphism of the opposite slice category
  from the terminal object `Over.mk (𝟙 V)` to `Over.mk (homOfLE h)`.

## Main results

* `Stacks.Cohomology.CechSheaf.hom_map_topSliceHom`: the ring map along which the slice site
  restricts scalars from `V` to `W` is the restriction map of the structure sheaf.
* `Stacks.Cohomology.CechSheaf.hom_map_topSliceHom_self`: at `W ≤ W` that ring map is the
  identity.
* `Stacks.Cohomology.CechSheaf.smul_sectionsModuleOfLE_val` and
  `Stacks.Cohomology.CechSheaf.smul_sectionsModuleOfLE`: the `R(V)`-action of
  `sectionsModuleOfLE` on the sections over `W` is the action of the restricted scalar, stated
  against the `ModuleCat` action of `R(W)` and against `sectionsModuleOfLE` at `W ≤ W`.
* `Stacks.Cohomology.CechSheaf.smul_restrictScalars_of_hom_eq`: restricting scalars along a ring
  map rewrites the action along any ring map provably equal to it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe uX uR uM v

namespace Stacks.Cohomology.CechSheaf

/-- The action obtained by restricting scalars along `f` is the action of `g r` whenever `g` is
equal to `f`. -/
theorem smul_restrictScalars_of_hom_eq {S T : Type*} [Ring S] [Ring T] {f g : S →+* T}
    (hfg : f = g) (M : ModuleCat.{v} T) (r : S) (m : ToType M) :
    letI : Module S (ToType M) := ((ModuleCat.restrictScalars f).obj M).isModule
    r • m = g r • m := by
  subst hfg
  rfl

noncomputable section

variable {X : Type uX} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{uR}}
  (V : Opens X) (I : SheafOfModules.{uM} R) {W : Opens X} (h : W ≤ V)

/-- The unique morphism of the opposite slice category over `V` from the terminal object
`Over.mk (𝟙 V)` to an open `W` contained in `V`. -/
abbrev topSliceHom (h : W ≤ V) :
    op (Over.mk (𝟙 V)) ⟶ op (Over.mk (homOfLE h)) :=
  (Over.mkIdTerminal (X := V)).op.to (op (Over.mk (homOfLE h)))

/-- The ring map `R(V) ⟶ R(W)` induced by the unique morphism out of the terminal slice object is
the restriction map of `R` along the inclusion `W ≤ V`. -/
theorem hom_map_topSliceHom :
    ((R.over V).obj.map (topSliceHom V h)).hom = (R.obj.map (homOfLE h).op).hom := by
  rw [(Over.mkIdTerminal (X := V)).op.hom_ext (topSliceHom V h)
    (Over.homMk (homOfLE h) (Subsingleton.elim _ _) :
      (Over.mk (homOfLE h) : Over V) ⟶ Over.mk (𝟙 V)).op]
  rfl

/-- The ring map `R(W) ⟶ R(W)` induced by the unique morphism out of the terminal slice object
over `W` is the identity. -/
theorem hom_map_topSliceHom_self (W : Opens X) :
    ((R.over W).obj.map (topSliceHom W (le_refl W))).hom = RingHom.id (SectionRing R W) := by
  rw [hom_map_topSliceHom W (le_refl W)]
  simp [homOfLE_refl]
  rfl

/-- The `R(V)`-action on sections over `W` is the `R(W)`-action on the restricted scalar. The
right-hand action is the `ModuleCat` action of `R(W)` on the sections of `I` over `W`. -/
theorem smul_sectionsModuleOfLE_val (a : SectionRing R V) (x : ToType (I.val.obj (op W))) :
    letI : Module (SectionRing R V) (ToType (I.val.obj (op W))) := sectionsModuleOfLE V I h
    a • x = (R.obj.map (homOfLE h).op).hom a • x :=
  smul_restrictScalars_of_hom_eq (hom_map_topSliceHom V h) (I.val.obj (op W)) a x

/-- The `R(V)`-action on sections over `W` is the `R(W)`-action on the restricted scalar, with both
actions taken from the slice site: the action of `a : R(V)` is the action of the restriction of
`a` to `W` for the module structure the slice site over `W` carries. -/
theorem smul_sectionsModuleOfLE (a : SectionRing R V)
    (x : ToType ((abSections I).obj (op W))) :
    letI := sectionsModuleOfLE V I h
    letI := sectionsModuleOfLE W I (le_refl W)
    a • x = ((R.obj.map (homOfLE h).op).hom a) • x :=
  (smul_restrictScalars_of_hom_eq (hom_map_topSliceHom V h) (I.val.obj (op W)) a x).trans
    (smul_restrictScalars_of_hom_eq (hom_map_topSliceHom_self W) (I.val.obj (op W))
      ((R.obj.map (homOfLE h).op).hom a) x).symm

end

end Stacks.Cohomology.CechSheaf

end
