module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentModules
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf

/-!
# Modules on a category fibred in groupoids (Stacks 06WB)

Let `p : 𝒳 ⥤ (Sch/S)_fppf` be a category fibred in groupoids over the big fppf category of a
scheme `S`. Since `𝒳` carries the structure sheaf `𝒪_𝒳` of Tag 06TV, it carries modules. A
presheaf of modules on `𝒳` is a presheaf of `𝒪_𝒳`-modules, and such a presheaf is called an
`𝒪_𝒳`-module, or a sheaf of `𝒪_𝒳`-modules, when its underlying presheaf of abelian groups
satisfies the sheaf condition for the fppf topology on `𝒳`. The two resulting categories are
written `PMod(𝒪_𝒳)` and `Mod(𝒪_𝒳)`.

The scalars are the presheaf of rings underlying `𝒪_𝒳`, whose sections at an object of `𝒳` are
the global functions on the underlying scheme. That presheaf is the same for each of the five
associated topologies of Tag 06TP, so `PMod(𝒪_𝒳)` does not depend on a choice of topology; only
the sheaf condition cutting out `Mod(𝒪_𝒳)` does, and there it is the fppf one.

## Main definitions

* `AlgebraicGeometry.Stack.ringStructurePresheaf`: the presheaf of rings underlying `𝒪_𝒳`.
* `AlgebraicGeometry.Stack.presheavesOfModules`: **Stacks 06WB**, part (1), the category
  `PMod(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.IsModule`: **Stacks 06WB**, part (2), the fppf sheaf condition
  singling out the `𝒪_𝒳`-modules among the presheaves of modules.
* `AlgebraicGeometry.Stack.ofIsModule`: a presheaf of modules satisfying that condition,
  regarded as an `𝒪_𝒳`-module.
* `AlgebraicGeometry.Stack.modules`: **Stacks 06WB**, part (2), the category `Mod(𝒪_𝒳)`.

## Main results

* `AlgebraicGeometry.Stack.modulesEquivFullSubcategory`: `Mod(𝒪_𝒳)` is the full subcategory of
  `PMod(𝒪_𝒳)` cut out by `AlgebraicGeometry.Stack.IsModule`, which is what part (2) says.
* `AlgebraicGeometry.Stack.quasicoherentModules_eq_fullSubcategory`: the quasi-coherent modules
  of Tag 06WG are a full subcategory of this `Mod(𝒪_𝒳)`.

## Implementation notes

A presheaf of modules over a presheaf of rings on a category, and a sheaf of modules over a
sheaf of rings on a site, are Mathlib's `CategoryTheory.PresheafOfModules` and
`CategoryTheory.SheafOfModules`. The latter is the general notion of Tag 03CW for an arbitrary
ringed site, which is not separately named in this library: part (2) below is that notion
instantiated at `𝒪_𝒳` on the fppf site of `𝒳`.

The coefficient sheaf is `AlgebraicGeometry.Stack.ringStructureSheafCore`, the sheaf of rings
underlying the structure sheaf that carries the Tag 06TV registration, taken at the fppf
topology `B.topology` with comparison hypothesis `le_rfl`. A second copy of that sheaf of rings
exists in the `AlgebraicGeometry.FibredSite` namespace, indexed by an enumeration of the five
topologies instead of by a topology and a comparison; it is an `rfl`-instantiation of this one
and is deliberately untagged, so the definitions here use the tagged one, which is also the one
the functoriality of Tags 06WD and 06WE is stated for.

The quasi-coherent modules of Tag 06WG were already stated as a full subcategory of sheaves of
modules over this same coefficient sheaf, before that ambient category had a name;
`quasicoherentModules_eq_fullSubcategory` records that the ambient category is exactly the
`modules` defined here, so the two cannot drift apart. That lemma is the only reason this file
imports the 06WG one. It is stated for `AlgebraicGeometry.Stack.quasicoherentModules`, the
copy over the coefficient sheaf used here; the tag registration for 06WG sits on the
`AlgebraicGeometry.FibredSite` copy, which is an `rfl`-instantiation of it.

## References

* [Stacks Project, Tag 06WB](https://stacks.math.columbia.edu/tag/06WB)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
* [Stacks Project, Tag 03CW](https://stacks.math.columbia.edu/tag/03CW)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- The presheaf of rings underlying the structure sheaf `𝒪_𝒳` of a category fibred in
groupoids: its sections at an object of `𝒳` are the global functions on the underlying scheme.
These are the scalars for presheaves of modules on `𝒳`. -/
noncomputable abbrev ringStructurePresheaf : 𝒳ᵒᵖ ⥤ RingCat.{u} :=
  (ringStructureSheafCore B S hS p hp B.topology le_rfl).obj

/-- The scalars do not depend on the associated topology: the structure sheaf for any topology
coarser than the fppf one has the same underlying presheaf of rings. -/
theorem ringStructurePresheaf_eq (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    ringStructurePresheaf B S hS p hp = (ringStructureSheafCore B S hS p hp τ hτ).obj := rfl

/-- **Stacks 06WB, part (1).** A presheaf of modules on a category fibred in groupoids `𝒳` over
the schemes over `S` is a presheaf of `𝒪_𝒳`-modules, and `PMod(𝒪_𝒳)` is the category they form,
with morphisms the morphisms of presheaves of modules. -/
@[stacks 06WB "part (1), the category of presheaves of modules"]
abbrev presheavesOfModules := PresheafOfModules.{m} (ringStructurePresheaf B S hS p hp)

/-- **Stacks 06WB, part (2).** A presheaf of `𝒪_𝒳`-modules is an `𝒪_𝒳`-module, or a sheaf of
`𝒪_𝒳`-modules, when it is an fppf sheaf, that is, when its underlying presheaf of abelian
groups satisfies the sheaf condition for the fppf topology on `𝒳`. -/
@[stacks 06WB "part (2), the fppf sheaf condition"]
abbrev IsModule : ObjectProperty (presheavesOfModules.{u, v, w, m} B S hS p hp) :=
  fun F ↦ Presheaf.IsSheaf (associatedTopology B S hS p B.topology) F.presheaf

/-- **Stacks 06WB, part (2).** The category `Mod(𝒪_𝒳)` of `𝒪_𝒳`-modules on a category fibred in
groupoids `𝒳` over the schemes over `S`: presheaves of `𝒪_𝒳`-modules that are fppf sheaves,
with morphisms the morphisms of presheaves of modules. -/
@[stacks 06WB "part (2), the category of modules"]
abbrev modules := SheafOfModules.{m} (ringStructureSheafCore B S hS p hp B.topology le_rfl)

/-- The underlying presheaf of modules of an `𝒪_𝒳`-module is an fppf sheaf. -/
theorem isModule_val (M : modules.{u, v, w, m} B S hS p hp) : IsModule B S hS p hp M.val :=
  M.isSheaf

/-- A presheaf of `𝒪_𝒳`-modules that is an fppf sheaf is an `𝒪_𝒳`-module. -/
noncomputable def ofIsModule (F : presheavesOfModules.{u, v, w, m} B S hS p hp)
    (hF : IsModule B S hS p hp F) : modules.{u, v, w, m} B S hS p hp :=
  ⟨F, hF⟩

/-- `Mod(𝒪_𝒳)` is the full subcategory of `PMod(𝒪_𝒳)` cut out by the fppf sheaf condition: an
`𝒪_𝒳`-module is nothing but a presheaf of modules satisfying that condition, and a morphism of
`𝒪_𝒳`-modules is nothing but a morphism of the underlying presheaves of modules. -/
@[simps]
noncomputable def modulesEquivFullSubcategory :
    modules.{u, v, w, m} B S hS p hp ≌ (IsModule.{u, v, w, m} B S hS p hp).FullSubcategory where
  functor :=
    { obj M := ⟨M.val, M.isSheaf⟩
      map f := ObjectProperty.homMk f.val }
  inverse :=
    { obj F := ⟨F.obj, F.property⟩
      map f := ⟨f.hom⟩ }
  unitIso := NatIso.ofComponents fun _ ↦ Iso.refl _
  counitIso := NatIso.ofComponents fun _ ↦ Iso.refl _

/-- The quasi-coherent modules of Tag 06WG are a full subcategory of `Mod(𝒪_𝒳)`: the ambient
category of `AlgebraicGeometry.Stack.quasicoherentModules` is the category of modules defined
here, so quasi-coherence is a condition on the objects of part (2)'s category and the two
constructions share one coefficient sheaf. -/
theorem quasicoherentModules_eq_fullSubcategory :
    quasicoherentModules.{u, v, w, m} B S hS p hp =
      (SheafOfModules.isQuasicoherentOnSite
        (ringStructureSheafCore B S hS p hp B.topology le_rfl) :
          ObjectProperty (modules.{u, v, w, m} B S hS p hp)).FullSubcategory :=
  rfl

end AlgebraicGeometry.Stack

end
