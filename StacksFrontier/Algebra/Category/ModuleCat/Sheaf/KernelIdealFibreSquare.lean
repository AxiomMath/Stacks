module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposSheafSetsFibreSquare

/-!
# An ideal cut out sectionwise by a morphism of sheaves of rings is a fibre square

Let `α : R ⟶ R'` be a morphism of sheaves of rings on a site and let `N ⊆ R` be an ideal
subsheaf — a `SheafOfModules.Submodule` of the unit module — whose sections over every object of
the site are exactly the sections of `R` that `α` kills.  This file exhibits that sectionwise
description as a **pullback square of sheaves of sets**

```
  N ------→ R
  |         |
  ↓         ↓ α
  ⊤ --0--→  R'
```

## Main definitions

* `Stacks.Sheaves.ToposPullback.submoduleInclSheafSets`: the inclusion of an ideal subsheaf into
  the sheaf of rings, on underlying sheaves of sets.
* `Stacks.Sheaves.ToposPullback.zeroModuleHom`: the zero morphism from an arbitrary sheaf of sets
  to the sheaf of sets underlying a sheaf of modules.

## Main results

* `Stacks.Sheaves.ToposPullback.isPullback_submoduleInclSheafSets`: **the fibre square.**
* `Stacks.Sheaves.ToposPullback.map_zeroModuleHom`: the zero morphism transports to the
  transported zero along a finite-product-preserving functor to types.  This is
  `AlgebraicGeometry.Space.map_zeroDerivationHom` with the source of the zero morphism left
  arbitrary instead of being the sheaf of sets of a sheaf of rings.
* `Stacks.Sheaves.ToposPullback.injective_sections_of_iso`: an isomorphism of sheaves of sets is
  injective on sections over every object of the site.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal sheaf
  as the kernel of the structure map.
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3), the kernel ideal of a
  closed immersion of topoi.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

namespace Stacks.Sheaves.ToposPullback

universe t w v u

section FibreSquare

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {R R' : Sheaf J RingCat.{w}}

/-- **The inclusion of an ideal subsheaf into the sheaf of rings, on underlying sheaves of
sets.**  The target is the sheaf of sets underlying `R` itself, rather than that underlying its
unit module. -/
noncomputable def submoduleInclSheafSets (N : (SheafOfModules.unit R).Submodule) :
    Sheaf.moduleSheaf R N.toSheafOfModules ⟶ Sheaf.ringSheaf R :=
  (Sheaf.moduleSheafFunctor R).map N.ι

/-- The inclusion of an ideal subsheaf is, on sections, the inclusion of a submodule. -/
lemma submoduleInclSheafSets_app (N : (SheafOfModules.unit R).Submodule) (U : Cᵒᵖ)
    (x : N.toSheafOfModules.val.obj U) :
    (submoduleInclSheafSets N).hom.app U x = x.1 :=
  rfl

/-- **An ideal subsheaf cut out sectionwise by a morphism of sheaves of rings is the fibre of
that morphism over the zero section**, as a pullback square of sheaves of sets. -/
theorem isPullback_submoduleInclSheafSets (α : R ⟶ R')
    (N : (SheafOfModules.unit R).Submodule)
    (hN : ∀ (U : Cᵒᵖ) (a : (SheafOfModules.unit R).val.obj U),
      a ∈ N.obj U ↔ (α.hom.app U).hom a = 0) :
    IsPullback (submoduleInclSheafSets N) (terminal.from _)
      ((sheafCompose J (forget RingCat.{w})).map α) (Sheaf.ringZeroHom R') := by
  refine isPullback_terminal_of_sections _ _ _ ?_
    (fun _ _ _ h ↦ Subtype.val_injective h)
    (fun U a ha ↦ ⟨⟨a, (hN U a).2 ha⟩, rfl⟩)
  refine hom_ext_sections fun U x ↦ ?_
  rw [(Sheaf.sectionsFunctor J U).map_comp_apply, (Sheaf.sectionsFunctor J U).map_comp_apply,
    Sheaf.sectionsFunctor_map_ringZeroHom]
  exact (hN U x.1).1 x.2

end FibreSquare

section Zero

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- The zero morphism from a sheaf of sets to the sheaf of sets underlying a sheaf of modules:
the unique morphism to the terminal sheaf followed by the zero section. -/
noncomputable def zeroModuleHom (A : Sheaf J (Type w)) (R : Sheaf J RingCat.{w})
    (G : SheafOfModules.{w} R) : A ⟶ Sheaf.moduleSheaf R G :=
  terminal.from A ≫ Sheaf.moduleZeroHom R G

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The zero morphism transports to the transported zero along a finite-product-preserving
functor to types. -/
lemma map_zeroModuleHom (A : Sheaf J (Type w)) (R : Sheaf J RingCat.{w})
    (G : SheafOfModules.{w} R) (P : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteProducts P]
    (x : P.obj A) :
    P.map (zeroModuleHom A R G) x = Sheaf.moduleZeroObj R G P := by
  rw [zeroModuleHom, P.map_comp_apply, Functor.map_terminalFrom_apply, Sheaf.moduleZeroObj]

end Zero

section Sections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **An isomorphism of sheaves of sets is injective on sections** over every object of the
site. -/
lemma injective_sections_of_iso {A A' : Sheaf J (Type w)} (e : A ≅ A') (U : Cᵒᵖ) :
    Function.Injective ((Sheaf.sectionsFunctor J U).map e.hom) :=
  ((Sheaf.sectionsFunctor J U).mapIso e).toEquiv.injective

end Sections

end Stacks.Sheaves.ToposPullback

end
