module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheafComparison

/-!
# Parasitic presheaves of modules are stable under flat pullback (Stacks 0774)

Let `g : 𝒴 ⟶ 𝒳` be a flat 1-morphism of algebraic stacks over a scheme `S` in a big fppf site
`B`, and let `F` be a presheaf of `𝒪_𝒳`-modules on one of the five sites associated with `𝒳`
by **Stacks 06TP**. Clause (1) of **Stacks 0774** says that if `F` is parasitic
(**Stacks 0773**) then so is its inverse image `g^*F`.

The inverse image is restriction along the functor underlying `g`, followed by the restriction
of scalars identifying the structure presheaf of `𝒴` with the restriction of the one of `𝒳`.
Its module of sections at an object `y` of `𝒴` is therefore the module of sections of `F` at
`g y`, so the clause reduces to the statement that `g` carries flat objects of `𝒴` to flat
objects of `𝒳`. That is the content of the source's proof: if `y` lies over a scheme `V` with
`y : V → 𝒴` flat, then `g y : V → 𝒴 → 𝒳` is flat because flatness of 1-morphisms of algebraic
stacks is stable under composition (**Stacks 06PX**).

## Main definitions

* `AlgebraicGeometry.Stack.modulePresheafPullbackOfHom`: the inverse image of presheaves of
  modules along a 1-morphism of algebraic stacks, on the site named by a `SiteKind`.

## Main results

* `AlgebraicGeometry.Stack.ringStructureSheafCore_obj_eq_hom`: the structure presheaf of rings
  of the source of a 1-morphism of algebraic stacks is the restriction along it of the one of
  the target.
* `AlgebraicGeometry.Stack.isParasitic_modulePresheafPullbackOfHom`: **Stacks 0774** (1).

## Implementation notes

A 1-morphism of algebraic stacks is strictly over the big fppf category: the functor
`g.hom.hom.toFunctor` it underlies satisfies `g.hom.hom.toFunctor ⋙ 𝒳.p = 𝒴.p` on the nose.
So the inverse image is literal precomposition with that functor, and the comparison of the two
sets of scalars is a `CategoryTheory.eqToHom` between two spellings of one presheaf of rings
rather than a transport along an isomorphism. This is the presentation
`AlgebraicGeometry.Stack.modulePullback` (**Stacks 06WE**) uses, and the pullback here is its
underlying functor on presheaves of modules, read at the topology a `SiteKind` names.

The parasitic condition of **Stacks 0773** is stated for presheaves of modules over the
structure presheaf of a named site, and that presheaf of rings does not depend on the name — only
its sheaf condition does. The clause is therefore proved once for all five topologies, with the
`SiteKind` carried along as a parameter.

The object-level step is not re-proved: it is
`AlgebraicGeometry.Stack.FlatFppf.flatObject_map`, which is where **Stacks 06PX** and the
2-Yoneda comparison between `g y : V → 𝒳` and the composite `V → 𝒴 → 𝒳` are already done.

## References

* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0774](https://stacks.math.columbia.edu/tag/0774)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 06PX](https://stacks.math.columbia.edu/tag/06PX)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (g : 𝒴 ⟶ 𝒳) (τ : SiteKind)

/-- The structure presheaf of rings of the source of a 1-morphism of algebraic stacks is the
restriction, along the functor the 1-morphism underlies, of the structure presheaf of rings of
the target.

This is `AlgebraicGeometry.Stack.ringStructureSheafCore_obj_eq` for the strict factorization
`g.hom.hom.w` that a 1-morphism of algebraic stacks carries, read at the topology named by a
`SiteKind`. It is the identification of scalars that makes restriction along `g` of a presheaf
of `𝒪_𝒳`-modules a presheaf of `𝒪_𝒴`-modules. -/
theorem ringStructureSheafCore_obj_eq_hom :
    (FibredSite.ringStructureSheafCore B S hS 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids τ).obj =
      g.hom.hom.toFunctor.op ⋙
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids τ).obj :=
  ringStructureSheafCore_obj_eq B S hS 𝒴.val.val.p 𝒳.val.val.p
    𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids g.hom.hom.toFunctor g.hom.hom.w
    (B.baseTopology τ) (B.baseTopology_le_topology τ)

/-- The inverse image `g^*` of presheaves of modules along a 1-morphism `g : 𝒴 ⟶ 𝒳` of
algebraic stacks, on the site named by a `SiteKind`: restriction along the functor `g`
underlies, then restriction of scalars along
`AlgebraicGeometry.Stack.ringStructureSheafCore_obj_eq_hom`.

This is the functor on presheaves of modules underlying
`AlgebraicGeometry.Stack.modulePullback` (**Stacks 06WE**). Neither step changes the module of
sections, so the sections of `g^*F` at an object `y` of `𝒴` are the sections of `F` at
`g y`. -/
noncomputable abbrev modulePresheafPullbackOfHom :
    PresheafOfModules.{t}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids τ).obj ⥤
      PresheafOfModules.{t}
        (FibredSite.ringStructureSheafCore B S hS 𝒴.val.val.p
          𝒴.val.isFiberedInGroupoids τ).obj :=
  PresheafOfModules.pushforward₀ g.hom.hom.toFunctor
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ).obj ⋙
    PresheafOfModules.restrictScalars
      (eqToHom (ringStructureSheafCore_obj_eq_hom B S hS g τ))

/-- **Stacks 0774** (1). If `F` is a parasitic presheaf of `𝒪_𝒳`-modules and `g : 𝒴 ⟶ 𝒳` is a
flat 1-morphism of algebraic stacks, then the inverse image `g^*F` is a parasitic presheaf of
`𝒪_𝒴`-modules.

Let `y` be an object of `𝒴` lying over a scheme `V` for which `y : V → 𝒴` is flat. Then
`g y : V → 𝒴 → 𝒳` is flat, being a composite of flat 1-morphisms (**Stacks 06PX**), so `F`
vanishes at `g y` by hypothesis. The sections of `g^*F` at `y` are the sections of `F` at
`g y`, whence the conclusion. -/
@[stacks 0774 "part (1): the inverse image of a parasitic presheaf of modules along a flat
1-morphism of algebraic stacks is parasitic"]
theorem isParasitic_modulePresheafPullbackOfHom
    (hg : AlgebraicStacks.IsFlat B S hS g)
    (F : PresheafOfModules.{t}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ).obj)
    (hF : IsParasitic B S hS 𝒳 τ F) :
    IsParasitic B S hS 𝒴 τ
      ((modulePresheafPullbackOfHom.{u, w, t} B S hS g τ).obj F) := fun y hy =>
  hF (g.hom.hom.toFunctor.obj y) (FlatFppf.flatObject_map B S hS g hg ⟨y, hy⟩)

end AlgebraicGeometry.Stack

end
