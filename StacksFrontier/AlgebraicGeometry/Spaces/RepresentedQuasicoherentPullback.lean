module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange

/-!
# Pullback across the comparison of quasi-coherent modules on a representable algebraic space

Let `B` be a big fppf site containing a scheme `S` and let `g : T' ⟶ T` be a morphism of the big
fppf category over `S`.  The quasi-coherent `AlgebraicGeometry.Scheme.Modules` on the scheme
underlying an object `U` are equivalent to `QCoh(𝒪_{yoneda.obj U})` by
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`.  This file matches that
equivalence with pullback: the inverse image of Stacks 03LU along the morphism `φ` of
representable algebraic spaces represented by `g` carries the `𝒪`-module that a quasi-coherent
module on the scheme underlying `T` becomes to the `𝒪`-module that its Zariski pullback becomes.

## Main definitions

* `AlgebraicGeometry.Space.representedQuasicoherentSchemePullback`: the Zariski pullback of a
  quasi-coherent module along the morphism of schemes underlying `g`, read as an object of the
  source category of the comparison equivalence at `T'`.

## Main results

* `AlgebraicGeometry.Space.representedQuasicoherentSchemePullbackIso`: **the comparison
  equivalence matches pullback.**

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

/-- The Zariski pullback of a quasi-coherent module along the morphism of schemes underlying
`g`, read as an object of the category of quasi-coherent `AlgebraicGeometry.Scheme.Modules` on
the scheme underlying `T'`.  Quasi-coherence of the pullback is Stacks 01BG. -/
noncomputable def representedQuasicoherentSchemePullback
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf).FullSubcategory) :
    (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf).FullSubcategory :=
  ⟨(_root_.AlgebraicGeometry.Scheme.Modules.pullback (B.inclusion.map g.left)).obj M.obj,
    @Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _
      (B.inclusion.map g.left) M.obj M.property⟩

/-- **The comparison of quasi-coherent modules on a representable algebraic space matches
pullback.**  For a quasi-coherent `AlgebraicGeometry.Scheme.Modules` `M` on the scheme underlying
`T`, the inverse image of Stacks 03LU along the morphism of representable algebraic spaces
represented by `g` of the `𝒪`-module that `M` becomes is the `𝒪`-module that the Zariski pullback
of `M` along the morphism of schemes underlying `g` becomes.

The source is written through `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`
and the associated module, which is the image of `M` under
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence` by
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence_functor_obj_obj`. -/
noncomputable def representedQuasicoherentSchemePullbackIso
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf).FullSubcategory) :
    (modulePullback B S hS (representedSpaceMap B S hS g)).obj
        ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj M.obj)) ≅
      ((representedQuasicoherentSchemeEquivalence B S hS T').functor.obj
        (representedQuasicoherentSchemePullback B S hS g M)).obj :=
  representedAssociatedModulePullbackIso B S hS g
      (relativelyRepresentable_yoneda_map B S hS g) M.obj

end AlgebraicGeometry.Space

end
