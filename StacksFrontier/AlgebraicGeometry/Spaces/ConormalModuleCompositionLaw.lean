module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleCompositionSections

/-!
# Pasting the square comparisons of the canonical map of conormal modules

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
|        |
f'       g'
↓        ↓
Z'' i''→ X''
```
be two vertically composable commutative squares of algebraic spaces over a scheme `S` contained
in a big fppf site `B`, with `Z ⊆ X`, `Z' ⊆ X'` and `Z'' ⊆ X''` closed subspaces.  This file
proves that **the comparison isomorphisms of the two squares paste**, at the defining ideal sheaf
of `Z''`, as an equation between composites of components.  The composition law for the
canonical map of conormal modules of [Stacks Project, Tag 04CP], part (3) of
[Stacks Project, Tag 04G2] for the small étale site of an algebraic space, is
`AlgebraicGeometry.Space.conormalMap_comp` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleComposition.lean`, where it is registered.

## Main results

* `AlgebraicGeometry.Space.comp_app_of_paste`: a pasting of two whiskered square comparisons,
  read at one object as a composite of three components.
* `AlgebraicGeometry.Space.conormalPullbackComparison_paste`: the comparison isomorphisms of the
  two squares paste, at the defining ideal sheaf of `Z''`.

## Implementation notes

The equation is the pasting `AlgebraicGeometry.Space.conormalPullbackCompIso_paste` of natural
transformations, read at the defining ideal sheaf of `Z''` and expanded into its three
components.

**Why the expansion goes through a statement about arbitrary functors.**  The pasted composite of
`AlgebraicGeometry.Space.conormalPullbackCompIso_paste_app` is a single natural transformation
evaluated at a module, and reading it as its three components is a defeq that the kernel does not
complete inside its budget: the composite's two inner junctions hold only up to associativity of
composition of functors, and at such a junction the comparison of two objects is a comparison of
`CategoryTheory.Functor.comp` of two inverse images with a single inverse image, whose refutation
by congruence forces `AlgebraicGeometry.Space.modulePullback` open to its construction by
sheafification.  Every component is accepted on its own, the budget is not raisable, and the
reducibility attribute that keeps the elaborator out of the sheafification is ignored by the
kernel.

`AlgebraicGeometry.Space.comp_app_of_paste` removes the difficulty rather than working around
it: it is the same reading of the same composite, stated for *arbitrary* functors between
arbitrary categories, so at a junction the only definitions that can be unfolded are
`CategoryTheory.Functor.comp` and the projections of a structure.  Instantiating it at the nine
inverse-image functors asks the kernel for nothing beyond substitution, and the expansion is
checked in under a second.  The same device is what makes
`AlgebraicGeometry.Space.app_conormalModule_eq` and
`AlgebraicGeometry.Space.map_conormalPullbackComparison_eq` below affordable: each is a `rfl`
between two spellings of one morphism, and each is past the budget when the comparison
isomorphism it is stated at is written out, because the elaborator then unfolds that isomorphism
through `CategoryTheory.Adjunction.leftAdjointUniq`.  With the transformation, respectively the
functor, left arbitrary there is nothing to unfold and both are immediate.  They are handed to
`comp_app_of_paste` as its two replacement hypotheses, so that the pasting is produced already in
the folded spelling of the conormal module of `Z''` in `X''`.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **A pasting of two whiskered square comparisons, read at one object.**  Let `out`, `cpc'` and
`cpc` be natural transformations of composites of functors, in the shape of the comparisons
attached to an outer rectangle and to the two squares that make it up, and let `kff'` and `kgg'`
compare the inverse images along the two composable edges.  If the pasting identity holds between
natural transformations, then at every object it holds between the corresponding composites of
components, each of which may be replaced by anything equal to it.

Stated for arbitrary functors on purpose; the implementation notes of this file record what that
buys. -/
theorem comp_app_of_paste {A A' A'' AZ AZ' AZ'' : Type*}
    [Category A] [Category A'] [Category A''] [Category AZ] [Category AZ'] [Category AZ'']
    (Pi : A ⥤ AZ) (Pi' : A' ⥤ AZ') (Pi'' : A'' ⥤ AZ'')
    (Pf : AZ' ⥤ AZ) (Pf' : AZ'' ⥤ AZ') (Pff' : AZ'' ⥤ AZ)
    (Pg : A' ⥤ A) (Pg' : A'' ⥤ A') (Pgg' : A'' ⥤ A)
    (kff' : Pff' ⟶ Pf' ⋙ Pf) (kgg' : Pgg' ⟶ Pg' ⋙ Pg)
    (out : Pi'' ⋙ Pff' ⟶ Pgg' ⋙ Pi)
    (cpc' : Pi'' ⋙ Pf' ⟶ Pg' ⋙ Pi') (cpc : Pi' ⋙ Pf ⟶ Pg ⋙ Pi)
    (h : out ≫ Functor.whiskerRight kgg' Pi =
      Functor.whiskerLeft Pi'' kff' ≫ Functor.whiskerRight cpc' Pf ≫
        Functor.whiskerLeft Pg' cpc)
    (M : A'') {c₁ : Pff'.obj (Pi''.obj M) ⟶ Pf.obj (Pf'.obj (Pi''.obj M))}
    (hc₁ : c₁ = kff'.app (Pi''.obj M))
    {c₂ : Pf.obj (Pf'.obj (Pi''.obj M)) ⟶ Pf.obj (Pi'.obj (Pg'.obj M))}
    (hc₂ : c₂ = Pf.map (cpc'.app M)) :
    out.app M ≫ Pi.map (kgg'.app M) = c₁ ≫ c₂ ≫ cpc.app (Pg'.obj M) := by
  rw [hc₁, hc₂]
  simpa using NatTrans.congr_app h M

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' X'' : AlgebraicSpaces B S hS} (g : X ⟶ X') (g' : X' ⟶ X'')

/-- The comparison factor of the conormal map, read as the component of
`AlgebraicGeometry.Space.conormalPullbackCompIso` at the defining ideal sheaf that it is by
definition. -/
theorem conormalPullbackComparison_eq
    (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1)
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z') :
    conormalPullbackComparison B S hS Z Z' g f hsq =
      (conormalPullbackCompIso B S hS Z Z' g f hsq).hom.app
        (definingIdealSheaf B S hS X' Z').toSheafOfModules :=
  rfl

variable (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1)
    (Z'' : ClosedSubspaces B S hS X''.1)
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (f' : (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (hsq' : subspaceInclusion B S hS X' Z' ≫ g' = f' ≫ subspaceInclusion B S hS X'' Z'')
    (hsq'' : subspaceInclusion B S hS X Z ≫ g ≫ g' =
      (f ≫ f') ≫ subspaceInclusion B S hS X'' Z'')

/-- The conormal module of `Z''` in `X''` read as the inverse image of the defining ideal sheaf
along `i''` that it is, inside the dependent argument of `CategoryTheory.NatTrans.app`.  The
transformation is left arbitrary; the implementation notes of this file record why. -/
theorem app_conormalModule_eq {D : AlgebraicSpaces B S hS}
    {F G : Modules.{u, u} B S hS Z''.1.toFunctor Z''.2.1 ⥤ Modules.{u, u} B S hS D.1 D.2}
    (α : F ⟶ G) :
    α.app (conormalModule B S hS X'' Z'') =
      α.app ((modulePullback B S hS (subspaceInclusion B S hS X'' Z'')).obj
        (definingIdealSheaf B S hS X'' Z'').toSheafOfModules) :=
  rfl

/-- `AlgebraicGeometry.Space.conormalPullbackComparison_eq` under a functor.  The functor is left
arbitrary; the implementation notes of this file record why. -/
theorem map_conormalPullbackComparison_eq {E : Type*} [Category E]
    (P : Modules.{u, u} B S hS Z'.1.toFunctor Z'.2.1 ⥤ E) :
    P.map (conormalPullbackComparison B S hS Z' Z'' g' f' hsq') =
      P.map ((conormalPullbackCompIso B S hS Z' Z'' g' f' hsq').hom.app
        (definingIdealSheaf B S hS X'' Z'').toSheafOfModules) :=
  rfl

/-- **The square comparisons of the two squares paste, at the defining ideal sheaf of `Z''`.**
The comparison factor of the conormal map of the outer rectangle, followed by the inverse image
along the inclusion of `Z` of the composition comparison of the two right-hand edges, is the
composition comparison of the two left-hand edges, followed by the inverse image along `f` of the
comparison factor of the lower square, followed by the comparison of the upper square at
`(g')^*𝓘''`.

This is `AlgebraicGeometry.Space.conormalPullbackCompIso_paste` read at one module, expanded into
its three components by `AlgebraicGeometry.Space.comp_app_of_paste`. -/
theorem conormalPullbackComparison_paste :
    conormalPullbackComparison B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'' ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          ((modulePullbackCompIso B S hS g g').inv.app
            (definingIdealSheaf B S hS X'' Z'').toSheafOfModules) =
      (modulePullbackCompIso B S hS f f').inv.app (conormalModule B S hS X'' Z'') ≫
        (modulePullback B S hS f).map
          (conormalPullbackComparison B S hS Z' Z'' g' f' hsq') ≫
          (conormalPullbackCompIso B S hS Z Z' g f hsq).hom.app
            ((modulePullback B S hS g').obj
              (definingIdealSheaf B S hS X'' Z'').toSheafOfModules) :=
  Eq.trans
    (eq_whisker (conormalPullbackComparison_eq B S hS (g ≫ g') Z Z'' (f ≫ f') hsq'') _)
    (comp_app_of_paste
      (modulePullback B S hS (subspaceInclusion B S hS X Z))
      (modulePullback B S hS (subspaceInclusion B S hS X' Z'))
      (modulePullback B S hS (subspaceInclusion B S hS X'' Z''))
      (modulePullback B S hS f) (modulePullback B S hS f')
      (modulePullback B S hS (f ≫ f'))
      (modulePullback B S hS g) (modulePullback B S hS g')
      (modulePullback B S hS (g ≫ g'))
      (modulePullbackCompIso B S hS f f').inv
      (modulePullbackCompIso B S hS g g').inv
      (conormalPullbackCompIso B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'').hom
      (conormalPullbackCompIso B S hS Z' Z'' g' f' hsq').hom
      (conormalPullbackCompIso B S hS Z Z' g f hsq).hom
      (conormalPullbackCompIso_paste B S hS Z Z' Z'' g g' f f' hsq hsq' hsq'')
      (definingIdealSheaf B S hS X'' Z'').toSheafOfModules
      (app_conormalModule_eq B S hS Z'' (modulePullbackCompIso B S hS f f').inv)
      (map_conormalPullbackComparison_eq B S hS g' Z' Z'' f' hsq'
        (modulePullback B S hS f)))

end AlgebraicGeometry.Space

end
