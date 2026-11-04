module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleCompositionSections

/-!
# The composition law for the conormal map of two stacked squares

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
proves **part (3) of [Stacks Project, Tag 04G2]**: the canonical map
`(f ≫ f')^*𝒞_{Z''/X''} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 04CP] attached to the outer rectangle
is the composition comparison of [Stacks Project, Tag 03LU] for `f` and `f'`, followed by the
inverse image along `f` of the map of the lower square, followed by the map of the upper square.

Both halves of the mathematics are already proved, unconditionally:
`AlgebraicGeometry.Space.conormalPullbackCompIso_paste_app` pastes the comparison isomorphisms
of the two squares, and `AlgebraicGeometry.Space.idealSheafMap_comp` is the composition law for
the maps of defining ideal sheaves.  What this file adds is the assembly of the two, which is
delicate for the reason recorded in the implementation notes below.

## Main results

* `AlgebraicGeometry.Space.conormalPullbackComparison_comp`: the comparison factors compose —
  the comparison of the outer rectangle, followed by the inverse image along the inclusion of `Z`
  of the composition comparison of the two vertical maps of ambient spaces, is the composition
  comparison of the two vertical maps of subspaces followed by the inverse image along `f` of the
  comparison of the lower square followed by the comparison of the upper square.

`AlgebraicGeometry.Space.conormalMap_comp` — **part (3) of [Stacks Project, Tag 04G2]**, the
composition law for the conormal map — is the one-line consequence of the comparison above, and
is stated in `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleComposition.lean`, which
reaches the same identity through its own pasting lemma.  It is not restated here.

## Implementation notes

The obstruction here is neither mathematical nor a matter of transparency settings: it is that
the *kernel* cannot compare `η.app A` with `η.app B`, nor `P.map a` with `P.map b`, when the
arguments are definitionally but not syntactically equal and `η`, `P` are the comparison
isomorphisms and inverse-image functors of this development.  Reducing those projections makes
the kernel unfold `AlgebraicGeometry.Space.modulePullbackCompIso` to
`CategoryTheory.Adjunction.leftAdjointUniq`, or
`AlgebraicGeometry.Space.modulePullback` to its construction by sheafification, and neither
terminates: every such comparison is rejected with `(kernel) deterministic timeout`
while the corresponding comparison of *objects*,
`(modulePullback h).obj A =?= (modulePullback h).obj B`, is accepted at once.

Two spellings of the conormal module unavoidably meet here.
`AlgebraicGeometry.Space.conormalPullbackCompIso_paste_app` delivers its leading factor at
`(modulePullback (subspaceInclusion X'' Z'')).obj (definingIdealSheaf X'' Z'').toSheafOfModules`,
because that is what whiskering on the left produces, while the statement of the composition law
needs it at `AlgebraicGeometry.Space.conormalModule`, because that is what the type of
`AlgebraicGeometry.Space.conormalMap` is phrased in.  The two are equal by
`AlgebraicGeometry.Space.conormalModule_eq`, which is `rfl`, but neither `rfl` nor `exact` nor
`rw` can be used to pass between them inside a `.app`: that is exactly the comparison the kernel
cannot make.

The two devices that work, and the reason each is needed, are:

* for a **functor** applied to a morphism, `CategoryTheory.Functor.map` is *not* dependent on the
  morphism — only on its source and target — so `congrArg` transports an equation of morphisms
  through it, and the kernel merely instantiates the general lemma instead of comparing the two
  sides.  This is `AlgebraicGeometry.Space.conormalPullbackCompIso_whiskerRight_app` below.
* for a **natural transformation** evaluated at an object, `CategoryTheory.NatTrans.app` *is*
  dependent on the object, so `congrArg` does not typecheck.  The equation is therefore first
  proved as a `HEq`, where the two types stay apart and the motive of the rewrite is type
  correct, and only then converted by `eq_of_heq`, whose single remaining obligation is that the
  two hom-types agree — a comparison of objects, which is cheap.  This is
  `AlgebraicGeometry.Space.modulePullbackCompIso_inv_app_conormalModule` below.

With those two bridges in place, the pasted composite is expanded one factor at a time by
`CategoryTheory.NatTrans.comp_app`, `CategoryTheory.Functor.whiskerLeft_app` and
`CategoryTheory.Functor.whiskerRight_app` and reassembled with
`CategoryTheory.eq_whisker` and `CategoryTheory.whisker_eq`.  No step ever presents the kernel
with the three-factor composite expanded all at once, which is itself rejected: that is the
measurement already recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleCompositionSections.lean`, and it is why
`conormalPullbackCompIso_paste_app` leaves its right-hand side unexpanded.

`AlgebraicGeometry.Space.modulePullback`,
`AlgebraicGeometry.Space.modulePullbackCompIso` and
`AlgebraicGeometry.Space.conormalPullbackCompIso` are made locally irreducible in the second
section, which is what keeps the *elaborator* from taking the same non-terminating route; the
kernel is unaffected by that and is handled by the two bridges instead.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' X'' : AlgebraicSpaces B S hS} (g : X ⟶ X') (g' : X' ⟶ X'')

/-! ### Splitting the two conormal maps along their shared right factor -/

section Decomposition

-- The statements below compare `(g'^* ⋙ g^*).obj 𝓘''` with `g^*(g'^*𝓘'')`; unfolding the
-- inverse image to its construction does not terminate, and is not needed to see they agree.
attribute [local irreducible] modulePullback

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


end Decomposition

/-! ### Passing between the two spellings of the conormal module -/

section Bridge

-- See the implementation notes: this keeps the *elaborator* from unfolding the inverse image and
-- the composition comparison to their constructions, which does not terminate.
attribute [local irreducible] modulePullback modulePullbackCompIso

/-- **Transporting an equality of morphisms through a functor, with the two hom-types kept
apart.**  `CategoryTheory.Functor.map` depends on the source and the target of the morphism it
is applied to, so `congrArg` through it requires the two morphisms to have the same type; this
is the form that does not require it, and it is what lets a definitional unfolding be pushed
under a `CategoryTheory.Functor.map` without the kernel ever being asked to compare two
`CategoryTheory.Functor.map` applications whose implicit objects are spelled differently.  See
the implementation notes of this file. -/
theorem map_heq_map {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {W V W' V' : C} {m : W ⟶ V} {m' : W' ⟶ V'} (hW : W = W') (hV : V = V') (h : HEq m m') :
    HEq (P.map m) (P.map m') := by
  subst hW
  subst hV
  rw [eq_of_heq h]

/-- **The composition comparison of [Stacks Project, Tag 03LU], read at the conormal module.**
Whiskering on the left by the inverse image along the inclusion of a closed subspace `Z ⊆ V`
produces the comparison at `i^*𝓘_Z`; that object is the conormal module `𝒞_{Z/V}` by
`AlgebraicGeometry.Space.conormalModule_eq`, and this is that identification.

Proved through `HEq`: `CategoryTheory.NatTrans.app` depends on the object it is evaluated at, so
`congrArg` does not typecheck and the motive of a rewrite is type correct only while the two
hom-types are kept apart.  The implementation notes of this file record why the direct proof by
`rfl` is not available. -/
theorem modulePullbackCompIso_inv_app_conormalModule {W Y V : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS V.1) (a : W ⟶ Y)
    (b : Y ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) :
    (modulePullbackCompIso B S hS a b).inv.app
        ((modulePullback B S hS (subspaceInclusion B S hS V Z)).obj
          (definingIdealSheaf B S hS V Z).toSheafOfModules) =
      (modulePullbackCompIso B S hS a b).inv.app (conormalModule B S hS V Z) := by
  have hobj : (modulePullback B S hS (subspaceInclusion B S hS V Z)).obj
      (definingIdealSheaf B S hS V Z).toSheafOfModules = conormalModule B S hS V Z := rfl
  have hheq : HEq
      ((modulePullbackCompIso B S hS a b).inv.app
        ((modulePullback B S hS (subspaceInclusion B S hS V Z)).obj
          (definingIdealSheaf B S hS V Z).toSheafOfModules))
      ((modulePullbackCompIso B S hS a b).inv.app (conormalModule B S hS V Z)) := by
    rw [hobj]
  exact eq_of_heq hheq

end Bridge

/-! ### The composition law -/

section Law

-- See the implementation notes: these keep the *elaborator* from unfolding the inverse image and
-- the comparison isomorphisms to their constructions, which does not terminate.
attribute [local irreducible] modulePullback modulePullbackCompIso conormalPullbackCompIso

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

/-- The middle factor of the pasted composite, read through the bridge
`AlgebraicGeometry.Space.conormalPullbackComparison`.

`CategoryTheory.Functor.map` does not depend on the morphism it is applied to, only on its source
and target, so the passage to the bridge is a `congrArg` whose type is left to be inferred; see
the implementation notes. -/
private theorem paste_mid :
    (Functor.whiskerRight (conormalPullbackCompIso B S hS Z' Z'' g' f' hsq').hom
          (modulePullback B S hS f)).app
        (definingIdealSheaf B S hS X'' Z'').toSheafOfModules =
      (modulePullback B S hS f).map
        (conormalPullbackComparison B S hS Z' Z'' g' f' hsq') :=
  (rfl :
      (Functor.whiskerRight (conormalPullbackCompIso B S hS Z' Z'' g' f' hsq').hom
            (modulePullback B S hS f)).app
          (definingIdealSheaf B S hS X'' Z'').toSheafOfModules =
        (modulePullback B S hS f).map
          ((conormalPullbackCompIso B S hS Z' Z'' g' f' hsq').hom.app
            (definingIdealSheaf B S hS X'' Z'').toSheafOfModules)).trans
    (eq_of_heq
      (map_heq_map (m := (conormalPullbackCompIso B S hS Z' Z'' g' f' hsq').hom.app
            (definingIdealSheaf B S hS X'' Z'').toSheafOfModules)
          (m' := conormalPullbackComparison B S hS Z' Z'' g' f' hsq')
        (modulePullback B S hS f) rfl rfl (HEq.refl _)))

/-- The lower two factors of the pasted composite, assembled from the middle factor. -/
private theorem paste_lower_app :
    (Functor.whiskerRight (conormalPullbackCompIso B S hS Z' Z'' g' f' hsq').hom
            (modulePullback B S hS f) ≫
          Functor.whiskerLeft (modulePullback B S hS g')
            (conormalPullbackCompIso B S hS Z Z' g f hsq).hom).app
        (definingIdealSheaf B S hS X'' Z'').toSheafOfModules =
      (modulePullback B S hS f).map
          (conormalPullbackComparison B S hS Z' Z'' g' f' hsq') ≫
        (conormalPullbackCompIso B S hS Z Z' g f hsq).hom.app
          ((modulePullback B S hS g').obj
            (definingIdealSheaf B S hS X'' Z'').toSheafOfModules) :=
  (NatTrans.comp_app _ _ _).trans
    ((eq_whisker (paste_mid B S hS g' Z Z' Z'' f f' hsq') _).trans
      (whisker_eq _ (Functor.whiskerLeft_app _ _ _)))

/-- The leading factor of the pasted composite, moved onto the conormal module of `Z''`. -/
private theorem paste_lead_app :
    (Functor.whiskerLeft (modulePullback B S hS (subspaceInclusion B S hS X'' Z''))
          (modulePullbackCompIso B S hS f f').inv).app
        (definingIdealSheaf B S hS X'' Z'').toSheafOfModules =
      (modulePullbackCompIso B S hS f f').inv.app (conormalModule B S hS X'' Z'') :=
  (rfl :
      (Functor.whiskerLeft (modulePullback B S hS (subspaceInclusion B S hS X'' Z''))
            (modulePullbackCompIso B S hS f f').inv).app
          (definingIdealSheaf B S hS X'' Z'').toSheafOfModules =
        (modulePullbackCompIso B S hS f f').inv.app
          ((modulePullback B S hS (subspaceInclusion B S hS X'' Z'')).obj
            (definingIdealSheaf B S hS X'' Z'').toSheafOfModules)).trans
    (modulePullbackCompIso_inv_app_conormalModule B S hS Z'' f f')

/-- **The comparison factors of the two squares compose.**  The comparison of the outer
rectangle, followed by the inverse image along the inclusion of `Z` of the composition comparison
of [Stacks Project, Tag 03LU] for `g` and `g'`, is the composition comparison for `f` and `f'` at
the conormal module of `Z''`, followed by the inverse image along `f` of the comparison of the
lower square, followed by the comparison of the upper square.

This is `AlgebraicGeometry.Space.conormalPullbackCompIso_paste_app` with its pasted composite
expanded; see the implementation notes of this file for why the expansion is staged. -/
theorem conormalPullbackComparison_comp :
    conormalPullbackComparison B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'' ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          ((modulePullbackCompIso B S hS g g').inv.app
            (definingIdealSheaf B S hS X'' Z'').toSheafOfModules) =
      (modulePullbackCompIso B S hS f f').inv.app (conormalModule B S hS X'' Z'') ≫
        ((modulePullback B S hS f).map
            (conormalPullbackComparison B S hS Z' Z'' g' f' hsq') ≫
          (conormalPullbackCompIso B S hS Z Z' g f hsq).hom.app
            ((modulePullback B S hS g').obj
              (definingIdealSheaf B S hS X'' Z'').toSheafOfModules)) :=
  (eq_whisker
      (rfl : conormalPullbackComparison B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'' =
        (conormalPullbackCompIso B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'').hom.app
          (definingIdealSheaf B S hS X'' Z'').toSheafOfModules) _).trans
    ((conormalPullbackCompIso_paste_app B S hS Z Z' Z'' g g' f f' hsq hsq' hsq''
        (definingIdealSheaf B S hS X'' Z'').toSheafOfModules).trans
      ((NatTrans.comp_app _ _ _).trans
        ((eq_whisker (paste_lead_app B S hS Z Z' Z'' f f') _).trans
          (whisker_eq _ (paste_lower_app B S hS g g' Z Z' Z'' f f' hsq hsq')))))

end Law

end AlgebraicGeometry.Space

end
