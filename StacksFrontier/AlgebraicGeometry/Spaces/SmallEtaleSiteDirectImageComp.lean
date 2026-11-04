module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateTransport

/-!
# The composition comparison for the direct image that the base change map consumes

The base change map of **Stacks 0736** for a square of algebraic spaces,
`AlgebraicGeometry.Space.BaseChangeDiagram.baseChangeMap`, is built from the direct image of
`𝒪`-modules in the shape `Stacks.Sheaves.RingedToposModules.pushforwardModules` of the modules
development, applied to the morphism of small étale ringed topoi of **Stacks 03G8**.  That
functor is `AlgebraicGeometry.Space.ringedDirectImage` below.  It is isomorphic, but not equal,
to the geometric direct image `AlgebraicGeometry.Space.modulePushforward` carrying the
comparison `f_* ∘ g_* ≅ (f ≫ g)_*` of **Stacks 03LU**, so the comparison has to be carried
across; this file does that and records the associativity coherence on the other side.

## Main definitions

* `AlgebraicGeometry.Space.ringedDirectImage`: the direct image of `𝒪`-modules in the shape the
  base change map consumes.
* `AlgebraicGeometry.Space.ringedDirectImageComp` and
  `AlgebraicGeometry.Space.ringedDirectImageComp'`: the comparison
  `f_* ∘ g_* ≅ (f ≫ g)_*` of **Stacks 03LU** for it, with the composite written out and with
  the composite carried as a named morphism together with an equation naming it.

## Main results

* `AlgebraicGeometry.Space.ringedDirectImageComp_assoc_app`: **the associativity pentagon**.  It
  is `AlgebraicGeometry.Space.pushforwardModulesCompAt_assoc` conjugated by
  `AlgebraicGeometry.RingedToposHom.pushforwardModulesIso`.
* `AlgebraicGeometry.Space.ringedDirectImageComp_def` and
  `AlgebraicGeometry.Space.ringedDirectImageComp'_def`: the two comparisons as rewrite rules.

## Implementation notes

Everything that involves a transport along
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` is done at the level of
*isomorphisms of functors*, never at a component, for the reason recorded in the implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCompTransport.lean`:
`eqToHom` is `Eq.mpr`-based, so projecting such a transport to a morphism asks the elaborator
to decide an equality of functors between categories of sheaves of modules, which unfolds
`AlgebraicGeometry.Space.modulePushforward` and does not terminate.  The associativity pentagon
is therefore *not* obtained from `AlgebraicGeometry.Space.modulePushforwardCompIso_assoc` but
from the pentagon one level down, `pushforwardModulesCompAt_assoc`, where no transport appears;
`CategoryTheory.Functor.compConj_cocycle_app` is the conjugation that carries it over.

*Why the pentagon is rewritten with `ringedDirectImageComp_def` before the conjugation is
applied.*  Checking `AlgebraicGeometry.Space.ringedDirectImageComp` against the
`CategoryTheory.Functor.compConj` it unfolds to is a defeq between two spellings of the
category of `𝒪`-modules — `Modules` over the small étale ringed site, and sheaves of modules
over the structure ring sheaf of the small étale ringed topos — and the kernel does not finish
it inside an equation between composites of morphisms.  Rewriting with the definition first
keeps that check at the size of an isomorphism of functors, where it does finish.  The same
check inside the named-composite form of the pentagon does *not* finish by any of the routes
tried, so that form is not stated here;  a caller needing it at concrete morphisms can obtain
it from `ringedDirectImageComp'_rfl` and the pentagon below.

The only transports surviving in the statements below are of the form
`eqToIso (congrArg ringedDirectImage e)` for an equality `e` of morphisms of algebraic spaces.
These are harmless: the two functors are one function applied to two equal arguments, so
projecting the transport decides nothing about the functor.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open Stacks.Sheaves.RingedToposModules (pushforwardModules)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The direct image of `𝒪`-modules along a morphism of algebraic spaces, in the shape the base
change map of **Stacks 0736** consumes: the direct image of **Stacks 03D6**, part (1) of the
modules development, applied to the morphism of small étale ringed topoi of **Stacks 03G8**. -/
abbrev ringedDirectImage {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :=
  pushforwardModules (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom

/-- The comparison of `AlgebraicGeometry.Space.ringedDirectImage` with the direct image built
from the two-field morphism of ringed topoi, which is the functor the composition comparison
`AlgebraicGeometry.Space.pushforwardModulesCompAt` is stated for. -/
abbrev ringedDirectImageIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    ringedDirectImage f ≅ (smallEtaleRingedToposHom B S hS f).pushforwardModules :=
  (smallEtaleRingedToposHom B S hS f).pushforwardModulesIso

variable {T X Y Z : AlgebraicSpaces B S hS}

/-- **Stacks 03LU, the direct image of a composite**, for the direct image the base change map
of **Stacks 0736** consumes: `AlgebraicGeometry.Space.pushforwardModulesCompAt` conjugated by
`AlgebraicGeometry.Space.ringedDirectImageIso`. -/
def ringedDirectImageComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    ringedDirectImage f ⋙ ringedDirectImage g ≅ ringedDirectImage (f ≫ g) :=
  compConj (ringedDirectImageIso f) (ringedDirectImageIso g) (ringedDirectImageIso (f ≫ g))
    (pushforwardModulesCompAt B S hS f g)

/-- `AlgebraicGeometry.Space.ringedDirectImageComp` is its own definition, as a rewrite rule.
The pentagon below is `CategoryTheory.Functor.compConj_cocycle_app` at these functors, and the
kernel does not check the two spellings against one another inside the pentagon; rewriting with
this equation of isomorphisms first keeps that check at the size of an isomorphism. -/
theorem ringedDirectImageComp_def (f : X ⟶ Y) (g : Y ⟶ Z) :
    ringedDirectImageComp f g =
      compConj (ringedDirectImageIso f) (ringedDirectImageIso g) (ringedDirectImageIso (f ≫ g))
        (pushforwardModulesCompAt B S hS f g) := rfl

/-- The same comparison with the composite carried as a named morphism together with an
equation naming it.  This is the vocabulary the associativity pentagon is used in: in the other
one the pentagon would have to be transported along `CategoryTheory.Category.assoc` at every
use. -/
def ringedDirectImageComp' (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    ringedDirectImage f ⋙ ringedDirectImage g ≅ ringedDirectImage fg :=
  ringedDirectImageComp f g ≪≫
    eqToIso (congrArg (ringedDirectImage (B := B) (S := S) (hS := hS)) hfg.symm)

/-- `AlgebraicGeometry.Space.ringedDirectImageComp'` is its own definition, as a rewrite rule,
for the same reason as `AlgebraicGeometry.Space.ringedDirectImageComp_def`. -/
theorem ringedDirectImageComp'_def (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    ringedDirectImageComp' f g fg hfg =
      ringedDirectImageComp f g ≪≫
        eqToIso (congrArg (ringedDirectImage (B := B) (S := S) (hS := hS)) hfg.symm) := rfl

/-- At the composite `f ≫ g` itself, `AlgebraicGeometry.Space.ringedDirectImageComp'` is
`AlgebraicGeometry.Space.ringedDirectImageComp`. -/
@[simp]
theorem ringedDirectImageComp'_rfl (f : X ⟶ Y) (g : Y ⟶ Z) :
    ringedDirectImageComp' f g (f ≫ g) rfl = ringedDirectImageComp f g := by
  rw [ringedDirectImageComp'_def]
  simp

/-- **The associativity pentagon** for `AlgebraicGeometry.Space.ringedDirectImageComp`: it is the
pentagon `AlgebraicGeometry.Space.pushforwardModulesCompAt_assoc` at the morphisms of ringed
topoi of **Stacks 03G8**, conjugated by `AlgebraicGeometry.Space.ringedDirectImageIso`. -/
theorem ringedDirectImageComp_assoc_app (f : T ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (M : Modules.{u, u} B S hS T.1 T.2) :
    (ringedDirectImage h).map ((ringedDirectImageComp f g).hom.app M) ≫
        (ringedDirectImageComp (f ≫ g) h).hom.app M =
      (ringedDirectImageComp g h).hom.app ((ringedDirectImage f).obj M) ≫
        (ringedDirectImageComp f (g ≫ h)).hom.app M := by
  rw [ringedDirectImageComp_def f g, ringedDirectImageComp_def (f ≫ g) h,
    ringedDirectImageComp_def g h, ringedDirectImageComp_def f (g ≫ h)]
  exact compConj_cocycle_app (ringedDirectImageIso f) (ringedDirectImageIso g)
    (ringedDirectImageIso h) (ringedDirectImageIso (f ≫ g)) (ringedDirectImageIso (g ≫ h))
    (ringedDirectImageIso (f ≫ g ≫ h)) (pushforwardModulesCompAt B S hS f g)
    (pushforwardModulesCompAt B S hS g h) (pushforwardModulesCompAt B S hS (f ≫ g) h)
    (pushforwardModulesCompAt B S hS f (g ≫ h))
    (pushforwardModulesCompAt_assoc B S hS f g h) M

end AlgebraicGeometry.Space

end
