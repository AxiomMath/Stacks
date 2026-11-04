module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# Derived upper shriek

Let `f : X ⟶ Y` be a finite type separated morphism of schemes and let `Λ` be a ring.  The
derived upper shriek `Rf^!` is the right adjoint of the derived lower shriek `Rf_!` of
`Stacks.EtaleCohomology.derivedLowerShriek`.  This file records the two things about it that are
formal: the right adjoint of `Rf_! = R(fbar)_* ∘ Rj_!` is the composite
`Rf^! = Rj^{-1} ∘ R(fbar)^!` of the right adjoints of the two factors, and, for a cartesian
square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
the base change isomorphism `Rf^! ∘ Rg_* ≅ Rg'_* ∘ R(f')^!`, which follows from the base change
isomorphism `g^{-1} ∘ Rf_! ≅ Rf'_! ∘ (g')^{-1}` for derived lower shriek by uniqueness of right
adjoints.

## Main definitions

* `Stacks.EtaleCohomology.derivedLowerShriekAdjunctionOfFactors`: the adjunction
  `Rf_! ⊣ R(fbar)^! ⋙ Rj^{-1}`, exhibiting `Rf^!` as the composite of the right adjoints of
  the two factors of `Rf_!`.
* `Stacks.EtaleCohomology.derivedUpperShriekBaseChange`: the base change isomorphism
  `Rg_* ⋙ Rf^! ≅ R(f')^! ⋙ Rg'_*` of a cartesian square.

## Implementation notes

The right adjoints are explicit data here, never a choice extracted from an existence
statement.  Three inputs are hypotheses rather than constructions, and each is a Stacks tag this
repository does not yet have:

* that `Rf_!` has a right adjoint at all is Stacks Tag 0G2C, proved there by Brown
  representability for a torsion coefficient ring.  In `derivedUpperShriekBaseChange` the two
  upper shrieks therefore enter as functors `Uf`, `Uf'` together with adjunctions
  `Rf_! ⊣ Uf` and `Rf'_! ⊣ Uf'`;
* the derived base change `g^{-1} ⊣ Rg_*` on the bounded below derived categories.  The
  underived adjunction is free, being the sheaf adjunction of the continuous functor of sites
  `Stacks.EtaleCohomology.smallEtaleBaseChange`, but deriving it needs exactness of `g^{-1}`
  for module coefficients, which this repository does not have;
* the base change isomorphism for derived lower shriek, Stacks Tag 0F7L, which is the
  mathematical input to `derivedUpperShriekBaseChange`.  Its conclusion is about the *left*
  adjoints, so passing to the right adjoints is genuine work and is exactly the uniqueness of
  right adjoints invoked by the source.

The cartesian square itself is unused once Stacks Tag 0F7L is hypothesised, since that is the
only place where it enters the argument of the source; it is retained so that the statement is
the statement of the source.

Both `Rf_!` functors take an explicit compactification, as in
`Stacks.EtaleCohomology.derivedLowerShriek`: Stacks Tag 0F7I, the independence of the choice, is
not available, so a compactification of `f` and one of `f'` are separate arguments.

## References

* [Stacks Project, Tag 0GLE](https://stacks.math.columbia.edu/tag/0GLE)
* [Stacks Project, Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)
* [Stacks Project, Tag 0G2C](https://stacks.math.columbia.edu/tag/0G2C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

/-! ### The upper shriek of a compactification -/

/-- The derived lower shriek `Rf_! = R(fbar)_* ∘ Rj_!` of a compactification `j` has right
adjoint the composite `Rj^{-1} ∘ R(fbar)^!` of right adjoints of its two factors, so that
`Rf^! = Ubar ⋙ Uj` for any such pair.  The hypothesis on `Ubar` is the only non-formal input,
and for `f` separated of finite type it is supplied by Stacks Tag 0G2C. -/
def derivedLowerShriekAdjunctionOfFactors {X Y : Scheme.{u}} {f : X ⟶ Y}
    (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ]
    {Uj : DerivedCategory.Plus (EtaleModules.{u, r} Λ j.space) ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ X)}
    (adjImmersion : etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion ⊣ Uj)
    {Ubar : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y) ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ j.space)}
    (adjToBase : etaleModuleDerivedDirectImage.{u, r} Λ j.toBase ⊣ Ubar) :
    derivedLowerShriek.{u, r} f j Λ ⊣ Ubar ⋙ Uj :=
  adjImmersion.comp adjToBase

/-! ### Base change -/

/-- **Stacks Project, Tag 0GLE.** Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of schemes, let `Λ` be a ring, and let `j`, `j'` be compactifications of
`f`, `f'`.  Let `Uf`, `Uf'` be right adjoints of `Rf_!`, `Rf'_!` and let `Pg`, `Pg'` be left
adjoints of `Rg_*`, `Rg'_*`.  Given the base change isomorphism
`Rf_! ⋙ Pg ≅ Pg' ⋙ Rf'_!` of Stacks Tag 0F7L for derived lower shriek, the derived upper
shrieks satisfy `Rf^! ∘ Rg_* ≅ Rg'_* ∘ R(f')^!`.

Both sides of the conclusion are right adjoint to `Rf_! ⋙ Pg`, so the isomorphism is the
uniqueness of right adjoints applied to the given base change isomorphism of the left
adjoints. -/
@[stacks 0GLE]
def derivedUpperShriekBaseChange {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) {f' : X' ⟶ Y'} {f : X ⟶ Y} (g : Y' ⟶ Y)
    (_sq : IsPullback g' f' f g)
    (j : CompactificationOf (Over.mk f)) (j' : CompactificationOf (Over.mk f'))
    (Λ : Type r) [Ring Λ]
    {Uf : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y) ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ X)}
    (adjF : derivedLowerShriek.{u, r} f j Λ ⊣ Uf)
    {Uf' : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y') ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ X')}
    (adjF' : derivedLowerShriek.{u, r} f' j' Λ ⊣ Uf')
    {Pg : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y) ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ Y')}
    (adjG : Pg ⊣ etaleModuleDerivedDirectImage.{u, r} Λ g)
    {Pg' : DerivedCategory.Plus (EtaleModules.{u, r} Λ X) ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ X')}
    (adjG' : Pg' ⊣ etaleModuleDerivedDirectImage.{u, r} Λ g')
    (baseChange : derivedLowerShriek.{u, r} f j Λ ⋙ Pg ≅
      Pg' ⋙ derivedLowerShriek.{u, r} f' j' Λ) :
    etaleModuleDerivedDirectImage.{u, r} Λ g ⋙ Uf ≅
      Uf' ⋙ etaleModuleDerivedDirectImage.{u, r} Λ g' :=
  (adjF.comp adjG).rightAdjointUniq ((adjG'.comp adjF').ofNatIsoLeft baseChange.symm)

end Stacks.EtaleCohomology

end
