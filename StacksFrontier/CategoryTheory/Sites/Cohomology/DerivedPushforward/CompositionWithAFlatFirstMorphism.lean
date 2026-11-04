module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Composition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.KInjectivePredicateBridge
public import StacksCore.Tactic.StacksAttribute

/-! # Composition of unbounded total direct images, for a flat first morphism

`AlgebraicGeometry.RingedToposHom.derivedPushforwardComparison_isIso` reduces Stacks 0D6E to
one hypothesis: that degreewise `f_*` preserves K-injectivity. This file discharges that
hypothesis when `f` is **flat**, and so proves Stacks 0D6E for a flat first morphism.

Flatness is taken in the form Stacks 03DJ gives it and that Stacks 093Y uses: exactness of
`f^* = O_C ⊗_{f⁻¹O_D} f⁻¹(-)`. Since `f^*` is a left adjoint it preserves colimits for free,
so the only hypothesis is `PreservesFiniteLimits (pullbackModules f)`.

## Main results

* `AlgebraicGeometry.RingedToposHom.isKInjective_mapHomologicalComplex_pushforwardModules`:
  Stacks 093Y for a morphism of ringed topoi in the sense of Stacks 01D3 — degreewise direct
  image along a flat morphism preserves K-injectivity.
* `AlgebraicGeometry.RingedToposHom.derivedPushforwardComparison_isIso_of_flat`: Stacks 0D6E
  with `f` flat.

## Implementation notes

The first result is the abstract Stacks 070G/093Y statement
`rightAdjoint_preserves_isKInjective` instantiated at
`u = f_*`, `v = f^*` and the adjunction
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules` (Stacks 03D7), with
`Stacks.Cohomology.isKInjectiveHomotopyCategory_iff_isKInjective` translating between that
  statement's
homotopy-category predicate and Mathlib's complex-level class.

**The source and target ringed topoi are taken in one universe triple here**, which the rest of
this development does not require. The reason is not mathematical:
`rightAdjoint_preserves_isKInjective` declares its two abelian categories over a single pair of
universe variables, so it cannot be cited for two ringed topoi with independent universes. A
one-line generalisation of that statement's universe variables would remove the restriction
from this file as well. The third ringed topos `Z` is unconstrained, since the hypothesis
discharged here concerns only `f`.

## References

* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.RingedToposHom

universe w w'' v u v'' u'' dX dY dZ

variable {X Y : RingedTopos.{v, u, w}} {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasSheafify Z.J AddCommGrpCat.{w''}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]

/-- **Stacks 093Y** for a morphism of ringed topoi in the sense of Stacks 01D3: if the pullback
`f^*` of sheaves of modules is left exact — i.e. `f` is flat, Stacks 03DJ, the right exactness
being automatic for a left adjoint — then degreewise direct image carries a K-injective complex
of `O_C`-modules to a K-injective complex of `O_D`-modules.

This is the abstract statement `rightAdjoint_preserves_isKInjective` at `u = f_*`, `v = f^*`
and the adjunction of Stacks 03D7, read through
`Stacks.Cohomology.isKInjectiveHomotopyCategory_iff_isKInjective`. -/
@[sga "4 V 4.9" "more general"]
theorem isKInjective_mapHomologicalComplex_pushforwardModules (f : RingedToposHom X Y)
    [PreservesFiniteLimits (f.toModulesHom.pullbackModules)] (I : CochainComplex X.Modules ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((pushforwardModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  have : PreservesColimitsOfSize.{0, 0} (f.toModulesHom.pullbackModules) :=
    (pullbackAdjPushforwardModules f).leftAdjoint_preservesColimits
  exact (Stacks.Cohomology.isKInjectiveHomotopyCategory_iff_isKInjective _).mp
    (rightAdjoint_preserves_isKInjective (pushforwardModules f) (f.toModulesHom.pullbackModules)
      (pullbackAdjPushforwardModules f) I
      ((Stacks.Cohomology.isKInjectiveHomotopyCategory_iff_isKInjective I).mpr hI))

/-- If `f` is flat, so that `f^*` is exact, then the canonical comparison
`R(g ∘ f)_* ⟶ Rf_* ⋙ Rg_*` is a natural isomorphism.

This is Stacks 0D6E for a flat first morphism. The source proves the statement with no flatness
hypothesis, by way of the unbounded derived pullbacks (Stacks 06YY, 07A6, 0D6D), which are not
available for `AlgebraicGeometry.RingedToposHom`; so this is the tag's content on a proper
subclass of its morphisms, and the tag is not attached here. It sits on the unconditional
statement `isIso_derivedPushforwardComparison_unconditional` in the namespace
`Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi`. -/
theorem derivedPushforwardComparison_isIso_of_flat
    [UnivLE.{u, w}] [UnivLE.{v, w}]
    [HasDerivedCategory.{dX} X.Modules] [HasDerivedCategory.{dY} Y.Modules]
    [HasDerivedCategory.{dZ} Z.Modules]
    (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
    [PreservesFiniteLimits (f.toModulesHom.pullbackModules)]
    (Rf : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules)
    (Rg : DerivedCategory Y.Modules ⥤ DerivedCategory Z.Modules)
    (Rh : DerivedCategory X.Modules ⥤ DerivedCategory Z.Modules)
    (αf : pushforwardToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ Rf)
    (αg : pushforwardToDerivedCategory g ⟶ DerivedCategory.Qh ⋙ Rg)
    (αh : pushforwardToDerivedCategory (g.comp f) ⟶ DerivedCategory.Qh ⋙ Rh)
    [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
    [Rg.IsRightDerivedFunctor αg (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))]
    [Rh.IsRightDerivedFunctor αh (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))] :
    IsIso (derivedPushforwardComparison f g Rf Rg Rh αf αg αh) :=
  derivedPushforwardComparison_isIso f g Rf Rg Rh αf αg αh
    (isKInjective_mapHomologicalComplex_pushforwardModules f)

end AlgebraicGeometry.RingedToposHom

end
