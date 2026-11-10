module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.DirectImageRestrictUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.Homology.DerivedCategory.RightDerivedExactChange

/-!
# Cohomology with compact support commutes with restriction of coefficients

Let `φ : Λ₁ → Λ₂` be a homomorphism of rings, `f : X ⟶ Y` a morphism of schemes and
`j : X ⟶ X̄` a compactification of `X` over `Y`.  Writing `Rf_! = R(f̄)_* ∘ Rj_!` for that
factorization, as in [Stacks, Tag 0F7H], the square
```
D(X_étale, Λ₂) --Rf_!--> D(Y_étale, Λ₂)
|                         |
res_φ                     res_φ
|                         |
D(X_étale, Λ₁) --Rf_!--> D(Y_étale, Λ₁)
```
commutes.

**This is the first of the two diagrams asserted in [Stacks, Remark 0GL6]**, registered under
the tag with a which-part note saying so.  The second one, that `Rf_!` commutes with
`- ⊗^L_{Λ₁} Λ₂`, is
`Stacks.EtaleCohomology.isIso_derivedLowerShriekUnboundedExtendScalarsMap_of_torsion`, proved
from the proper base change theorem; see the implementation notes.  Nothing in this file depends
on it.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnboundedRestrictScalarsIso`: the square
  for the unbounded derived direct image `Rf_*`.
* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroRestrictScalarsIso` and
  `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroUnboundedRestrictScalarsIso`: the
  square for extension by zero `j_!`, underived and derived.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedRestrictScalarsIso`: **the first diagram of
  [Stacks, Remark 0GL6]**, the two squares composed.

## Implementation notes

Both squares are instances of `Stacks.DerivedSquare.rightDerivedExactChangeIso`: restriction of
coefficients is exact, so a square of underived functors commuting up to isomorphism gives a
square of unbounded right derived functors commuting up to isomorphism, as soon as the unit of
the lower right derived functor is invertible at the restriction of every K-injective complex.
What that hypothesis costs is completely different in the two cases, and the asymmetry is the
shape of the source's own proof.

* For `Rf_*` it is the whole content of the tag:
  `Stacks.EtaleCohomology.isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_restrictScalars`,
  which is [Stacks, Tag 0D6J] applied at both coefficient rings.  The underived square is an
  equality, direct image and restriction of coefficients being precomposition and
  postcomposition of the underlying presheaf.
* For `j_!` the hypothesis is free -- `j_!` is exact, so
  `Stacks.DerivedSquare.isIso_rightDerivedUnit_app_of_exact` gives invertibility of its
  derivation unit at *every* complex, not only at the restricted K-injective ones.  It is the
  *underived* square that costs something here: `j_!` is a left Kan extension followed by
  sheafification, and neither commutes with a change of coefficient category for free.  That
  comparison is `Stacks.EtaleCohomology.coefficientPullbackTwoSquare`, already in the tree for
  the proper base change development, and its two hypotheses hold for restriction of
  coefficients for one reason: restriction of scalars is a *left* adjoint
  (`ModuleCat.restrictCoextendScalarsAdj`), so it preserves all colimits -- hence left Kan
  extensions -- and it preserves sheafification.  This is the same observation that makes
  restriction of coefficients exact in
  `StacksFrontier/AlgebraicGeometry/EtaleCohomology/RestrictionOfScalars.lean`, used a third time.

  So "the diagram commutes for `j_!` by inspection", as the source puts it, is accurate about
  the mathematics and inverted about the formalization effort: the derived step is free and the
  underived one is not.

The compactification is explicit data, as it is in
`Stacks.EtaleCohomology.derivedLowerShriekUnbounded` and as the source's own phrasing ("writing
`Rf_! = Rf̄_* ∘ j_!` for a factorization as in Section 0F7H") licenses.  [Stacks, Tag 0F7I],
that different compactifications give canonically isomorphic functors, is not needed for a
statement about one fixed factorization.

*The second diagram.*  Its horizontal functor is
`Stacks.EtaleCohomology.etaleModuleDerivedExtendScalars`, left adjoint to restriction of
coefficients, and its comparison map `Rf_!(E) ⊗^L_{Λ₁} Λ₂ ⟶ Rf_!(E ⊗^L_{Λ₁} Λ₂)` is the mate of
the first diagram (`Stacks.EtaleCohomology.derivedLowerShriekUnboundedExtendScalarsMap`).
`Stacks.EtaleCohomology.isIso_derivedLowerShriekUnboundedExtendScalarsMap` proves it invertible
for `Λ₁` torsion and `Y` quasi-compact.  The `Rj_!` half is formal.  The `R(f̄)_*` half is the
projection formula against the constant sheaf `Λ̲₂` (the special case of [Stacks, Tag 0GL5] that
the remark uses), obtained by dévissage from `Λ₁` itself ([Stacks, Tag 09PB]); the dévissage needs
`R(f̄)_*` to commute with direct sums, hence the finite cohomological dimension of `f̄_*` on
torsion sheaves, `exists_isZero_rightDerived_etaleModuleDirectImage_of_isProper_of_fiberDim`.
That finite cohomological dimension comes from the proper base change theorem
([Stacks, Tag 095T]) and the cohomology of proper curves ([Stacks, Tag 0A53]); the second diagram
is `Stacks.EtaleCohomology.isIso_derivedLowerShriekUnboundedExtendScalarsMap_of_torsion`,
registered under the tag, and both diagrams together are
`Stacks.EtaleCohomology.derivedLowerShriekUnbounded_commutes_restrictScalars_and_extendScalars`.

## References

* [Stacks Project, Remark 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
* [Stacks Project, Tag 0F7H](https://stacks.math.columbia.edu/tag/0F7H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂)

/-! ### The square for the derived direct image -/

/-- **The unbounded derived direct image commutes with restriction of coefficients.**  Both
composites are right derived functors of one and the same underived functor -- the underived
square being an equality -- and the unit of the `Λ₁`-linear one is invertible at the restriction
of a K-injective complex of `Λ₂`-modules, which is [Stacks, Tag 0D6J] applied twice. -/
def etaleModuleDerivedDirectImageUnboundedRestrictScalarsIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₂ f ⋙
        etaleModuleDerivedRestrictScalars.{u, r} φ Y ≅
      etaleModuleDerivedRestrictScalars.{u, r} φ X ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ f :=
  Stacks.DerivedSquare.rightDerivedExactChangeIso
    (etaleModuleDirectImage.{u, r} Λ₂ f) (etaleModuleDirectImage.{u, r} Λ₁ f)
    (etaleModuleRestrictScalarsUniv.{u, r} φ X) (etaleModuleRestrictScalarsUniv.{u, r} φ Y)
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₂ f)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ₂ f)
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ f)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ₁ f)
    (eqToIso (etaleModuleDirectImage_comp_restrictScalars.{u, r} φ f))
    (isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_restrictScalars.{u, r} φ f)

/-! ### The square for extension by zero -/

section ExtensionByZero

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- Restriction of scalars preserves left Kan extensions along composition with an étale
morphism of schemes, being a left adjoint and so preserving all colimits. -/
instance etaleModuleRestrictScalars_preservesLeftKanExtensions :
    (ModuleCat.restrictScalars.{max (u + 1) r} φ).PreservesLeftKanExtensions
      (Scheme.Etale.smallEtaleCompose j).op :=
  fun _ => inferInstance

/-- Restriction of scalars preserves sheafification on the small étale site, being a left
adjoint.  The same observation makes restriction of coefficients exact. -/
instance etaleModuleRestrictScalars_preservesSheafification (X : Scheme.{u}) :
    X.smallEtaleTopology.PreservesSheafification
      (ModuleCat.restrictScalars.{max (u + 1) r} φ) :=
  Sheaf.preservesSheafification_of_adjunction _
    (ModuleCat.restrictCoextendScalarsAdj.{max (u + 1) r} φ)

/-- **Extension by zero commutes with restriction of coefficients.**  This is the comparison
`Stacks.EtaleCohomology.coefficientPullbackTwoSquare`, invertible because restriction of scalars
preserves both the left Kan extension and the sheafification out of which `j_!` is built. -/
def etaleModuleExtensionByZeroRestrictScalarsIso :
    etaleModuleExtensionByZero.{u, r} Λ₂ j ⋙ etaleModuleRestrictScalarsUniv.{u, r} φ X ≅
      etaleModuleRestrictScalarsUniv.{u, r} φ U ⋙ etaleModuleExtensionByZero.{u, r} Λ₁ j :=
  (asIso (coefficientPullbackTwoSquare (Scheme.Etale.smallEtaleCompose j)
    U.smallEtaleTopology X.smallEtaleTopology
    (ModuleCat.restrictScalars.{max (u + 1) r} φ) : _ ⋙ _ ⟶ _ ⋙ _)).symm

/-- **The unbounded derived extension by zero commutes with restriction of coefficients.**
`j_!` is exact, so the hypothesis on the derivation unit is automatic. -/
def etaleModuleDerivedExtensionByZeroUnboundedRestrictScalarsIso :
    etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ₂ j ⋙
        etaleModuleDerivedRestrictScalars.{u, r} φ X ≅
      etaleModuleDerivedRestrictScalars.{u, r} φ U ⋙
        etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ₁ j :=
  Stacks.DerivedSquare.rightDerivedExactChangeIso
    (etaleModuleExtensionByZero.{u, r} Λ₂ j) (etaleModuleExtensionByZero.{u, r} Λ₁ j)
    (etaleModuleRestrictScalarsUniv.{u, r} φ U) (etaleModuleRestrictScalarsUniv.{u, r} φ X)
    (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ₂ j)
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ₂ j)
    (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ₁ j)
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ₁ j)
    (etaleModuleExtensionByZeroRestrictScalarsIso.{u, r} φ j)
    (fun _ _ => Stacks.DerivedSquare.isIso_rightDerivedUnit_app_of_exact
      (etaleModuleExtensionByZero.{u, r} Λ₁ j)
      (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ₁ j)
      (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ₁ j) _)

end ExtensionByZero

/-! ### The first diagram of Remark 0GL6 -/

/-- **The first diagram of [Stacks, Remark 0GL6].**  Cohomology with compact support commutes
with restriction of coefficients: for a compactification `j` of `X` over `Y` and
`Rf_! = R(f̄)_* ∘ Rj_!` the resulting functor on unbounded derived categories, restricting the
coefficients along `φ : Λ₁ → Λ₂` before or after `Rf_!` gives canonically isomorphic functors.

The second diagram asserted in the same remark, that `Rf_!` commutes with
`- ⊗^L_{Λ₁} Λ₂`, is
`Stacks.EtaleCohomology.isIso_derivedLowerShriekUnboundedExtendScalarsMap_of_torsion`; see the
module docstring.

No separatedness, finite type or quasi-compactness hypothesis on `f` appears: the source needs
them only to produce the compactification, which is data here, so this is more general than the
source's phrasing.  Neither coefficient ring is assumed torsion, for the same reason — the
torsion hypothesis of the remark is consumed by Tag 0GL5, which only the second diagram uses. -/
@[stacks 0GL6 "the first of the two diagrams: Rf_! commutes with restriction of coefficients
res_φ along φ : Λ₁ → Λ₂, for a chosen compactification. The second diagram, that Rf_! commutes
with - ⊗^L_{Λ₁} Λ₂, is isIso_derivedLowerShriekUnboundedExtendScalarsMap_of_torsion."]
def derivedLowerShriekUnboundedRestrictScalarsIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) :
    derivedLowerShriekUnbounded.{u, r} f j Λ₂ ⋙
        etaleModuleDerivedRestrictScalars.{u, r} φ Y ≅
      etaleModuleDerivedRestrictScalars.{u, r} φ X ⋙ derivedLowerShriekUnbounded.{u, r} f j Λ₁ :=
  Functor.isoWhiskerLeft (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ₂ j.immersion)
      (etaleModuleDerivedDirectImageUnboundedRestrictScalarsIso.{u, r} φ j.toBase) ≪≫
    Functor.isoWhiskerRight
      (etaleModuleDerivedExtensionByZeroUnboundedRestrictScalarsIso.{u, r} φ j.immersion)
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ j.toBase)

end Stacks.EtaleCohomology

end
