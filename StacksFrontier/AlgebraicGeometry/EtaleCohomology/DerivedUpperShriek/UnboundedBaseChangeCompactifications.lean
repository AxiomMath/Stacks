module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.UnboundedBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.UpperShriekExistence
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Independence
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCompactification

/-!
# Base change for `Rf^!`, for arbitrary compactifications

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of quasi-compact and quasi-separated schemes with `f` separated and of
finite type, and let `Λ` be a torsion ring. For compactifications `j` of `f` and `j'` of `f'`,
the derived lower shrieks `Rf_!` and `Rf'_!` on `D(-_étale, Λ)` have right adjoints `Rf^!` and
`R(f')^!` ([Stacks, Tag 0G2C], `Stacks.EtaleCohomology.isLeftAdjoint_derivedLowerShriekUnbounded`).

This file reduces [Stacks, Tag 0GLE], `Rf^! ∘ Rg_* ≅ Rg'_* ∘ R(f')^!`, to its one input, the base
change isomorphism `g^{-1} ∘ Rf_! ≅ Rf'_! ∘ (g')^{-1}` of [Stacks, Tag 0F7L] for the
compactification `j` and its base change `j.baseChange sq`: that isomorphism is transported to
the compactification `j'` along the canonical comparison of [Stacks, Tag 0F7I]
(`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompactificationIso`), and then passed to the
right adjoints by `Stacks.EtaleCohomology.derivedUpperShriekUnboundedBaseChangeIsoOfIso`.

## Main definitions

* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChangeIsoOfCompactifications`: an
  isomorphism `g^{-1} ∘ Rf_! ≅ Rf'_! ∘ (g')^{-1}` for `j` and `j.baseChange sq`, carried to `j'`.
* `Stacks.EtaleCohomology.derivedUpperShriekUnboundedBaseChangeIsoOfCompactifications`: the
  resulting `Rf^! ∘ Rg_* ≅ Rg'_* ∘ R(f')^!` for the right adjoints of [Stacks, Tag 0G2C].
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : IsPullback g' f' f g)
  [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (Λ : Type) [CommRing Λ] (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)
  (j : CompactificationOf (Over.mk f)) (j' : CompactificationOf (Over.mk f'))

omit [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y'] in
include sq in
/-- The base change `f'` of the separated morphism of finite type `f` along `g` is separated and
of finite type. -/
theorem locallyOfFiniteType_and_quasiCompact_and_isSeparated_of_isPullback :
    LocallyOfFiniteType f' ∧ QuasiCompact f' ∧ IsSeparated f' :=
  ⟨MorphismProperty.of_isPullback sq inferInstance, MorphismProperty.of_isPullback sq inferInstance,
    MorphismProperty.of_isPullback sq inferInstance⟩

include hn hΛ in
/-- **An isomorphism `g^{-1} ∘ Rf_! ≅ Rf'_! ∘ (g')^{-1}` for the base change of `j`, carried to an
arbitrary compactification `j'` of `f'`** along the canonical comparison of
[Stacks, Tag 0F7I] between the derived lower shrieks of `j.baseChange sq` and of `j'`. -/
def derivedLowerShriekUnboundedBaseChangeIsoOfCompactifications
    (e : derivedLowerShriekUnbounded.{u, 0} f j Λ ⋙ etaleModuleDerivedInverseImage.{u, 0} Λ g ≅
      etaleModuleDerivedInverseImage.{u, 0} Λ g' ⋙
        derivedLowerShriekUnbounded.{u, 0} f' (j.baseChange sq) Λ) :
    derivedLowerShriekUnbounded.{u, 0} f j Λ ⋙ etaleModuleDerivedInverseImage.{u, 0} Λ g ≅
      etaleModuleDerivedInverseImage.{u, 0} Λ g' ⋙ derivedLowerShriekUnbounded.{u, 0} f' j' Λ :=
  have h := locallyOfFiniteType_and_quasiCompact_and_isSeparated_of_isPullback sq
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2
  e ≪≫ Functor.isoWhiskerLeft (etaleModuleDerivedInverseImage.{u, 0} Λ g')
    (derivedLowerShriekUnboundedCompactificationIso f' (j.baseChange sq) j' Λ ⟨n, hn, hΛ⟩)

/-- **The reduction of [Stacks, Tag 0GLE] to [Stacks, Tag 0F7L].** For compactifications `j` of
`f` and `j'` of `f'`, let `Rf^!` and `R(f')^!` be the right adjoints of the derived lower shrieks
([Stacks, Tag 0G2C]). An isomorphism `g^{-1} ∘ Rf_! ≅ Rf'_! ∘ (g')^{-1}` for `j` and its base
change gives `Rf^! ∘ Rg_* ≅ Rg'_* ∘ R(f')^!`, by [Stacks, Tag 0F7I] and uniqueness of right
adjoints. -/
def derivedUpperShriekUnboundedBaseChangeIsoOfCompactifications
    (e : derivedLowerShriekUnbounded.{u, 0} f j Λ ⋙ etaleModuleDerivedInverseImage.{u, 0} Λ g ≅
      etaleModuleDerivedInverseImage.{u, 0} Λ g' ⋙
        derivedLowerShriekUnbounded.{u, 0} f' (j.baseChange sq) Λ) :
    letI := DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded Λ n hn hΛ f j
    letI := DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded Λ n hn hΛ f' j'
    etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ g ⋙
        (derivedLowerShriekUnbounded.{u, 0} f j Λ).rightAdjoint ≅
      (derivedLowerShriekUnbounded.{u, 0} f' j' Λ).rightAdjoint ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ g' :=
  letI := DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded Λ n hn hΛ f j
  letI := DerivedUpperShriek.isLeftAdjoint_derivedLowerShriekUnbounded Λ n hn hΛ f' j'
  derivedUpperShriekUnboundedBaseChangeIsoOfIso g' g j j' Λ
    (derivedLowerShriekUnboundedBaseChangeIsoOfCompactifications sq Λ n hn hΛ j j' e)

end Stacks.EtaleCohomology

end
