module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.InverseImage

/-!
# Base change for the derived upper shriek on unbounded derived categories

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a square of schemes, let `Λ` be a commutative ring and let `j`, `j'` be compactifications of
`f` and `f'`, so that the derived lower shrieks `Rf_! = Rf̄_* ∘ j_!` and `Rf'_!` are functors
`D(X_étale, Λ) ⥤ D(Y_étale, Λ)` and `D(X'_étale, Λ) ⥤ D(Y'_étale, Λ)`
(`Stacks.EtaleCohomology.derivedLowerShriekUnbounded`). When both have right adjoints
`Rf^!` and `R(f')^!`, an isomorphism `g^{-1} ∘ Rf_! ≅ Rf'_! ∘ (g')^{-1}` gives an isomorphism

`Rf^! ∘ Rg_* ≅ Rg'_* ∘ R(f')^!`

by uniqueness of right adjoints: `Rf^! ∘ Rg_*` is right adjoint to `g^{-1} ∘ Rf_!` and
`Rg'_* ∘ R(f')^!` is right adjoint to `Rf'_! ∘ (g')^{-1}`, through the adjunctions
`g^{-1} ⊣ Rg_*` and `(g')^{-1} ⊣ Rg'_*` of
`Stacks.EtaleCohomology.etaleModuleDerivedInverseImageAdj`. This is the argument of the proof
of [Stacks, Tag 0GLE].

## Main definitions

* `Stacks.EtaleCohomology.derivedUpperShriekUnboundedBaseChangeIsoOfIso`: the isomorphism
  `Rg_* ⋙ Rf^! ≅ R(f')^! ⋙ Rg'_*` attached to an isomorphism
  `Rf_! ⋙ g^{-1} ≅ (g')^{-1} ⋙ Rf'_!`.

## Main results

* `Stacks.EtaleCohomology.derivedUpperShriekUnboundedBaseChangeIsoOfIso_hom_app`: the
  isomorphism is the conjugate of the given one: its components are determined by the
  adjunctions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable {X' X Y' Y : Scheme.{u}} {f' : X' ⟶ Y'} {f : X ⟶ Y} (g' : X' ⟶ X) (g : Y' ⟶ Y)
  (j : CompactificationOf (Over.mk f)) (j' : CompactificationOf (Over.mk f'))
  (Λ : Type r) [CommRing Λ]
  [(derivedLowerShriekUnbounded.{u, r} f j Λ).IsLeftAdjoint]
  [(derivedLowerShriekUnbounded.{u, r} f' j' Λ).IsLeftAdjoint]

/-- **The adjoint-uniqueness step of [Stacks, Tag 0GLE].** An isomorphism
`g^{-1} ∘ Rf_! ≅ Rf'_! ∘ (g')^{-1}` of functors `D(X_étale, Λ) ⥤ D(Y'_étale, Λ)` induces an
isomorphism `Rf^! ∘ Rg_* ≅ Rg'_* ∘ R(f')^!` of functors `D(Y'_étale, Λ) ⥤ D(X_étale, Λ)`, where
`Rf^!` and `R(f')^!` are the right adjoints of the two derived lower shrieks: both functors are
right adjoint to the two isomorphic left adjoints, through `g^{-1} ⊣ Rg_*` and
`(g')^{-1} ⊣ Rg'_*`. -/
def derivedUpperShriekUnboundedBaseChangeIsoOfIso
    (e : derivedLowerShriekUnbounded.{u, r} f j Λ ⋙ etaleModuleDerivedInverseImage.{u, r} Λ g ≅
      etaleModuleDerivedInverseImage.{u, r} Λ g' ⋙ derivedLowerShriekUnbounded.{u, r} f' j' Λ) :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g ⋙
        (derivedLowerShriekUnbounded.{u, r} f j Λ).rightAdjoint ≅
      (derivedLowerShriekUnbounded.{u, r} f' j' Λ).rightAdjoint ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g' :=
  conjugateIsoEquiv
    ((Adjunction.ofIsLeftAdjoint (derivedLowerShriekUnbounded.{u, r} f j Λ)).comp
      (etaleModuleDerivedInverseImageAdj.{u, r} Λ g))
    ((etaleModuleDerivedInverseImageAdj.{u, r} Λ g').comp
      (Adjunction.ofIsLeftAdjoint (derivedLowerShriekUnbounded.{u, r} f' j' Λ)))
    e.symm

/-- The components of `derivedUpperShriekUnboundedBaseChangeIsoOfIso` are those of the conjugate
of the given isomorphism of left adjoints. -/
theorem derivedUpperShriekUnboundedBaseChangeIsoOfIso_hom_app
    (e : derivedLowerShriekUnbounded.{u, r} f j Λ ⋙ etaleModuleDerivedInverseImage.{u, r} Λ g ≅
      etaleModuleDerivedInverseImage.{u, r} Λ g' ⋙ derivedLowerShriekUnbounded.{u, r} f' j' Λ)
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y')) :
    (derivedUpperShriekUnboundedBaseChangeIsoOfIso g' g j j' Λ e).hom.app K =
      (conjugateEquiv
        ((Adjunction.ofIsLeftAdjoint (derivedLowerShriekUnbounded.{u, r} f j Λ)).comp
          (etaleModuleDerivedInverseImageAdj.{u, r} Λ g))
        ((etaleModuleDerivedInverseImageAdj.{u, r} Λ g').comp
          (Adjunction.ofIsLeftAdjoint (derivedLowerShriekUnbounded.{u, r} f' j' Λ)))
        e.inv).app K :=
  rfl

end Stacks.EtaleCohomology

end
