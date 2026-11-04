module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsZariskiSite
public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedSectionsOverObject

/-!
# `RΓ` across `ε`, landing in the derived category of modules over the base ring

Let `S` be a scheme over a ring `A`, by `f : S ⟶ Spec A`, and let
`ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites of Stacks 070R/08H7.  The
clause of Stacks 0D6H on sections over an object, taken at `ε` and at the open `⊤` of `S`, reads

`RΓ(ε(⊤), -) ≅ RΓ(⊤, -) ∘ Rε_*`

with both sides valued in the derived category of modules over the *section ring* `𝒪_S(⊤)`
(`AlgebraicGeometry.SmallEtale.derivedModuleSectionsRestrictModuleIso`).  This file reads it over
the base ring `A` instead, by composing with
`AlgebraicGeometry.derivedGlobalSectionsOverEvaluationIso`, so that the right-hand side becomes
the `RΓ(S, -) : D(𝒪_S) ⥤ D(A)` that the affine comparisons of Stacks 08E7 and Stacks 06Z0 are
stated with.

That is the whole of comparison (ii) of the chain the site-level form of Stacks 0DII needs; see
the "What 0DII still owes" section of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/RelativeAbsolute.lean`.

## Main results

* `AlgebraicGeometry.SmallEtale.derivedModuleSectionsGlobalSectionsOverIso`: unbounded derived
  sections over `ε(⊤)` on the small étale site, read over the base ring, are the base-ring
  derived global sections of the unbounded derived direct image along `ε`.

## Implementation notes

**Two restrictions of scalars appear, and neither can be dropped.**  The inner one, on the étale
side, is the one `AlgebraicGeometry.SmallEtale.derivedModuleSectionsRestrictModuleIso` carries:
`AlgebraicGeometry.SmallEtale.structureMap` at an open `V` is
`(AlgebraicGeometry.Scheme.Opens.topIso V).inv` and not the identity, so `𝒪_S(V)` and `𝒪(ε(V))`
are isomorphic rings and not equal ones, and sections over `ε(V)` are `𝒪_S(V)`-modules only after
transport.  The outer one, applied to the derived category, is the passage from `𝒪_S(⊤)` to `A`
along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(S, 𝒪_S)`, which is what
`AlgebraicGeometry.globalSectionsOver` is built from.

*The model of the derived category.* `attribute [local instance 10000] HasDerivedCategory.standard`
fixes every derived category here at `CategoryTheory.HasDerivedCategory.standard`, which is the
universe `u + 1` on both sides of `ε` — see the module documentation of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDerivedSectionsOverObject.lean`
for why that is available, and the implementation notes of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean` for why the
priority has to be `10000`.

## References

* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 0D6I](https://stacks.math.columbia.edu/tag/0D6I)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.SmallEtale

universe u

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A] (f : S ⟶ Spec (.of A))

/-- **Derived sections over `ε(⊤)` on the small étale site, read over the base ring, are the
base-ring derived global sections of `Rε_*`.**  For a scheme `S` over a ring `A`,

`R(Γ(ε(⊤), -) ⊗ 𝒪_S(⊤) ⊗ A) ≅ RΓ(S, -) ∘ Rε_*`

as functors `D(S_étale, 𝒪) ⥤ D(A)` — precisely, the unbounded right derived functor of sections
over `ε(⊤)` with scalars restricted to `𝒪_S(⊤)`, followed by restriction of scalars to `A` on the
derived category, is `AlgebraicGeometry.derivedGlobalSectionsOver f` applied after
`AlgebraicGeometry.SmallEtale.derivedRestrictModule`.

This is the clause of Stacks 0D6H on sections over an object at `ε` and at the open `⊤`,
`AlgebraicGeometry.SmallEtale.derivedModuleSectionsRestrictModuleIso`, followed by
`AlgebraicGeometry.derivedGlobalSectionsOverEvaluationIso`, which identifies derived evaluation at
the final object of the small Zariski site of `S` over the base ring with `RΓ(S, -)`. -/
def derivedModuleSectionsGlobalSectionsOverIso :
    Stacks.DerivedFunctor.totalRightDerived
        (SheafOfModules.evaluation.{u} (structureSheaf B S hS)
              (op ((opensToSmallEtale B S hS).obj (⊤ : S.Opens))) ⋙
            ModuleCat.restrictScalars.{u}
              ((structureMap B S hS).hom.app (op (⊤ : S.Opens))).hom) ⋙
        (ModuleCat.restrictScalars.{u} (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom) :
          ModuleCat.{u} ↑(S.ringCatSheaf.obj.obj (op (⊤ : S.Opens))) ⥤
            ModuleCat.{u} A).mapDerivedCategory ≅
      derivedRestrictModule B S hS ⋙ derivedGlobalSectionsOver f :=
  Functor.isoWhiskerRight (derivedModuleSectionsRestrictModuleIso B S hS (⊤ : S.Opens)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (derivedGlobalSectionsOverEvaluationIso f)

end AlgebraicGeometry.SmallEtale

end
