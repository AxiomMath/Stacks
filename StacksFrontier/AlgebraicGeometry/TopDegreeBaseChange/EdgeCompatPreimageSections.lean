module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedSectionsModelCrossing

/-!
# Derived sections over an inverse image, against the scheme model

`…TopDegreeBaseChange.derivedSectionsOverOpenHomologyIso` identifies the two models of derived
sections over an open of a scheme: it says that the degree-`n` term of the unbounded total right
derived functor of `Γ(U, -)` at `F[0]` is the classical `H^n(U, F|_U)`. The consumer of
that bridge — the computation of `Γ(V, γ⁺)` that conclusion (c) of [Stacks, Tag 0EX3] is reduced
to — does not meet it at `U`, though.
`…TopDegreeBaseChange.topDirectImageSectionsIsoDerivedSections` computes `Γ(V, H^d(Rf'_*(F'[0])))`
with the derived sections of `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections`
— the derived functor of sections over `f'⁻¹V` **read over `Γ(V, 𝒪_{Y'})`**, not over
`Γ(X', f'⁻¹V)`.

This file reads the bridge across `f`: the same identification with the scalars restricted along
`Γ(V, 𝒪_Y) ⟶ Γ(f⁻¹V, 𝒪_X)`.

## Main definitions

* `…TopDegreeBaseChange.preimageSectionsRightDerivedIso`: restriction of scalars commutes with
  deriving sections over the inverse image.
* `…TopDegreeBaseChange.derivedPreimageSectionsRightDerivedIso`: the unbounded model of derived
  sections over an inverse image computes the classical right derived functor.
* `…TopDegreeBaseChange.derivedPreimageSectionsHomologyIso`: **the bridge, read across `f`.**

## Implementation notes

*Nothing is re-derived.* `Stacks.Cohomology.DerivedSectionsLeray.preimageSections` is by
definition sections over `f⁻¹V` followed by restriction of scalars, so the comparison of the two
classical right derived functors is `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` — an
exact functor commutes with right derived functors — at the **identity**, and the crossing of the
unbounded model with the classical one is
`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso`, exactly as
`derivedSectionsOverOpenRightDerivedIso` does it over an open. The scheme-model half is then
`sectionsOnRightDerivedRestrictIso` unchanged.

*The four instance arguments of `rightDerivedCompIso` are supplied positionally, and that is
forced.* `CategoryTheory.Functor.Additive` carries the `Preadditive` structures of its source and
target as instance arguments, and at this application they are the ones `rightDerivedCompIso`
derives from its `Abelian` binders, whereas every additivity instance in the tree for these three
functors — `Stacks.Cohomology.DerivedSectionsLeray.preimageSections_additive` among them — is
stated at the `Preadditive` instances of `SheafOfModules` and `ModuleCat` directly. Instance search
does not cross between the two, and neither does a local `haveI` carrying the library instance:
the goal it is asked to close is a different term. Supplying the three additivity instances in
**argument** position as `{ map_add := rfl }` — which holds at any `Preadditive` structure for
these functors, each being the identity on underlying maps — closes it at whatever instances the
application demands. This is the same kind of crossing
`StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedSectionsModelCrossing` records
for `Scheme.Opens.toScheme`, one level further in.

*No `@[stacks …]` attribute is placed.* What is here is dictionary between two spellings of the
same derived functor; the covering sets of [Stacks, Tag 0EX3] and [Stacks, Tag 01XK] are discussed
in `StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree` and
`StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineOpenSectionsCohomology`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray
  (derivedPreimageSections derivedPreimageSectionsUnit preimageSections sectionsOverOpen)
open Stacks.Cohomology.ModuleComparison (rightDerivedCompIso)

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)

/-- **Restriction of scalars commutes with deriving sections over an inverse image.** Sections
over `f⁻¹V` with scalars restricted along `Γ(V, 𝒪_Y) ⟶ Γ(f⁻¹V, 𝒪_X)` is by definition the functor
whose right derived functor is the one `derivedPreimageSections` derives, and restriction of
scalars is exact, so deriving and then restricting agrees with deriving the composite. -/
def preimageSectionsRightDerivedIso (n : ℕ) :
    (sectionsOverOpen X.toRingedSpace
          ((opensMap f.toLRSHom.toShHom).obj V)).rightDerived n ⋙
        ModuleCat.restrictScalars
          ((structureSheafHom f.toLRSHom.toShHom).hom.app (op V)).hom ≅
      (preimageSections f.toLRSHom.toShHom V).rightDerived n :=
  @rightDerivedCompIso _ _ _ _ _ _ _ _ _ _
    (AlgebraicGeometry.sectionsOn X (f ⁻¹ᵁ V))
    (ModuleCat.restrictScalars (f.app V).hom)
    (preimageSections f.toLRSHom.toShHom V)
    { map_add := rfl } { map_add := rfl } { map_add := rfl } inferInstance (Iso.refl _) n

/-- **The unbounded model of derived sections over an inverse image computes the classical right
derived functor.** This is `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` at
`Stacks.Cohomology.DerivedSectionsLeray.preimageSections`, whose unbounded total right derived
functor together with its unit is `derivedPreimageSections`, read at `F`.

*Why that crossing and not `Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso`.* The two
inhabit the same object-level statement and are built by different routes — the latter from a
chosen injective resolution of `F`, the former from the extended chosen resolution through
`Stacks.DerivedIndexing.resH` — and nothing in the tree relates them. The difference that matters
is that only the one used here is a component of a **natural** isomorphism and only it is pinned
down: `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app` identifies it
with `CategoryTheory.Functor.boundedDerivedIso` at the single complex, which is what relates this
reading of the classical right derived functor to the one
`…TopDegreeBaseChange.homologyFunctorDerivedPushforwardIso` carries. The other has no equational
lemma of any kind, so a consumer holding it can prove nothing about it. -/
def derivedPreimageSectionsRightDerivedIso (F : X.Modules) (n : ℕ) :
    (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) (n : ℤ)).obj
        ((derivedPreimageSections f.toLRSHom.toShHom V).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)) ≅
      ((preimageSections f.toLRSHom.toShHom V).rightDerived n).obj F :=
  (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (preimageSections f.toLRSHom.toShHom V) (derivedPreimageSections f.toLRSHom.toShHom V)
    (derivedPreimageSectionsUnit f.toLRSHom.toShHom V)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective _) n).app F

/-- **The bridge of `…TopDegreeBaseChange.derivedSectionsOverOpenHomologyIso`, read across `f`.**
For a morphism of schemes `f : X ⟶ Y`, an open `V ⊆ Y`, a sheaf of `𝒪_X`-modules `F` and a
degree `n`, the degree-`n` term of the unbounded total right derived functor of `Γ(f⁻¹V, -)` —
in the spelling `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections`, over
`Γ(V, 𝒪_Y)` — at `F` placed in degree `0` is the degree-`n` cohomology of the restriction of `F`
to the open subscheme `f⁻¹V`:

> `H^n(RΓ(f⁻¹V, F[0])) ≅ H^n(f⁻¹V, F|_{f⁻¹V})`,

the right-hand side read over `Γ(V, 𝒪_Y)` by restriction of scalars along
`Γ(V, 𝒪_Y) ⟶ Γ(f⁻¹V, 𝒪_X)` and then along `(Scheme.Opens.topIso _).inv`. There is no hypothesis
on `X`, on `Y`, on `V` or on `F`. -/
def derivedPreimageSectionsHomologyIso (F : X.Modules) (n : ℕ) :
    (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) (n : ℤ)).obj
        ((derivedPreimageSections f.toLRSHom.toShHom V).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F)) ≅
      (ModuleCat.restrictScalars
          ((structureSheafHom f.toLRSHom.toShHom).hom.app (op V)).hom).obj
        ((ModuleCat.restrictScalars (Scheme.Opens.topIso (f ⁻¹ᵁ V)).inv.hom).obj
          (((Stacks.Cohomology.AffineBase.moduleGlobalSections
            (f ⁻¹ᵁ V).toScheme).rightDerived n).obj
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F))) :=
  derivedPreimageSectionsRightDerivedIso f V F n ≪≫
    (preimageSectionsRightDerivedIso f V n).symm.app F ≪≫
    (ModuleCat.restrictScalars
        ((structureSheafHom f.toLRSHom.toShHom).hom.app (op V)).hom).mapIso
      ((sectionsOnRightDerivedRestrictIso X (f ⁻¹ᵁ V) n).app F)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
