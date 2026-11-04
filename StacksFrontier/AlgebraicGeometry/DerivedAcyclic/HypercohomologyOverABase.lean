module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSectionsOverABase
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence.HypercohomologySpectralSequence

/-!
# Hypercohomology of a scheme over a base ring, read through restriction of scalars

Let `X` be a scheme over a commutative ring `A`, with structure morphism
`f : X ⟶ Spec A`. Two derived global-sections functors on `D(𝒪_X)` are in play, and the
geometry produces results about both:

* the one carried by a `Stacks.Cohomology.FilteredComplex.CanonicalTruncationSpectralSequence`,
  `T.RΓ : D(𝒪_X) ⥤ D(Γ(X, 𝒪_X))`, which is what the hypercohomology spectral sequence of
  [Stacks, Tag 0BKK] abuts to, and which is linear only over the ring of global functions;
* `AlgebraicGeometry.derivedGlobalSectionsOver f : D(𝒪_X) ⥤ D(A)`, the `A`-linear one, which is
  what statements over the base ring — [Stacks, Tag 0G9P], [Stacks, Tag 0G9Z] — are phrased with.

Restriction of scalars along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)` is exact, so composing `T.RΓ` with
the functor it induces on derived categories gives a right derived functor of `A`-linear global
sections; uniqueness of right derived functors identifies it with
`derivedGlobalSectionsOver f`, and exactness again lets the identification be read on homology.
The outcome is `AlgebraicGeometry.baseHypercohomologyIso`: the hypercohomology module of the
truncation datum, regarded as an `A`-module, is the cohomology of `A`-linear derived global
sections.

This is the same assembly as `AlgebraicGeometry.groupDerivedSections` and
`AlgebraicGeometry.groupHypercohomologyIso`, which carry it out for the forgetful functor to
abelian groups instead of for restriction of scalars.

## Main definitions

* `AlgebraicGeometry.baseSections`: `A`-linear global sections of `𝒪_X`-modules.
* `AlgebraicGeometry.baseDerivedSections`: a derived global-sections functor read over `A`, and
  `AlgebraicGeometry.baseDerivedSectionsUnit` its comparison from underived sections.

## Main results

* `AlgebraicGeometry.baseDerivedSections_isRightDerivedFunctor`: the composite really is the
  right derived functor of `A`-linear global sections.
* `AlgebraicGeometry.baseDerivedSectionsIso`: it is therefore
  `AlgebraicGeometry.derivedGlobalSectionsOver f`.
* `AlgebraicGeometry.baseHypercohomologyIso`: **the hypercohomology module of the truncation
  datum, over `A`, is the cohomology of `A`-linear derived global sections.**

## Implementation notes

`AlgebraicGeometry.globalSectionsOver`, the `A`-linear global sections of
`StacksFrontier.AlgebraicGeometry.DerivedGlobalSections`, is phrased with `X.Modules`, the scheme
API's alias for `SheafOfModules X.ringCatSheaf`, whereas the truncation datum is phrased with
`SheafOfModules (structureSheafRing X.toRingedSpace)`. The two are definitionally equal but carry
separately declared instances, and instance search does not cross between them: a goal mixing the
two spellings — `DerivedCategory.Qh.IsLocalization` with `Qh` taken at one and the
quasi-isomorphisms at the other — has no solution even though it is true. Two consequences shape
this file.

First, `globalSectionsOver` is declared under binders
`[HasDerivedCategory.{w₁} X.Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} A)]`, which mention
`X` and `A` and are therefore included in its signature even though its body does not use them.
So `globalSectionsOver f` carries two universe metavariables and two pending instance goals, and
`(globalSectionsOver f).Additive` is *not* synthesizable while those are open — which is exactly
what `Functor.mapHomotopyCategoryCompIso` asks for when the comparison below is assembled, even
though `example : (globalSectionsOver f).Additive := inferInstance` succeeds on its own. Hence
`baseSections`, which is the same functor written in the truncation datum's spelling and with no
derived category in its signature.

Second, the identification with `derivedGlobalSectionsOver f` is obtained by comparing
`baseDerivedSections` with the *total* right derived functor of `homotopyBaseSections f`, which
is a comparison of two functors in one spelling, so every instance it needs is synthesizable;
`derivedGlobalSectionsOver f` is then reached by a single type ascription, which is a
definitional unfolding and not an instance search.

## References

* [Stacks Project, Tag 0G9P](https://stacks.math.columbia.edu/tag/0G9P)
* [Stacks Project, Tag 0BKK](https://stacks.math.columbia.edu/tag/0BKK)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.FilteredComplex

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- **`A`-linear global sections of a scheme over `A`**, in the spelling of the canonical
truncation datum: sections over `⊤` of a sheaf of `𝒪_X`-modules, regarded as an `A`-module by
restriction of scalars along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`. It is
`AlgebraicGeometry.globalSectionsOver f` by `rfl`. -/
abbrev baseSections : SheafOfModules.{u} (structureSheafRing X.toRingedSpace) ⥤
    ModuleCat.{u} A :=
  SheafOfModules.evaluation (structureSheafRing X.toRingedSpace) (op (⊤ : Opens X.carrier)) ⋙
    restrictScalarsOver f

/-- `A`-linear global sections read on the homotopy category of cochain complexes of
`𝒪_X`-modules, with values in `D(A)`: the functor both comparisons below are units of. -/
abbrev homotopyBaseSections :
    HomotopyCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (baseSections f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

variable (L : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ)
  (T : CanonicalTruncationSpectralSequence X.toRingedSpace L)

/-- A derived global-sections functor on `D(𝒪_X)`, read over the base ring `A`: the one carried
by the truncation datum, composed with the functor restriction of scalars induces on derived
categories. -/
abbrev baseDerivedSections :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u} A) :=
  T.RΓ ⋙ (restrictScalarsOver f).mapDerivedCategory

/-- The comparison from the complex of `A`-linear global sections to derived global sections over
`A`: the comparison `T.α` of the truncation datum, pushed through restriction of scalars. -/
def baseDerivedSectionsUnit :
    homotopyBaseSections f ⟶ DerivedCategory.Qh ⋙ baseDerivedSections f L T :=
  (Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso
          (F := SheafOfModules.evaluation (structureSheafRing X.toRingedSpace)
            (op (⊤ : Opens X.carrier)))
          (G := restrictScalarsOver f) (H := baseSections f) (Iso.refl _)
          (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        ((SheafOfModules.evaluation (structureSheafRing X.toRingedSpace)
          (op (⊤ : Opens X.carrier))).mapHomotopyCategory (ComplexShape.up ℤ))
        (restrictScalarsOver f).mapDerivedCategoryFactorsh.symm ≪≫
      (Functor.associator _ _ _).symm).hom ≫
    Functor.whiskerRight T.α (restrictScalarsOver f).mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

open Stacks.Injectives.KInjectiveResolution
  Stacks.Cohomology.HypercohomologyEdge.HomologyComparison in
/-- **Derived global sections over the base ring is the right derived functor of `A`-linear
global sections.** The unit is invertible at a K-injective complex because `T.α` is
([Stacks, Tag 070K]) and restriction of scalars carries that isomorphism along; the recognition
criterion of [Stacks, Tag 070K] then applies. -/
theorem baseDerivedSections_isRightDerivedFunctor :
    (baseDerivedSections f L T).IsRightDerivedFunctor (baseDerivedSectionsUnit f L T)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)) := by
  have : IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) := inferInstance
  refine isRightDerivedFunctor_of_isIso_app_quotient_isKInjective
    (exists_quasiIso_isKInjective_sheafOfModules (structureSheafRing X.toRingedSpace)) _ _ _
    (fun I hI => ?_)
  have := T.isRightDerived
  have := isIso_unit_app_of_isKInjective X.toRingedSpace T.RΓ T.α I hI
  dsimp only [baseDerivedSectionsUnit]
  simp only [NatTrans.comp_app, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  infer_instance

/-- **The derived global sections of the truncation datum, read over `A`, are the `A`-linear
derived global sections** `AlgebraicGeometry.derivedGlobalSectionsOver f`. Both are right derived
functors of `A`-linear global sections, and a right derived functor is unique up to a canonical
isomorphism. -/
def baseDerivedSectionsIso : baseDerivedSections f L T ≅ derivedGlobalSectionsOver f :=
  have := baseDerivedSections_isRightDerivedFunctor f L T
  Functor.rightDerivedUnique (baseDerivedSections f L T)
    ((homotopyBaseSections f).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)))
    (baseDerivedSectionsUnit f L T)
    ((homotopyBaseSections f).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ))

/-- **The hypercohomology module of the truncation datum, regarded as an `A`-module, is the
cohomology of `A`-linear derived global sections.** This is what identifies the abutment of the
hypercohomology spectral sequence — a `Γ(X, 𝒪_X)`-module — with the `A`-module that statements
over the base ring, such as [Stacks, Tag 0G9Z], compute.

Restriction of scalars is exact, so it commutes with homology on the derived category; and the
two derived global-sections functors agree by `baseDerivedSectionsIso`. -/
def baseHypercohomologyIso
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) (n : ℤ) :
    (restrictScalarsOver f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) n).obj (T.RΓ.obj E)) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        ((derivedGlobalSectionsOver f).obj E) :=
  ((Stacks.Homology.derivedHomologyIso (restrictScalarsOver f) n).app (T.RΓ.obj E)).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).mapIso
      ((baseDerivedSectionsIso f L T).app E)

end AlgebraicGeometry

end
