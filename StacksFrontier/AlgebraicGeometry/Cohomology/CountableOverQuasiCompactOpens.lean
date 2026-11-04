module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Grp.CountableCohomology
public import StacksFrontier.AlgebraicGeometry.CompactOpenInduction.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.UnboundedDerivedSections
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace

/-!
# Countability of cohomology over the quasi-compact opens of a scheme

Let `X` be a quasi-separated scheme and let `M` be an object of `D(𝒪_X)`. If the cohomology
groups `H^i(V, M)` are countable for every affine open `V`, then they are countable for every
quasi-compact open `U`. Applied to `M = K ⊗^L E` this gives the cohomology half of
[Stacks, Tag 0CRP].

## Main definitions

* `Stacks.Cohomology.CountableSections.sectionsData`,
  `Stacks.Cohomology.CountableSections.derivedSectionsOpen`: the derived section functors of the
  ringed site of the opens of `X`, and `RΓ(U, -) : D(𝒪_X) ⥤ D(Ab)` for one open subset, as the
  right derived functor of degreewise sections over `U`.
* `Stacks.Cohomology.CountableSections.sectionsOpen`, `cohomologyOpen`,
  `cohomologySheafSectionsOpen`: `Γ(U, -)`, `H^i(U, -)` and `Γ(U, H^i(-))`.

## Main results

* `Stacks.Cohomology.CountableSections.hasCountableCohomology_sup`: the union step, countable
  cohomology over `U`, over `V` and over `U ∩ V` gives countable cohomology over `U ∪ V`.
* `Stacks.Cohomology.CountableSections.countable_cohomology_of_isCompact`: countable cohomology
  over every affine open gives countable cohomology over every quasi-compact open.
* `Stacks.Cohomology.CountableSections.hasCountableCohomology_of_cohomologySheafSections`:
  countable sections of the cohomology sheaves over an open where they compute the cohomology
  make the cohomology groups there countable.
* `Stacks.Cohomology.CountableSections.countable_cohomology_derivedTensor_of_isCompact`:
  **[Stacks, Tag 0CRP]** for `H^i(U, K ⊗^L E)`, countability over every quasi-compact open from
  countable sections of the cohomology sheaves over affine opens.

## Implementation notes

`derivedSectionsOpen` is the derived sections functor of the ringed site of the opens of `X`,
taken from
`Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedSectionsData`, which is the one the
Mayer--Vietoris triangle is stated for; its unit is taken at the cochain level, with
`HomologicalComplex.quasiIso` as the localizer. Its values are abelian groups rather than
`Γ(U, 𝒪_X)`-modules, which is all the statement needs: countability is a condition on the
underlying set of a cohomology group.

The derived categories are the standard ones, as they are in the construction of the
Mayer--Vietoris triangle and in the derived tensor product of a ringed space; the local instance
is given a high priority so that it is found at the scheme spelling of the category of
`𝒪_X`-modules as well.

## References

* [Stacks Project, Tag 0CRP](https://stacks.math.columbia.edu/tag/0CRP)
* [Stacks Project, Tag 08BX](https://stacks.math.columbia.edu/tag/08BX)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Pretriangulated
open AlgebraicGeometry.RingedSpace (ringedSite)
open Stacks.Cohomology.SpaceMayerVietoris (ModuleSheaves relativeUnboundedMayerVietoris)
open Stacks.Cohomology.MayerVietoris (sections)
open Stacks.MayerVietoris
open AddCommGrpCat (HasCountableCohomology)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Cohomology.CountableSections

/-- Sheaves of modules on the ringed site of a ringed space are a Grothendieck abelian
category at the universe of the space: all four universes coincide there, so
`SheafOfModules.isGrothendieckAbelian_of_univLE` applies. -/
local instance isGrothendieckAbelian_moduleSheaves (X : RingedSpace.{u, u}) :
    IsGrothendieckAbelian.{u} (ModuleSheaves X) :=
  SheafOfModules.isGrothendieckAbelian_of_univLE
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O)

/-- The system of derived section functors over the objects of the ringed site of `X`, with
their units and their right-derived-functor property: the `DerivedSectionsData` of
[Stacks, Tag 0F16] at the structure sheaf of `X`. -/
abbrev sectionsData (X : RingedSpace.{u, u}) :
    CanonicalMapOfComplexes.DerivedSectionsData.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O) :=
  CanonicalMapOfComplexes.derivedSectionsData.{u, u}
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X).O))

/-- **`RΓ(U, -) : D(𝒪_X) ⥤ D(Ab)`**, derived sections over an open subset of a ringed space:
the right derived functor of degreewise sections over `U`, with the module structure on the
sections forgotten. -/
abbrev derivedSectionsOpen (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    DerivedCategory (ModuleSheaves X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (sectionsData X).functor.obj (op U)

/-- **`Γ(U, -)`**, the sections of a sheaf of `𝒪_X`-modules over an open subset of a ringed
space, as an abelian group. -/
abbrev sectionsOpen (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    ModuleSheaves X ⥤ AddCommGrpCat.{u} :=
  sections.{u, u, u, u} (ringedSite X) U

/-- `H^i(U, M)`, the `i`-th cohomology group of `M` over the open subset `U`. -/
abbrev cohomologyOpen (X : RingedSpace.{u, u}) (U : Opens X.carrier) (i : ℤ) :
    DerivedCategory (ModuleSheaves X) ⥤ AddCommGrpCat.{u} :=
  derivedSectionsOpen X U ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i

/-- `Γ(U, H^i(M))`, the sections over `U` of the `i`-th cohomology sheaf of `M`. -/
abbrev cohomologySheafSectionsOpen (X : RingedSpace.{u, u}) (U : Opens X.carrier) (i : ℤ) :
    DerivedCategory (ModuleSheaves X) ⥤ AddCommGrpCat.{u} :=
  DerivedCategory.homologyFunctor (ModuleSheaves X) i ⋙ sectionsOpen X U

/-- **The union step.** If the cohomology of `M` over each of two open subsets and over their
intersection is countable, then so is its cohomology over their union. -/
theorem hasCountableCohomology_sup (X : RingedSpace.{u, u})
    (M : DerivedCategory (ModuleSheaves X)) (U V : Opens X.carrier)
    (hU : HasCountableCohomology ((derivedSectionsOpen X U).obj M))
    (hV : HasCountableCohomology ((derivedSectionsOpen X V).obj M))
    (hUV : HasCountableCohomology ((derivedSectionsOpen X (U ⊓ V)).obj M)) :
    HasCountableCohomology ((derivedSectionsOpen X (U ⊔ V)).obj M) := by
  have := (sectionsData X).isRightDerivedFunctor (U ⊔ V)
  have := (sectionsData X).isRightDerivedFunctor U
  have := (sectionsData X).isRightDerivedFunctor V
  have := (sectionsData X).isRightDerivedFunctor (U ⊓ V)
  obtain ⟨δ, hδ⟩ := relativeUnboundedMayerVietoris X U V (U ⊔ V) rfl
    (derivedSectionsOpen X (U ⊔ V)) (derivedSectionsOpen X U) (derivedSectionsOpen X V)
    (derivedSectionsOpen X (U ⊓ V))
    ((sectionsData X).unit (U ⊔ V)) ((sectionsData X).unit U)
    ((sectionsData X).unit V) ((sectionsData X).unit (U ⊓ V))
  exact HasCountableCohomology.obj₁ _ (hδ M) (hU.biprod hV) hUV

/-- **Countability over the quasi-compact opens of a quasi-separated scheme.** If the cohomology
of `M` over every affine open is countable, then it is countable over every quasi-compact
open. -/
theorem countable_cohomology_of_isCompact (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (M : DerivedCategory (ModuleSheaves X.toRingedSpace))
    (haffine : ∀ V : X.Opens, IsAffineOpen V →
      HasCountableCohomology ((derivedSectionsOpen X.toRingedSpace V).obj M))
    (U : X.Opens) (hU : IsCompact (U : Set X)) (i : ℤ) :
    Countable ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
      ((derivedSectionsOpen X.toRingedSpace U).obj M)) :=
  AlgebraicGeometry.CompactOpenInduction.of_isCompact
    (P := fun W : X.Opens =>
      HasCountableCohomology ((derivedSectionsOpen X.toRingedSpace W).obj M))
    haffine
    (fun W V _ _ hW hV hWV => hasCountableCohomology_sup X.toRingedSpace M W V hW hV hWV) U hU i

/-- **The affine case from the cohomology sheaves.** Over an open subset on which the
cohomology of `M` is computed by the sections of its cohomology sheaves, countability of those
sections makes the cohomology groups countable. -/
theorem hasCountableCohomology_of_cohomologySheafSections (X : RingedSpace.{u, u})
    (M : DerivedCategory (ModuleSheaves X)) (V : Opens X.carrier)
    (hsections : ∀ i : ℤ, Countable ((cohomologySheafSectionsOpen X V i).obj M))
    (hcomparison : ∀ i : ℤ,
      Nonempty ((cohomologyOpen X V i).obj M ≅ (cohomologySheafSectionsOpen X V i).obj M)) :
    HasCountableCohomology ((derivedSectionsOpen X V).obj M) := fun i => by
  obtain ⟨e⟩ := hcomparison i
  have := hsections i
  exact Function.Injective.countable
    ((AddCommGrpCat.mono_iff_injective e.hom).1 inferInstance)

/-- Let `X` be a quasi-separated scheme and let `K` and `E` be objects of `D(𝒪_X)`. Suppose the
cohomology sheaves of `K ⊗^L E` have countable sets of sections over affine opens, and that over
an affine open the cohomology of `K ⊗^L E` is computed by those sections. Then for every
quasi-compact open `U` the set `H^i(U, K ⊗^L E)` is countable. -/
@[stacks 0CRP "countability of H^i(U, K ⊗^L E) over every quasi-compact open, from countable \
sections of the cohomology sheaves of K ⊗^L E over affine opens. Two inputs are hypotheses \
rather than proved. First, that the cohomology of an affine open is the sections of the \
cohomology sheaves there: the library has this only at another model of the derived category. \
Second, that the cohomology sheaves of K ⊗^L E inherit countable sections over affine opens \
from those of K when E is perfect, which is why perfectness of E does not appear. The \
Ext^i(E|_U, K|_U) half is not covered: it needs the isomorphism K ⊗^L E^∨ ≅ RHom(E, K) for \
perfect E, which is unproved here"]
theorem countable_cohomology_derivedTensor_of_isCompact (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (K E : DerivedCategory (ModuleSheaves X.toRingedSpace))
    (hsections : ∀ (V : X.Opens), IsAffineOpen V → ∀ i : ℤ,
      Countable ((cohomologySheafSectionsOpen X.toRingedSpace V i).obj
        (((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor.obj K).obj E)))
    (hcomparison : ∀ (V : X.Opens), IsAffineOpen V → ∀ i : ℤ,
      Nonempty ((cohomologyOpen X.toRingedSpace V i).obj
          (((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor.obj K).obj E) ≅
        (cohomologySheafSectionsOpen X.toRingedSpace V i).obj
          (((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor.obj K).obj E)))
    (U : X.Opens) (hU : IsCompact (U : Set X)) (i : ℤ) :
    Countable ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
      ((derivedSectionsOpen X.toRingedSpace U).obj
        (((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor.obj K).obj E))) :=
  countable_cohomology_of_isCompact X _
    (fun V hV => hasCountableCohomology_of_cohomologySheafSections X.toRingedSpace _ V
      (hsections V hV) (hcomparison V hV)) U hU i

end Stacks.Cohomology.CountableSections

end
