module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.AbelianSheafSpectralSequence
public import StacksFrontier.Topology.Sheaves.Modules.DeRhamExistence

/-!
# The Hodge filtration on de Rham cohomology

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a topological space, with
`𝒪_X` the structure sheaf of a ringed space `X`, and let `Ω^•_{𝒪_X/A}` be the relative de Rham
complex of `φ` (`AlgebraicGeometry.SheafOfModules.deRhamComplex`). Relative de Rham cohomology is
the hypercohomology of that complex, and the *Hodge filtration* on it is the filtration whose
`p`-th step is the image of the hypercohomology of the brutal truncation `σ^{≥p}Ω^•_{𝒪_X/A}`:

`F^p H^n_{dR} = Im (H^n(X, σ^{≥p}Ω^•_{𝒪_X/A}) ⟶ H^n(X, Ω^•_{𝒪_X/A}))`.

Two realizations of this are recorded, because de Rham cohomology is used in both forms. In the
first the de Rham complex is read in sheaves of `A`-modules and its hypercohomology is a module
over the ring `A(X)` of global sections of the base ring sheaf; the derived functor used is the
unbounded derived sections functor `RΓ(X, -)` of
`Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen`. In the second the de Rham
complex is read in sheaves of abelian groups, and its hypercohomology is the bounded-below one,
computed by the right derived functor of global sections of abelian sheaves. The de Rham complex
is concentrated in nonnegative degrees, so no information is lost by passing to the
bounded-below derived category, and the brutal truncation is concentrated in degrees `≥ p`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.baseRingedSpace`: the ringed space whose structure sheaf is
  the base ring sheaf `A`. Its sheaves of modules are the sheaves of `A`-modules in which the
  relative de Rham complex lives.
* `AlgebraicGeometry.SheafOfModules.derivedSectionsBase`: `RΓ(X, -)` for sheaves of
  `A`-modules, with values in the derived category of `A(X)`-modules.
* `AlgebraicGeometry.SheafOfModules.deRhamComplexInt`: the relative de Rham complex, extended by
  zero to negative degrees so that the brutal truncations of `ℤ`-indexed cochain complexes
  apply.
* `AlgebraicGeometry.SheafOfModules.deRhamCohomology`: relative de Rham cohomology in degree `n`,
  as an `A(X)`-module.
* `AlgebraicGeometry.SheafOfModules.hodgeFiltration`: **the Hodge filtration**, as a subobject of
  relative de Rham cohomology.
* `AlgebraicGeometry.SheafOfModules.deRhamAbelianComplex`,
  `AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexInt` and
  `AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus`: the relative de Rham complex read
  in abelian sheaves, the same complex extended by zero to negative degrees, and the result
  regarded as a bounded-below complex.
* `AlgebraicGeometry.SheafOfModules.deRhamAbelianTruncationPlus` and
  `AlgebraicGeometry.SheafOfModules.ιDeRhamAbelianTruncationPlus`: the brutal truncation of the
  de Rham complex of abelian sheaves, as a bounded-below complex, and its inclusion.
* `AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelian` and
  `AlgebraicGeometry.SheafOfModules.hodgeFiltrationAbelian`: relative de Rham cohomology and its
  Hodge filtration in the abelian-sheaf realization, in every degree.

## Implementation notes

Everything is stated for an arbitrary package `B` of the three algebras of Stacks Section 17.21
on the sheaf of relative differentials of `φ` and an arbitrary de Rham differential `D` on it,
exactly as `StacksFrontier.Topology.Sheaves.Modules.DeRham` is; the canonical choices are
`AlgebraicGeometry.SheafOfModules.differentialAlgebras` and
`AlgebraicGeometry.SheafOfModules.deRhamDifferential`, which by
`AlgebraicGeometry.SheafOfModules.deRhamDifferential_unique` is the only de Rham differential, so
nothing below depends on the choice.

The ringed space `baseRingedSpace` is what makes the first realization available: the derived
sections functor of `LerayForDerivedSections` is stated for sheaves of modules over the structure
sheaf of a ringed space, and the de Rham complex is a complex of sheaves of `A`-modules, so `A`
has to be presented as the structure sheaf of a ringed space with the same underlying space. The
identification `structureSheafRing (baseRingedSpace A) = underlyingRingSheaf A` holds by
definition, which is why `derivedSectionsBase` can be ascribed the type it has.

Brutal truncation is Mathlib's `HomologicalComplex.stupidTrunc` along
`ComplexShape.embeddingUpIntGE p`, and its inclusion into the ambient complex is
`HomologicalComplex.ιStupidTrunc`; it is a monomorphism, so the truncations really do
form a decreasing filtration of the de Rham complex by subcomplexes.

## References

* [Stacks Project, Tag 0FM8](https://stacks.math.columbia.edu/tag/0FM8)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
* [Stacks Project, Tag 0118](https://stacks.math.columbia.edu/tag/0118)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray (derivedSectionsOverOpen)

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-- The ringed space whose underlying space is that of `X` and whose structure sheaf is the base
ring sheaf `A`. Sheaves of modules over its structure sheaf are the sheaves of `A`-modules in
which the relative de Rham complex of a morphism `A ⟶ 𝒪_X` lives. -/
def baseRingedSpace (A : TopCat.Sheaf CommRingCat.{u} X.carrier) : RingedSpace.{u, u} where
  carrier := X.carrier
  presheaf := A.obj
  IsSheaf := A.property

/-- `RΓ(X, -)` for sheaves of `A`-modules: the unbounded derived functor of global sections, with
values in the derived category of modules over the ring `A(X)` of global sections of `A`. This is
`Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen` of
`AlgebraicGeometry.SheafOfModules.baseRingedSpace` over the whole space. -/
abbrev derivedSectionsBase (A : TopCat.Sheaf CommRingCat.{u} X.carrier) :
    DerivedCategory (_root_.SheafOfModules.{u} (underlyingRingSheaf A)) ⥤
      DerivedCategory (ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤))) :=
  derivedSectionsOverOpen (baseRingedSpace A) ⊤

variable {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-! ### The Hodge filtration on de Rham cohomology of sheaves of modules -/

/-- The relative de Rham complex `⋀⁰ Ω → ⋀¹ Ω → ⋯`, extended by zero to negative degrees. The
brutal truncations of Stacks Section 12.14 are taken along embeddings of `ℤ`-indexed cochain
complexes, so the de Rham complex has to be read as such a complex first. -/
def deRhamComplexInt :
    CochainComplex (_root_.SheafOfModules.{u} (underlyingRingSheaf A)) ℤ :=
  (deRhamComplex B D).extend embeddingUpNat

/-- **Relative de Rham cohomology** `H^n_{dR}` in degree `n`, as a module over the ring of global
sections of the base ring sheaf: the `n`-th cohomology of the derived global sections of the
relative de Rham complex. -/
abbrev deRhamCohomology (n : ℤ) : ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤)) :=
  (DerivedCategory.homologyFunctor _ n).obj
    ((derivedSectionsBase A).obj (DerivedCategory.Q.obj (deRhamComplexInt B D)))

/-- **The Hodge filtration** on relative de Rham cohomology: the `p`-th step
`F^p H^n_{dR} = Im (H^n(X, σ^{≥p}Ω^•) ⟶ H^n_{dR})` is the image of the hypercohomology of the
brutal truncation `σ^{≥p}Ω^•` of the de Rham complex, under the map induced by the inclusion of
that truncation. -/
@[stacks 0FM8]
def hodgeFiltration (p n : ℤ) : Subobject (deRhamCohomology B D n) :=
  imageSubobject
    ((DerivedCategory.homologyFunctor _ n).map
      ((derivedSectionsBase A).map
        (DerivedCategory.Q.map
          (HomologicalComplex.ιStupidTrunc
            (deRhamComplexInt B D) (embeddingUpIntGE p)))))

/-! ### The Hodge filtration in the abelian-sheaf realization -/

/-- The relative de Rham complex read in sheaves of abelian groups, forgetting the module
structure on its terms. -/
abbrev deRhamAbelianComplex :
    CochainComplex (Stacks.Cohomology.Leray.AbelianSheaf X.carrier) ℕ :=
  ((_root_.SheafOfModules.toSheaf.{u, u, u, u}
    (underlyingRingSheaf A)).mapHomologicalComplex (ComplexShape.up ℕ)).obj (deRhamComplex B D)

/-- The relative de Rham complex of abelian sheaves, extended by zero to negative degrees. -/
abbrev deRhamAbelianComplexInt :
    CochainComplex (Stacks.Cohomology.Leray.AbelianSheaf X.carrier) ℤ :=
  (deRhamAbelianComplex B D).extend embeddingUpNat

/-- The relative de Rham complex of abelian sheaves as a **bounded-below** complex: it is
concentrated in nonnegative degrees, being extended by zero from a complex indexed by `ℕ`. -/
def deRhamAbelianComplexPlus :
    CochainComplex.Plus (Stacks.Cohomology.Leray.AbelianSheaf X.carrier) :=
  ⟨deRhamAbelianComplexInt B D, 0, by
    change CochainComplex.IsStrictlyGE ((deRhamAbelianComplex B D).extend embeddingUpNat) 0
    infer_instance⟩

/-- The brutal truncation `σ^{≥p}Ω^•` of the de Rham complex of abelian sheaves, as a
bounded-below complex: it is concentrated in degrees `≥ p`. -/
abbrev deRhamAbelianTruncationPlus (p : ℤ) :
    CochainComplex.Plus (Stacks.Cohomology.Leray.AbelianSheaf X.carrier) :=
  ⟨(deRhamAbelianComplexInt B D).stupidTrunc (embeddingUpIntGE p), p, inferInstance⟩

/-- The inclusion of the brutal truncation, as a morphism of bounded-below complexes of abelian
sheaves. -/
abbrev ιDeRhamAbelianTruncationPlus (p : ℤ) :
    deRhamAbelianTruncationPlus B D p ⟶ deRhamAbelianComplexPlus B D :=
  ⟨HomologicalComplex.ιStupidTrunc
    (deRhamAbelianComplexInt B D) (embeddingUpIntGE p)⟩

/-- **Relative de Rham cohomology in the abelian-sheaf realization**, in every degree: the `n`-th
cohomology of the bounded-below derived global sections of the de Rham complex of abelian
sheaves. -/
abbrev deRhamCohomologyAbelian (n : ℤ) : AddCommGrpCat.{u} :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).obj
    ((Stacks.Cohomology.Leray.sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.obj
      (DerivedCategory.Plus.Q.obj (deRhamAbelianComplexPlus B D)))

/-- **The Hodge filtration** on relative de Rham cohomology in the abelian-sheaf realization, in
every degree: the image of the hypercohomology of the brutal truncation `σ^{≥p}Ω^•` under the map
induced by its inclusion into the de Rham complex. -/
@[stacks 0FM8 "abelian-sheaf realization in every degree"]
def hodgeFiltrationAbelian (p n : ℤ) : Subobject (deRhamCohomologyAbelian B D n) :=
  imageSubobject
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
      ((Stacks.Cohomology.Leray.sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map (ιDeRhamAbelianTruncationPlus B D p))))

end AlgebraicGeometry.SheafOfModules

end
