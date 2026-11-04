module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KernelIdealSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProj

/-!
# The graded ideal cut out by a closed subspace of a relative Proj

Let `S` be a scheme, `X` an algebraic space over `S` and `𝒜` a quasi-coherent graded
`𝒪_X`-algebra — the relative Proj situation of Stacks 0849.  Let `π : P ⟶ X` be the relative
Proj of `𝒜` and let `i : Z ⟶ P` be a closed subspace.  Stacks 085L defines a graded ideal
`ℐ ⊆ 𝒜` as the kernel of the canonical map

`𝒜 ⟶ ⨁_{d ≥ 0} π_*((i_*𝒪_Z)(d))`

and asserts, for `π` quasi-compact, that `Z = Proj_X(𝒜/ℐ)`.

This file writes that ideal down.  The Serre twists `(·)(d)` on the relative Proj of an
algebraic space are not constructed in this repository, so they are carried as an explicit
datum, `AlgebraicGeometry.Space.ClosedSubspaceTwistSections`; everything else is a definition
with a real body.  In particular the canonical map is the composite the source names and not a
parameter: the twisted module `(i_*𝒪_Z)(d)` is `i_*𝒪_Z ⊗_{𝒪_P} 𝒪_P(d)` for the tensor product
of Stacks 01CA, the map `𝒪_P(d) ⟶ (i_*𝒪_Z)(d)` is the twist of the structure map
`𝒪_P ⟶ i_*𝒪_Z` of the closed immersion, and `ℐ_d` is the sectionwise kernel of the result.

The direct sum over `d ≥ 0` is not formed.  The canonical map is graded, so its kernel is the
degreewise kernel, and `ℐ` is therefore given degree by degree; this is the same object, and it
avoids a coproduct of sheaves of modules that would have to be compared with the direct sum.

## Main definitions

* `AlgebraicGeometry.Space.ClosedSubspaceTwistSections`: the carried datum — the twists
  `𝒪_P(d)` on the relative Proj, their quasi-coherence, and the homogeneous section maps
  `𝒜_d ⟶ π_*(𝒪_P(d))`.  This is the part of Stacks 01NR that the canonical map consumes.
* `AlgebraicGeometry.Space.closedSubspacePushforwardStructure`: the direct image `i_*𝒪_Z` of
  the structure sheaf of a closed subspace.
* `AlgebraicGeometry.Space.closedSubspacePushforwardUnit`: the structure map
  `𝒪_P ⟶ i_*𝒪_Z`.
* `AlgebraicGeometry.Space.twistedClosedSubspaceMap`: its twist
  `𝒪_P(d) ⟶ (i_*𝒪_Z)(d)`.
* `AlgebraicGeometry.Space.closedSubspaceSectionMap`: **the canonical map
  `𝒜_d ⟶ π_*((i_*𝒪_Z)(d))` of Stacks 085L.**
* `AlgebraicGeometry.Space.closedSubspaceGradedIdeal`: **the graded ideal `ℐ_d ⊆ 𝒜_d` of
  Stacks 085L**, as a submodule of the degree-`d` piece, and
  `AlgebraicGeometry.Space.closedSubspaceGradedIdealObj`: the same kernel as an object of the
  category of `𝒪_X`-modules.
* `AlgebraicGeometry.Space.ClosedSubspaceQuotientPresentation`: the remaining assertion of
  Stacks 085L, `Z = Proj_X(𝒜/ℐ)`, as hypothesis data.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_closedSubspaceGradedIdealObj`: **`ℐ_d` is
  quasi-coherent**, which is the third step of the source's proof.
* `AlgebraicGeometry.Space.closedSubspaceGradedIdeal_eq_ker` and
  `AlgebraicGeometry.Space.mem_closedSubspaceGradedIdeal`: the sections of `ℐ_d` over an object
  of the small étale site are exactly the sections of `𝒜_d` killed by the canonical map, so the
  ideal is the kernel of that map and nothing else.

## Implementation notes

**Why the twists are carried, and what exactly is carried.**  `(i_*𝒪_Z)(d)` cannot be written
without the twists `𝒪_P(d)` on the relative Proj.  Those are the subject of Stacks 01NR, which
this repository states but does not prove: `Stacks.AlgebraicGeometry.RelativeProjTwists.
TwistData` is a structure with no inhabitant, and Stacks 01NR is carried only in its uniqueness
clauses.  That statement is moreover for the relative Proj of a *scheme*, so even an inhabitant
of it would not twist modules on the relative Proj of an algebraic space.  Accordingly
`ClosedSubspaceTwistSections` carries, on the algebraic space `P`, exactly the two pieces of
data the canonical map consumes: the modules `𝒪_P(d)` with their quasi-coherence, and the
section maps `𝒜_d ⟶ π_*(𝒪_P(d))` of Stacks 01MP.  It carries no identification of those
modules with the twists on an étale chart, because the restriction of a module on `P` to the
chart-level relative Proj, matched against
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.chartData`, is not available here; so
the datum constrains the twists only through its own fields, and the two statements that use it
below are statements about that datum.  This is recorded again under *What is not proved*.

**The tensor unit is the structure sheaf on the nose.**  `(i_*𝒪_Z)(d)` is formed with the
monoidal structure `AlgebraicGeometry.Space.modulesMonoidalCategory` rather than with
`AlgebraicGeometry.Space.tensorModule`, because the canonical map needs the tensor product on
*morphisms* and not only on objects: the map `𝒪_P(d) ⟶ (i_*𝒪_Z)(d)` is
`MonoidalCategory.whiskerRight` of the structure map.  That is possible with no transport at all
because `AlgebraicGeometry.Space.modulesTensorUnit_eq` holds by `rfl`: the tensor unit *is*
`SheafOfModules.unit` of the structure sheaf, so the structure map of the closed immersion is
literally a morphism out of `𝟙_`, and the left unitor supplies `𝒪_P(d) ⟶ 𝒪_P ⊗ 𝒪_P(d)`.
Without that identity the whiskering would have to be conjugated by an isomorphism of unit
objects.

**The structure map of the closed immersion.**  `𝒪_P ⟶ i_*𝒪_Z` is
`SheafOfModules.unitToRestrictScalarsObjUnit` of `AlgebraicGeometry.Space.structureSharp`.  This
typechecks as a map into `(modulePushforward i).obj (SheafOfModules.unit _)` because
`AlgebraicGeometry.Space.modulePushforward` is the direct image followed by restriction of
scalars along the structure map, and the direct image of a unit module is the unit module of the
direct-image sheaf of rings — by `rfl`, which is what
`closedSubspacePushforwardStructure_eq_unit` records.  No hypothesis that `i` is a closed
immersion is needed to *write* the map; it is the structure map of an arbitrary morphism, and it
is the closed immersion that makes it surjective.

**Degreewise rather than summed.**  The source's map has the direct sum
`⨁_{d ≥ 0} π_*((i_*𝒪_Z)(d))` for target.  Sheaves of modules on the small étale site have
coproducts but no `⨁` instance, and the comparison of the coproduct with the objectwise direct
sum is a separate piece of work (`Stacks.sheafifyDirectSumIso`).  Since a graded map's kernel is
computed degreewise, nothing is lost by indexing the canonical map and the ideal by the degree,
and the degreewise form is what every consumer of `ℐ` uses.

## What is not proved

**The isomorphism `Z = Proj_X(𝒜/ℐ)` is not proved, and no part of it is.**  It is written down
as the hypothesis structure `ClosedSubspaceQuotientPresentation`, mirroring
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.GradedQuotientPresentation`, which carries the
scheme-level assertion of Stacks 0801 in exactly the same way and for the same reason.  Three
things block it.  The quotient `𝒜/ℐ` of a graded algebra of sheaves by a graded ideal is
constructed at the level of a scheme —
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.quotAlgebra`, for a graded ideal with
quasi-coherent pieces — but not at the level of an algebraic space.  The relative
Proj of an algebraic space is glued from *chart-level* graded algebras — the fields of
`AlgebraicGeometry.Space.RelativeProjGlueingData` are `Stacks.RelativeProj.Situation`s on the
presenting and relation schemes — so there is no operation taking a graded algebra on `X` to its
relative Proj, and `Proj_X(𝒜/ℐ)` cannot be formed even once the quotient exists; the
presentation structure therefore carries the space and its morphism to `P`.  And the final step
of the source's proof descends an isomorphism of closed subspaces from the étale charts, for
which the space-level counterpart of `AlgebraicGeometry.IsClosedImmersion.lift` — the lifting
property that drives the scheme case `Stacks.ClosedSubschemeProjQuotient.projQuotientIso` — does
not exist.

**Stacks 03M9 and Stacks 03M1(3) are hypotheses, not theorems.**  Quasi-coherence of `ℐ_d` needs
quasi-coherence of the target of the canonical map, which the source gets from Stacks 03M9 for
the quasi-compact separated morphism `π`, and closure of quasi-coherence under kernels, which is
Stacks 03M1(3).  Stacks 03M9 is carried in this repository only conditionally, and
`SheafOfModules.isClosedUnderKernels_isQuasicoherentOnSite` derives kernel closure from
cokernel closure, which is itself a hypothesis there.  Both are therefore arguments of
`isQuasicoherentOnSite_closedSubspaceGradedIdealObj`, and the `stacks` attribute on it names
them.  Separatedness of `π` — Stacks 084E,
`AlgebraicGeometry.Space.isSeparated_relativeProj` — is the input to Stacks 03M9 and so is
subsumed by carrying the latter; no quasi-compactness hypothesis appears for the same reason.

## References

* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 084E](https://stacks.math.columbia.edu/tag/084E)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

/-! ### The carried twists -/

/-- The twists on the relative Proj of an algebraic space, as far as the canonical map of
Stacks 085L consumes them: the modules `𝒪_P(d)` for `d ≥ 0`, their quasi-coherence, and the
homogeneous section maps `𝒜_d ⟶ π_*(𝒪_P(d))` of Stacks 01MP.

This is the datum Stacks 01NR would supply.  No `TwistData` is constructed in this repository,
and the one that is stated is for the relative Proj of a scheme; see the implementation notes
for what this carries and what it does not. -/
structure ClosedSubspaceTwistSections (s : RelativeProjSituation.{u, u})
    (P : AlgebraicSpaces s.site s.base s.containsBase) (π : P ⟶ s.space) where
  /-- The degree-`d` twist `𝒪_P(d)` on the relative Proj. -/
  twist (d : ℕ) : Modules.{u, u} s.site s.base s.containsBase P.1 P.2
  /-- Every twist is quasi-coherent. -/
  isQuasicoherent (d : ℕ) : (twist d).IsQuasicoherentOnSite
  /-- The homogeneous section map `𝒜_d ⟶ π_*(𝒪_P(d))` of Stacks 01MP. -/
  sectionMap (d : ℕ) : s.algebra.piece (d : ℤ) ⟶
    (modulePushforward s.site s.base s.containsBase π).obj (twist d)

attribute [instance] ClosedSubspaceTwistSections.isQuasicoherent

/-! ### The structure sheaf of a closed subspace, and its twists -/

section ClosedSubspace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {P Z : AlgebraicSpaces B S hS}

/-- The direct image `i_*𝒪_Z` of the structure sheaf of `Z` along a morphism `i : Z ⟶ P` of
algebraic spaces, as an `𝒪_P`-module. -/
def closedSubspacePushforwardStructure (i : Z ⟶ P) : Modules.{u, u} B S hS P.1 P.2 :=
  (modulePushforward B S hS i).obj (SheafOfModules.unit (structureRingSheaf B S hS Z))

/-- The direct image of the structure sheaf is the unit module of the direct-image sheaf of
rings, read through restriction of scalars along the structure map.  This holds by definition
and is what lets the structure map of `i` be written as a morphism of `𝒪_P`-modules. -/
theorem closedSubspacePushforwardStructure_eq_unit (i : Z ⟶ P) :
    closedSubspacePushforwardStructure i =
      (SheafOfModules.restrictScalars (structureSharp B S hS i)).obj
        (SheafOfModules.unit (structureRingSheafDirectImage B S hS i)) :=
  rfl

/-- The structure map `𝒪_P ⟶ i_*𝒪_Z` of a morphism `i : Z ⟶ P` of algebraic spaces, read as a
morphism of `𝒪_P`-modules out of the tensor unit.

For a closed immersion this is the surjection whose kernel is the ideal sheaf cutting `Z` out,
and it is the map the canonical map of Stacks 085L twists. -/
def closedSubspacePushforwardUnit (i : Z ⟶ P) :
    (𝟙_ (Modules.{u, u} B S hS P.1 P.2)) ⟶ closedSubspacePushforwardStructure i :=
  SheafOfModules.unitToRestrictScalarsObjUnit (structureSharp B S hS i)

/-- The twist of the structure map of `i : Z ⟶ P` by an `𝒪_P`-module `L`: the morphism
`L ⟶ (i_*𝒪_Z) ⊗ L`.

At `L = 𝒪_P(d)` this is the map `𝒪_P(d) ⟶ (i_*𝒪_Z)(d)` whose direct image along `π` the
canonical map of Stacks 085L composes with the homogeneous section map. -/
def twistedClosedSubspaceMap (i : Z ⟶ P) (L : Modules.{u, u} B S hS P.1 P.2) :
    L ⟶ closedSubspacePushforwardStructure i ⊗ L :=
  (λ_ L).inv ≫ (closedSubspacePushforwardUnit i ▷ L)

end ClosedSubspace

/-! ### The canonical map and its kernel -/

section Ideal

variable {s : RelativeProjSituation.{u, u}}
    {P : AlgebraicSpaces s.site s.base s.containsBase} {π : P ⟶ s.space}
    {Z : AlgebraicSpaces s.site s.base s.containsBase}

/-- The direct image `π_*((i_*𝒪_Z)(d))` along `π` of the degree-`d` twist of the structure sheaf
of the closed subspace `Z`, for the carried twists `T`. -/
def twistedStructureDirectImage (T : ClosedSubspaceTwistSections s P π) (i : Z ⟶ P) (d : ℕ) :
    SheafOfModules.{u} (structureRingSheaf s.site s.base s.containsBase s.space) :=
  (modulePushforward s.site s.base s.containsBase π).obj
    (closedSubspacePushforwardStructure i ⊗ T.twist d)

/-- **The canonical map `𝒜_d ⟶ π_*((i_*𝒪_Z)(d))` of Stacks 085L**, in degree `d`: the
homogeneous section map `𝒜_d ⟶ π_*(𝒪_P(d))` of Stacks 01MP followed by the direct image of the
twist `𝒪_P(d) ⟶ (i_*𝒪_Z)(d)` of the structure map of the closed subspace.

The source states the map into the direct sum over `d ≥ 0`; it is graded, and this is its
degree-`d` component.  Only the twists are carried: the composite itself is the one the source
names. -/
@[stacks 085L "the canonical map 𝒜 ⟶ ⨁ π_*((i_*𝒪_Z)(d)), degreewise, built from the carried \
twists 𝒪_P(d) and homogeneous section maps of Tag 01NR"]
def closedSubspaceSectionMap (T : ClosedSubspaceTwistSections s P π) (i : Z ⟶ P) (d : ℕ) :
    s.algebra.piece (d : ℤ) ⟶ twistedStructureDirectImage T i d :=
  T.sectionMap d ≫ (modulePushforward s.site s.base s.containsBase π).map
    (twistedClosedSubspaceMap i (T.twist d))

/-- **The graded ideal `ℐ ⊆ 𝒜` of Stacks 085L**, in degree `d`: the sectionwise kernel of the
canonical map, as a submodule of the degree-`d` piece of `𝒜`.

This is the kernel of the map the source writes down, not a choice of ideal with the right
properties; the only carried ingredient is the twists. -/
@[stacks 085L "the graded ideal ℐ ⊆ 𝒜, degreewise, as the kernel of that canonical map"]
def closedSubspaceGradedIdeal (T : ClosedSubspaceTwistSections s P π) (i : Z ⟶ P) (d : ℕ) :
    (s.algebra.piece (d : ℤ)).Submodule :=
  Stacks.SheafOfModules.kerSubmodule (closedSubspaceSectionMap T i d)

/-- The graded ideal of Stacks 085L, in degree `d`, as an object of the category of
`𝒪_X`-modules: the categorical kernel of the canonical map.  Its inclusion into `𝒜_d` is
`CategoryTheory.Limits.kernel.ι`, a monomorphism, which is the containment `ℐ ⊆ 𝒜` of the
source. -/
def closedSubspaceGradedIdealObj (T : ClosedSubspaceTwistSections s P π) (i : Z ⟶ P) (d : ℕ) :
    SheafOfModules.{u} (structureRingSheaf s.site s.base s.containsBase s.space) :=
  kernel (closedSubspaceSectionMap T i d)

/-- The submodule and the categorical kernel have the same sections: a local section of `𝒜_d`
lies in `ℐ_d` exactly when the canonical map kills it. -/
theorem mem_closedSubspaceGradedIdeal (T : ClosedSubspaceTwistSections s P π) (i : Z ⟶ P)
    (d : ℕ) (U : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ)
    (x : (s.algebra.piece (d : ℤ)).val.obj U) :
    x ∈ (closedSubspaceGradedIdeal T i d).obj U ↔
      (closedSubspaceSectionMap T i d).val.app U x = 0 :=
  Stacks.SheafOfModules.mem_kerSubmodule_obj _ U x

/-- The graded ideal of Stacks 085L is the kernel of the canonical map, as subsheaves of
`𝒜_d`. -/
theorem closedSubspaceGradedIdeal_eq_ker (T : ClosedSubspaceTwistSections s P π) (i : Z ⟶ P)
    (d : ℕ) :
    closedSubspaceGradedIdeal T i d =
      Stacks.SheafOfModules.kerSubmodule (closedSubspaceSectionMap T i d) :=
  rfl

/-- **Stacks 085L, the quasi-coherence of `ℐ`.**  The degree-`d` piece of the graded ideal cut
out by a closed subspace of the relative Proj is a quasi-coherent `𝒪_X`-module.

There is exactly one carried input, and it is one the source cites.  `hpush` is Stacks 03M9 for
`π`, in the form in which the source uses it: the direct image along `π` of the quasi-coherent
module `(i_*𝒪_Z)(d)` is quasi-coherent — this is where quasi-compactness of `π` and its
separatedness (Stacks 084E) enter.  It is carried because the library's Stacks 03M9,
`AlgebraicGeometry.Space.pushforward_isQuasicoherentOnSite_of_chartwiseKernel`, is itself
conditional on the exact sequence of Stacks 03M8.

The kernel clause of Stacks 03M1(3) is **not** carried: it is discharged from
`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_smallEtale`, whose own
Stacks 03DX(2) input is already proved for the small étale site.  The `letI` ascribes it at this
module's spelling of the structure ring sheaf, which instance resolution does not identify with
the `RingedSite.ringSheaf` spelling of that lemma on its own.  Quasi-coherence of `𝒜_d` is a
field of the relative Proj situation of Stacks 0849. -/
@[stacks 085L "ℐ is a quasi-coherent 𝒪_X-module, degreewise; granted only Tag 03M9 for π as \
quasi-coherence of the direct images π_*((i_*𝒪_Z)(d)), the kernel clause of Tag 03M1(3) being \
discharged from the closure lemma, and built from the carried twists of Tag 01NR"]
theorem isQuasicoherentOnSite_closedSubspaceGradedIdealObj
    (T : ClosedSubspaceTwistSections s P π) (i : Z ⟶ P)
    (hpush : ∀ d : ℕ, (twistedStructureDirectImage T i d).IsQuasicoherentOnSite) (d : ℕ) :
    (closedSubspaceGradedIdealObj T i d).IsQuasicoherentOnSite :=
  let : CategoryTheory.ObjectProperty.IsClosedUnderKernels
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureRingSheaf s.site s.base s.containsBase s.space)) :=
    AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_smallEtale
      s.site s.base s.containsBase s.space.1 s.space.2
  CategoryTheory.ObjectProperty.prop_kernel _ (closedSubspaceSectionMap T i d)
    (s.isQuasicoherent (d : ℤ)) (hpush d)

end Ideal

/-! ### The remaining assertion, as hypothesis data -/

/-- The assertion `Z = Proj_X(𝒜/ℐ)` of Stacks 085L, as data: a graded algebra `ℬ` on `X`, a
degreewise surjection `𝒜 ⟶ ℬ` whose kernel is the graded ideal `ℐ` cut out by `Z`, an algebraic
space over `X` playing the part of `Proj_X(ℬ)` together with a closed immersion of it into `P`,
and an identification of `Z` with that space over `P`.

Nothing here is proved.  This mirrors
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.GradedQuotientPresentation`, which carries the
scheme-level assertion of Stacks 0801 in the same shape; see *What is not proved* in the module
docstring for the three constructions that are missing, and note in particular that the field
`space` is tied to `quotient` only through `ker_eq` and `isClosedImmersion`, because this
repository has no operation taking a graded algebra on an algebraic space to its relative
Proj. -/
structure ClosedSubspaceQuotientPresentation {s : RelativeProjSituation.{u, u}}
    {P : AlgebraicSpaces s.site s.base s.containsBase} {π : P ⟶ s.space}
    {Z : AlgebraicSpaces s.site s.base s.containsBase}
    (T : ClosedSubspaceTwistSections s P π) (i : Z ⟶ P) where
  /-- The quotient graded algebra `ℬ = 𝒜/ℐ`. -/
  quotient : SheafOfModules.GradedAlgebra.{u, u, u, u + 1}
    (structureRingSheaf s.site s.base s.containsBase s.space)
  /-- The quotient homomorphism, degreewise. -/
  quotientMap (d : ℕ) : s.algebra.piece (d : ℤ) ⟶ quotient.piece (d : ℤ)
  /-- It is an epimorphism in each degree. -/
  epi (d : ℕ) : Epi (quotientMap d)
  /-- Its kernel is the graded ideal cut out by the closed subspace: this is what makes `ℬ` the
  quotient `𝒜/ℐ` rather than an unrelated graded algebra. -/
  ker_eq (d : ℕ) : Stacks.SheafOfModules.kerSubmodule (quotientMap d) =
    closedSubspaceGradedIdeal T i d
  /-- The algebraic space playing the part of `Proj_X(ℬ)`. -/
  space : AlgebraicSpaces s.site s.base s.containsBase
  /-- Its morphism into the ambient relative Proj. -/
  toAmbient : space ⟶ P
  /-- That morphism is a closed immersion — the assertion of Stacks 085H for the surjection
  `𝒜 ⟶ ℬ`. -/
  isClosedImmersion : IsClosedImmersion s.site s.base s.containsBase toAmbient.hom
  /-- **The isomorphism `Z = Proj_X(𝒜/ℐ)`.** -/
  iso : Z ≅ space
  /-- The identification is one over the ambient relative Proj. -/
  iso_comp : iso.hom ≫ toAmbient = i

end AlgebraicGeometry.Space

end
