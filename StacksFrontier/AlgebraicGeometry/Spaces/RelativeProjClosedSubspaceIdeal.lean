module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KernelIdealSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesTensorQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProj
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Space
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# The graded ideal cut out by a closed subspace of a relative Proj

Let `S` be a scheme, `X` an algebraic space over `S` and `𝒜` a quasi-coherent graded
`𝒪_X`-algebra — the relative Proj situation of Stacks 0849.  Let `π : P ⟶ X` be the relative
Proj of `𝒜` and let `i : Z ⟶ P` be a closed subspace.  Stacks 085L defines a graded ideal
`ℐ ⊆ 𝒜` as the kernel of the canonical map

`𝒜 ⟶ ⨁_{d ≥ 0} π_*((i_*𝒪_Z)(d))`

and asserts, for `π` quasi-compact, that `Z = Proj_X(𝒜/ℐ)`.

The complete statement of Stacks 085L, with the twists `𝒪_P(d)` and the maps
`ψ_d : π^*𝒜_d ⟶ 𝒪_P(d)` of Stacks 084D constructed on `P = Proj_X(𝒜)`, the ideal `ℐ` proved
quasi-coherent and `Z ≅ Proj_X(𝒜/ℐ)` over `P`, is
`AlgebraicGeometry.Space.C1359Bridge.exists_iso_quotientProjHom_psiKernelGradedIdeal`
(`StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceKernelProj`).

This file writes the ideal down for an arbitrary morphism `π : P ⟶ X` equipped with a datum of
twists and homogeneous section maps, `AlgebraicGeometry.Space.ClosedSubspaceTwistSections`;
everything else is a definition with a real body.  In particular the canonical map is the
composite the source names and not a parameter: the twisted module `(i_*𝒪_Z)(d)` is
`i_*𝒪_Z ⊗_{𝒪_P} 𝒪_P(d)` for the tensor product of Stacks 01CA, the map
`𝒪_P(d) ⟶ (i_*𝒪_Z)(d)` is the twist of the structure map `𝒪_P ⟶ i_*𝒪_Z` of the closed
immersion, and `ℐ_d` is the sectionwise kernel of the result.

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
* `AlgebraicGeometry.Space.ClosedSubspaceQuotientPresentation`: the shape of the assertion
  `Z = Proj_X(𝒜/ℐ)` of Stacks 085L for such a datum, as a structure.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_closedSubspaceGradedIdealObj`: **`ℐ_d` is
  quasi-coherent** for `P = Proj_X(𝒜)` with quasi-coherent twists, `π` quasi-compact and `i` a
  closed immersion, which is the third step of the source's proof.  At the twists of Stacks 084D,
  `AlgebraicGeometry.Space.C1359Bridge.psiTwistSections`, it is
  `AlgebraicGeometry.Space.C1359Bridge.isQuasicoherentOnSite_psiClosedSubspaceIdeal`.
* `AlgebraicGeometry.Space.closedSubspaceGradedIdeal_eq_ker` and
  `AlgebraicGeometry.Space.mem_closedSubspaceGradedIdeal`: the sections of `ℐ_d` over an object
  of the small étale site are exactly the sections of `𝒜_d` killed by the canonical map, so the
  ideal is the kernel of that map and nothing else.

## Implementation notes

**What the datum is.**  `ClosedSubspaceTwistSections` carries, on an algebraic space `P` over
`X`, exactly the two pieces of data the canonical map consumes: modules `𝒪_P(d)` with their
quasi-coherence, and section maps `𝒜_d ⟶ π_*(𝒪_P(d))` of Stacks 01MP.  It carries no
identification of those modules with the twists on an étale chart, so the statements of this
file are statements about that datum.  For the relative Proj `P = Proj_X(𝒜)` itself the twists
are constructed — `AlgebraicGeometry.Space.RelativeProjSituation.twistModule`, descended from
the twists of Stacks 01NR on the charts — together with `ψ_d`,
`AlgebraicGeometry.Space.RelativeProjSituation.psiTwistHom`; the datum they form is
`AlgebraicGeometry.Space.C1359Bridge.psiTwistSections`, and the ideal they cut out is
`AlgebraicGeometry.Space.C1359Bridge.psiKernelGradedIdeal`.

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

## Relation to the complete statement

The isomorphism `Z = Proj_X(𝒜/ℐ)` of Stacks 085L, for `π` quasi-compact, is proved for the
relative Proj of Stacks 084C with its constructed twists, as
`AlgebraicGeometry.Space.C1359Bridge.exists_iso_quotientProjHom_psiKernelGradedIdeal`: the
quotient `𝒜/ℐ` is `AlgebraicGeometry.Space.RelativeProjSituation.GradedIdeal.quotientSituation`,
its relative Proj and the closed immersion into `P` of Stacks 085H are
`AlgebraicGeometry.Space.RelativeProjSituation.GradedIdeal.quotientProjHom`, and the isomorphism
is descended from the atlas.  `ClosedSubspaceQuotientPresentation` below only records the shape
of that assertion for an arbitrary datum of twists.

**Quasi-coherence.**  `isQuasicoherentOnSite_closedSubspaceGradedIdealObj` follows the source:
`π` is separated (Stacks 084E,
`AlgebraicGeometry.Space.RelativeProjSituation.isSeparated_relativeProjπ`), so for `π`
quasi-compact the direct images `π_*((i_*𝒪_Z)(d))` are quasi-coherent by Stacks 03M9,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`, and the kernel is
quasi-coherent by Stacks 03M1(3),
`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_smallEtale`.

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

This is the part of the datum of Stacks 01NR that the canonical map consumes, for an arbitrary
morphism `π : P ⟶ X`.  On the relative Proj itself the twists are constructed, as
`AlgebraicGeometry.Space.C1359Bridge.psiTwistSections` from
`AlgebraicGeometry.Space.RelativeProjSituation.twistModule`; see the implementation notes. -/
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
degree-`d` component.  The composite is the one the source names, for any datum of twists; at the
twists of Stacks 084D on `P = Proj_X(𝒜)`, `AlgebraicGeometry.Space.C1359Bridge.psiTwistSections`,
it is the canonical map of the source. -/
@[stacks 085L "the canonical map 𝒜 ⟶ ⨁ π_*((i_*𝒪_Z)(d)), degreewise; at the twists of \
Tag 084D it is the source's map"]
def closedSubspaceSectionMap (T : ClosedSubspaceTwistSections s P π) (i : Z ⟶ P) (d : ℕ) :
    s.algebra.piece (d : ℤ) ⟶ twistedStructureDirectImage T i d :=
  T.sectionMap d ≫ (modulePushforward s.site s.base s.containsBase π).map
    (twistedClosedSubspaceMap i (T.twist d))

/-- **The graded ideal `ℐ ⊆ 𝒜` of Stacks 085L**, in degree `d`: the sectionwise kernel of the
canonical map, as a submodule of the degree-`d` piece of `𝒜`.

This is the kernel of the map the source writes down, not a choice of ideal with the right
properties; at the twists `AlgebraicGeometry.Space.C1359Bridge.psiTwistSections` it is the ideal
`ℐ` of the source. -/
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

end Ideal

/-- **Stacks 085L, the quasi-coherence of `ℐ`.**  Let `π : P = Proj_X(𝒜) ⟶ X` be quasi-compact
and `i : Z ⟶ P` a closed immersion.  Then for any quasi-coherent twists `𝒪_P(d)` with homogeneous
section maps, in particular those of Stacks 084D
(`AlgebraicGeometry.Space.C1359Bridge.psiTwistSections`), the degree-`d` piece of the graded
ideal `ℐ`, the kernel of the canonical map `𝒜_d ⟶ π_*((i_*𝒪_Z)(d))`, is a quasi-coherent
`𝒪_X`-module.

The proof is the source's.  `π` is separated (Stacks 084E), hence quasi-separated; `i_*𝒪_Z` is
quasi-coherent as `i` is a closed immersion, and so is its tensor product with the quasi-coherent
`𝒪_P(d)`; the direct image along the quasi-compact quasi-separated `π` is quasi-coherent by
Stacks 03M9, `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`; and the
kernel of a map of quasi-coherent modules is quasi-coherent (Stacks 03M1(3),
`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_smallEtale`).  The `let`
ascribes the last at this module's spelling of the structure ring sheaf, which instance
resolution does not identify with the `RingedSite.ringSheaf` spelling of that lemma on its own. -/
@[stacks 085L "ℐ is a quasi-coherent 𝒪_X-module, degreewise, for π quasi-compact and i a closed \
immersion, for any quasi-coherent twists on Proj_X(𝒜), those of Tag 084D included"]
theorem isQuasicoherentOnSite_closedSubspaceGradedIdealObj {s : RelativeProjSituation.{u, u}}
    (T : ClosedSubspaceTwistSections s s.Proj s.π)
    {Z : AlgebraicSpaces s.site s.base s.containsBase} (i : Z ⟶ s.Proj)
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.π.hom)
    (hi : IsClosedImmersion s.site s.base s.containsBase i.hom) (d : ℕ) :
    (closedSubspaceGradedIdealObj T i d).IsQuasicoherentOnSite :=
  let : CategoryTheory.ObjectProperty.IsClosedUnderKernels
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureRingSheaf s.site s.base s.containsBase s.space)) :=
    AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_smallEtale
      s.site s.base s.containsBase s.space.1 s.space.2
  have : (closedSubspacePushforwardStructure i).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_structureSheafPushforward s.site s.base s.containsBase i hi
  CategoryTheory.ObjectProperty.prop_kernel _
    (closedSubspaceSectionMap T i d) (s.isQuasicoherent (d : ℤ))
    (isQuasicoherentOnSite_modulePushforward_of_qcqs s.site s.base s.containsBase s.π hπ
      (isQuasiSeparated_of_isSeparated s.site s.base s.containsBase s.isSeparated_relativeProjπ)
      _ (isQuasicoherentOnSite_tensorObj s.site s.base s.containsBase s.Proj.1 s.Proj.2 _ _))

/-! ### The shape of the assertion `Z = Proj_X(𝒜/ℐ)`, for a datum of twists -/

/-- The assertion `Z = Proj_X(𝒜/ℐ)` of Stacks 085L, as data: a graded algebra `ℬ` on `X`, a
degreewise surjection `𝒜 ⟶ ℬ` whose kernel is the graded ideal `ℐ` cut out by `Z`, an algebraic
space over `X` playing the part of `Proj_X(ℬ)` together with a closed immersion of it into `P`,
and an identification of `Z` with that space over `P`.

This mirrors `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.GradedQuotientPresentation`,
the same shape at the level of schemes.  The field `space` is tied to `quotient` only through
`ker_eq` and `isClosedImmersion`.  For the relative Proj of Stacks 084C with its constructed
twists the assertion is proved, with `Proj_X(𝒜/ℐ)` the relative Proj of
`AlgebraicGeometry.Space.RelativeProjSituation.GradedIdeal.quotientSituation`, as
`AlgebraicGeometry.Space.C1359Bridge.exists_iso_quotientProjHom_psiKernelGradedIdeal`. -/
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
