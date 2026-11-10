module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.IdealSheafSequence.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomExactness
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InternalHomSheafUnitEvaluation
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InvertibleDerivedDual

/-!
# The derived dual of the ideal sequence of an effective Cartier divisor

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor with closed immersion `i : D ⟶ X`
and ideal sheaf `ℐ_D`, which is invertible by definition. The computation of
`R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X)` that the isomorphism assertion of
[Stacks, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B) rests on applies the derived
internal Hom into `𝒪_X` to the ideal sequence

`0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0`

of [Stacks, Tag 0C6K]. This file supplies the two inputs that computation needs on the `X` side:
the distinguished triangle the ideal sequence produces, and the identification of its third
vertex.

## The third vertex

`R ℰom(ℐ_D[0], 𝒪_X[0])` is `𝒪_X(D)[0]`. The ideal sheaf of an effective Cartier divisor is
invertible, so the derived dual is the underived one
(`Stacks.SheafOfModules.derivedSheafHomSingleStructureSheafIso`, which is [Stacks, Tag 08JH]
relaxed to a locally free source through [Stacks, Tag 0B8M]), and the underived dual of `ℐ_D`
*is* `𝒪_X(D)`: `Stacks.Divisors.invertibleSheaf'` is defined as the dual sheaf of the ideal
sheaf, and the dual sheaf of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafHom.lean` is the
internal Hom sheaf into the structure sheaf on the nose. So
`Stacks.Divisors.derivedDualIdealSheafIso` below is the general statement with its target
re-ascribed, with no transport.

## Main definitions

* `Stacks.Divisors.divisorIdealShortComplex`: the ideal sequence as a short complex, with its
  short exactness `Stacks.Divisors.divisorIdealShortComplex_shortExact`.
* `Stacks.Divisors.derivedDualIdealSheafIso`: `R ℰom(ℐ_D[0], 𝒪_X[0]) ≅ 𝒪_X(D)[0]`.

## Main results

* `Stacks.Divisors.canonicalSectionHom_eq_internalHomPre`: **the canonical section `1_D`, read as
  a morphism `𝒪_X ⟶ ℰom(ℐ_D, 𝒪_X)`, is precomposition with the ideal inclusion.** This is the
  underived content of the second morphism of the dual triangle.
* `Stacks.Divisors.exists_distinguished_derivedDual_divisorIdeal`: **the dual triangle of the
  ideal sequence.** The two morphisms
  `R ℰom(i_* 𝒪_D, 𝒪_X) ⟶ R ℰom(𝒪_X, 𝒪_X) ⟶ R ℰom(ℐ_D, 𝒪_X)` induced by `𝒪_X ⟶ i_* 𝒪_D` and
  `ℐ_D ⟶ 𝒪_X` extend by a connecting morphism to a distinguished triangle of `D(𝒪_X)`. This is
  [Stacks, Tag 08I0] at the triangle of [Stacks, Tag 0C6K].

## Implementation notes

The ideal sequence is stated in the library as the existence of a zero composite making the sequence
short exact, so the short complex is formed with `Exists.choose` of that statement and its short
exactness is the corresponding `Exists.choose_spec`; the arrows themselves — the kernel
inclusion and the unit `𝒪_X ⟶ i_* 𝒪_D` — are the named ones and are not chosen.

The two morphisms of the dual triangle are spelled as the images of the morphisms of
`CategoryTheory.ShortComplex.ShortExact.singleTriangle` rather than as the images of
`(singleFunctor _ 0).map` of the two arrows, which is what keeps the statement an instance of
[Stacks, Tag 08I0] with nothing in between;
`CategoryTheory.ShortComplex.ShortExact.singleTriangle_mor₁` and `…_mor₂` rewrite the former into
the latter.

## References

* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
* [Stacks Project, Tag 08I0](https://stacks.math.columbia.edu/tag/08I0)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.SheafOfModules (StructureSheafModules derivedSheafHom ringedSite)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-- The ideal sheaf of an effective Cartier divisor is invertible, at the index the
representation theorem of [Stacks, Tag 08JH] is stated with: the presheaf of commutative rings
underlying the structure sheaf of `X` together with its sheaf condition. This is
`Stacks.Divisors.isTensorInvertible_negativeTwist` re-spelled; the two indices are the same. -/
instance isInvertible_negativeTwist_sheaf :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property
      (negativeTwist' D) :=
  isTensorInvertible_negativeTwist D

/-- **The derived dual of the ideal sheaf of an effective Cartier divisor is `𝒪_X(D)`:**

`R ℰom(ℐ_D[0], 𝒪_X[0]) ≅ 𝒪_X(D)[0]` in `D(𝒪_X)`.

`ℐ_D` is invertible, so its derived dual is its underived dual
(`Stacks.SheafOfModules.derivedSheafHomSingleStructureSheafIso`), and its underived dual is
`𝒪_X(D)` by the definition of `Stacks.Divisors.invertibleSheaf'` ([Stacks, Tag 01WX]). -/
def derivedDualIdealSheafIso :
    ((derivedSheafHom X.sheaf).obj (op (DerivedCategory.Q.obj
          ((HomologicalComplex.single (StructureSheafModules X.sheaf)
            (ComplexShape.up ℤ) 0).obj (negativeTwist' D))))).obj
        (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite X.sheaf))) ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single (StructureSheafModules X.sheaf)
          (ComplexShape.up ℤ) 0).obj (invertibleSheaf' D)) :=
  Stacks.SheafOfModules.derivedSheafHomSingleStructureSheafIso X.sheaf (negativeTwist' D)

omit [IsEffectiveCartierDivisor D] in
/-- **The canonical section `1_D` is the dual of the ideal inclusion.** Read as a morphism
`𝒪_X ⟶ 𝒪_X(D) = ℰom(ℐ_D, 𝒪_X)` of sheaves of modules, the canonical section of
[Stacks, Tag 01WX] is precomposition with the inclusion `ℐ_D ⟶ 𝒪_X`, once `𝒪_X` is identified
with `ℰom(𝒪_X, 𝒪_X)` by `Stacks.SheafOfModules.internalHomSheafUnitIso`.

This is the underived content of the second morphism of the dual triangle of the ideal sequence.

A morphism out of the structure sheaf is its value at the unit section
(`SheafOfModules.unitHomEquiv`), so it is enough to compare the two at the unit section over
every open, where both are a section of `ℰom(ℐ_D, 𝒪_X)`, that is a morphism
`ℐ_D|_U ⟶ 𝒪_X|_U`. The inverse identification carries the unit section to the identity of
`𝒪_X|_U` (`Stacks.SheafOfModules.internalHomSheafUnitIso_inv_sectionsEquiv_one`); precomposition
with the inclusion then returns the inclusion itself, and that is `1_D`, whose component over
`U` is the restricted ideal inclusion by definition
(`Stacks.Divisors.canonicalSection_val`). -/
theorem canonicalSectionHom_eq_internalHomPre :
    (Stacks.SheafOfModules.internalHomSheafUnitIso X.sheaf
          (_root_.SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X.sheaf).O))).hom ≫
        (invertibleSheaf' D).unitHomEquiv.symm (canonicalSection' D) =
      RingedSite.internalHomPre (ringedSite X.sheaf)
        (Stacks.IdealSheafSequence.divisorIdealMap D) := by
  refine ((Iso.inv_comp_eq (Stacks.SheafOfModules.internalHomSheafUnitIso X.sheaf
    (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X.sheaf).O)))).1 ?_).symm
  refine ((invertibleSheaf' D).unitHomEquiv.eq_symm_apply).2 ?_
  refine Subtype.ext (funext fun U => ?_)
  refine (_root_.SheafOfModules.unitHomEquiv_apply_coe _ _ U).trans ?_
  refine ((Stacks.SheafOfModules.internalHomSheafHom X.sheaf (negativeTwist' D)
    (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X.sheaf).O))).sectionsEquiv
        U.unop).injective ?_
  refine Eq.trans (Stacks.SheafOfModules.isPrecomp_internalHomPre X.sheaf
    (Stacks.IdealSheafSequence.divisorIdealMap D)
    (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite X.sheaf).O)) U.unop _) ?_
  refine Eq.trans (congrArg
    (_root_.SheafOfModules.Hom.over (Stacks.IdealSheafSequence.divisorIdealMap D) U.unop ≫ ·)
    (Stacks.SheafOfModules.internalHomSheafUnitIso_inv_sectionsEquiv_one X.sheaf U.unop)) ?_
  exact Category.comp_id _

/-- The ideal sequence `0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0` of a closed subscheme as a short complex.
Its arrows are the kernel inclusion of the ideal sheaf and the unit `𝒪_X ⟶ i_* 𝒪_D`; only the
vanishing of the composite is taken from the existence statement of [Stacks, Tag 0C6K]. -/
def divisorIdealShortComplex : ShortComplex (StructureSheafModules X.sheaf) :=
  ShortComplex.mk (Stacks.IdealSheafSequence.divisorIdealMap D)
    (Stacks.IdealSheafSequence.divisorQuotientMap D)
    (Stacks.IdealSheafSequence.divisorIdeal_shortExact D).choose

omit [IsEffectiveCartierDivisor D] in
/-- **[Stacks, Tag 0C6K], the ideal sequence is short exact.** -/
theorem divisorIdealShortComplex_shortExact : (divisorIdealShortComplex D).ShortExact :=
  (Stacks.IdealSheafSequence.divisorIdeal_shortExact D).choose_spec

omit [IsEffectiveCartierDivisor D] in
/-- **The dual triangle of the ideal sequence of a closed subscheme.** Applying the derived
internal Hom into `𝒪_X` to the triangle of the ideal sequence
`0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0` gives a distinguished triangle of `D(𝒪_X)`:

`R ℰom(i_* 𝒪_D, 𝒪_X) ⟶ R ℰom(𝒪_X, 𝒪_X) ⟶ R ℰom(ℐ_D, 𝒪_X) ⟶ R ℰom(i_* 𝒪_D, 𝒪_X)⟦1⟧`,

the first two morphisms being induced by `𝒪_X ⟶ i_* 𝒪_D` and by `ℐ_D ⟶ 𝒪_X`, in that order —
the contravariance of the first variable reverses them.

This is [Stacks, Tag 08I0] in the source variable at the triangle of the short exact sequence.
The connecting morphism is only asserted to exist, which is all that tag gives; for the
computation of [Stacks, Tag 0B4B] the two named morphisms carry the content, the third vertex
being `𝒪_X(D)[0]` by `Stacks.Divisors.derivedDualIdealSheafIso`. -/
theorem exists_distinguished_derivedDual_divisorIdeal :
    ∃ δ : ((derivedSheafHom X.sheaf).flip.obj
          (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite X.sheaf)))).obj
        (op (divisorIdealShortComplex_shortExact D).singleTriangle.obj₁) ⟶
      (((derivedSheafHom X.sheaf).flip.obj
          (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite X.sheaf)))).obj
        (op (divisorIdealShortComplex_shortExact D).singleTriangle.obj₃))⟦(1 : ℤ)⟧,
      Triangle.mk
        (((derivedSheafHom X.sheaf).flip.obj
            (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite X.sheaf)))).map
          (divisorIdealShortComplex_shortExact D).singleTriangle.mor₂.op)
        (((derivedSheafHom X.sheaf).flip.obj
            (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite X.sheaf)))).map
          (divisorIdealShortComplex_shortExact D).singleTriangle.mor₁.op)
        δ ∈ distTriang (DerivedCategory (StructureSheafModules X.sheaf)) :=
  Stacks.SheafOfModules.exists_distinguished_derivedSheafHom_first X.sheaf _ _
    (divisorIdealShortComplex_shortExact D).singleTriangle_distinguished

end Stacks.Divisors

end
