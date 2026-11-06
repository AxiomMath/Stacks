module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.DualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexModelIndependence
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplexOfCharts

/-!
# The dualizing complexes `ω_{U/k}^•` and `ω_{X/k}^•` at the standard model

Let `k` be a field and `p : U ⟶ Spec k` separated of finite type, with a compactification
`j : U ⟶ X`, `q : X ⟶ Spec k` proper. [Stacks, Section 0G59] works with
`ω_{U/k}^• = p^!𝒪_{Spec k}` and `ω_{X/k}^• = q^!𝒪_{Spec k}`, and the proof of
[Stacks, Tag 0G5A] uses that `ω_{U/k}^• = ω_{X/k}^•|_U`, "because `p^!` is constructed as `q^!`
composed with restriction to `U`".

Both complexes are built in the library at the locally small model of `D(𝒪)`
(`Stacks.Duality.upperShriek`, `Stacks.Duality.relativeDualizingComplex`), while the bounded
coherent derived categories, Deligne systems and compactly supported cohomology of
[Stacks, Section 0G4Z] live at `CategoryTheory.HasDerivedCategory.standard`. This file carries the
two complexes to the standard model and records the facts about them that are used there.

## Main definitions

* `AlgebraicGeometry.standardRelativeDualizingComplex`: `ω_{X/k}^• = q^!𝒪_{Spec k}` for `q`
  proper, at the standard model.
* `AlgebraicGeometry.standardUpperShriekDualizingComplex`: `ω_{U/k}^• = p^!𝒪_{Spec k}`, `p^!`
  computed at a compactification `c`, at the standard model.

## Main results

* `AlgebraicGeometry.standardUpperShriekDualizingComplexIso`: `ω_{U/k}^• ≅ ω_{X/k}^•|_U`, where
  `X` is the compactification.
* `AlgebraicGeometry.isDualizingComplex_standardRelativeDualizingComplex` and
  `AlgebraicGeometry.isDualizingComplex_standardUpperShriekDualizingComplex`: both are dualizing
  complexes ([Stacks, Tag 0FVV] and [Stacks, Tag 0AA3]).

## Implementation notes

The global instances in scope are the locally small models
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, at which the two complexes are constructed;
the standard model `CategoryTheory.HasDerivedCategory.standard`, at which they are consumed, is
named explicitly.

## References

* [Stacks Project, Tag 0G5A](https://stacks.math.columbia.edu/tag/0G5A)
* [Stacks Project, Tag 0FVV](https://stacks.math.columbia.edu/tag/0FVV)
* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory StacksDraft.DerivedModel Stacks.Duality

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- **`ω_{X/k}^• = q^!𝒪_{Spec k}` at the standard model**, for `q : X ⟶ Spec k` proper: the
relative dualizing complex `a(𝒪_{Spec k})` of [Stacks, Tag 0FVV], carried from the locally
small model by the comparison equivalence. -/
def standardRelativeDualizingComplex {X : Scheme.{u}} (q : X ⟶ Spec (.of k)) [IsProper q] :
    @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules) :=
  (modelEquiv (Scheme.Modules.hasDerivedCategory X)
      (HasDerivedCategory.standard X.Modules)).functor.obj
    (relativeDualizingComplex q (isQuasicoherent_homology_derivedPushforward_of_qcqs q)
      (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj

/-- `ω_{X/k}^•` is a dualizing complex, [Stacks, Tag 0FVV]. -/
theorem isDualizingComplex_standardRelativeDualizingComplex {X : Scheme.{u}}
    (q : X ⟶ Spec (.of k)) [IsProper q] :
    letI := LocallyOfFiniteType.isLocallyNoetherian q
    @IsDualizingComplex X _ (HasDerivedCategory.standard X.Modules)
      (standardRelativeDualizingComplex q) :=
  have := LocallyOfFiniteType.isLocallyNoetherian q
  (isDualizingComplex_modelEquiv_iff (Scheme.Modules.hasDerivedCategory X)
    (HasDerivedCategory.standard X.Modules) _).2
    (isDualizingComplex_relativeDualizingComplex_of_isProper q)

variable {U : Scheme.{u}} (p : U ⟶ Spec (.of k)) [IsSeparated p] [LocallyOfFiniteType p]
  [QuasiCompact p] (c : CompactificationOf (Over.mk p))

/-- **`ω_{U/k}^• = p^!𝒪_{Spec k}` at the standard model**: the upper shriek functor of
[Stacks, Tag 0A9Y], computed at the compactification `c`, applied to `𝒪_{Spec k}` and carried
from the locally small model by the comparison equivalence. -/
def standardUpperShriekDualizingComplex :
    @DerivedCategory U.Modules _ _ (HasDerivedCategory.standard U.Modules) :=
  (modelEquiv (Scheme.Modules.hasDerivedCategory U)
      (HasDerivedCategory.standard U.Modules)).functor.obj
    ((upperShriek (ftsHomToBase p) c).obj
      (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj

/-- **`ω_{U/k}^• = ω_{X/k}^•|_U`.** For the compactification `j : U ⟶ X`, `q : X ⟶ Spec k` of `p`
at which `p^!` is computed, `p^!𝒪_{Spec k} = j^*(q^!𝒪_{Spec k})`: `p^!` is by definition
`Lj^* ∘ q^!`, derived pullback along the open immersion `j` is restriction
(`Stacks.Duality.derivedRestrictIsoDerivedPullback`), and restriction commutes with the change of
model (`StacksDraft.DerivedModel.mapDerivedCategoryCompModelEquivIso` and
`StacksDraft.DerivedModel.modelEquivCompMapDerivedCategoryIso`). -/
def standardUpperShriekDualizingComplexIso :
    standardUpperShriekDualizingComplex p c ≅
      (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard c.space.Modules) _ _ _
        (HasDerivedCategory.standard U.Modules) (Scheme.Modules.restrictFunctor c.immersion) _ _
        _).obj (standardRelativeDualizingComplex c.toBase) :=
  let hLS := Scheme.Modules.hasDerivedCategory
  let ω := (relativeDualizingComplex c.toBase
    (isQuasicoherent_homology_derivedPushforward_of_qcqs c.toBase)
    (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj
  (modelEquiv (hLS U) (HasDerivedCategory.standard U.Modules)).functor.mapIso
      ((derivedRestrictIsoDerivedPullback c.immersion).app ω).symm ≪≫
    (mapDerivedCategoryCompModelEquivIso (Scheme.Modules.restrictFunctor c.immersion) (hLS c.space)
      (hLS _) (HasDerivedCategory.standard _)).app ω ≪≫
    ((modelEquivCompMapDerivedCategoryIso (Scheme.Modules.restrictFunctor c.immersion) (hLS c.space)
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)).app ω).symm

/-- `ω_{U/k}^•` is a dualizing complex: `𝒪_{Spec k}` is one, and `p^!` carries dualizing
complexes to dualizing complexes, [Stacks, Tag 0AA3]
(`Stacks.Duality.isDualizingComplex_upperShriek_obj`). -/
theorem isDualizingComplex_standardUpperShriekDualizingComplex :
    letI := LocallyOfFiniteType.isLocallyNoetherian p
    @IsDualizingComplex U _ (HasDerivedCategory.standard U.Modules)
      (standardUpperShriekDualizingComplex p c) := by
  let := LocallyOfFiniteType.isLocallyNoetherian p
  refine (isDualizingComplex_modelEquiv_iff (Scheme.Modules.hasDerivedCategory U)
    (HasDerivedCategory.standard U.Modules) _).2 ?_
  refine isDualizingComplex_upperShriek_obj (ftsHomToBase p) c _ ?_
  exact isDualizingComplex_of_iso ((ObjectProperty.ι _).mapIso
    ((twistedInverseImageIdIso (Spec (.of k))
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 _))).app _))
    (isDualizingComplex_relativeDualizingComplex_of_isProper (𝟙 (Spec (.of k))))

end AlgebraicGeometry

end
