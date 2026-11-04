module

public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDerivedSheafHomIso
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportHomComplexSingleSource
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportKInjectiveCounit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.StructureSheafHomEvaluationSingle

/-!
# The trace description of the derived internal Hom bifunctor at the structure sheaf

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor, with closed immersion
`i : D ⟶ X`.  [Stacks, Tag 0A77] identifies `Ri_* R ℰom(𝒪_D, -)` with
`R ℰom_{𝒪_X}(Ri_* 𝒪_D, -)`, and the trace of [Stacks, Tag 0A76] — the counit of
`Ri_* ⊣ R ℰom(𝒪_D, -)` — has to be read, through that identification, as the map the derived
internal Hom bifunctor supplies on its own: precomposition with the unit `𝒪_X ⟶ i_* 𝒪_D`
followed by `R ℰom_{𝒪_X}(𝒪_X, 𝒪_X) ≅ 𝒪_X`.

This file supplies the two inputs to that description which concern the ambient scheme alone:
the identification `R ℰom_{𝒪_X}(𝒪_X, 𝒪_X) ≅ 𝒪_X` that the comparison of triangles of
[Stacks, Tag 08I0] is built from is evaluation at the unit section, and the restriction map
`𝒪_X ⟶ i_* 𝒪_D` carries the unit section to the unit section.  Both are what the degreewise
trace identity `…exactSupportHomComplexIso_comp_evaluation` consumes.

## Main definitions

* `Stacks.Divisors.divisorQuotientSingle`: the restriction map `𝒪_X ⟶ i_* 𝒪_D` of the ideal
  sequence, placed in degree zero.

## Main results

* `Stacks.Divisors.strictlyPerfectHomComparison_comp_structureDualIso`: **the identification
  `R ℰom_{𝒪_X}(𝒪_X, 𝒪_X) ≅ 𝒪_X` that the comparison of triangles of [Stacks, Tag 08I0] is built
  from is evaluation at the unit section**, read through the comparison
  `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison`.
* `Stacks.Divisors.divisorQuotientSingle_one`: the restriction map carries the unit section to
  the unit section.

## Implementation notes

`Stacks.Divisors.structureDualIso` is the inverse of the comparison
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison` at an invertible source, followed by
the collapse of the internal Hom complex of two single complexes and
`ℰom_{𝒪_X}(𝒪_X, 𝒪_X) ≅ 𝒪_X`; that collapse *is* evaluation at the unit section, which is
`Stacks.SheafOfModules.structureSheafHomEvaluation_eq_sheafHomComplexSingleIso`.  The statement
below is that identity with the comparison cancelled from the left, which is the shape the
derived statements consume.

The structure sheaf placed in degree zero occurs under the two spellings
`AlgebraicGeometry.RingedSite.structureSheafComplex` and
`HomologicalComplex.single … 0` applied to the middle term of the ideal sequence; they are equal
by `rfl`, and the ascription on `Stacks.Divisors.divisorQuotientSingle` is what keeps the first
one visible, so that evaluation at the unit section elaborates.

## References

* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 08I0](https://stacks.math.columbia.edu/tag/08I0)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard


universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-- The ambient scheme, read as a ringed site. -/
abbrev siteOf (Y : Scheme.{u}) : RingedSite.{u, u, u} := Stacks.SheafOfModules.ringedSite Y.sheaf

/-- The structure sheaf of a scheme placed in degree zero, as a cochain complex. -/
abbrev structureComplexOf (Y : Scheme.{u}) :=
  AlgebraicGeometry.RingedSite.structureSheafComplex (siteOf Y)

/-- The chosen K-injective resolution of the structure sheaf placed in degree zero. -/
abbrev structureKInjectiveOf (Y : Scheme.{u}) :=
  (AlgebraicGeometry.RingedSite.kInjectiveResolution (siteOf Y)).obj (structureComplexOf Y)

/-- The augmentation of the structure sheaf in degree zero into its chosen K-injective
resolution. -/
abbrev structureAugmentationOf (Y : Scheme.{u}) :=
  (AlgebraicGeometry.RingedSite.kInjectiveAugmentation (siteOf Y)).app (structureComplexOf Y)

/-- The structure sheaf of a scheme, as a module over itself, is invertible. -/
local instance isInvertibleUnitOf (Y : Scheme.{u}) :
    Stacks.SheafOfModules.IsInvertible (siteOf Y).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (siteOf Y).O).property
      (SheafOfModules.unit (structureSheaf Y.sheaf)) :=
  Stacks.SheafOfModules.isInvertible_unit _ _

/-- The class of the K-injective augmentation of the structure sheaf is invertible: the
augmentation is a quasi-isomorphism. -/
instance isIso_Q_map_structureAugmentationOf :
    IsIso (DerivedCategory.Q.map (structureAugmentationOf X)) := by
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
  infer_instance

/-- The comparison to the derived internal Hom at the structure sheaf, in both variables, is
invertible: the structure sheaf is invertible. -/
instance isIso_strictlyPerfectHomComparison_structure :
    IsIso (AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison (siteOf X)
      (Stacks.SheafOfModules.derivedInternalHom X.sheaf) (structureComplexOf X)
      (structureComplexOf X)) :=
  AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso_of_isInvertible (siteOf X)
    (Stacks.SheafOfModules.derivedInternalHom X.sheaf) 0
    (SheafOfModules.unit (structureSheaf X.sheaf)) (structureComplexOf X)

/-- **The comparison, followed by the identification `R ℰom_{𝒪_X}(𝒪_X, 𝒪_X) ≅ 𝒪_X` that the
triangle comparison of [Stacks, Tag 08I0] is built from, is evaluation at the unit section.**

`Stacks.Divisors.structureDualIso` is the inverse of the comparison to the derived internal Hom
followed by the collapse of the internal Hom complex of two single complexes and
`ℰom_{𝒪_X}(𝒪_X, 𝒪_X) ≅ 𝒪_X`; that collapse *is* evaluation at the unit section, by
`Stacks.SheafOfModules.structureSheafHomEvaluation_eq_sheafHomComplexSingleIso`. -/
theorem strictlyPerfectHomComparison_comp_structureDualIso :
    AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison (siteOf X)
          (Stacks.SheafOfModules.derivedInternalHom X.sheaf) (structureComplexOf X)
          (structureComplexOf X) ≫ (structureDualIso D).hom =
      DerivedCategory.Q.map (AlgebraicGeometry.RingedSite.structureSheafHomEvaluation (siteOf X)
        (structureComplexOf X)) :=
  Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans
      (congrArg
        (fun t => t ≫ DerivedCategory.Q.map
          ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map
            (Stacks.SheafOfModules.internalHomSheafUnitIso X.sheaf
              (SheafOfModules.unit (structureSheaf X.sheaf))).hom))
        (IsIso.hom_inv_id_assoc
          (AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison (siteOf X)
            (Stacks.SheafOfModules.derivedInternalHom X.sheaf) (structureComplexOf X)
            (structureComplexOf X))
          (DerivedCategory.Q.map
            (AlgebraicGeometry.RingedSite.sheafHomComplexSingleIso (siteOf X)
              (SheafOfModules.unit (structureSheaf X.sheaf))
              (SheafOfModules.unit (structureSheaf X.sheaf))).hom)))
      (Eq.trans (DerivedCategory.Q.map_comp _ _).symm
        (congrArg (fun t => DerivedCategory.Q.map t)
          (Stacks.SheafOfModules.structureSheafHomEvaluation_eq_sheafHomComplexSingleIso
            X.sheaf).symm)))


/-- The restriction map `𝒪_X ⟶ i_* 𝒪_D` of the ideal sequence, placed in degree zero. -/
abbrev divisorQuotientSingle :
    AlgebraicGeometry.RingedSite.structureSheafComplex (siteOf X) ⟶
      (closedQuotient D).pushforwardStructureSingleComplex :=
  (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map (idealShortComplex D).g

omit [IsEffectiveCartierDivisor D] in
/-- In degree zero the single complex of the restriction map is that map. -/
theorem divisorQuotientSingle_f_zero :
    (divisorQuotientSingle D).f 0 = (idealShortComplex D).g := rfl

omit [IsEffectiveCartierDivisor D] in
/-- **The restriction map carries the unit section to the unit section.** -/
theorem divisorQuotientSingle_one (U : (siteOf X).C) :
    (((divisorQuotientSingle D).f 0).val.app (op U))
        (AlgebraicGeometry.RingedSite.structureSheafOne (siteOf X) U) =
      (1 : ((closedQuotient D).pushedRingSheaf.obj.obj (op U) : Type u)) := by
  rw [divisorQuotientSingle_f_zero]
  exact map_one (ConcreteCategory.hom
    ((structureSheafHom D.subschemeι.toLRSHom.toShHom).hom.app (op U)))

end Stacks.Divisors

end
