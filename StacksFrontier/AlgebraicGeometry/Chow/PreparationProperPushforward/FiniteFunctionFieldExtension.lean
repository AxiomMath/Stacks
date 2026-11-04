module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NoetherianFibre
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport

/-!
# Equal delta-dimension forces a finite extension of function fields

Let `f : X ⟶ Y` be a morphism of integral schemes locally of finite type over a Chow base
`(S, δ)`. If `X` and `Y` have the same delta-dimension then either `f(X)` lies inside a proper
closed subscheme of `Y`, or `f` is dominant and the induced extension of function fields
`R(X)/R(Y)` is finite.

## Main results

* `Stacks.Chow.exists_properClosedSubscheme_or_finiteDimensional_functionField` — the
  dichotomy (Stacks 02R1).

## Implementation notes

A proper closed subscheme of `Y` is presented as a closed immersion `i : Z ⟶ Y` whose range is
not all of `Y`, and the containment `f(X) ⊆ Z` as an inclusion of ranges of the underlying
continuous maps; when `f` is not dominant the closure of its image, with its reduced induced
structure, is such a subscheme. The extension `R(Y) ⊆ R(X)` is
`AlgebraicGeometry.dominantFunctionFieldMap`, the stalk map at the generic point of `X`
transported along the identification of its image with the generic point of `Y`; the algebra
structure it defines is supplied by a `letI` inside the statement so that it is the same
instance throughout.

Equality of the delta-dimensions is an equality of the relative dimensions at the two generic
points. Both relative dimensions are computed over the same point of the base, so the terms
coming from `δ` cancel, and additivity of transcendence degree in the tower
`κ(s(η_X)) ⊆ R(Y) ⊆ R(X)` leaves `R(X)` of transcendence degree `0` over `R(Y)`. Since `f` is
locally of finite type, `R(X)` is essentially of finite type over `R(Y)`, and an algebraic
extension which is essentially of finite type is finite.

## References

* [Stacks Project, Tag 02R1](https://stacks.math.columbia.edu/tag/02R1)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Chow

/-- A dominant morphism of integral schemes maps the generic point to the generic point. -/
private theorem map_genericPoint_eq_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] : f (genericPoint X) = genericPoint Y :=
  ((tfae_isDominant_of_isIntegral f).out 1 2).mp ‹IsDominant f›

/-- The extension of function fields of a dominant morphism is the stalk map at the generic point
precomposed with the identification of the stalk at the generic point of the target. -/
private theorem dominantFunctionFieldMap_eq_stalkCongr_comp_stalkMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    dominantFunctionFieldMap f =
      ((Y.presheaf.stalkCongr (.of_eq (map_genericPoint_eq_genericPoint f).symm)).hom ≫
        f.stalkMap (genericPoint X)).hom := by
  dsimp [dominantFunctionFieldMap]
  rw [stalkMap_cast_target]
  rfl

/-- For a dominant morphism of integral schemes the extension of function fields and the
extension of residue fields at the generic point of the source have the same transcendence
degree: the residue map of a stalk which is already a field is an isomorphism. -/
private theorem trdeg_functionField_eq_trdeg_residueField
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
    letI : Algebra (Y.residueField (f (genericPoint X))) (X.residueField (genericPoint X)) :=
      (f.residueFieldMap (genericPoint X)).hom.toAlgebra
    Algebra.trdeg Y.functionField X.functionField =
      Algebra.trdeg (Y.residueField (f (genericPoint X))) (X.residueField (genericPoint X)) := by
  let η := genericPoint X
  let ξ := genericPoint Y
  have hgen : f η = ξ := map_genericPoint_eq_genericPoint f
  let eX : X.functionField ≃+* X.residueField η :=
    RingEquiv.ofBijective (X.residue η).hom
      ⟨RingHom.injective (X.residue η).hom, X.residue_surjective η⟩
  let eY₀ : Y.functionField ≃+* Y.residueField ξ :=
    RingEquiv.ofBijective (Y.residue ξ).hom
      ⟨RingHom.injective (Y.residue ξ).hom, Y.residue_surjective ξ⟩
  let eY : Y.functionField ≃+* Y.residueField (f η) :=
    eY₀.trans (Y.residueFieldCongr hgen.symm).commRingCatIsoToRingEquiv
  let : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  let : Algebra (Y.residueField (f η)) (X.residueField η) :=
    (f.residueFieldMap η).hom.toAlgebra
  refine Algebra.trdeg_eq_of_ringEquiv eY eX fun a => ?_
  have hmaps : ((Y.residue ξ ≫ (Y.residueFieldCongr hgen.symm).hom) ≫ f.residueFieldMap η) =
      ((Y.presheaf.stalkCongr (.of_eq hgen.symm)).hom ≫ f.stalkMap η) ≫ X.residue η := by
    calc
      _ = ((Y.presheaf.stalkCongr (.of_eq hgen.symm)).hom ≫ Y.residue (f η)) ≫
            f.residueFieldMap η := by rw [Scheme.residue_residueFieldCongr]
      _ = (Y.presheaf.stalkCongr (.of_eq hgen.symm)).hom ≫
            (Y.residue (f η) ≫ f.residueFieldMap η) := Category.assoc _ _ _
      _ = (Y.presheaf.stalkCongr (.of_eq hgen.symm)).hom ≫
            (f.stalkMap η ≫ X.residue η) := by rw [Scheme.residue_residueFieldMap]
      _ = _ := (Category.assoc _ _ _).symm
  change eX.toRingHom (dominantFunctionFieldMap f a) =
    (f.residueFieldMap η).hom (eY.toRingHom a)
  rw [show eX.toRingHom = (X.residue η).hom from rfl,
    dominantFunctionFieldMap_eq_stalkCongr_comp_stalkMap f,
    show eY.toRingHom = (Y.residue ξ ≫ (Y.residueFieldCongr hgen.symm).hom).hom from rfl]
  exact (congrArg (fun k : CommRingCat.Hom _ _ => k.hom a) hmaps).symm

/-- For a dominant morphism of integral schemes which is locally of finite type the extension
of function fields is essentially of finite type. -/
private theorem essFiniteType_functionField {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [LocallyOfFiniteType f] :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
    Algebra.EssFiniteType Y.functionField X.functionField := by
  let η := genericPoint X
  have hgen : f η = genericPoint Y := map_genericPoint_eq_genericPoint f
  let : Algebra Y.functionField (Y.presheaf.stalk (f η)) :=
    (Y.presheaf.stalkCongr (.of_eq hgen.symm)).hom.hom.toAlgebra
  let : Algebra (Y.presheaf.stalk (f η)) X.functionField := (f.stalkMap η).hom.toAlgebra
  let : Algebra.EssFiniteType (Y.presheaf.stalk (f η)) X.functionField :=
    LocallyOfFiniteType.stalkMap f η
  let : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  have : Algebra.EssFiniteType Y.functionField (Y.presheaf.stalk (f η)) :=
    Algebra.EssFiniteType.of_surjective
      (Algebra.ofId Y.functionField (Y.presheaf.stalk (f η)))
      (Y.presheaf.stalkCongr (.of_eq hgen.symm)).commRingCatIsoToRingEquiv.surjective
  have : IsScalarTower Y.functionField (Y.presheaf.stalk (f η)) X.functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    exact dominantFunctionFieldMap_eq_stalkCongr_comp_stalkMap f
  exact Algebra.EssFiniteType.comp Y.functionField (Y.presheaf.stalk (f η)) X.functionField

/-- **Stacks Project, Tag 02R1.** Let `X` and `Y` be integral schemes locally of finite type
over a Chow base `(S, δ)` and let `f : X ⟶ Y` be a morphism over `S` with
`dim_δ X = dim_δ Y`. Then either `f(X)` is contained in a proper closed subscheme of `Y`, or
`f` is dominant and the extension of function fields `R(X)/R(Y)` is finite. -/
@[stacks 02R1]
theorem exists_properClosedSubscheme_or_finiteDimensional_functionField
    (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (hf : f ≫ sY = sX)
    (hdim : schemeDeltaDimension C sX = schemeDeltaDimension C sY) :
    (∃ (Z : Scheme.{u}) (i : Z ⟶ Y), IsClosedImmersion i ∧
        Set.range f.base ⊆ Set.range i.base ∧ Set.range i.base ≠ Set.univ) ∨
      (∃ hdom : IsDominant f,
        letI : IsDominant f := hdom
        letI : Algebra Y.functionField X.functionField :=
          (dominantFunctionFieldMap f).toAlgebra
        FiniteDimensional Y.functionField X.functionField) := by
  classical
  let : LocallyOfFiniteType (f ≫ sY) := by rw [hf]; infer_instance
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f sY
  by_cases hdom : IsDominant f
  · let : IsDominant f := hdom
    refine Or.inr ⟨hdom, ?_⟩
    let η := genericPoint X
    have hgen : f η = genericPoint Y := map_genericPoint_eq_genericPoint f
    -- the two delta-dimensions are the relative dimensions at the generic points
    have hdimX := schemeDeltaDimension_eq_genericPoint C sX
    have hdimY := schemeDeltaDimension_eq_genericPoint C sY
    rw [hdimX, hdimY] at hdim
    have hdimℤ : relativeDimension C.dimensionFunction sX η =
        relativeDimension C.dimensionFunction sY (genericPoint Y) :=
      WithBotTop.coe_injective hdim
    rw [← hgen, ← hf] at hdimℤ
    -- the base points agree, so the two transcendence degrees over the base agree
    let K := C.S.residueField (sY (f η))
    let L := Y.residueField (f η)
    let M := X.residueField η
    let : Algebra K L := (sY.residueFieldMap (f η)).hom.toAlgebra
    let : Algebra L M := (f.residueFieldMap η).hom.toAlgebra
    let : Algebra K M :=
      ((f.residueFieldMap η).hom.comp (sY.residueFieldMap (f η)).hom).toAlgebra
    let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let : Algebra.EssFiniteType K L :=
      residueField_essFiniteType_of_locallyOfFiniteType sY (f η)
    let : Algebra.EssFiniteType L M :=
      residueField_essFiniteType_of_locallyOfFiniteType f η
    have hcomp : (let : Algebra (C.S.residueField ((f ≫ sY) η)) M :=
          ((f ≫ sY).residueFieldMap η).hom.toAlgebra
        Algebra.trdeg (C.S.residueField ((f ≫ sY) η)) M) = Algebra.trdeg K M := by
      rw [show ((f ≫ sY).residueFieldMap η).hom =
        ((f.residueFieldMap η).hom).comp ((sY.residueFieldMap (f η)).hom) from
          congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp f sY η)]
      rfl
    have hnatKM : Cardinal.toNat (Algebra.trdeg K M) = Cardinal.toNat (Algebra.trdeg K L) := by
      have hcast : (Cardinal.toNat (let : Algebra (C.S.residueField ((f ≫ sY) η)) M :=
            ((f ≫ sY).residueFieldMap η).hom.toAlgebra
          Algebra.trdeg (C.S.residueField ((f ≫ sY) η)) M) : ℤ) =
          (Cardinal.toNat (Algebra.trdeg K L) : ℤ) :=
        Int.add_left_cancel (a := C.dimensionFunction (sY (f η))) hdimℤ
      rw [hcomp] at hcast
      exact_mod_cast hcast
    -- transcendence degree is additive in the tower, so `M/L` has degree zero
    have htrdeg : Algebra.trdeg L M = 0 := by
      have hadd := trdeg_add_eq K L (A := M)
      have hnatAdd := Cardinal.toNat_add (trdeg_lt_aleph0 K L) (trdeg_lt_aleph0 L M)
      have hnatZero : Cardinal.toNat (Algebra.trdeg L M) = 0 := by
        rw [← hadd, hnatAdd] at hnatKM; omega
      rcases Cardinal.toNat_eq_zero.mp hnatZero with hzero | hlarge
      · exact hzero
      · exact absurd hlarge (not_le_of_gt (trdeg_lt_aleph0 L M))
    -- the same holds for the extension of function fields, which is therefore finite
    let : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
    have : Algebra.EssFiniteType Y.functionField X.functionField :=
      essFiniteType_functionField f
    have : Algebra.IsAlgebraic Y.functionField X.functionField :=
      trdeg_eq_zero_iff.mp ((trdeg_functionField_eq_trdeg_residueField f).trans htrdeg)
    exact Algebra.finite_of_essFiniteType_of_isAlgebraic
  · -- if `f` is not dominant, the closure of its image is a proper closed subscheme
    refine Or.inl ?_
    let I := Scheme.IdealSheafData.vanishingIdeal (X := Y)
      ⟨closure (Set.range f.base), isClosed_closure⟩
    refine ⟨I.subscheme, I.subschemeι, inferInstance, ?_, ?_⟩
    · rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact subset_closure
    · rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      intro hrange
      exact hdom ⟨denseRange_iff_closure_range.mpr (by
        simpa [I, Scheme.IdealSheafData.coe_support_vanishingIdeal] using hrange)⟩

end Stacks.Chow

end
