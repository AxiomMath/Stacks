module

public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtension.OfDifferentialsExtensionConormal
public import StacksFrontier.AlgebraicGeometry.Thickenings.LineBundleLiftNondegenerate
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationOfDifferentialsExtension
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic.ExtOneAndVanishing

/-!
# Every Kodaira–Spencer class of a smooth proper scheme over a field comes from a deformation

Let `X` be a smooth proper scheme over a field `k`. Every class
`α ∈ Ext¹_{𝒪_X}(Ω_{X/k}, 𝒪_X)` is the Kodaira–Spencer class of a first-order deformation `X'` of
`X` over `k[ε]`: the class of the conormal sequence `0 ⟶ 𝒞_{X/X'} ⟶ i^*Ω_{X'/k} ⟶ Ω_{X/k} ⟶ 0`,
read in `Ext¹(Ω_{X/k}, 𝒪_X)` through an isomorphism `𝒞_{X/X'} ≅ 𝒪_X`.

The deformation is built from an extension `0 ⟶ 𝒪_X ⟶ 𝓔 ⟶ Ω_{X/k} ⟶ 0` of class `α`:
`𝒪_{X'} = 𝒪_X ×_{Ω_{X/k}} 𝓔` (`Deformation.Examples.differentialsExtensionDeformation`), whose
conormal sequence maps to the given extension by the identity on both ends
(`Stacks.Thickenings.DifferentialsExtension.extClass_comp_thickeningConormalHom`).

## Main results

* `Deformation.Examples.exists_schemeDeformation_kodairaSpencerClass_eq`.

## Implementation notes

Properness is not used by the construction. It is assumed because
`Stacks.Thickenings.LineBundleLift.kodairaSpencerClassOf`, in whose terms the statement is made, is
declared under `[IsProper f]`.

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
* [Stacks Project, Tag 06AA](https://stacks.math.columbia.edu/tag/06AA)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open Stacks.Thickenings Stacks.Thickenings.DifferentialsExtension
open Stacks.Thickenings.LineBundleLift (conormalModule kodairaSpencerClassOf)

universe u

namespace Deformation.Examples

attribute [local instance] deformationSpecialMap_isClosedImmersion

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- `kodairaSpencerClassOf f i q hq` is the class of the conormal sequence of `i` over `q`, read
along the identification of `Ω_{X/k}` for the two spellings `f` and `i ≫ q`. -/
theorem kodairaSpencerClassOf_eq (f : X ⟶ Spec (.of k)) [IsProper f]
    [AlgebraicGeometry.Smooth f]
    {X' : Scheme.{u}} (i : X ⟶ X') [IsImmersion i] (q : X' ⟶ Spec (.of k)) (hq : i ≫ q = f)
    (hsm : AlgebraicGeometry.Smooth (i ≫ q)) :
    kodairaSpencerClassOf f i q hq =
      (Ext.mk₀ (eqToHom (congrArg Scheme.Hom.relativeDifferentials hq.symm))).comp
        (Stacks.ConormalSequenceRight.conormalShortComplex_shortExact i q hsm).extClass
        (zero_add 1) := by
  subst hq
  rw [eqToHom_refl]
  exact (Ext.mk₀_id_comp _).symm

/-- **Every class of `Ext¹(Ω_{X/k}, 𝒪_X)` is the Kodaira–Spencer class of a first-order
deformation**, with the closed immersion `X ⟶ X'` followed by `X' ⟶ Spec k[ε] ⟶ Spec k` as the
structure morphism. -/
theorem exists_schemeDeformation_kodairaSpencerClass_eq_of_toBase (f : X ⟶ Spec (.of k))
    [IsProper f] [AlgebraicGeometry.Smooth f]
    (α : Ext.{u} (Scheme.Hom.relativeDifferentials f) (SheafOfModules.unit X.ringCatSheaf) 1) :
    ∃ (P : SchemeDeformationCategory (Λ := k) (k := k) (Over.mk f))
      (_ : P.base = Deformation.artinianDualNumbers.{u, u, u} k k)
      (q : P.scheme ⟶ Spec (.of k)) (hq : P.specialMap ≫ q = f)
      (ψ : conormalModule P.specialMap ≅ SheafOfModules.unit X.ringCatSheaf),
      q = P.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap k P.base)) ∧
      (kodairaSpencerClassOf f P.specialMap q hq).comp (Ext.mk₀ ψ.hom) (add_zero 1) = α := by
  obtain ⟨E, j, p, w, hT, rfl⟩ :=
    (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum _ _ _).1 α
  have hiso : IsIso (thickeningConormalHom w hT) := isIso_thickeningConormalHom w hT
  have := isClosedImmersion_differentialsThickeningι w hT
  refine ⟨differentialsExtensionDeformation w hT, rfl, differentialsThickeningToBase w hT,
    differentialsThickeningι_comp_toBase w hT, @asIso _ _ _ _ (thickeningConormalHom w hT) hiso,
    (thickeningToDualNumbers_comp_structure w hT).symm, ?_⟩
  have hsm : AlgebraicGeometry.Smooth
      (differentialsThickeningι w hT ≫ differentialsThickeningToBase w hT) :=
    Eq.mpr (congrArg AlgebraicGeometry.Smooth (differentialsThickeningι_comp_toBase w hT))
      inferInstance
  change (kodairaSpencerClassOf f (differentialsThickeningι w hT)
      (differentialsThickeningToBase w hT) (differentialsThickeningι_comp_toBase w hT)).comp
      (Ext.mk₀ (thickeningConormalHom w hT)) (add_zero 1) = hT.extClass
  rw [kodairaSpencerClassOf_eq f _ _ _ hsm]
  refine (Ext.comp_assoc_of_third_deg_zero _ _ _ _).trans ?_
  refine (congrArg (fun z => Ext.comp (Ext.mk₀ (eqToHom (congrArg Scheme.Hom.relativeDifferentials
    (differentialsThickeningι_comp_toBase w hT).symm))) z (zero_add 1))
      (extClass_comp_thickeningConormalHom w hT hsm)).trans ?_
  refine (Ext.mk₀_comp_mk₀_assoc _ _ _).trans ?_
  refine (congrArg (fun φ => (Ext.mk₀ φ).comp hT.extClass (zero_add 1))
    ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).trans ?_
  exact Ext.mk₀_id_comp _

/-- **Every class of `Ext¹(Ω_{X/k}, 𝒪_X)` is the Kodaira–Spencer class of a first-order
deformation of `X` over `k[ε]`.** For `X` smooth and proper over a field `k` and
`α ∈ Ext¹_{𝒪_X}(Ω_{X/k}, 𝒪_X)` there is a deformation `X'` of `X` over the dual numbers
`k[ε]` (`Deformation.artinianDualNumbers k k`), a structure morphism `X' ⟶ Spec k` extending
that of `X`, and an isomorphism `ψ : 𝒞_{X/X'} ≅ 𝒪_X` carrying the class of the conormal sequence
`0 ⟶ 𝒞_{X/X'} ⟶ i^*Ω_{X'/k} ⟶ Ω_{X/k} ⟶ 0` to `α`. -/
theorem exists_schemeDeformation_kodairaSpencerClass_eq (f : X ⟶ Spec (.of k))
    [IsProper f] [AlgebraicGeometry.Smooth f]
    (α : Ext.{u} (Scheme.Hom.relativeDifferentials f) (SheafOfModules.unit X.ringCatSheaf) 1) :
    ∃ (P : SchemeDeformationCategory (Λ := k) (k := k) (Over.mk f))
      (_ : P.base = Deformation.artinianDualNumbers.{u, u, u} k k)
      (q : P.scheme ⟶ Spec (.of k)) (hq : P.specialMap ≫ q = f)
      (ψ : conormalModule P.specialMap ≅ SheafOfModules.unit X.ringCatSheaf),
      (kodairaSpencerClassOf f P.specialMap q hq).comp (Ext.mk₀ ψ.hom) (add_zero 1) = α := by
  obtain ⟨P, hP, q, hq, ψ, -, h⟩ := exists_schemeDeformation_kodairaSpencerClass_eq_of_toBase f α
  exact ⟨P, hP, q, hq, ψ, h⟩

end Deformation.Examples

end
