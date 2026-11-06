module

public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafGeneral
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PointClosureAssociatedPoints

/-!
# The degree on the Picard group of a proper curve, and effective representatives

Let `Z` be a proper scheme of dimension at most one over a field `E`. The degree of invertible
modules, `deg ℒ = χ(ℒ) - χ(𝒪_Z)` ([Stacks, Tag 0AYR]), is an isomorphism invariant and additive
in the tensor product ([Stacks, Tag 0AYX]), so it is a homomorphism `Pic(Z) → ℤ`,
`Stacks.Picard.picardDegree`. The class of an effective Cartier divisor `D` has degree
`dim_E Γ(D, 𝒪_D)` ([Stacks, Tag 0AYY]).

If `Z` is moreover an integral curve of genus `g`, every class of degree at least `g` is the class
of an effective Cartier divisor.

## Main definitions

* `Stacks.Picard.picardDegree`: the degree homomorphism `Pic(Z) →+ ℤ`.

## Main results

* `Stacks.Picard.picardDegreeFun_picardClass`: the degree of a Picard class is the degree of any
  representative.
* `Stacks.Picard.picardDegree_divisorPicardClass`: `deg 𝒪_Z(D) = dim_E Γ(D, 𝒪_D)`.
* `Stacks.Picard.exists_divisorPicardClass_eq_of_genus_le`: classes of degree `≥ g` are
  effective.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.RingedSpace (structureIsSheaf)

universe u

namespace Stacks.Picard

variable {E : Type u} [Field E] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of E)) [IsProper f]
  (hdim : topologicalKrullDim Z ≤ 1)

/-- The degree of the chosen representative of a Picard class. -/
def picardDegreeFun (z : ofScheme Z) : ℤ :=
  @invertibleCurveDegree E _ Z f _ hdim (picardRepresentative Z.toRingedSpace z).obj
    (picardRepresentative Z.toRingedSpace z).property

/-- **The degree of a Picard class is the degree of any representative.** -/
theorem picardDegreeFun_picardClass (L : Z.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Z.presheaf (structureIsSheaf Z.toRingedSpace) L) :
    picardDegreeFun f hdim
        (Stacks.SheafOfModules.picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace) L hL) =
      @invertibleCurveDegree E _ Z f _ hdim L hL := by
  exact @invertibleCurveDegree_eq_of_iso E _ Z f _ hdim _ _
    (picardRepresentative Z.toRingedSpace _).property hL
    ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1
      (classOf_picardRepresentative Z.toRingedSpace (Stacks.SheafOfModules.picardClass
        Z.presheaf (structureIsSheaf Z.toRingedSpace) L hL))).some

/-- The degree is additive on Picard classes ([Stacks, Tag 0AYX]). -/
theorem picardDegreeFun_add (x y : ofScheme Z) :
    picardDegreeFun f hdim (x + y) = picardDegreeFun f hdim x + picardDegreeFun f hdim y := by
  set L : Z.Modules := (picardRepresentative Z.toRingedSpace x).obj
  set N : Z.Modules := (picardRepresentative Z.toRingedSpace y).obj
  have hL : Stacks.SheafOfModules.IsInvertible Z.presheaf (structureIsSheaf Z.toRingedSpace) L :=
    (picardRepresentative Z.toRingedSpace x).property
  have hN : Stacks.SheafOfModules.IsInvertible Z.presheaf (structureIsSheaf Z.toRingedSpace) N :=
    (picardRepresentative Z.toRingedSpace y).property
  have hLN := @Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ Z.presheaf
    (structureIsSheaf Z.toRingedSpace) _ _ _ _ hL hN
  have key : x + y = Stacks.SheafOfModules.picardClass Z.presheaf
      (structureIsSheaf Z.toRingedSpace) _ hLN := by
    conv_lhs => rw [← classOf_picardRepresentative Z.toRingedSpace x,
      ← classOf_picardRepresentative Z.toRingedSpace y]
    exact Stacks.SheafOfModules.picardClass_tensorSheaf _ _ _ _ hL hN hLN
  rw [key]
  refine (picardDegreeFun_picardClass f hdim _ hLN).trans ?_
  have : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L := hL
  have : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 N := hN
  have : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(Z.toRingedSpace).presheaf,
        (Z.toRingedSpace).IsSheaf⟩).obj (L)).obj (N))) := hLN
  exact invertibleCurveDegree_tensorSheaf_eq_add E f hdim L N

/-- **The degree homomorphism `Pic(Z) → ℤ`** of a proper scheme of dimension at most one over a
field. -/
def picardDegree : ofScheme Z →+ ℤ :=
  AddMonoidHom.mk' (picardDegreeFun f hdim) (picardDegreeFun_add f hdim)

/-- The degree homomorphism sends a Picard class to the degree of its chosen representative. -/
theorem picardDegree_apply (z : ofScheme Z) :
    picardDegree f hdim z = picardDegreeFun f hdim z := rfl

/-- **The degree of the class of an effective Cartier divisor `D` is `dim_E Γ(D, 𝒪_D)`.** -/
theorem picardDegree_divisorPicardClass (D : Z.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    letI : Algebra E Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of E)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    picardDegree f hdim (Stacks.Divisors.picardClass D) =
      (Module.finrank E Γ(D.subscheme, ⊤) : ℤ) := by
  exact (picardDegreeFun_picardClass f hdim _ _).trans
    (invertibleCurveDegree_invertibleSheaf_eq_finrank_globalSections E f hdim D)

/-- **Classes of degree at least the genus are effective.** On a proper integral curve of genus
`g` over a field, every Picard class of degree `≥ g` is the class `[𝒪_Z(D)]` of an effective
Cartier divisor `D`. -/
theorem exists_divisorPicardClass_eq_of_genus_le [IsCurve E f] (z : ofScheme Z)
    (hz : (genus f : ℤ) ≤ picardDegree f hdim z) :
    ∃ (D : Z.IdealSheafData) (_ : Stacks.Divisors.IsEffectiveCartierDivisor D),
      Stacks.Divisors.picardClass D = z := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
  set M : Z.Modules := (picardRepresentative Z.toRingedSpace z).obj
  have hM : Stacks.SheafOfModules.IsInvertible Z.presheaf (structureIsSheaf Z.toRingedSpace) M :=
    (picardRepresentative Z.toRingedSpace z).property
  have : Stacks.Ample.IsInvertibleModule Z M := hM
  have : SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property M := hM
  have hRR := finrank_cohomologyOverField_zero_sub_one_eq E f hdim M hM
  have hO := zero_lt_finrank_cohomologyOverField_zero_unit E f
  have hdeg : @invertibleCurveDegree E _ Z f _ hdim M hM = picardDegree f hdim z := rfl
  have hpos : 0 < Module.finrank E (cohomologyOverField E f M 0) := by omega
  obtain ⟨s, hs⟩ := exists_section_of_finrank_pos E f M hpos
  have hne := nonempty_nonvanishingLocus_of_eval_top_ne_zero M s hs
  have heq : Stacks.NonvanishingTrivialize.nonvanishingLocus Z.toRingedSpace M s =
      Stacks.SheafOfModules.nonvanishingLocus (X := Z.toRingedSpace) M s := by
    rw [Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq]
    exact (Stacks.NonvanishingSpelling.nonvanishingLocus_symm_eq Z M _).symm.trans
      (congrArg _ ((Stacks.NonvanishingSpelling.sectionsEquiv Z M).symm_apply_apply s))
  have hopen : IsOpen (Stacks.SheafOfModules.nonvanishingLocus (X := Z.toRingedSpace) M s) := by
    rw [Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq]
    exact (Stacks.NonvanishingOpen.nonvanishingOpen Z M _).isOpen
  obtain ⟨D, hD, -, ⟨e⟩⟩ := exists_effectiveCartierDivisor_of_nonvanishing (E := ∅) M s
    (Set.empty_subset _) (by
      rw [schemeAssociatedPoints_eq_singleton_genericPoint, Set.singleton_subset_iff, heq]
      exact ((genericPoint_spec Z).mem_open_set_iff hopen).2 (by simpa using hne))
  refine ⟨D, hD, ?_⟩
  rw [← classOf_picardRepresentative Z.toRingedSpace z]
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨e.symm⟩

end Stacks.Picard

end
