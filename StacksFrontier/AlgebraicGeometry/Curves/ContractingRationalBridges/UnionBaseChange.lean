module

public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.BaseChangeDegree
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.SubcurveDegreeSum
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.ComponentGeometricallyReduced
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Basic

/-!
# The absolute and the relative complementary degree

The degree clause of `AlgebraicGeometry.IsRationalBridge` is a dimension over the ring of global
functions of the subcurve, while the bookkeeping of
`Stacks.Curves.sum_finrank_sup_complementaryCurveIdeal_eq` is in dimensions over the ground field.
This file relates the two by the tower formula.

## Main results

* `AlgebraicGeometry.finrank_structureSheafCohomology_zero_intersection_eq_mul`: for a closed
  subscheme `Z` of a proper curve over `k` whose global functions form a field,
  `h⁰(Z ∩ X'_Z) = h⁰(Z) · deg_{Γ(Z)}(Z ∩ X'_Z)`.

## References

* [Stacks Project, Tag 0E65](https://stacks.math.columbia.edu/tag/0E65)
* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData
open Stacks.Curves

universe u

namespace AlgebraicGeometry

/-- The two algebra structures on the global functions of the intersection of a closed subscheme
with the closure of its complement — over the ground field and over the global functions of the
subscheme — form a tower. -/
theorem isScalarTower_globalSections_intersection {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (J : X.IdealSheafData)
    [QuasiCompact (Scheme.Opens.ι J.support.compl)] :
    letI : Algebra k Γ(J.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (J.subschemeι ≫ f).appTop).hom.toAlgebra
    letI : Algebra k Γ((intersectionWithComplementaryCurveIdeal J).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((intersectionWithComplementaryCurveIdeal J).subschemeι ≫ f).appTop).hom.toAlgebra
    letI : Algebra Γ(J.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal J).subscheme, ⊤) :=
      (Scheme.IdealSheafData.inclusion
        (le_sup_left : J ≤ intersectionWithComplementaryCurveIdeal J)).appTop.hom.toAlgebra
    IsScalarTower k Γ(J.subscheme, ⊤)
      Γ((intersectionWithComplementaryCurveIdeal J).subscheme, ⊤) := by
  let : Algebra k Γ(J.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (J.subschemeι ≫ f).appTop).hom.toAlgebra
  let : Algebra k Γ((intersectionWithComplementaryCurveIdeal J).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      ((intersectionWithComplementaryCurveIdeal J).subschemeι ≫ f).appTop).hom.toAlgebra
  let : Algebra Γ(J.subscheme, ⊤)
      Γ((intersectionWithComplementaryCurveIdeal J).subscheme, ⊤) :=
    (Scheme.IdealSheafData.inclusion
      (le_sup_left : J ≤ intersectionWithComplementaryCurveIdeal J)).appTop.hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  have hfac : (intersectionWithComplementaryCurveIdeal J).subschemeι ≫ f =
      Scheme.IdealSheafData.inclusion
        (le_sup_left : J ≤ intersectionWithComplementaryCurveIdeal J) ≫ (J.subschemeι ≫ f) := by
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  show ((Scheme.ΓSpecIso (.of k)).inv ≫
    ((intersectionWithComplementaryCurveIdeal J).subschemeι ≫ f).appTop).hom x = _
  rw [hfac, Scheme.Hom.comp_appTop]
  rfl


/-- **The degree of the intersection of a closed subscheme with the closure of its complement is
the degree of the subscheme times the relative degree of the intersection.** The relative degree
is the quantity clause (4) of `AlgebraicGeometry.IsRationalBridge` constrains to be two, and the
two absolute degrees are the quantities the bookkeeping of
`Stacks.Curves.sum_finrank_sup_complementaryCurveIdeal_eq` is phrased in. This is the tower
formula, the global functions of an integral closed subscheme proper over `k` forming a finite
field extension of `k`. -/
theorem finrank_structureSheafCohomology_zero_intersection_eq_mul {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (J : X.IdealSheafData)
    [IsIntegral J.subscheme] [QuasiCompact (Scheme.Opens.ι J.support.compl)] :
    letI : Algebra Γ(J.subscheme, ⊤)
        Γ((intersectionWithComplementaryCurveIdeal J).subscheme, ⊤) :=
      (Scheme.IdealSheafData.inclusion
        (le_sup_left : J ≤ intersectionWithComplementaryCurveIdeal J)).appTop.hom.toAlgebra
    Module.finrank k (structureSheafCohomology
        ((intersectionWithComplementaryCurveIdeal J).subschemeι ≫ f) 0)
      = Module.finrank k (structureSheafCohomology (J.subschemeι ≫ f) 0) *
        Module.finrank Γ(J.subscheme, ⊤)
          Γ((intersectionWithComplementaryCurveIdeal J).subscheme, ⊤) := by
  have hprop : IsProper (J.subschemeι ≫ f) := inferInstance
  let : Field Γ(J.subscheme, ⊤) :=
    (isField_of_universallyClosed k (J.subschemeι ≫ f)).toField
  let : Algebra k Γ(J.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (J.subschemeι ≫ f).appTop).hom.toAlgebra
  let : Algebra k Γ((intersectionWithComplementaryCurveIdeal J).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      ((intersectionWithComplementaryCurveIdeal J).subschemeι ≫ f).appTop).hom.toAlgebra
  let : Algebra Γ(J.subscheme, ⊤)
      Γ((intersectionWithComplementaryCurveIdeal J).subscheme, ⊤) :=
    (Scheme.IdealSheafData.inclusion
      (le_sup_left : J ≤ intersectionWithComplementaryCurveIdeal J)).appTop.hom.toAlgebra
  have : Module.Finite k Γ(J.subscheme, ⊤) :=
    RingHom.Finite.comp (finite_appTop_of_universallyClosed k (J.subschemeι ≫ f))
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.finite
  have := isScalarTower_globalSections_intersection f J
  rw [finrank_structureSheafCohomology_zero_eq_finrank_globalSections k
      ((intersectionWithComplementaryCurveIdeal J).subschemeι ≫ f),
    finrank_structureSheafCohomology_zero_eq_finrank_globalSections k (J.subschemeι ≫ f)]
  exact (Module.finrank_mul_finrank k Γ(J.subscheme, ⊤)
    Γ((intersectionWithComplementaryCurveIdeal J).subscheme, ⊤)).symm


end AlgebraicGeometry

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- **Over a separably closed field, interchangeable components of a genus-zero subcurve whose own
complementary degree is twice its degree have complementary degree exactly two.**

The bookkeeping `Stacks.Curves.sum_finrank_sup_complementaryCurveIdeal_eq` says the complementary
degrees of the components sum to twice their number, each component having `h⁰ = 1` over a
separably closed field; the hypothesis `hsym` that they are all equal then pins each at two. That
hypothesis is the symmetry input of [Stacks, Tag 0E65] and nothing weaker will do: without it the
sum alone is satisfied by a chain of three components with complementary degrees `(1, 4, 1)`. -/
theorem finrank_sup_complementaryCurveIdeal_component_eq_two [IsSepClosed k]
    (hX_equidimensional : Equidimensional X) (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme]
    (hY_equidimensional : Equidimensional I.subscheme)
    (hY_dimension : topologicalKrullDim I.subscheme = 1)
    (Λ : Finset (Set X))
    (hΛ : ∀ Z : Set X, Z ∈ Λ ↔ Z ∈ irreducibleComponents X ∧ Z ⊆ (I.support : Set X))
    (hZred : ∀ Z ∈ Λ, IsReduced (vanishingIdeal (Closeds.closure Z)).subscheme)
    (hZeq : ∀ Z ∈ Λ, Equidimensional (vanishingIdeal (Closeds.closure Z)).subscheme)
    (hZdim : ∀ Z ∈ Λ,
      topologicalKrullDim (vanishingIdeal (Closeds.closure Z)).subscheme = 1)
    (hgenus : genus (I.subschemeι ≫ (X ↘ Spec (.of k))) = 0)
    (hdeg : Module.finrank k (structureSheafCohomology
        ((I ⊔ complementaryCurveIdeal I).subschemeι ≫ (X ↘ Spec (.of k))) 0)
      = 2 * Module.finrank k (structureSheafCohomology
          (I.subschemeι ≫ (X ↘ Spec (.of k))) 0))
    (hsym : ∀ Z ∈ Λ, ∀ W ∈ Λ,
      Module.finrank k (structureSheafCohomology
          ((vanishingIdeal (Closeds.closure Z) ⊔
            complementaryCurveIdeal (vanishingIdeal (Closeds.closure Z))).subschemeι ≫
              (X ↘ Spec (.of k))) 0)
        = Module.finrank k (structureSheafCohomology
          ((vanishingIdeal (Closeds.closure W) ⊔
            complementaryCurveIdeal (vanishingIdeal (Closeds.closure W))).subschemeι ≫
              (X ↘ Spec (.of k))) 0))
    {Z₀ : Set X} (hZ₀ : Z₀ ∈ Λ) :
    Module.finrank k (structureSheafCohomology
        ((vanishingIdeal (Closeds.closure Z₀) ⊔
          complementaryCurveIdeal (vanishingIdeal (Closeds.closure Z₀))).subschemeι ≫
            (X ↘ Spec (.of k))) 0) = 2 := by
  classical
  have hunion := eq_union_irreducibleComponents hX_equidimensional hX_dimension hX_nodal I
    hY_equidimensional hY_dimension
  rw [Scheme.IdealSheafData.vanishingIdeal_iSup] at hunion
  have hI : I = Λ.inf fun Z : Set X => vanishingIdeal (Closeds.closure Z) := by
    rw [hunion, Finset.inf_eq_iInf, iInf_subtype]
    simp only [hΛ]
  -- each component has `h⁰ = 1` over a separably closed field
  have hone : ∀ Z ∈ Λ, Module.finrank k (structureSheafCohomology
      ((vanishingIdeal (Closeds.closure Z)).subschemeι ≫ (X ↘ Spec (.of k))) 0) = 1 :=
    fun Z hZ => finrank_structureSheafCohomology_zero_vanishingIdeal_component_eq_one
      hX_equidimensional hX_dimension hX_nodal ((hΛ Z).mp hZ).1
  -- each component has genus zero, being a closed subcurve of one
  have hgenusZ : ∀ Z ∈ Λ, genus ((vanishingIdeal (Closeds.closure Z)).subschemeι ≫
      (X ↘ Spec (.of k))) = 0 := by
    intro Z hZ
    have hins : I = vanishingIdeal (Closeds.closure Z) ⊓
        (Λ.erase Z).inf fun W : Set X => vanishingIdeal (Closeds.closure W) := by
      rw [hI]
      conv_lhs => rw [← Finset.insert_erase hZ]
      rw [Finset.inf_insert]
    have : IsReduced (vanishingIdeal (Closeds.closure Z)).subscheme := hZred Z hZ
    have hint := isZero_structureSheafCohomology_of_intersection_le hX_equidimensional
      hX_dimension hX_nodal (vanishingIdeal (Closeds.closure Z)) (hZeq Z hZ) (hZdim Z hZ)
      (vanishingIdeal (Closeds.closure Z) ⊔
        (Λ.erase Z).inf fun W : Set X => vanishingIdeal (Closeds.closure W))
      (by
        show vanishingIdeal (Closeds.closure Z) ⊔
          complementaryCurveIdeal (vanishingIdeal (Closeds.closure Z)) ≤ _
        refine sup_le_sup_left (Finset.le_inf fun W hW => ?_) _
        refine (complementaryCurveIdeal_vanishingIdeal_eq_inf hX_nodal I Λ hΛ hZ).le.trans ?_
        exact inf_le_of_right_le (Finset.inf_le hW)) 1 one_pos
    have hle := genus_add_le_genus_union k (X ↘ Spec (.of k))
      (vanishingIdeal (Closeds.closure Z))
      ((Λ.erase Z).inf fun W : Set X => vanishingIdeal (Closeds.closure W))
      hint
    rw [← hins, hgenus] at hle
    omega
  have hsum := sum_finrank_sup_complementaryCurveIdeal_eq hX_equidimensional hX_dimension
    hX_nodal I hY_equidimensional hY_dimension Λ hΛ hZred hZeq hZdim hgenus hgenusZ
  rw [Finset.sum_congr rfl hone, hdeg, Finset.sum_const, smul_eq_mul, mul_one] at hsum
  rw [Finset.sum_congr rfl (fun Z hZ => hsym Z hZ Z₀ hZ₀), Finset.sum_const,
    smul_eq_mul] at hsum
  have hpos : 0 < Λ.card := Finset.card_pos.mpr ⟨Z₀, hZ₀⟩
  have := hsum
  rcases Nat.eq_zero_or_pos (Module.finrank k (structureSheafCohomology
      ((vanishingIdeal (Closeds.closure Z₀) ⊔
        complementaryCurveIdeal (vanishingIdeal (Closeds.closure Z₀))).subschemeι ≫
          (X ↘ Spec (.of k))) 0)) with h | h
  · rw [h] at this
    omega
  · have hmul : Λ.card * Module.finrank k (structureSheafCohomology
        ((vanishingIdeal (Closeds.closure Z₀) ⊔
          complementaryCurveIdeal (vanishingIdeal (Closeds.closure Z₀))).subschemeι ≫
            (X ↘ Spec (.of k))) 0) = Λ.card * 2 := by omega
    exact Nat.eq_of_mul_eq_mul_left hpos hmul

end Stacks.Curves

end
