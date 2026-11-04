module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegree
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertAbelMapDegree
public import StacksFrontier.AlgebraicGeometry.Picard.CurveDegreeHom

/-!
# Picard classes of degree at least the genus are effective

On an integral scheme proper of dimension at most one over a field whose global functions are
the constants, an invertible module of degree at least the genus has a nonzero section
(the existence half of Riemann-Roch), and so its class is the class of an effective Cartier
divisor finite locally free over the field of the same degree.

## Main results

* `AlgebraicGeometry.exists_section_ne_zero_of_genus_le_invertibleCurveDegree`: the nonzero
  section.
* `AlgebraicGeometry.exists_isEffectiveCartierDivisor_picardClass_eq`: the effective divisor.

## Implementation notes

The degree is `χ(ℒ) - χ(𝒪_X)`, so with `H^i = 0` for `i ≥ 2` (Tag 02UZ) it reads
`deg ℒ = h⁰(ℒ) - h¹(ℒ) - 1 + g`, whence `deg ℒ ≥ g` forces `h⁰(ℒ) ≥ 1`. The divisor is the zero
scheme of the section, an effective Cartier divisor because `X` is integral; its degree is read
off its Picard class by Tag 0AYY.

## References

* [Stacks Project, Tag 0BS6](https://stacks.math.columbia.edu/tag/0BS6)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 0AYY](https://stacks.math.columbia.edu/tag/0AYY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The genus is the dimension of the first cohomology of the structure sheaf, read in the
`AlgebraicGeometry.cohomologyOverField` spelling that the degree uses. -/
theorem genus_eq_finrank_cohomologyOverField_unit_one' :
    genus f = Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) :=
  (structureSheafCohomologyIsoCohomologyOverField k f 1).toLinearEquiv.finrank_eq


/-- **A module whose space of global sections is nonzero has a nonzero global section.** -/
lemma exists_eval_top_ne_zero_of_nontrivial_h0 (L : X.Modules)
    (h : Nontrivial (cohomologyOverField k f L 0)) :
    ∃ s : L.sections, s.eval (Opposite.op ⊤) ≠ 0 := by
  have := h
  have : Nontrivial Γ(L, ⊤) :=
    (cohomologyOverFieldZeroEquivSections k f L).injective.nontrivial
  obtain ⟨t, ht⟩ := exists_ne (0 : Γ(L, ⊤))
  refine ⟨Stacks.PresheafOfModules.sectionOfTop L.val t, ?_⟩
  rw [show (Stacks.PresheafOfModules.sectionOfTop L.val t).eval (Opposite.op ⊤) = t from
    Stacks.PresheafOfModules.sectionOfTop_val_top L.val t]
  exact ht

variable [IsProper f] (hdim : topologicalKrullDim X ≤ 1)

include hdim in
/-- On a scheme of dimension at most one proper over a field, all cohomology above degree one
vanishes. This is Tag 02UZ specialised to `d = 1`. -/
theorem isZero_cohomologyOverField_of_two_le' (F : X.Modules) (m : ℕ) (hm : 2 ≤ m) :
    IsZero (cohomologyOverField k f F m) :=
  isZero_cohomologyOverField_of_topologicalKrullDim_le k f F (d := 1) (by simpa using hdim)
    (by omega)

/-- **The dimension count of the Riemann-Roch formula.** On a proper scheme of dimension at most
one over a field whose only global functions are the constants, an invertible module of degree at
least the genus has `h⁰(ℒ) ≥ 1 + h¹(ℒ)`. -/
theorem one_le_finrank_h0_of_genus_le_invertibleCurveDegree
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : (genus f : ℤ) ≤ @invertibleCurveDegree k _ X f _ hdim L hL) :
    1 + Module.finrank k (cohomologyOverField k f L 1) ≤
      Module.finrank k (cohomologyOverField k f L 0) := by
  have hdegeq := invertibleCurveDegree_eq_sub_of_isZero k f hdim L
    (isZero_cohomologyOverField_of_two_le' k f hdim L)
    (isZero_cohomologyOverField_of_two_le' k f hdim (SheafOfModules.unit X.ringCatSheaf))
  rw [hdegeq, finrank_cohomologyOverField_unit_zero_eq_one f,
    ← genus_eq_finrank_cohomologyOverField_unit_one' k f] at hdeg
  omega

/-- **An invertible module of degree at least the genus has a nonzero global section.** This is
the existence half of the Riemann-Roch formula on a proper scheme of dimension at most one over a
field whose only global regular functions are the constants. -/
theorem exists_section_ne_zero_of_genus_le_invertibleCurveDegree
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : (genus f : ℤ) ≤ @invertibleCurveDegree k _ X f _ hdim L hL) :
    ∃ s : L.sections, s.eval (op ⊤) ≠ 0 :=
  exists_eval_top_ne_zero_of_nontrivial_h0 k f L
    (Module.nontrivial_of_finrank_pos (R := k)
      (M := (cohomologyOverField k f L 0 : Type u)) (by
        have := one_le_finrank_h0_of_genus_le_invertibleCurveDegree
          k f hdim L hdeg
        omega))

/-- **A Picard class of degree at least the genus is the class of an effective Cartier divisor.**
On an integral scheme proper of dimension at most one over a field `k` whose only global
functions are the constants, every Picard class `c` with `deg c ≥ g` is `[𝒪_X(D)]` for an
effective Cartier divisor `D` finite locally free over `k` of degree `deg c`. -/
theorem exists_isEffectiveCartierDivisor_picardClass_eq [IsIntegral X]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (c : Stacks.Picard.ofScheme X)
    (hc : (genus f : ℤ) ≤ invertibleCurveDegreeHom k f hdim c) :
    ∃ (D : X.IdealSheafData) (_ : Stacks.Divisors.IsEffectiveCartierDivisor D) (d : ℕ),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.subschemeι ≫ f) d ∧
      (d : ℤ) = invertibleCurveDegreeHom k f hdim c ∧ Stacks.Divisors.picardClass D = c := by
  set L := Stacks.Picard.picardRepresentative X.toRingedSpace c
  have hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L.obj := L.property
  obtain ⟨s, hs⟩ := exists_section_ne_zero_of_genus_le_invertibleCurveDegree k f hdim L.obj hc
  have hL' : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L.obj := hL
  set D := zeroScheme X L.obj (s.eval (op ⊤))
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor D :=
    isEffectiveCartierDivisor_zeroScheme_of_ne_zero L.obj (s.eval (op ⊤)) hs
  have hreg : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s :=
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X L.obj s).1 hcart
  let : Algebra k Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  have hrank := isFiniteLocallyFreeOfRank_divisorSubscheme k f hdim D
  have hclass : Stacks.Divisors.picardClass D = c := by
    refine Eq.trans ?_ (Stacks.Picard.classOf_picardRepresentative X.toRingedSpace c)
    exact ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
      ⟨(invertibleSheafIsoZeroSchemeOfIsRegularSection L.obj s hreg).symm⟩)
  refine ⟨D, hcart, _, hrank, ?_, hclass⟩
  rw [← hclass]
  exact (invertibleCurveDegreeHom_picardClass_of_isFiniteLocallyFreeOfRank k f hdim D _).symm

end AlgebraicGeometry

end
