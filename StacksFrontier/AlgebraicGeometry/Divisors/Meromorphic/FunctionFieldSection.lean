module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.ConstantOnIntegral
public import StacksFrontier.AlgebraicGeometry.Meromorphic.RegularSectionExistence

/-!
# The meromorphic section of the structure sheaf attached to a rational function

Let `X` be an integral scheme. A meromorphic section of `𝒪_X` is a global section of
`K_X(𝒪_X)`, and extension of scalars along `𝒪_X ⟶ K_X` takes `𝒪_X` to `K_X`
(`AlgebraicGeometry.unitIsoMeromorphicSectionSheafUnit`), so a meromorphic section of `𝒪_X` is
the same thing as a global section of the sheaf `K_X` of meromorphic functions. On an integral
scheme `K_X` is the constant sheaf on the function field (Stacks 01X5 part (1)), so every
rational function gives such a global section, and a nonzero one gives an *invertible* global
section, hence a regular meromorphic section of `𝒪_X` in the sense of Stacks 02OX.

This is the meromorphic section whose divisor is the principal divisor of the rational
function, and it is what makes the two denominator quotients of Stacks 02SW available for
`𝒪_X` with a rational function in place of a section of an invertible module.

## Main definitions

* `AlgebraicGeometry.functionFieldToTotalQuotientSheaf` — the morphism from the constant
  presheaf on the function field to the sheaf of meromorphic functions.
* `AlgebraicGeometry.meromorphicFunctionsSectionOfFunctionField` — a rational function, as a
  global section of `K_X` viewed as a module over itself.
* `AlgebraicGeometry.unitIsoOfFunctionFieldUnit` — a nonzero rational function, as an
  automorphism of `K_X` as a module over itself.
* `AlgebraicGeometry.meromorphicSectionOfFunctionField` — **the meromorphic section of `𝒪_X`
  attached to a unit of the function field.**

## Main results

* `AlgebraicGeometry.functionFieldToTotalQuotientSheaf_germ` — on the germ at the generic point
  of a section of `𝒪_X`, the comparison is the canonical map `𝒪_X ⟶ K_X`.
* `AlgebraicGeometry.functionFieldToTotalQuotientSheaf_app_injective` — it is injective on the
  sections over every nonempty open set.
* `AlgebraicGeometry.isRegularMeromorphicSection_meromorphicSectionOfFunctionField` — the
  section attached to a unit of the function field is regular.

## Implementation notes

The comparison with the constant sheaf is a *choice*
(`AlgebraicGeometry.totalQuotientSheafIsoConstant`), so the morphism out of the constant
presheaf is built from it and the sheafification map, and the only two of its properties used
are read off the characterisation the choice is packaged with: the value on a germ at the
generic point, and injectivity on sections. Injectivity is the statement that the sheafification
map is injective on a nonempty open set, which holds because the sieve on which two sections
with equal sheafifications agree is a covering sieve, and a covering sieve of a nonempty open
set of a topological space contains a nonempty member — so the two sections already agree.

Regularity is not proved sectionwise. Multiplication by the section attached to a unit of the
function field *is* the composite of two isomorphisms by construction, because the section is
defined as the image of that composite under `CategoryTheory.SheafOfModules.unitHomEquiv`; so
`Equiv.symm_apply_apply` returns the composite and the monomorphism is an instance.

## References

* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 02OX](https://stacks.math.columbia.edu/tag/02OX)
* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) [IsIntegral X]

/-- The sheaf of meromorphic functions of a scheme, read as a sheaf of (not necessarily
commutative) rings — the form in which the `SheafOfModules` API indexes modules over it. -/
abbrev meromorphicFunctionRingCatSheaf : Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
    X.totalQuotientSheaf

/-- The morphism from the constant presheaf on the function field to the sheaf of meromorphic
functions: the sheafification map followed by the inverse of the comparison of Stacks 01X5
part (1). -/
def functionFieldToTotalQuotientSheaf :
    (Functor.const (Opens X)ᵒᵖ).obj X.functionField ⟶ (totalQuotientSheaf X.sheaf).obj :=
  toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj X.functionField) ≫
    (totalQuotientSheafIsoConstant X).val.inv.hom

/-- On the germ at the generic point of a section of the structure sheaf, the comparison from
the constant presheaf on the function field is the canonical map `𝒪_X ⟶ K_X`. -/
theorem functionFieldToTotalQuotientSheaf_germ (U : X.Opens) (s : X.presheaf.obj (op U))
    (h : genericPoint X ∈ U) :
    (functionFieldToTotalQuotientSheaf X).app (op U)
        (X.presheaf.germ U (genericPoint X) h s) =
      (toTotalQuotientSheaf X.sheaf).hom.app (op U) s := by
  have he := (totalQuotientSheafIsoConstant X).property U s h
  change (totalQuotientSheafIsoConstant X).val.inv.hom.app (op U)
      ((toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (op U)
          (X.presheaf.germ U (genericPoint X) h s)) = _
  rw [← he]
  exact ConcreteCategory.congr_hom
    (congrArg (fun f => f.hom.app (op U)) (totalQuotientSheafIsoConstant X).val.hom_inv_id) _

/-- The comparison from the constant presheaf on the function field is injective on the
sections over every nonempty open set: two rational functions with the same sheafification
agree on a covering sieve, and a covering sieve of a nonempty open set has a nonempty
member. -/
theorem functionFieldToTotalQuotientSheaf_app_injective (U : X.Opens)
    (hU : (U : Set X).Nonempty) :
    Function.Injective ((functionFieldToTotalQuotientSheaf X).app (op U)) := by
  intro a b hab
  have h : (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (op U) a =
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (op U) b := by
    have hc (z) := ConcreteCategory.congr_hom
      (congrArg (fun q => q.hom.app (op U)) (totalQuotientSheafIsoConstant X).val.inv_hom_id) z
    exact (hc _).symm.trans
      ((congrArg (fun z => (totalQuotientSheafIsoConstant X).val.hom.hom.app (op U) z) hab).trans
        (hc _))
  obtain ⟨y, hy⟩ := hU
  obtain ⟨V, i, hi, _⟩ := (Opens.mem_grothendieckTopology X).mp
    (CategoryTheory.Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)) a b h) y hy
  exact hi

/-- A rational function, as a global section of the sheaf of meromorphic functions viewed as a
module over itself: on every open set, the value of the comparison from the constant presheaf,
which is compatible with restriction by naturality. -/
def meromorphicFunctionsSectionOfFunctionField (g : X.functionField) :
    (SheafOfModules.unit (meromorphicFunctionRingCatSheaf X)).sections :=
  PresheafOfModules.sectionsMk (fun U => (functionFieldToTotalQuotientSheaf X).app U g)
    fun {_ _} f =>
      (ConcreteCategory.congr_hom ((functionFieldToTotalQuotientSheaf X).naturality f) g).symm

/-- A unit of the function field, as an automorphism of the sheaf of meromorphic functions
viewed as a module over itself: multiplication by it, with multiplication by its inverse as the
inverse. -/
def unitIsoOfFunctionFieldUnit (g : X.functionFieldˣ) :
    SheafOfModules.unit (meromorphicFunctionRingCatSheaf X) ≅
      SheafOfModules.unit (meromorphicFunctionRingCatSheaf X) where
  hom := (SheafOfModules.unit (meromorphicFunctionRingCatSheaf X)).unitHomEquiv.symm
    (meromorphicFunctionsSectionOfFunctionField X (g : X.functionField))
  inv := (SheafOfModules.unit (meromorphicFunctionRingCatSheaf X)).unitHomEquiv.symm
    (meromorphicFunctionsSectionOfFunctionField X ((g⁻¹ : X.functionFieldˣ) : X.functionField))
  hom_inv_id := by
    apply (SheafOfModules.unit (meromorphicFunctionRingCatSheaf X)).unitHomEquiv.injective
    ext U
    change (1 * (functionFieldToTotalQuotientSheaf X).app U (g : X.functionField)) *
      (functionFieldToTotalQuotientSheaf X).app U
        ((g⁻¹ : X.functionFieldˣ) : X.functionField) = 1
    rw [one_mul, ← map_mul]
    simp
  inv_hom_id := by
    apply (SheafOfModules.unit (meromorphicFunctionRingCatSheaf X)).unitHomEquiv.injective
    ext U
    change (1 * (functionFieldToTotalQuotientSheaf X).app U
        ((g⁻¹ : X.functionFieldˣ) : X.functionField)) *
      (functionFieldToTotalQuotientSheaf X).app U (g : X.functionField) = 1
    rw [one_mul, ← map_mul]
    simp

/-- **The meromorphic section of `𝒪_X` attached to a unit of the function field.**
Multiplication by it is the automorphism of `K_X` given by that unit, followed by the
identification `K_X ≅ K_X(𝒪_X)` of
`AlgebraicGeometry.unitIsoMeromorphicSectionSheafUnit`. -/
def meromorphicSectionOfFunctionField (g : X.functionFieldˣ) :
    MeromorphicSection X.sheaf (SheafOfModules.unit X.ringCatSheaf) :=
  (meromorphicSectionSheaf X.sheaf (SheafOfModules.unit X.ringCatSheaf)).unitHomEquiv
    ((unitIsoOfFunctionFieldUnit X g).hom ≫ (unitIsoMeromorphicSectionSheafUnit X).hom)

/-- **The meromorphic section attached to a unit of the function field is regular**, in the
sense of Stacks 02OX: multiplication by it is a composite of two isomorphisms, hence a
monomorphism. -/
theorem isRegularMeromorphicSection_meromorphicSectionOfFunctionField (g : X.functionFieldˣ) :
    IsRegularMeromorphicSection X.sheaf (SheafOfModules.unit X.ringCatSheaf)
      (meromorphicSectionOfFunctionField X g) := by
  have h : (meromorphicSectionSheaf X.sheaf (SheafOfModules.unit X.ringCatSheaf)).unitHomEquiv.symm
      (meromorphicSectionOfFunctionField X g) =
      (unitIsoOfFunctionFieldUnit X g).hom ≫ (unitIsoMeromorphicSectionSheafUnit X).hom :=
    Equiv.symm_apply_apply _ _
  change Mono ((meromorphicSectionSheaf X.sheaf
    (SheafOfModules.unit X.ringCatSheaf)).unitHomEquiv.symm
      (meromorphicSectionOfFunctionField X g))
  rw [h]
  infer_instance

end AlgebraicGeometry
