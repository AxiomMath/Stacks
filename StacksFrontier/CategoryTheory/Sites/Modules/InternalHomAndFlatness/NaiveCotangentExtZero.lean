module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import StacksFrontier.Algebra.Homology.DerivedCategory.TwoTermExtZero
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent
import StacksCore.Tactic.StacksAttribute

/-!
# `Ext⁰` out of the naive cotangent complex of a polynomial presentation

Let `a : A ⟶ B` be a homomorphism of sheaves of commutative rings on a site, let `α : E ⟶ B` be
a polynomial presentation of `B` over `A` and let `𝒢` be a sheaf of `B`-modules. The naive
cotangent complex `NL(α)` is the two-term complex `I/I² ⟶ B ⊗_{A[E]} Ω_{A[E]/A}` in cohomological
degrees `-1` and `0`, so `Ext^i_B(NL(α), 𝒢)` vanishes for `i < 0` and

`Ext⁰_B(NL(α), 𝒢) = Hom_B(H⁰(NL(α)), 𝒢) = Hom_B(Ω_{B/A}, 𝒢)`.

## Main definitions

* `Stacks.SheafOfModules.presentationConormalCokernelIsoDifferentials`: the cokernel of the
  conormal map of the presentation is isomorphic to `Ω_{B/A}`.
* `Stacks.SheafOfModules.presentationNaiveCotangentObj`: `NL(α)` as an object of the derived
  category of sheaves of `B`-modules.
* `Stacks.SheafOfModules.presentationNaiveCotangentExt`: `Ext^i_B(NL(α), 𝒢)`.
* `Stacks.SheafOfModules.presentationNaiveCotangentExtZeroAddEquivCokernel`: the identification
  of `Ext⁰_B(NL(α), 𝒢)` with `Hom_B(coker(I/I² ⟶ B ⊗ Ω), 𝒢)`.
* `Stacks.SheafOfModules.presentationNaiveCotangentExtZeroAddEquiv`: the identification of
  `Ext⁰_B(NL(α), 𝒢)` with `Hom_B(Ω_{B/A}, 𝒢)`.

## Main results

* `Stacks.SheafOfModules.presentationNaiveCotangentComplex_eq_twoTermComplex`: `NL(α)` is the
  two-term complex of the conormal map of the presentation.
* `Stacks.SheafOfModules.presentationNaiveCotangentExt_eq_zero_of_neg`:
  `Ext^i_B(NL(α), 𝒢) = 0` for `i < 0`.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), `H⁰(NL(α)) = Ω_{B/A}`
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW), the naive cotangent
  complex of a homomorphism of sheaves of rings
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS), `Ext` between complexes
  with disjoint homology ranges
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (moduleOfDifferentialsOfSite)

universe v u w z t

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) (E : Functor Cᵒᵖ (Type w))
  (α : E ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom]
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]

/-! ### `NL(α)` as a two-term complex -/

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The naive cotangent complex of a polynomial presentation is the two-term complex of its
conormal map, with `I/I²` in degree `-1` and `B ⊗_{A[E]} Ω_{A[E]/A}` in degree `0`. -/
theorem presentationNaiveCotangentComplex_eq_twoTermComplex :
    presentationNaiveCotangentComplex.{v, u, w, z} J A B a E α =
      StacksDraft.TwoTermExt.twoTermComplex
        (presentationConormalSequence.{v, u, w, z} J A B a E α).f :=
  rfl

/-- The cokernel of the conormal map of a polynomial presentation is isomorphic to the sheaf of
relative differentials `Ω_{B/A}`. -/
noncomputable def presentationConormalCokernelIsoDifferentials :
    cokernel (presentationConormalSequence.{v, u, w, z} J A B a E α).f ≅
      moduleOfDifferentialsOfSite.{v, u, w, z} A B a :=
  (presentationNaiveCotangentComplexHomologyZeroIsoCokernel.{v, u, w, z} J A B a E α).symm ≪≫
    presentationNaiveCotangentComplexHomologyZeroIso.{v, u, w, z} J A B a E α

/-! ### `Ext` out of `NL(α)` -/

variable [HasDerivedCategory.{t}
  (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))]

/-- `NL(α)` as an object of the derived category of sheaves of `B`-modules. -/
noncomputable abbrev presentationNaiveCotangentObj :
    DerivedCategory
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
  DerivedCategory.Q.obj (presentationNaiveCotangentComplex.{v, u, w, z} J A B a E α)

variable (G : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))

/-- The extension group `Ext^i_B(NL(α), 𝒢)` of the naive cotangent complex of a polynomial
presentation by a sheaf of `B`-modules. -/
noncomputable abbrev presentationNaiveCotangentExt (i : ℤ) : Type _ :=
  DerivedCategory.Ext (presentationNaiveCotangentObj.{v, u, w, z, t} J A B a E α)
    ((DerivedCategory.singleFunctor _ 0).obj G) i

/-- The identification of `Ext⁰_B(NL(α), 𝒢)` with the group of homomorphisms to `𝒢` out of the
cokernel of the conormal map of the presentation, given by taking `H⁰`. -/
noncomputable def presentationNaiveCotangentExtZeroAddEquivCokernel :
    presentationNaiveCotangentExt.{v, u, w, z, t} J A B a E α G 0 ≃+
      (cokernel (presentationConormalSequence.{v, u, w, z} J A B a E α).f ⟶ G) :=
  StacksDraft.TwoTermExt.twoTermExtZeroAddEquiv
    (presentationConormalSequence.{v, u, w, z} J A B a E α).f G

/-- The identification of `Ext⁰_B(NL(α), 𝒢)` with `Hom_B(Ω_{B/A}, 𝒢)`, for `NL(α)` the naive
cotangent complex of a polynomial presentation of `B` over `A`. -/
@[stacks 08U8 "clause (2): the identification of the acting group Hom(H^0(NL(α)), G) = \
Hom(Omega_{B/A}, G) with Ext^0(NL(α), G), for NL(α) the naive cotangent complex of a polynomial \
presentation of a homomorphism of sheaves of rings on a site — the form the source's diagram \
takes after its own reduction to sheaves on one space. No hypothesis beyond the source. The \
remaining two links of the source's display, the adjunction Hom(Omega_{X_1/S_1}, g_* G_2) = \
Hom(g^* Omega_{X_1/S_1}, G_2) and the passage from NL(α) to Lg^* NL_{X_1/S_1}, are not proved \
here; clause (1) and the principal homogeneous space structure itself are elsewhere"]
noncomputable def presentationNaiveCotangentExtZeroAddEquiv :
    presentationNaiveCotangentExt.{v, u, w, z, t} J A B a E α G 0 ≃+
      (moduleOfDifferentialsOfSite.{v, u, w, z} A B a ⟶ G) :=
  (presentationNaiveCotangentExtZeroAddEquivCokernel.{v, u, w, z, t} J A B a E α G).trans
    (StacksDraft.TwoTermExt.precompAddEquiv
      (presentationConormalCokernelIsoDifferentials.{v, u, w, z} J A B a E α) G).symm

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `Ext^i_B(NL(α), 𝒢)` vanishes in negative degrees. -/
theorem presentationNaiveCotangentExt_eq_zero_of_neg {i : ℤ} (hi : i < 0)
    (ξ : presentationNaiveCotangentExt.{v, u, w, z, t} J A B a E α G i) : ξ = 0 :=
  StacksDraft.TwoTermExt.twoTermExt_eq_zero_of_neg
    (presentationConormalSequence.{v, u, w, z} J A B a E α).f G hi ξ

end Stacks.SheafOfModules

end
