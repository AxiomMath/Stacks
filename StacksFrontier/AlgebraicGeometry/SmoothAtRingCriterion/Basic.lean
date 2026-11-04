module

public import StacksFrontier.RingTheory.Smooth.SmoothAt
public import Mathlib.RingTheory.Smooth.Locus
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.StandardSmooth
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Condition (1) of Tag 01V9 at the level of rings

For `f : X ⟶ S` locally of finite presentation, condition (1) of Stacks Tag 01V9, smoothness of
`f` at `x`, is `Algebra.IsSmoothAt` of the ring map on any affine neighbourhoods of `x` and of
`f x`: formal smoothness of the localization of `Γ(X, U)` at the prime of `x` over `Γ(S, V)`.

## Main results

* `Stacks.SmoothAtRingCriterion.isSmoothAt_of_exists_notMem_smooth`: a ring map that becomes
  smooth after inverting some element outside a prime is smooth at that prime.
* `Stacks.SmoothAtRingCriterion.condition1_iff_isSmoothAt_appLE`: condition (1) of Tag 01V9 is
  `Algebra.IsSmoothAt` of `AlgebraicGeometry.Scheme.Hom.appLE` at the prime of `x`.
* `Stacks.SmoothAtRingCriterion.flat_localizationAtPrime_of_flat_stalkMap`: flatness of the stalk
  map at `x` gives flatness of the localization of `Γ(X, U)` at the prime of `x` over `Γ(S, V)`.
* `Stacks.SmoothAtRingCriterion.condition1_of_exists_notMem_smooth`: condition (1) follows from
  the conclusion of Tag 00TF on an affine chart.
* `Stacks.SmoothAtRingCriterion.condition1_of_isSmoothAt_fiber`: if the stalk map at `x` is flat
  and the fibre ring over the prime of `f x` is smooth at the prime of `x`, then condition (1)
  holds.

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
* [Stacks Project, Tag 00TB](https://stacks.math.columbia.edu/tag/00TB)
* [Stacks Project, Tag 00TF](https://stacks.math.columbia.edu/tag/00TF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Stacks.SmoothAtJacobian

universe u

namespace Stacks.SmoothAtRingCriterion

/-- A finitely presented algebra that becomes smooth after inverting an element outside a prime
`q` is smooth at `q`. -/
public theorem isSmoothAt_of_exists_notMem_smooth {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FinitePresentation R A] (q : Ideal A) [q.IsPrime]
    (h : ∃ g ∉ q, Algebra.Smooth R (Localization.Away g)) : Algebra.IsSmoothAt R q := by
  obtain ⟨g, hgq, hg⟩ := h
  exact Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hg
    (show (⟨q, ‹_›⟩ : PrimeSpectrum A) ∈ PrimeSpectrum.basicOpen g from hgq)

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- For `f` locally of finite presentation, `f` is smooth at `x` exactly when the localization of
`Γ(X, U)` at the prime of `x` is formally smooth over `Γ(S, V)`, for any affine open `U ∋ x` lying
over an affine open `V`. -/
public theorem condition1_iff_isSmoothAt_appLE [LocallyOfFinitePresentation f]
    (U : X.affineOpens) (V : S.affineOpens) (hxU : x ∈ U.1) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    letI := (f.appLE V.1 U.1 hUV).hom.toAlgebra
    Condition1 f x ↔
      Algebra.IsSmoothAt Γ(S, V.1) (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal := by
  let _ := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  rw [condition1_iff_mem_smoothLocus f x, Scheme.Hom.mem_smoothLocus,
    AlgebraicGeometry.formallySmooth_stalkMap_iff V.1 V.2 U.1 U.2 hUV hxU]
  exact Iff.rfl

/-- If the induced map of local rings `𝒪_{S,f x} → 𝒪_{X,x}` is flat, then the localization of
`Γ(X, U)` at the prime of `x` is flat over `Γ(S, V)`, for affine opens `U ∋ x` and `V` with
`U ≤ f ⁻¹ᵁ V`. -/
public theorem flat_localizationAtPrime_of_flat_stalkMap
    (U : X.affineOpens) (V : S.affineOpens) (hxU : x ∈ U.1) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (hflat : (f.stalkMap x).hom.Flat) :
    letI := (f.appLE V.1 U.1 hUV).hom.toAlgebra
    Module.Flat Γ(S, V.1)
      (Localization.AtPrime (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal) := by
  let _ := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  let _ : Algebra Γ(X, U.1) ↥(X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk (U := U.1) ⟨x, hxU⟩
  have _ : IsLocalization (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      ↥(X.presheaf.stalk x) := U.2.isLocalization_stalk ⟨x, hxU⟩
  let _ : Algebra Γ(S, V.1) ↥(S.presheaf.stalk (f x)) :=
    S.presheaf.algebra_section_stalk (U := V.1) ⟨f x, hUV hxU⟩
  have _ : IsLocalization (V.2.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal.primeCompl
      ↥(S.presheaf.stalk (f x)) := V.2.isLocalization_stalk ⟨f x, hUV hxU⟩
  let _ : Algebra ↥(S.presheaf.stalk (f x)) ↥(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let _ : Algebra Γ(S, V.1) ↥(X.presheaf.stalk x) :=
    (f.appLE V.1 U.1 hUV ≫ X.presheaf.germ U.1 x hxU).hom.toAlgebra
  have _ : IsScalarTower Γ(S, V.1) Γ(X, U.1) ↥(X.presheaf.stalk x) :=
    .of_algebraMap_eq' (CommRingCat.hom_comp _ _)
  have _ : IsScalarTower Γ(S, V.1) ↥(S.presheaf.stalk (f x)) ↥(X.presheaf.stalk x) :=
    .of_algebraMap_eq' <| (congrArg CommRingCat.Hom.hom
      (Stacks.RelativeDifferentialStalkMap.appLE_germ_eq_germ_stalkMap f x U.1 V.1 hxU hUV)).trans
      (CommRingCat.hom_comp _ _)
  have hstalk : Module.Flat Γ(S, V.1) ↥(X.presheaf.stalk x) :=
    (Module.flat_iff_of_isLocalization ↥(S.presheaf.stalk (f x))
      (V.2.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal.primeCompl ↥(X.presheaf.stalk x)).mp hflat
  exact Module.Flat.of_linearEquiv
    (((IsLocalization.algEquiv (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (Localization.AtPrime (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal)
      ↥(X.presheaf.stalk x)).restrictScalars Γ(S, V.1)).toLinearEquiv)

/-- If the ring map on affine neighbourhoods of `x` and `f x` becomes smooth after inverting some
section not vanishing at `x`, then `f` is smooth at `x`. -/
public theorem condition1_of_exists_notMem_smooth [LocallyOfFinitePresentation f]
    (U : X.affineOpens) (V : S.affineOpens) (hxU : x ∈ U.1) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (h : letI := (f.appLE V.1 U.1 hUV).hom.toAlgebra
      ∃ g ∉ (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal,
        Algebra.Smooth Γ(S, V.1) (Localization.Away g)) :
    Condition1 f x := by
  let _ := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  have _ : Algebra.FinitePresentation Γ(S, V.1) Γ(X, U.1) :=
    f.finitePresentation_appLE V.2 U.2 hUV
  exact (condition1_iff_isSmoothAt_appLE f x U V hxU hUV).mpr
    (isSmoothAt_of_exists_notMem_smooth _ h)

/-- For `f` locally of finite presentation, if the induced map of local rings at `x` is flat and
the fibre ring `Ideal.Fiber p Γ(X, U)` over the prime `p` of `f x` is smooth at a prime lying over
the prime of `x`, then `f` is smooth at `x`. -/
@[ega "IV 17.5.1" "b ⇒ a", sga "1 II 2.1" "sufficiency"]
public theorem condition1_of_isSmoothAt_fiber [LocallyOfFinitePresentation f]
    (U : X.affineOpens) (V : S.affineOpens) (hxU : x ∈ U.1) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (hflat : (f.stalkMap x).hom.Flat)
    (hfib : letI := (f.appLE V.1 U.1 hUV).hom.toAlgebra
      ∃ (Q : Ideal ((V.2.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal.Fiber Γ(X, U.1)))
        (_ : Q.IsPrime),
        Ideal.comap Algebra.TensorProduct.includeRight Q
            = (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal ∧
          Algebra.IsSmoothAt
            (V.2.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal.ResidueField Q) :
    Condition1 f x := by
  let _ := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  have _ : Algebra.FinitePresentation Γ(S, V.1) Γ(X, U.1) :=
    f.finitePresentation_appLE V.2 U.2 hUV
  obtain ⟨Q, _, hcomap, _⟩ := hfib
  have _ : Module.Flat Γ(S, V.1)
      (Localization.AtPrime (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal) :=
    flat_localizationAtPrime_of_flat_stalkMap f x U V hxU hUV hflat
  exact condition1_of_exists_notMem_smooth f x U V hxU hUV <|
    Algebra.exists_notMem_smooth_of_isSmoothAt_fiber (V.2.primeIdealOf ⟨f x, hUV hxU⟩).asIdeal Q
      (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal hcomap ⟨1, Ideal.one_notMem _, inferInstance⟩

end Stacks.SmoothAtRingCriterion

end
