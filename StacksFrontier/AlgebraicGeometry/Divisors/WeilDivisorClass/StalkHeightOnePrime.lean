module

public import Mathlib.RingTheory.Localization.AsSubring
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.VanishingIdealStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.PrimeDivisorStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.GenericPoint

/-!
# Height-one primes of a local ring and the prime divisors through the point

Let `X` be a locally Noetherian integral scheme, `x` a point of `X` and `𝔭 ⊆ 𝒪_{X, x}` a prime
ideal of height one. This file produces the prime divisor of `X` that `𝔭` cuts out: a point `y`
of codimension one specializing to `x`, whose local ring is the localization `(𝒪_{X, x})_𝔭` and
whose reduced closure induces `𝔭` in `𝒪_{X, x}`.

This is the dictionary through which the orders of vanishing of a rational function at the
codimension-one points of `X` are read as orders in the localizations of `𝒪_{X, x}`, which is
what the implication from condition (2) to condition (1) of [Stacks, Tag 0BE9] needs.

## Main results

* `AlgebraicGeometry.IsAffineOpen.primeIdealOf_fromSpec`: on an affine open, the prime of a point
  in the image of `Spec Γ(X, U)` is the one it came from.
* `AlgebraicGeometry.exists_primeDivisor_stalk_eq_of_height_eq_one`: the dictionary.

## Implementation notes

The point `y` is obtained on an affine open neighbourhood `U` of `x` contained in a prescribed
open `V`: the prime `𝔭` contracts to a prime `𝔯 ⊆ Γ(X, U)` of height one contained in the prime
of `x`, and `y` is the corresponding point of `U`. Both `(𝒪_{X, x})_𝔭` — realized as a subring of
the function field, so that orders can be compared there — and `𝒪_{X, y}` are localizations of
`Γ(X, U)` at `𝔯`, which gives the comparison isomorphism.

## References

* [Stacks Project, Tag 0BE9](https://stacks.math.columbia.edu/tag/0BE9)
* [Stacks Project, Tag 0BE2](https://stacks.math.columbia.edu/tag/0BE2)
* [Stacks Project, Tag 02RO](https://stacks.math.columbia.edu/tag/02RO)
-/

@[expose] public noncomputable section

open Order TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- On an affine open, the prime ideal attached to a point of the image of `Spec Γ(X, U)` is the
prime it is the image of. -/
theorem IsAffineOpen.primeIdealOf_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (y : PrimeSpectrum Γ(X, U)) (hy : hU.fromSpec.base y ∈ U) :
    hU.primeIdealOf ⟨hU.fromSpec.base y, hy⟩ = y := by
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  exact hU.fromSpec.isOpenEmbedding.injective
    (hU.fromSpec_primeIdealOf ⟨hU.fromSpec.base y, hy⟩)

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]

omit [IsLocallyNoetherian X] in
/-- **Height-one primes of a local ring are the prime divisors through the point.** Let `X` be a
locally Noetherian integral scheme, `x ∈ X`, `𝔭 ⊆ 𝒪_{X, x}` a prime of height one and `V` an open
neighbourhood of `x`. There is a prime divisor `Z` of `X` whose generic point lies in `V` and
specializes to `x`, which induces `𝔭` in `𝒪_{X, x}`, and whose local ring is the localization of
`𝒪_{X, x}` at `𝔭` read inside the function field. -/
theorem exists_primeDivisor_stalk_eq_of_height_eq_one
    (x : X) (p : Ideal (X.presheaf.stalk x)) [p.IsPrime] (hp : p.height = 1)
    (V : X.Opens) (hxV : x ∈ V) :
    ∃ Z : PrimeDivisor X, Z.genericPoint ⤳ x ∧ Z.genericPoint ∈ V ∧
      IdealSheafData.stalk Z.idealSheaf x = p ∧
      ∃ e : (Localization.subalgebra.ofField X.functionField _
          p.primeCompl_le_nonZeroDivisors) ≃+* X.presheaf.stalk Z.genericPoint,
        ∀ a, algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField (e a) = a := by
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset (U := V) (x := x) hxV
  set U : X.affineOpens := ⟨W, hW⟩ with hUdef
  have hxU : x ∈ U.1 := hxW
  let : Algebra Γ(X, U.1) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  set q : PrimeSpectrum Γ(X, U.1) := hW.primeIdealOf ⟨x, hxU⟩ with hqdef
  have : IsLocalization.AtPrime (X.presheaf.stalk x) q.asIdeal := hW.isLocalization_stalk ⟨x, hxU⟩
  -- The contraction of `p` to the affine chart.
  set r : Ideal Γ(X, U.1) := p.under Γ(X, U.1) with hrdef
  have hrprime : r.IsPrime := by rw [hrdef]; infer_instance
  have hrheight : r.height = 1 := by
    rw [hrdef, IsLocalization.height_under q.asIdeal.primeCompl p]
    exact hp
  -- The point of `U` it names.
  set ySpec : PrimeSpectrum Γ(X, U.1) := ⟨r, hrprime⟩ with hySpecdef
  have : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
  set y : X := hW.fromSpec.base ySpec with hydef
  have hyU : y ∈ U.1 := by
    have hmem : y ∈ Set.range hW.fromSpec.base := ⟨ySpec, rfl⟩
    rw [hW.range_fromSpec] at hmem
    exact hmem
  have hyprime : hW.primeIdealOf ⟨y, hyU⟩ = ySpec := hW.primeIdealOf_fromSpec ySpec hyU
  let : Algebra Γ(X, U.1) (X.presheaf.stalk y) := X.presheaf.algebra_section_stalk ⟨y, hyU⟩
  have hylocal : IsLocalization.AtPrime (X.presheaf.stalk y) r := by
    have h := hW.isLocalization_stalk ⟨y, hyU⟩
    rwa [hyprime] at h
  -- `y` specializes to `x`, because `r ≤ q`.
  have hrq : r ≤ q.asIdeal := by
    intro a ha
    by_contra hnot
    have hunit : IsUnit (algebraMap Γ(X, U.1) (X.presheaf.stalk x) a) :=
      IsLocalization.map_units (M := q.asIdeal.primeCompl) (X.presheaf.stalk x) ⟨a, hnot⟩
    exact (‹p.IsPrime›).ne_top (p.eq_top_of_isUnit_mem (by rw [hrdef] at ha; exact ha) hunit)
  have hyx : y ⤳ x := by
    have hspec : ySpec ⤳ q :=
      (PrimeSpectrum.le_iff_specializes ySpec q).mp
        ((PrimeSpectrum.asIdeal_le_asIdeal ySpec q).mpr hrq)
    have hmap := hspec.map hW.fromSpec.continuous
    rwa [show hW.fromSpec.base q = x from hW.fromSpec_primeIdealOf ⟨x, hxU⟩] at hmap
  -- `y` has coheight one.
  have hycoh : coheight y = 1 := by
    have hdim : ringKrullDim (X.presheaf.stalk y) = 1 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height r (X.presheaf.stalk y), hrheight]
      rfl
    have := (ringKrullDim_stalk_eq_one_iff_codimension_closureSingleton_eq_one y).mp hdim
    rw [coheight_eq_codimension_closureSingleton]
    exact this
  refine ⟨PrimeDivisor.ofCoheightOne y hycoh, ?_, ?_, ?_, ?_⟩
  · rwa [PrimeDivisor.genericPoint_ofCoheightOne]
  · rw [PrimeDivisor.genericPoint_ofCoheightOne]
    exact hWV hyU
  · -- The ideal induced in `𝒪_{X, x}` is `p`.
    have hideal : (Stacks.Chow.integralComponentAt y).ideal U = r := by
      rw [show Stacks.Chow.integralComponentAt y =
          Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X)) from rfl,
        Stacks.Divisors.ideal_vanishingIdeal_closure_singleton y U hW hyU, hyprime]
    change IdealSheafData.stalk (Stacks.Chow.integralComponentAt y) x = p
    rw [IdealSheafData.stalk_eq_map_germ _ x U hxU, hideal, hrdef]
    exact IsLocalization.map_under q.asIdeal.primeCompl (X.presheaf.stalk x) p
  · -- The comparison of the two localizations of `Γ(X, U)` at `r`.
    rw [PrimeDivisor.genericPoint_ofCoheightOne]
    set A := Localization.subalgebra.ofField X.functionField _
      p.primeCompl_le_nonZeroDivisors with hAdef
    have : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
    have : IsScalarTower Γ(X, U.1) (X.presheaf.stalk x) X.functionField :=
      functionField_isScalarTower X U.1 ⟨x, hxU⟩
    let : Algebra Γ(X, U.1) A :=
      ((algebraMap (X.presheaf.stalk x) A).comp
        (algebraMap Γ(X, U.1) (X.presheaf.stalk x))).toAlgebra
    have : IsScalarTower Γ(X, U.1) (X.presheaf.stalk x) A :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsLocalization.AtPrime A r :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        q.asIdeal.primeCompl A p
    let e : A ≃ₐ[Γ(X, U.1)] X.presheaf.stalk y :=
      IsLocalization.algEquiv r.primeCompl A (X.presheaf.stalk y)
    refine ⟨e.toRingEquiv, fun a => ?_⟩
    have hmap : (algebraMap (X.presheaf.stalk y) X.functionField).comp e.toRingHom =
        (Subalgebra.val A).toRingHom := by
      apply IsLocalization.ringHom_ext r.primeCompl
      ext b
      change algebraMap (X.presheaf.stalk y) X.functionField
        (e (algebraMap Γ(X, U.1) A b)) = _
      rw [e.commutes]
      have : IsScalarTower Γ(X, U.1) (X.presheaf.stalk y) X.functionField :=
        functionField_isScalarTower X U.1 ⟨y, hyU⟩
      rw [← IsScalarTower.algebraMap_apply Γ(X, U.1) (X.presheaf.stalk y) X.functionField]
      change algebraMap Γ(X, U.1) X.functionField b =
        algebraMap (X.presheaf.stalk x) X.functionField (algebraMap Γ(X, U.1) _ b)
      exact IsScalarTower.algebraMap_apply Γ(X, U.1) (X.presheaf.stalk x) X.functionField b
    exact congrArg (fun f : A →+* X.functionField => f a) hmap

end AlgebraicGeometry

end
