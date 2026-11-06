module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.Contraction
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StructureMorphism
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Comparison

/-!
# The Euler sequence on projective space

Let `R` be a commutative ring, grade `R[T₀, …, Tₙ]` by total degree and write `X = P^n_R` for
`Proj R[T]` with its structure morphism `f : X ⟶ Spec R`. The Euler sequence is

`0 ⟶ Ω_{X/R} ⟶ 𝒪_X(-1)^{⊕ (n+1)} ⟶ 𝒪_X ⟶ 0`.

This file constructs the two arrows and proves that they compose to zero. The second arrow is
contraction with the coordinate row `(T₀, …, Tₙ)`, followed by the identification of `𝒪_X(0)`
with the structure sheaf; it is an epimorphism. The first arrow is the morphism out of the sheaf
of relative differentials corresponding, under the universal property of `Ω_{X/R}`, to the
derivation `g ↦ ∑ⱼ ιⱼ (∂g/∂Tⱼ)`, whose `j`-th component is the coordinate derivative in the `j`-th
summand; on the chart `D₊(Tᵢ)` it is the map `∑_{j≠i} gⱼ d(Tⱼ/Tᵢ) ↦ ∑_{j≠i} (gⱼ/Tᵢ) dTⱼ -
(∑_{j≠i} gⱼTⱼ/Tᵢ²) dTᵢ` of the source.

That the composite vanishes is **Euler's identity**: a morphism out of `Ω_{X/R}` is determined by
the derivation it induces, and the derivation induced by the composite is `g ↦ ∑ⱼ Tⱼ ∂g/∂Tⱼ`. On
a local fraction `g = m / s` with `m` and `s` homogeneous of degree `k` the quotient rule gives
`∑ⱼ Tⱼ (s ∂ⱼm - m ∂ⱼs) / s²`, and
`MvPolynomial.IsHomogeneous.sum_X_mul_pderiv` turns the numerator into `s (k m) - m (k s) = 0`.

## Main definitions

* `twistMinusOneSum`: the middle term `𝒪_X(-1)^{⊕ (n+1)}`, and `projDifferentials` the left-hand
  term `Ω_{X/R}`, both read in the category of sheaves of modules in which the twisting sheaves
  live.
* `eulerDerivation`: the derivation `g ↦ ∑ⱼ ιⱼ (∂g/∂Tⱼ)` of `𝒪_X` with values in
  `𝒪_X(-1)^{⊕ (n+1)}`, relative to the inverse image of `𝒪_{Spec R}`.
* `eulerFirstArrow`: the first arrow `Ω_{X/R} ⟶ 𝒪_X(-1)^{⊕ (n+1)}`.
* `eulerSurjection`: the second arrow `𝒪_X(-1)^{⊕ (n+1)} ⟶ 𝒪_X`.

## Main results

* `d_finsetSum`: a finite sum of relative derivations acts on a local section as the sum of
  their values.
* `universalRelativeDerivation_postcomp_eulerFirstArrow`: the first arrow induces the derivation
  `g ↦ ∑ⱼ ιⱼ (∂g/∂Tⱼ)`, which characterizes it.
* `epi_eulerSurjection`: the second arrow is an epimorphism.
* `eulerFirstArrow_comp_eulerContraction` and `eulerFirstArrow_comp_eulerSurjection`: the two
  arrows compose to zero.

All names are in the namespace `Stacks.AlgebraicGeometry.ProjEulerSequence`.

## Implementation notes

Two categories of sheaves of modules on `Proj 𝒮` are in play and they are definitionally equal
but not interchangeable: `AlgebraicGeometry.Scheme.Modules (Proj 𝒮)`, in which
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials` and its universal property are stated, and
sheaves of modules over `Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf`, in which
the twisting sheaves, the contraction and the biproduct live. `AlgebraicGeometry.Scheme.Modules`
is a semireducible definition carrying its own `CategoryTheory.Category` instance, so a composite
written across the two spellings has a hom type that is not type-correct at reducible
transparency and instance search for its zero morphism fails. `twistMinusOneSum` and
`projDifferentials` pin every object of the sequence into the `projRingSheaf` spelling once;
being `abbrev`s they are transparent, and the single bridging unification happens in their
bodies.

`HasFiniteBiproducts` is supplied as a local instance at the `projRingSheaf` spelling, for the
reason spelled out in `StacksFrontier/AlgebraicGeometry/ProjEulerSequence/Contraction.lean`.

`AlgebraicGeometry.Proj` is deliberately *not* given `implicit_reducible`: with it, `isDefEq`
unfolds `Proj` while destructuring the local-fraction witness of a section of the structure
sheaf and exhausts the heartbeat budget.

The vanishing of the composite is proved against `eulerContraction` and only then composed with
the identification `𝒪_X(0) ≅ 𝒪_X`. In `𝒪_X(0)` a section is a family of elements of the
localizations, so the computation is pointwise arithmetic of fractions; in the structure sheaf it
would have to be carried through `HomogeneousLocalization.val`, and the two spellings of the
sections differ by an unfolding that `rw`'s keyed matching has to redo at every step.

For the same reason the local-fraction witness is destructured inside
`sum_X_mul_pderivApp_apply_eq_zero`, whose goal mentions only `pderivApp` — whose target type is
already `AlgebraicGeometry.ProjectiveSpectrum.Proj.moduleSections` — rather than inside the
statement about the contraction, where each case of the destructuring would have to retypecheck
a goal containing the sections of a twisting sheaf.

## References

* [Stacks Project, Tag 0FMH](https://stacks.math.columbia.edu/tag/0FMH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjEulerSequence

universe u

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTrivialization

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The homogeneous ideal of a point of `Proj R[T₀, …, Tₙ]` is prime. -/
local instance (x : ProjectiveSpectrum.top (polyGrading R n)) :
    x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

/-- A finite sum of relative derivations acts on a local section as the sum of their values:
the additive group structure on relative derivations is pointwise. -/
theorem d_finsetSum {X S : Scheme.{u}} (f : X ⟶ S) {M : X.Modules} {ι : Type*} (s : Finset ι)
    (E : ι → AlgebraicGeometry.SheafOfModules.SheafDerivation
      (AlgebraicGeometry.inverseImageStructureMap f) M)
    {W : (Opens ↥X)ᵒᵖ} (a : X.presheaf.obj W) :
    (∑ j ∈ s, E j).d a = ∑ j ∈ s, (E j).d a := by
  classical
  induction s using Finset.induction with
  | empty => rfl
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
    rfl

/-- The derivation `pderivSheafDerivation R n j` acts on a local section `g` of the structure
sheaf as the coordinate derivative `pderivApp R n j`. -/
@[simp] theorem pderivSheafDerivation_d (j : Fin (n + 1))
    {W : (Opens (ProjectiveSpectrum.top (polyGrading R n)))ᵒᵖ}
    (g : (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)).obj.obj W) :
    (pderivSheafDerivation R n j).d g = pderivApp R n j W.unop g := rfl

/-- `𝒪(-1)^{⊕ (n+1)}`, the middle term of the Euler sequence, in the category of sheaves of
modules over the structure sheaf of `Proj R[T₀, …, Tₙ]` in which the twisting sheaves live. -/
abbrev twistMinusOneSum : SheafOfModules.{u} (projRingSheaf (polyGrading R n)) :=
  ⨁ twistMinusOneFamily R n

/-- The sheaf of differentials of `P^n_R` relative to `Spec R`, read in the same category. -/
abbrev projDifferentials : SheafOfModules.{u} (projRingSheaf (polyGrading R n)) :=
  Scheme.Hom.relativeDifferentials (projToSpecCoeff R n)

/-- **The derivation `g ↦ ∑ⱼ ιⱼ (∂ⱼ g)` into the direct sum.** Its `j`-th component is the
coordinate derivative `∂/∂Tⱼ`, placed in the `j`-th summand of `𝒪(-1)^{⊕ (n+1)}`. -/
def eulerDerivation :
    AlgebraicGeometry.SheafOfModules.SheafDerivation
      (AlgebraicGeometry.inverseImageStructureMap (projToSpecCoeff R n))
      (twistMinusOneSum R n) :=
  ∑ j : Fin (n + 1), (pderivSheafDerivation R n j).postcomp
    (biproduct.ι (twistMinusOneFamily R n) j).val

/-- The derivation `eulerDerivation R n` sends a local section `g` to `∑ⱼ ιⱼ (∂ⱼ g)`. -/
theorem eulerDerivation_d
    {W : (Opens (ProjectiveSpectrum.top (polyGrading R n)))ᵒᵖ}
    (g : (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)).obj.obj W) :
    (eulerDerivation R n).d g =
      ∑ j : Fin (n + 1), (biproduct.ι (twistMinusOneFamily R n) j).val.app W
        (pderivApp R n j W.unop g) :=
  d_finsetSum (projToSpecCoeff R n) _ _ g

/-- **The first arrow of the Euler sequence**, `Ω ⟶ 𝒪(-1)^{⊕ (n+1)}`: the unique morphism out of
the sheaf of relative differentials whose associated derivation is `g ↦ ∑ⱼ ιⱼ (∂ⱼ g)`. On the
chart `D₊(Tᵢ)` it sends `d(Tⱼ/Tᵢ)` to `eⱼ - (Tⱼ/Tᵢ) eᵢ`. -/
def eulerFirstArrow : projDifferentials R n ⟶ twistMinusOneSum R n :=
  (Scheme.Hom.existsUnique_hom_relativeDifferentials (projToSpecCoeff R n) _
    (eulerDerivation R n)).exists.choose

/-- The defining property of the first arrow: it induces the derivation `g ↦ ∑ⱼ ιⱼ (∂ⱼ g)`. -/
theorem universalRelativeDerivation_postcomp_eulerFirstArrow :
    (Scheme.Hom.universalRelativeDerivation (projToSpecCoeff R n)).postcomp
        (eulerFirstArrow R n).val = eulerDerivation R n :=
  (Scheme.Hom.existsUnique_hom_relativeDifferentials (projToSpecCoeff R n) _
    (eulerDerivation R n)).exists.choose_spec

/-- **The second arrow of the Euler sequence**, `𝒪(-1)^{⊕ (n+1)} ⟶ 𝒪`: contraction with the row
`(T₀, …, Tₙ)`, with its target `𝒪(0)` identified with the structure sheaf. -/
def eulerSurjection :
    twistMinusOneSum R n ⟶ SheafOfModules.unit (projRingSheaf (polyGrading R n)) :=
  eulerContraction R n ≫ (twistingSheafZeroIsoUnit (polyGrading R n)).hom

/-- **The second arrow is an epimorphism**, being the Euler contraction followed by an
isomorphism. -/
instance epi_eulerSurjection : Epi (eulerSurjection R n) := by
  rw [eulerSurjection]
  have := epi_eulerContraction R n
  infer_instance

/-- **Euler's identity, on polynomials.** For `m` and `s` homogeneous of the same degree `k`,
`∑ⱼ Tⱼ (s ∂ⱼm - m ∂ⱼs) = s (k m) - m (k s) = 0`: this is the numerator of the contraction of
the derivative of a degree-zero fraction with the coordinate row. -/
private theorem sum_X_mul_quotient_num_eq_zero {k : ℕ} {m s : MvPolynomial (Fin (n + 1)) R}
    (hm : m ∈ polyGrading R n k) (hs : s ∈ polyGrading R n k) :
    ∑ j : Fin (n + 1), (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) *
        (s * MvPolynomial.pderiv j m - m * MvPolynomial.pderiv j s) = 0 := by
  have hsplit : ∑ j : Fin (n + 1), (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) *
        (s * MvPolynomial.pderiv j m - m * MvPolynomial.pderiv j s) =
      s * (∑ j : Fin (n + 1), (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) *
          MvPolynomial.pderiv j m) -
        m * (∑ j : Fin (n + 1), (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) *
          MvPolynomial.pderiv j s) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit, (show m.IsHomogeneous k from hm).sum_X_mul_pderiv,
    (show s.IsHomogeneous k from hs).sum_X_mul_pderiv, nsmul_eq_mul, nsmul_eq_mul]
  ring

/-- Applying a morphism of sheaves of modules to a finite sum of sections. -/
private theorem app_sum {M N : SheafOfModules.{u} (projRingSheaf (polyGrading R n))}
    (φ : M ⟶ N) (U : (Opens (ProjectiveSpectrum.top (polyGrading R n)))ᵒᵖ)
    {ι : Type*} (s : Finset ι) (σ : ι → M.val.obj U) :
    φ.val.app U (∑ j ∈ s, σ j) = ∑ j ∈ s, φ.val.app U (σ j) :=
  map_sum (φ.val.app U).hom σ s

/-- Evaluation of a section of a twist at a point, as an additive map: sections of a twist are
families of elements of the fibres, and addition is pointwise. -/
private def twistEvalAt (d : ℤ) (U : Opens (ProjectiveSpectrum.top (polyGrading R n)))
    (x : U) :
    (twistingSheaf (polyGrading R n) d).val.obj (op U) →+
      ProjectiveSpectrum.Proj.ModuleFiber (M := MvPolynomial (Fin (n + 1)) R)
        (polyGrading R n) x.1 where
  toFun σ := σ.1 x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The value at a point of a finite sum of sections of a twist is the sum of the values. -/
private theorem twist_sum_apply {ι : Type*} (s : Finset ι) (d : ℤ)
    (U : Opens (ProjectiveSpectrum.top (polyGrading R n))) (x : U)
    (σ : ι → (twistingSheaf (polyGrading R n) d).val.obj (op U)) :
    (∑ j ∈ s, σ j).1 x = ∑ j ∈ s, (σ j).1 x :=
  map_sum (twistEvalAt R n d U x) σ s

/-- Two sections of a twist with the same value at every point are equal. -/
private theorem twist_sections_ext {d : ℤ}
    {U : Opens (ProjectiveSpectrum.top (polyGrading R n))}
    {a b : (twistingSheaf (polyGrading R n) d).val.obj (op U)}
    (h : ∀ x : U, a.1 x = b.1 x) : a = b :=
  Subtype.ext (funext h)

/-- **Contracting the derivative of a section with the coordinate row gives zero at every
point.** If `g` has value `m / s` at the point, with `m` and `s` homogeneous of degree `k`, the
`j`-th term is `Tⱼ (s ∂ⱼm - m ∂ⱼs) / s²`, and the numerators sum to `s (k m) - m (k s) = 0` by
Euler's identity. -/
private theorem sum_X_mul_pderivApp_apply_eq_zero
    (W : Opens (ProjectiveSpectrum.top (polyGrading R n)))
    (g : (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)).obj.obj (op W)) (x : W) :
    ∑ j : Fin (n + 1),
      Localization.mk (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) 1 *
        (pderivApp R n j W g).1 x = 0 := by
  obtain ⟨V, hxV, iV, k, num, den, hden, hw⟩ := g.2 x
  have hs : (den : MvPolynomial (Fin (n + 1)) R) ∈
      x.1.asHomogeneousIdeal.toIdeal.primeCompl := hden ⟨x.1, hxV⟩
  have hval : HomogeneousLocalization.val (g.1 x) =
      Localization.mk (num : MvPolynomial (Fin (n + 1)) R) ⟨(den : _), hs⟩ :=
    (congrArg HomogeneousLocalization.val (hw ⟨x.1, hxV⟩)).trans
      (HomogeneousLocalization.val_mk _)
  have hss : (den : MvPolynomial (Fin (n + 1)) R) * (den : MvPolynomial (Fin (n + 1)) R) ∈
      x.1.asHomogeneousIdeal.toIdeal.primeCompl :=
    x.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hs hs
  have hterm : ∀ j : Fin (n + 1),
      Localization.mk (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) 1 *
          (pderivApp R n j W g).1 x =
        Localization.mk ((MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) *
          ((den : MvPolynomial (Fin (n + 1)) R) *
              MvPolynomial.pderiv j (num : MvPolynomial (Fin (n + 1)) R) -
            (num : MvPolynomial (Fin (n + 1)) R) *
              MvPolynomial.pderiv j (den : MvPolynomial (Fin (n + 1)) R)))
          ⟨_, hss⟩ := by
    intro j
    rw [pderivApp_apply_of_val_eq_mk R n j W g x hs hval, Localization.mk_mul]
    exact congrArg _ (Subtype.ext (one_mul _))
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hterm j, ← Localization.mk_sum,
    sum_X_mul_quotient_num_eq_zero R n num.2 den.2, Localization.mk_zero]

/-- **The Euler contraction kills the derivation `g ↦ ∑ⱼ ιⱼ (∂ⱼ g)`.** -/
private theorem eulerContraction_app_eulerDerivation
    (W : Opens (ProjectiveSpectrum.top (polyGrading R n)))
    (g : (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)).obj.obj (op W)) :
    (eulerContraction R n).val.app (op W) ((eulerDerivation R n).d g) = 0 := by
  have key : ∀ x : W, ∑ j : Fin (n + 1),
      ((contraction R n j).val.app (op W) (pderivApp R n j W g)).1 x = 0 := fun x =>
    (Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) =>
        contraction_apply R n j W (pderivApp R n j W g) x).trans
      (sum_X_mul_pderivApp_apply_eq_zero R n W g x)
  rw [eulerDerivation_d, app_sum,
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) =>
      eulerContraction_app_biproduct_ι R n j W (pderivApp R n j W g)]
  exact twist_sections_ext R n fun x =>
    (twist_sum_apply R n Finset.univ 0 W x
      (fun j => (contraction R n j).val.app (op W) (pderivApp R n j W g))).trans (key x)

/-- **The first arrow followed by the Euler contraction is zero.** A morphism out of the sheaf of
relative differentials is determined by the derivation it induces, and the derivation induced by
this composite is `g ↦ ∑ⱼ Tⱼ ∂ⱼ g`, which vanishes by Euler's identity applied to the
homogeneous numerator and denominator of a local fraction. -/
theorem eulerFirstArrow_comp_eulerContraction :
    eulerFirstArrow R n ≫ eulerContraction R n = 0 := by
  refine Scheme.Hom.eq_of_postcomp_eq_universalRelativeDerivation (projToSpecCoeff R n) ?_
  refine (Scheme.Hom.relativeDerivation_postcomp_comp (projToSpecCoeff R n) _ _ _).trans ?_
  refine (Scheme.Hom.relativeDerivation_postcomp_congr (projToSpecCoeff R n)
    (universalRelativeDerivation_postcomp_eulerFirstArrow R n)
    (eulerContraction R n)).trans ?_
  ext W g
  simp only [PresheafOfModulesOfCommRing.Derivation.postcomp_d_apply]
  refine (eulerContraction_app_eulerDerivation R n W.unop g).trans ?_
  rfl

/-- **The two arrows of the Euler sequence compose to zero.** -/
theorem eulerFirstArrow_comp_eulerSurjection :
    eulerFirstArrow R n ≫ eulerSurjection R n = 0 := by
  rw [eulerSurjection, ← Category.assoc, eulerFirstArrow_comp_eulerContraction, zero_comp]

end Stacks.AlgebraicGeometry.ProjEulerSequence

end
