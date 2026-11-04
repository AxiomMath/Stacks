module

public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceTwistSections
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistedSectionsIdealPow
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.RegularLocalBlowupTwistLength
public import StacksCore.Tactic.StacksAttribute

/-!
# The negative twisted global sections of the blowup of a regular local surface

Let `(A, 𝔪, κ)` be a regular local ring of dimension two and let `f : X ⟶ S = Spec A` be the
blowing up of `A` in `𝔪`. This file proves part (4) of [Stacks, Tag 0AGS],
$$ H^0(X, \mathcal{O}_X(n)) = \mathfrak m^{\max(0, n)}, $$
for every `n : ℤ`; in the range `n < 0` the exponent is `0` and the assertion reads
`Γ(X, 𝒪_X(n)) = A`.

## Main definitions

The elided prefix is `Stacks.Blowup`.

* `twistStepHom`: the first map `𝒪_X(n) ⟶ 𝒪_X(n-1)` of the twist short exact sequence, the
  inclusion `𝒪_X(n) = ℐ_E · 𝒪_X(n-1) ⊆ 𝒪_X(n-1)`.
* `twistShift`: the `d`-fold composite `𝒪_X(m) ⟶ 𝒪_X(m - d)` of those inclusions.
* `negSections`: the canonical map `A = 𝔪⁰ ⟶ Γ(X, 𝒪_X(0)) ⟶ Γ(X, 𝒪_X(n))` for `n ≤ 0`.
* `maxSections`: the canonical map `𝔪^{max(0,n)} ⟶ Γ(X, 𝒪_X(max(0,n))) ⟶ Γ(X, 𝒪_X(n))` for
  every `n : ℤ`; for `n ≥ 0` it is `Stacks.LocalCohomology.UniformityIII.ambientSections`.

## Main results

* `bijective_negSections_maximalIdeal`: part (4) of [Stacks, Tag 0AGS] for `n < 0`, the
  bijectivity of the canonical `A`-linear map `A ⟶ Γ(X, 𝒪_X(n))`.
* `bijective_maxSections_maximalIdeal`: part (4) of [Stacks, Tag 0AGS] over all `n : ℤ`, the
  bijectivity of the canonical `A`-linear map `𝔪^{max(0,n)} ⟶ Γ(X, 𝒪_X(n))`.
* `isIso_globalSections_map_twistStepHom`: `Γ(X, 𝒪_X(n)) ≅ Γ(X, 𝒪_X(n-1))` for `n ≤ 0`.

## Implementation notes

The composite of the inclusions is built for an abstract family `G : ℤ → C` with steps
`st k : G k ⟶ G (k - 1)`, as `Stacks.Blowup.compDrop`, written with `Nat.rec` so that its
recursion equation `Stacks.Blowup.compDrop_succ` is a single iota step on terms of constant size.
With `G` and `st` instantiated at the twists of a `Proj` and the maps of the twist sequence, the
kernel runs out of budget on the same unfolding.

## References

* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.LocalCohomology.UniformityIII (ambientSections)

universe u u₁ v₁ u₂ v₂

namespace Stacks.Blowup

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The descending composite along a family indexed by the integers -/

section Composite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The `d`-fold composite `G m ⟶ G (m - d)` along a family of steps `st k : G k ⟶ G (k-1)`. -/
def compDrop (G : ℤ → C) (st : ∀ k : ℤ, G k ⟶ G (k - 1)) (m : ℤ) (d : ℕ) :
    G m ⟶ G (m - (d : ℤ)) :=
  Nat.rec (motive := fun d : ℕ => G m ⟶ G (m - (d : ℤ)))
    (eqToHom (congrArg G (show m = m - ((0 : ℕ) : ℤ) by push_cast; ring)))
    (fun d prev => prev ≫ st (m - (d : ℤ)) ≫
      eqToHom (congrArg G (show m - (d : ℤ) - 1 = m - ((d + 1 : ℕ) : ℤ) by push_cast; ring))) d

/-- The empty composite is the identification of `G m` with `G (m - 0)`. -/
theorem compDrop_zero (G : ℤ → C) (st : ∀ k : ℤ, G k ⟶ G (k - 1)) (m : ℤ) :
    compDrop G st m 0 =
      eqToHom (congrArg G (show m = m - ((0 : ℕ) : ℤ) by push_cast; ring)) := rfl

/-- One step of the recursion defining `Stacks.Blowup.compDrop`. -/
theorem compDrop_succ (G : ℤ → C) (st : ∀ k : ℤ, G k ⟶ G (k - 1)) (m : ℤ) (d : ℕ) :
    compDrop G st m (d + 1) = compDrop G st m d ≫ st (m - (d : ℤ)) ≫
      eqToHom (congrArg G
        (show m - (d : ℤ) - 1 = m - ((d + 1 : ℕ) : ℤ) by push_cast; ring)) := rfl

/-- `Stacks.Blowup.compDrop` with its target index given as a variable, so that the composite can
be read at an index that is only propositionally `m - d`. -/
def compShift (G : ℤ → C) (st : ∀ k : ℤ, G k ⟶ G (k - 1)) {m n : ℤ} (d : ℕ)
    (h : n = m - (d : ℤ)) : G m ⟶ G n :=
  compDrop G st m d ≫ eqToHom (congrArg G h.symm)

/-- `Stacks.Blowup.compShift` unfolded. -/
theorem compShift_eq (G : ℤ → C) (st : ∀ k : ℤ, G k ⟶ G (k - 1)) {m n : ℤ} (d : ℕ)
    (h : n = m - (d : ℤ)) :
    compShift G st d h = compDrop G st m d ≫ eqToHom (congrArg G h.symm) := rfl

/-- A functor that inverts the first `d` steps inverts the `d`-fold composite. -/
theorem isIso_map_compShift (F : C ⥤ D) (G : ℤ → C) (st : ∀ k : ℤ, G k ⟶ G (k - 1)) {m n : ℤ}
    (d : ℕ) (h : n = m - (d : ℤ))
    (hst : ∀ k : ℕ, k < d → IsIso (F.map (st (m - (k : ℤ))))) :
    IsIso (F.map (compShift G st d h)) := by
  have key : ∀ e : ℕ, (∀ k : ℕ, k < e → IsIso (F.map (st (m - (k : ℤ))))) →
      IsIso (F.map (compDrop G st m e)) := by
    intro e
    induction e with
    | zero => intro _; rw [compDrop_zero]; infer_instance
    | succ e ih =>
      intro he
      have := ih fun k hk => he k (by omega)
      have := he e (by omega)
      rw [compDrop_succ, F.map_comp, F.map_comp]
      infer_instance
  have := key d hst
  rw [compShift_eq, F.map_comp]
  infer_instance

end Composite

variable {R : Type u} [CommRing R] (I : Ideal R)

/-! ### The twist sequence as a named short complex -/

section Complex

/-- The twist short exact sequence `0 ⟶ 𝒪_X(n) ⟶ 𝒪_X(n-1) ⟶ i_* i^* 𝒪_X(n-1) ⟶ 0` of the blowup
`X = Proj (⨁ₙ Iⁿ)`, as a short complex. -/
def twistExceptionalComplex (n : ℤ) : ShortComplex (blowUpSpec I).Modules :=
  ShortComplex.mk _ _ (shortExact_twist_exceptional I (show n = n - 1 + 1 by ring)).choose

/-- The short complex `Stacks.Blowup.twistExceptionalComplex` is short exact. -/
theorem shortExact_twistExceptionalComplex (n : ℤ) :
    (twistExceptionalComplex I n).ShortExact :=
  (shortExact_twist_exceptional I (show n = n - 1 + 1 by ring)).choose_spec

/-- The inclusion `𝒪_X(n) ⊆ 𝒪_X(n-1)`, the first map of the twist short exact sequence: the
identification of `𝒪_X(n)` with `ℐ_E · 𝒪_X(n-1)` inside `𝒪_X(n-1)`. -/
def twistStepHom (n : ℤ) : blowUpTwist I n ⟶ blowUpTwist I (n - 1) :=
  (twistExceptionalComplex I n).f

/-- The `d`-fold inclusion `𝒪_X(m) ⊆ 𝒪_X(n)` for `n = m - d`, the composite of `d` of the
inclusions `Stacks.Blowup.twistStepHom`. -/
def twistShift {m n : ℤ} (d : ℕ) (h : n = m - (d : ℤ)) :
    blowUpTwist I m ⟶ blowUpTwist I n :=
  compShift (blowUpTwist I) (twistStepHom I) d h

end Complex

/-! ### The canonical maps into the twisted global sections -/

section CanonicalMaps

/-- The canonical `A`-linear map `A = I⁰ ⟶ Γ(X, 𝒪_X(n))` for `n ≤ 0`: the canonical section map in
degree `0` of [Stacks, Tag 0AG2] followed by the `d`-fold inclusion `𝒪_X(0) ⊆ 𝒪_X(-d)`, with `A`
identified with `I⁰ = ⊤`. -/
def negSections {n : ℤ} (d : ℕ) (h : n = ((0 : ℕ) : ℤ) - (d : ℤ)) :
    R →ₗ[R] ((globalSectionsOver (toSpec I)).obj (blowUpTwist I n) : Type u) :=
  (((globalSectionsOver (toSpec I)).map (twistShift I d h)).hom.comp
      (ambientSectionsLinear I 0)).comp
    (((LinearEquiv.ofEq (I ^ 0) ⊤ (by rw [pow_zero, Ideal.one_eq_top])).trans
      Submodule.topEquiv).symm.toLinearMap)

/-- The canonical `A`-linear map `I^{max(0,n)} ⟶ Γ(X, 𝒪_X(n))`, for every `n : ℤ`: the canonical
section map in degree `max(0, n)` of [Stacks, Tag 0AG2] followed by the inclusion
`𝒪_X(max(0,n)) ⊆ 𝒪_X(n)`. For `n ≥ 0` the inclusion is the empty composite and this is the
canonical map `Stacks.LocalCohomology.UniformityIII.ambientSections` of degree `n`; for `n < 0` the
exponent is `0` and `Stacks.Blowup.negSections` is this map precomposed with the identification
`A ≅ I⁰`. -/
def maxSections (n : ℤ) :
    (I ^ (max 0 n).toNat : Ideal R) →ₗ[R]
      ((globalSectionsOver (toSpec I)).obj (blowUpTwist I n) : Type u) :=
  ((globalSectionsOver (toSpec I)).map
      (twistShift I (max 0 n - n).toNat
        (show n = (((max 0 n).toNat : ℕ) : ℤ) - (((max 0 n - n).toNat : ℕ) : ℤ) by
          omega))).hom.comp
    (ambientSectionsLinear I (max 0 n).toNat)

end CanonicalMaps

/-! ### The descending induction -/

section Descent

open IsLocalRing

variable (x : Fin 2 → R) (hx : ∀ i, x i ∈ I) (hspan : I = Ideal.span (Set.range x))
  (ρ : (exceptionalIdealData I).subscheme ≅
    AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) (R ⧸ I)))
  (hcomp : (exceptionalIdealData I).subschemeι ≫ blowUpSpecToProjSpace I x hx hspan =
    ρ.hom ≫ AlgebraicGeometry.Proj.map
      (Stacks.ProjectiveCohomology.polyGradedMap (Fin 2) (Ideal.Quotient.mk I))
      (Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap (Fin 2)
        (Ideal.Quotient.mk I)))

include hcomp in
/-- For `n ≤ 0` the inclusion `𝒪_X(n) ⊆ 𝒪_X(n-1)` is an isomorphism on global sections,
`Γ(X, 𝒪_X(n)) ≅ Γ(X, 𝒪_X(n-1))`. -/
theorem isIso_globalSections_map_twistStepHom {n : ℤ} (hn : n ≤ 0) :
    IsIso ((globalSectionsOver (toSpec I)).map (twistStepHom I n)) := by
  have hSE := shortExact_twistExceptionalComplex I n
  have h0 : IsZero (((AlgebraicGeometry.moduleGlobalSections (blowUpSpec I)).rightDerived 0).obj
      (twistExceptionalComplex I n).X₃) :=
    isZero_rightDerived_zero_pushforward_pullback_blowUpTwist I x hx hspan ρ hcomp
      (n := n - 1) (by omega)
  have : Mono (((AlgebraicGeometry.moduleGlobalSections (blowUpSpec I)).rightDerived 0).map
      (twistStepHom I n)) :=
    (Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor (blowUpSpec I)).mono_map_f hSE
  have : Epi (((AlgebraicGeometry.moduleGlobalSections (blowUpSpec I)).rightDerived 0).map
      (twistStepHom I n)) :=
    ((Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor (blowUpSpec I)).exact_map
      hSE 0).epi_f (h0.eq_zero_of_tgt _)
  have : IsIso (((AlgebraicGeometry.moduleGlobalSections (blowUpSpec I)).rightDerived 0).map
      (twistStepHom I n)) := isIso_of_mono_of_epi _
  have : IsIso ((AlgebraicGeometry.moduleGlobalSections (blowUpSpec I)).map
      (twistStepHom I n)) := by
    rw [← NatIso.naturality_1
      (AlgebraicGeometry.moduleGlobalSections (blowUpSpec I)).rightDerivedZeroIsoSelf
      (twistStepHom I n)]
    infer_instance
  exact (inferInstance : IsIso ((ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toSpec I).appTop).hom).map
      ((AlgebraicGeometry.moduleGlobalSections (blowUpSpec I)).map (twistStepHom I n))))

include hcomp in
/-- The composite inclusion `𝒪_X(m) ⊆ 𝒪_X(n)`, `n = m - d`, is an isomorphism on global sections as
soon as every degree it passes through is nonpositive. -/
theorem isIso_globalSections_map_twistShift {m n : ℤ} (d : ℕ) (h : n = m - (d : ℤ))
    (hstep : ∀ k : ℕ, k < d → m - (k : ℤ) ≤ 0) :
    IsIso ((globalSectionsOver (toSpec I)).map (twistShift I d h)) :=
  isIso_map_compShift (globalSectionsOver (toSpec I)) (blowUpTwist I) (twistStepHom I) d h
    fun k hk => isIso_globalSections_map_twistStepHom I x hx hspan ρ hcomp (hstep k hk)

include hcomp in
/-- The canonical map `Iᵉ ⟶ Γ(X, 𝒪_X(e)) ⟶ Γ(X, 𝒪_X(e - d))` is bijective when the canonical map is
bijective in degree `e` and every degree the inclusion passes through is nonpositive. -/
theorem bijective_globalSections_map_twistShift_comp_ambientSectionsLinear (e d : ℕ) {n : ℤ}
    (h : n = ((e : ℕ) : ℤ) - (d : ℤ)) (hstep : ∀ k : ℕ, k < d → ((e : ℕ) : ℤ) - (k : ℤ) ≤ 0)
    (hbij : Function.Bijective (ambientSections I e)) :
    Function.Bijective (((globalSectionsOver (toSpec I)).map (twistShift I d h)).hom.comp
      (ambientSectionsLinear I e)) := by
  have := isIso_globalSections_map_twistShift I x hx hspan ρ hcomp d h hstep
  rw [LinearMap.coe_comp]
  refine Function.Bijective.comp ?_ hbij
  exact (asIso ((globalSectionsOver (toSpec I)).map (twistShift I d h))).toLinearEquiv.bijective

include hcomp in
/-- The canonical map `A = I⁰ ⟶ Γ(X, 𝒪_X(n))` is bijective for `n ≤ 0`, given the bijectivity of
the canonical map in degree `0`. -/
theorem bijective_negSections {n : ℤ} (d : ℕ) (h : n = ((0 : ℕ) : ℤ) - (d : ℤ))
    (hbij : Function.Bijective (ambientSections I 0)) :
    Function.Bijective (negSections I d h) := by
  rw [negSections, LinearMap.coe_comp]
  refine Function.Bijective.comp ?_ (LinearEquiv.bijective _)
  exact bijective_globalSections_map_twistShift_comp_ambientSectionsLinear I x hx hspan ρ hcomp
    0 d h (fun k _ => by push_cast; omega) hbij

include hcomp in
/-- The canonical map `I^{max(0,n)} ⟶ Γ(X, 𝒪_X(n))` is bijective for every `n : ℤ`, given the
bijectivity of the canonical map in degree `max(0, n)`. -/
theorem bijective_maxSections (n : ℤ)
    (hbij : Function.Bijective (ambientSections I (max 0 n).toNat)) :
    Function.Bijective (maxSections I n) :=
  bijective_globalSections_map_twistShift_comp_ambientSectionsLinear I x hx hspan ρ hcomp
    (max 0 n).toNat (max 0 n - n).toNat _ (fun k _ => by omega) hbij

end Descent

/-! ### Part (4) of Stacks 0AGS -/

section MaximalIdeal

open IsLocalRing

/-- Over a regular local ring of dimension two, the canonical map `𝔪ᵉ ⟶ Γ(X, 𝒪_X(e - d))` is
bijective when every degree the inclusion passes through is nonpositive. -/
private theorem bijective_globalSections_map_twistShift_comp_ambientSectionsLinear_maximalIdeal
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) (e d : ℕ) {n : ℤ}
    (h : n = ((e : ℕ) : ℤ) - (d : ℤ)) (hstep : ∀ k : ℕ, k < d → ((e : ℕ) : ℤ) - (k : ℤ) ≤ 0) :
    Function.Bijective (((globalSectionsOver (toSpec (maximalIdeal A))).map
      (twistShift (maximalIdeal A) d h)).hom.comp (ambientSectionsLinear (maximalIdeal A) e)) := by
  obtain ⟨x, hspan⟩ := exists_range_eq_maximalIdeal A hdim
  have hx : ∀ i, x i ∈ maximalIdeal A := fun i ↦ by
    rw [hspan]; exact Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨ρ, hcomp⟩ := exists_iso_exceptional_projectiveLine A hdim x hx hspan
  exact bijective_globalSections_map_twistShift_comp_ambientSectionsLinear _ x hx hspan ρ hcomp e d
    h hstep (bijective_ambientSections_maximalIdeal A hdim e)

/-- Let `(A, 𝔪, κ)` be a regular local ring of dimension two and let `f : X ⟶ S = Spec A` be the
blowing up of `A` in `𝔪`. For every `n < 0` the canonical `A`-linear map

`A = 𝔪⁰ ⟶ Γ(X, 𝒪_X(0)) ⟶ Γ(X, 𝒪_X(n))`

is bijective, which is the assertion `Γ(X, 𝒪_X(n)) = 𝔪^{max(0,n)} = 𝔪⁰ = A` in that range. The map
is `Stacks.Blowup.negSections`: the canonical section map in degree `0` followed by the `(-n)`-fold
inclusion `𝒪_X(0) ⊆ 𝒪_X(n)`. -/
@[stacks 0AGS "part (4) for n < 0: for the blowup X of Spec A in the maximal ideal m of a regular \
local ring A of dimension two, the canonical A-linear map from A = m^0 to the global sections of \
O_X(n) is bijective for every n < 0, which is Gamma(X, O_X(n)) = m^(max 0 n) = A in that range"]
theorem bijective_negSections_maximalIdeal (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2) {n : ℤ} (hn : n < 0) :
    Function.Bijective (negSections (maximalIdeal A) (-n).toNat
      (show n = ((0 : ℕ) : ℤ) - (((-n).toNat : ℕ) : ℤ) by omega)) := by
  rw [negSections, LinearMap.coe_comp]
  exact (bijective_globalSections_map_twistShift_comp_ambientSectionsLinear_maximalIdeal A hdim
    0 _ _ fun k _ => by push_cast; omega).comp (LinearEquiv.bijective _)

/-- Let `(A, 𝔪, κ)` be a regular local ring of dimension two and let `f : X ⟶ S = Spec A` be the
blowing up of `A` in `𝔪`. For every `n : ℤ` the canonical `A`-linear map

`𝔪^{max(0,n)} ⟶ Γ(X, 𝒪_X(max(0,n))) ⟶ Γ(X, 𝒪_X(n))`

is bijective, which is the equality `H⁰(X, 𝒪_X(n)) = 𝔪^{max(0,n)}` read as an isomorphism of
`A`-modules. -/
@[stacks 0AGS "part (4): for the blowup X of Spec A in the maximal ideal m of a regular local \
ring A of dimension two, the canonical A-linear map from m^(max 0 n) to the global sections of \
O_X(n) is bijective for every integer n, i.e. H^0(X, O_X(n)) = m^(max 0 n)"]
theorem bijective_maxSections_maximalIdeal (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2) (n : ℤ) :
    Function.Bijective (maxSections (maximalIdeal A) n) := by
  exact bijective_globalSections_map_twistShift_comp_ambientSectionsLinear_maximalIdeal A hdim
    (max 0 n).toNat (max 0 n - n).toNat _ fun k _ => by omega

end MaximalIdeal

end Stacks.Blowup

end
