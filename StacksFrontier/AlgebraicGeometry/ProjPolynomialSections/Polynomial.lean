module

public import StacksFrontier.AlgebraicGeometry.ProjPolynomialSections.Basic
public import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# The polynomial graded algebra of a scheme, and `Proj_S(𝒪_S[T₀, …, Tₙ]) ≅ ℙⁿ_S`

This file builds the graded `𝒪_S`-algebra whose sections over an affine open `U` of a scheme `S`
are the polynomials in `n + 1` variables over `Γ(S, U)`, graded by total degree, and reads the
reduction of the sibling file at it: **the relative homogeneous spectrum of that algebra is
relative projective `n`-space over `S`, unconditionally.**

Quasi-coherence — the only field of `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra` with
content — is Mathlib's `MvPolynomial.isLocalization` together with
`AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`: the sections of the structure sheaf
over a basic open are a localization away from the defining section, and a polynomial ring over a
localization away from `f` is the localization of the polynomial ring away from the constant `f`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjPolynomialSections.polyGradingAddSubgroup`: the total-degree
  grading of `R[T₀, …, Tₙ]`, valued in additive subgroups rather than in submodules, which is
  what `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra` grades by.
* `Stacks.AlgebraicGeometry.ProjPolynomialSections.polyAlgebra`: **`𝒪_S[T₀, …, Tₙ]` as a
  quasi-coherent graded `𝒪_S`-algebra**, the data of Situation 01NN.
* `Stacks.AlgebraicGeometry.ProjPolynomialSections.polySections`: its section rings are
  polynomial rings, on the nose.

## Main results

* `Stacks.AlgebraicGeometry.ProjPolynomialSections.isLocalization_away_C`: a polynomial ring over
  a localization away from `f` is the localization of the polynomial ring away from `C f`, in the
  form the quasi-coherence field asks for.
* `Stacks.AlgebraicGeometry.ProjPolynomialSections.exists_iso_relativeProj_polyAlgebra`:
  **`Proj_S(𝒪_S[T₀, …, Tₙ]) ≅ ℙⁿ_S` over `S`.**

## Implementation notes

**The two spellings of the total-degree grading are bridged by a graded ring homomorphism, not by
an equality.** `polyGradingAddSubgroup R n i` is `(polyGrading R n i).toAddSubgroup`, so the two
have literally the same members and the `DirectSum.Decomposition` instance transports field by
field; but `AddSubgroup A` and `Submodule R A` are different types, so
`AlgebraicGeometry.Proj` of the two gradings are different terms with different instance paths.
`polyGradingToAddSubgroup` and `polyGradingOfAddSubgroup` are the identity ring homomorphism read
as a graded ring homomorphism each way, and every clause of
`Stacks.AlgebraicGeometry.ProjPolynomialSections.polySections` is then `rfl`.

**The localization statement is stated at a bare ring homomorphism's algebra structure.**
`Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra`'s quasi-coherence field puts
`RingHom.toAlgebra` of the restriction map on the sections, while Mathlib's
`MvPolynomial.isLocalization` is stated for `MvPolynomial.algebraMvPolynomial`; the two have the
same `algebraMap` (`MvPolynomial.algebraMap_def` is `rfl`), so no transport along
`Algebra.algebra_ext` is needed and `exact` closes it.

## References

* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)

## Not done here

**No project tag is attached.** `Proj_S(𝒪_S[T₀, …, Tₙ]) ≅ ℙⁿ_S` is not a labelled assertion of
Tag 01NF — that tag's assertions are about projective space over a ring and over a scheme, both
already formalized in `StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace` — and Tag 01NQ's
assertions are about the glueing, which is formalized in a sibling file.

**Nothing identifies `polyAlgebra` with the symmetric algebra of a free module.** That
identification is what part (1) of Tag 087S still owes; see the `Not done here` section of
`StacksDraft.AlgebraicGeometry.F3.ProjPolynomialSections.Basic`. In particular this file does
**not** give `𝐏(𝒪_S^{⊕(n+1)}) ≅ ℙⁿ_S`, because `𝐏` is `Proj_S` of
`Stacks.SymGraded.schemeSheafGradedAlgebra` and not of `polyAlgebra`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjGlue
open Stacks.AlgebraicGeometry.ProjPolyChart

namespace Stacks.AlgebraicGeometry.ProjPolynomialSections

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The total-degree grading as a family of additive subgroups -/

variable (R : Type u) [CommRing R] (n : ℕ)

/-- **The total-degree grading of `R[T₀, …, Tₙ]`, valued in additive subgroups.** The grading of
`Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra` is by `AddSubgroup`, while
`Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading` is by `Submodule`; the two have the same
members, but they are different types, so the two `AlgebraicGeometry.Proj`s are different terms
and the comparison between them is a graded ring homomorphism. -/
public def polyGradingAddSubgroup : ℕ → AddSubgroup (MvPolynomial (Fin (n + 1)) R) :=
  fun i => (polyGrading R n i).toAddSubgroup

/-- A polynomial lies in the `i`-th piece of `polyGradingAddSubgroup R n` if and only if it is
homogeneous of total degree `i`. -/
@[simp] public theorem mem_polyGradingAddSubgroup {i : ℕ}
    {p : MvPolynomial (Fin (n + 1)) R} :
    p ∈ polyGradingAddSubgroup R n i ↔ p.IsHomogeneous i :=
  Iff.rfl

/-- The total-degree grading `polyGradingAddSubgroup R n` is a graded monoid: the constant `1` is
homogeneous of degree `0`, and a product of homogeneous polynomials of degrees `i` and `j` is
homogeneous of degree `i + j`. -/
public instance gradedMonoid_polyGradingAddSubgroup :
    SetLike.GradedMonoid (polyGradingAddSubgroup R n) where
  one_mem := MvPolynomial.isHomogeneous_one (Fin (n + 1)) R
  mul_mem := @fun _ _ _ _ ha hb => MvPolynomial.IsHomogeneous.mul ha hb

/-- Every polynomial in `R[T₀, …, Tₙ]` decomposes uniquely as a direct sum of its homogeneous
components for `polyGradingAddSubgroup R n`, transported from the decomposition for
`Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading`. -/
public instance decomposition_polyGradingAddSubgroup :
    DirectSum.Decomposition (polyGradingAddSubgroup R n) :=
  let e : DirectSum.Decomposition (polyGrading R n) := inferInstance
  { decompose' := e.decompose', left_inv := e.left_inv, right_inv := e.right_inv }

/-- `R[T₀, …, Tₙ]` is a graded ring for the total-degree grading `polyGradingAddSubgroup R n`. -/
public instance gradedRing_polyGradingAddSubgroup :
    GradedRing (polyGradingAddSubgroup R n) where

variable {R' : Type u} [CommRing R']

/-- Coefficient change as a homomorphism of the additive-subgroup gradings. -/
public def coeffGradedHomAddSubgroup (θ : R →+* R') :
    polyGradingAddSubgroup R n →+*ᵍ polyGradingAddSubgroup R' n where
  toRingHom := MvPolynomial.map θ
  map_mem hx := MvPolynomial.IsHomogeneous.map hx θ

/-- The coefficient change `coeffGradedHomAddSubgroup R n θ` sends a polynomial `p` to
`MvPolynomial.map θ p`. -/
@[simp] public theorem coeffGradedHomAddSubgroup_apply (θ : R →+* R')
    (p : MvPolynomial (Fin (n + 1)) R) :
    coeffGradedHomAddSubgroup R n θ p = MvPolynomial.map θ p :=
  rfl

/-- The identification of the two spellings of the grading, from `Submodule` to `AddSubgroup`. -/
public def polyGradingToAddSubgroup :
    polyGrading R n →+*ᵍ polyGradingAddSubgroup R n where
  toRingHom := RingHom.id _
  map_mem hx := hx

/-- The identification of the two spellings of the grading, from `AddSubgroup` to `Submodule`. -/
public def polyGradingOfAddSubgroup :
    polyGradingAddSubgroup R n →+*ᵍ polyGrading R n where
  toRingHom := RingHom.id _
  map_mem hx := hx

/-! ### Restriction of the structure sheaf, as a ring homomorphism -/

variable (S : Scheme.{u})

/-- Restriction along the identity inclusion of opens is the identity. -/
public theorem resHom_le_refl (U : S.Opens) : resHom (le_refl U) = RingHom.id ↥Γ(S, U) := by
  change (S.presheaf.map (homOfLE (le_refl U)).op).hom = RingHom.id ↥Γ(S, U)
  rw [show (homOfLE (le_refl U)).op = 𝟙 (Opposite.op U) from rfl,
    CategoryTheory.Functor.map_id, CommRingCat.hom_id]

/-- Restriction is functorial. -/
public theorem resHom_trans {U V W : S.Opens} (hUV : U ≤ V) (hVW : V ≤ W) :
    resHom (hUV.trans hVW) = (resHom hUV).comp (resHom hVW) := by
  change (S.presheaf.map (homOfLE (hUV.trans hVW)).op).hom = _
  rw [show (homOfLE (hUV.trans hVW)).op = (homOfLE hVW).op ≫ (homOfLE hUV).op from rfl,
    CategoryTheory.Functor.map_comp, CommRingCat.hom_comp]

/-! ### The localization statement -/

/-- **A polynomial ring over a localization away from `f` is the localization of the polynomial
ring away from the constant `f`.** This is Mathlib's `MvPolynomial.isLocalization` together with
`Submonoid.map_powers`, stated for the algebra structure attached to a bare ring
homomorphism, which is the form
`Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra`'s quasi-coherence field asks for. -/
public theorem isLocalization_away_C {A B : Type u} [CommRing A] [CommRing B] (θ : A →+* B)
    (f : A) (h : @IsLocalization.Away A _ f B _ θ.toAlgebra) (m : ℕ) :
    @IsLocalization.Away (MvPolynomial (Fin (m + 1)) A) _ (MvPolynomial.C f)
      (MvPolynomial (Fin (m + 1)) B) _ (MvPolynomial.map θ).toAlgebra := by
  let : Algebra A B := θ.toAlgebra
  have := h
  let : Algebra (MvPolynomial (Fin (m + 1)) A) (MvPolynomial (Fin (m + 1)) B) :=
    MvPolynomial.algebraMvPolynomial
  have h2 : IsLocalization ((Submonoid.powers f).map (MvPolynomial.C (σ := Fin (m + 1))))
      (MvPolynomial (Fin (m + 1)) B) := MvPolynomial.isLocalization _ _
  rw [Submonoid.map_powers] at h2
  exact h2

/-! ### The polynomial graded algebra of a scheme -/

/-- **The polynomial graded algebra `𝒪_S[T₀, …, Tₙ]`**: the quasi-coherent, commutative,
nonnegatively graded `𝒪_S`-algebra whose sections over an affine open `U` are the polynomials in
`n + 1` variables over `Γ(S, U)`, graded by total degree.

Quasi-coherence is `Stacks.AlgebraicGeometry.ProjPolynomialSections.isLocalization_away_C` on top
of `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`. -/
public def polyAlgebra : GradedAlgebra S where
  ring U := CommRingCat.of (MvPolynomial (Fin (n + 1)) ↥Γ(S, U.toOpens))
  grading U := polyGradingAddSubgroup ↥Γ(S, U.toOpens) n
  gradedRing U := inferInstance
  str U := CommRingCat.ofHom (MvPolynomial.C)
  str_mem U r := MvPolynomial.isHomogeneous_C _ _
  res h := coeffGradedHomAddSubgroup _ n (resHom h)
  res_id U := by
    refine GradedRingHom.ext fun p => ?_
    rw [coeffGradedHomAddSubgroup_apply, resHom_le_refl S U.toOpens, MvPolynomial.map_id]
    rfl
  res_comp hUV hVW := by
    refine GradedRingHom.ext fun p => ?_
    rw [coeffGradedHomAddSubgroup_apply, resHom_trans S hUV hVW, ← MvPolynomial.map_map]
    rfl
  res_str h r := MvPolynomial.map_C _ _
  isLocalization U f :=
    isLocalization_away_C (resHom (S.basicOpen_le f)) f (U.2.isLocalization_basicOpen f) n

/-- **The section rings of the polynomial graded algebra are polynomial rings**, on the nose:
the identification is the identity, read across the two spellings of the grading. -/
public def polySections : PolynomialSections (polyAlgebra n S) n where
  ofPoly U := polyGradingToAddSubgroup ↥Γ(S, U.toOpens) n
  toPoly U := polyGradingOfAddSubgroup ↥Γ(S, U.toOpens) n
  ofPoly_toPoly _ _ := rfl
  toPoly_ofPoly _ _ := rfl
  ofPoly_C _ _ := rfl
  res_ofPoly _ _ := rfl

/-- **`Proj_S(𝒪_S[T₀, …, Tₙ]) ≅ ℙⁿ_S` over `S`**, unconditionally: the relative homogeneous
spectrum of the polynomial graded algebra of a scheme is relative projective `n`-space over that
scheme, by an isomorphism over the base. -/
public theorem exists_iso_relativeProj_polyAlgebra :
    ∃ e : relativeProj (polyAlgebra n S) ≅ projectiveSpaceOver n S,
      e.hom ≫ pullback.fst (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) = relativeProjToBase (polyAlgebra n S) :=
  (polySections n S).exists_schemeIso

end Stacks.AlgebraicGeometry.ProjPolynomialSections

end
