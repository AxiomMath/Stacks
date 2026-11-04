module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.ExtSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.QuotientExtComparison

/-!
# The alternating Čech spectral sequence, with its first page read on the quotients `U_p`

Let `S` be a scheme, let `f : U → X` be a surjective, étale and separated morphism of algebraic
spaces over `S` and let `ℱ` be an abelian sheaf on the spaces-étale site of `X`. For `p ≥ 0`
write

`W_p = U ×_X ⋯ ×_X U ∖ (all diagonals)`   (`p + 1` factors),

let `U_p = W_p/S_{p+1}` and let `ℤ(χ_p)` be the rank one twist of [Stacks 0727] attached to the
sign character `χ_p` of `S_{p+1}`. **Stacks 0728** says that the spectral sequence of
[Stacks 0725] has

`E₁^{p,q} = H^q(U_p, ℱ|_{U_p} ⊗_ℤ ℤ(χ_p))`

and converges to `H^{p+q}(X, ℱ)`. This file assembles that statement from the spectral sequence
of [Stacks 0725] and the identification of its first page in every degree,
`AlgebraicGeometry.Space.SpacesEtale.nonempty_zExtKoszulSignTwistAddEquiv`.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.exists_alternatingCechQuotientSpectralSequence`:
  **Stacks 0728**, the whole statement: the first-quadrant spectral sequence whose first page
  is `H^q(U_p, ℱ|_{U_p} ⊗_ℤ ℤ(χ_p))` in every degree `q`, converging to `H^{p+q}(X, ℱ)`.

## Implementation notes

Cohomology is written as the `Ext` group out of the constant sheaf `ℤ` read in the derived
category, `CategoryTheory.Abelian.zExt (constantIntSheaf …) …`, which is how the abutment of
[Stacks 0725] is already written in
`AlgebraicGeometry.Space.SpacesEtale.exists_alternatingCechCohomologySpectralSequence`; two of
the conjuncts record that both those groups are the sheaf cohomology `CategoryTheory.Sheaf.H`
of Mathlib, on `X` for the abutment and on `U_p` for the first page. The identification of the
first page is stated as an `AddEquiv` rather than as an isomorphism of `AddCommGrpCat`, the
pages of the spectral sequence living at universe level `u + 2` and the cohomology of `U_p` at
`u + 1`. The coefficient sheaf on `U_p` is the sheafification of the objectwise tensor product
over `ℤ` with the twist presheaf, and the last conjunct identifies it with the tensor product
against the twist `ℤ(χ_p)` of [Stacks 0727] itself.

The first page is identified at every pair of natural numbers, which is the whole of it: one
conjunct is the vanishing outside the first quadrant.

Existence of sheafification for presheaves of sets on the big fppf site is assumed, as in
`AlgebraicGeometry.Space.SpacesEtale.diagonalComplementQuotient`: the quotient `U_p` of
[Stacks 071S] is a sheafification, so the statement cannot be made without it.

## References

* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
* [Stacks Project, Tag 0725](https://stacks.math.columbia.edu/tag/0725)
* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (U : SpacesEtale B S hS X)
    (hsep : IsSeparated B S hS U.1.hom.hom) (p : ℕ)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **`ℱ|_{U_p} ⊗_ℤ ℤ(χ_p)`**: the restriction of `ℱ` to the quotient `U_p = W_p/S_{p+1}`,
tensored with the rank one twist of [Stacks 0727] attached to the sign character. -/
abbrev diagonalComplementTwistedRestriction
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    Sheaf (topology B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep))
      AddCommGrpCat.{u + 1} :=
  (diagonalComplementTwistTensorFunctor B S hS X U hsep p).obj
    ((diagonalComplementQuotientRestriction B S hS X U (p + 1) hsep).obj F)

/-- **Stacks 0728.** Let `S` be a scheme, let `f : U ⟶ X` be a surjective, étale and separated
morphism of algebraic spaces over `S` and let `ℱ` be an abelian sheaf on the spaces-étale site
of `X`. Write `W_p = U ×_X ⋯ ×_X U ∖ (all diagonals)` with `p + 1` factors, let
`U_p = W_p/S_{p+1}` and let `ℤ(χ_p)` be the rank one twist of [Stacks 0727] attached to the
sign character of `S_{p+1}`. The spectral sequence of [Stacks 0725] is concentrated in the
first quadrant, its first page is

`E₁^{p,q} = H^q(U_p, ℱ|_{U_p} ⊗_ℤ ℤ(χ_p))`

in every degree `q`, and it converges to the sheaf cohomology `H^{p+q}(X, ℱ)`.

Cohomology is written as the `Ext` group out of the constant sheaf `ℤ` read in the derived
category; two conjuncts identify those groups with Mathlib's sheaf cohomology, on `X` for the
abutment and on `U_p` for the first page, and the last one identifies the coefficient sheaf on
`U_p` with the tensor product of `ℱ|_{U_p}` against the twist of [Stacks 0727]. The first
conjunct records the first page in the `Ext` form of [Stacks 0725] out of the terms
`K^p = ∧^{p+1} j_{U!} ℤ` of the Koszul complex. -/
@[stacks 0728 "the E₁-page is H^q(U_p, F|_{U_p} ⊗ Z(χ_p)) in every degree q, and the \
convergence to H^{p+q}(X, F)"]
theorem exists_alternatingCechQuotientSpectralSequence
    (hsurj : IsSurjective B S hS U.1.hom.hom)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{u + 2} 1,
      (∀ (p : ℕ) (q : ℤ), Nonempty ((E.page 1).X ((p : ℤ), q) ≅
        AddCommGrpCat.of (zExt ((koszulComplex B S hS X U).X p) F q))) ∧
      (∀ p q : ℕ, Nonempty ((E.page 1).X ((p : ℤ), (q : ℤ)) ≃+
        zExt (constantIntSheaf B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep))
          (diagonalComplementTwistedRestriction B S hS X U hsep p F) (q : ℤ))) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 1).X (p, q))) ∧
      SpectralSequence.AbutsTo E
        (fun n ↦ AddCommGrpCat.of (zExt (constantIntSheaf B S hS X) F n)) ∧
      (∀ n : ℕ, Nonempty (AddCommGrpCat.of (Sheaf.H F n) ≅
        AddCommGrpCat.of (zExt (constantIntSheaf B S hS X) F (n : ℤ)))) ∧
      (∀ p q : ℕ, Nonempty (AddCommGrpCat.of
          (Sheaf.H (diagonalComplementTwistedRestriction B S hS X U hsep p F) q) ≅
        AddCommGrpCat.of
          (zExt (constantIntSheaf B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep))
            (diagonalComplementTwistedRestriction B S hS X U hsep p F) (q : ℤ)))) ∧
      ∀ p : ℕ, Nonempty (diagonalComplementTwistedRestriction B S hS X U hsep p F ≅
        (presheafToSheaf (topology B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep))
            AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.presheafTensor
            ((diagonalComplementQuotientRestriction B S hS X U (p + 1) hsep).obj F).obj
            (characterTwistOfDiagonalComplement B S hS X U (p + 1) hsep
              (diagonalComplementSignCharacter (p + 1))).twist.obj)) := by
  obtain ⟨E, hE, hvanish, hAbuts, hH⟩ :=
    exists_alternatingCechCohomologySpectralSequence B S hS X U hsurj F
  refine ⟨E, hE, fun p q => ?_, hvanish, hAbuts, hH, fun p q =>
    ⟨sheafHIsoZExt B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep)
      (diagonalComplementTwistedRestriction B S hS X U hsep p F) q⟩,
    fun p => ⟨characterTwistTensorIso (diagonalComplementSignCharacter (p + 1))
      ((diagonalComplementQuotientRestriction B S hS X U (p + 1) hsep).obj F).obj
      (diagonalComplementQuotientAut B S hS X U (p + 1) hsep)⟩⟩
  obtain ⟨e⟩ := hE p (q : ℤ)
  obtain ⟨g⟩ := nonempty_zExtKoszulSignTwistAddEquiv B S hS X U hsep p q F
  exact ⟨e.addCommGroupIsoToAddEquiv.trans g⟩

end AlgebraicGeometry.Space.SpacesEtale

end
