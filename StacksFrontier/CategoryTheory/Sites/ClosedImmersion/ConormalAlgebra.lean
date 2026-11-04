module

public import StacksFrontier.CategoryTheory.Sites.ClosedImmersion.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImageDirect.Criterion
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule
public import StacksCore.Tactic.StacksAttribute

/-!
# Powers of an ideal subsheaf, and the pieces of a conormal algebra

Let `𝓘 ⊆ 𝒪` be an ideal subsheaf of the structure sheaf of a ringed site.  This file
constructs the powers `𝓘^n`, with `𝓘^0 = 𝒪`, `𝓘^1 = 𝓘` and `𝓘^{n+1}` the smallest ideal
subsheaf containing every product of a section of `𝓘` with a section of `𝓘^n`, and proves the
product law and the monotonicity that an associated graded algebra `⨁_{n ≥ 0} 𝓘^n/𝓘^{n+1}` is
built from.

It then applies this to a closed subspace `Z` of an algebraic space `X`: the degree-`n` piece
`𝒞_{Z/X, n}` of the conormal algebra of `Z` in `X` is the inverse image along the inclusion
`i : Z ⟶ X` of the `n`-th power of the defining ideal sheaf of Stacks 03MB.  In degree one this
is the conormal module `𝒞_{Z/X}` on the nose, which is the compatibility
`𝒞_{Z/X, 1} = 𝒞_{Z/X}` of the source.

## Main definitions

* `Stacks.IdealPowerSheaf.idealPow`: the powers `𝓘^n` of an ideal subsheaf of the structure
  sheaf of a ringed site.
* `Stacks.IdealPowerSheaf.idealPowSuccHom`: the inclusion `𝓘^{n+1} ⟶ 𝓘^n`, whose cokernel is
  the graded piece `𝓘^n/𝓘^{n+1}`.
* `AlgebraicGeometry.Space.conormalAlgebraPiece`: the degree-`n` piece `𝒞_{Z/X, n}` of the
  conormal algebra of a closed subspace of an algebraic space.
* `AlgebraicGeometry.Space.conormalAlgebraPieceSuccHom`: the inverse image of the inclusion of
  consecutive ideal powers, relating consecutive pieces.

## Main results

* `Stacks.IdealPowerSheaf.smul_mem_idealPow_succ` and
  `Stacks.IdealPowerSheaf.smul_mem_idealPow_one`: **the product law** `𝓘 · 𝓘^n ⊆ 𝓘^{n+1}`,
  which is what makes each graded piece `𝓘^n/𝓘^{n+1}` annihilated by `𝓘`.
* `Stacks.IdealPowerSheaf.idealPow_succ_le` and `Stacks.IdealPowerSheaf.idealPow_antitone`: the
  powers decrease with the exponent.
* `Stacks.IdealPowerSheaf.idealPow_zero` and `Stacks.IdealPowerSheaf.idealPow_one`: `𝓘^0 = 𝒪`
  and `𝓘^1 = 𝓘`.
* `AlgebraicGeometry.Space.conormalAlgebraPiece_one`: **the degree-one piece is the conormal
  module**, `𝒞_{Z/X, 1} = 𝒞_{Z/X}`.
* `AlgebraicGeometry.Space.conormalAlgebraPiece_zero`: the degree-zero piece is the inverse
  image of the structure sheaf of `X`.

## Implementation notes

The powers are defined by recursion on the exponent, as an infimum of ideal subsheaves rather
than as a sheafification of the sectionwise powers.  Two things follow.  The infimum of sheaf
submodules is computed section by section, which is what makes a *membership* in `𝓘^{n+1}`
provable and hence makes the product law available; and no hypothesis on the site, no
quasi-coherence and no finite generation is needed, so none is assumed.  This follows
`Deformation.ToposThickening.idealProductSubmodule`, the same infimum for the square-zero ideal
of a first-order thickening.

The first power is a separate branch of the recursion, so that `𝓘^1 = 𝓘` holds by definition.
This is what makes the degree-one compatibility with the conormal module hold by definition
too, rather than through a comparison isomorphism, and it also keeps that branch free of the
commutativity of the section rings: deriving `𝓘^1 = 𝓘` from the recursive clause would need a
section of `𝓘` to absorb multiplication on either side.  The degree-zero product law
`Stacks.IdealPowerSheaf.smul_mem_idealPow_one` does need commutativity, which is carried as the
hypothesis `hcomm` in the shape used by `Stacks.SheafOfModules.annihilatorSubmodule`.

The conormal pieces are the inverse images `i^*(𝓘^n)`.  Stacks 76.6 instead forms the graded
algebra `⨁_{n ≥ 0} 𝓘^n/𝓘^{n+1}` of `𝒪_X`-modules, observes that each piece is annihilated by
`𝓘`, and takes the graded `𝒪_Z`-algebra corresponding to it under the equivalence of Stacks
04CJ.  The degree-`n` module of that description is `i^*(𝓘^n)`, because
`i_*i^*(𝓘^n) = 𝓘^n ⊗_{𝒪_X} 𝒪_X/𝓘 = 𝓘^n/𝓘^{n+1}`; that identification is **not** formalized
here, since the equivalence of Stacks 04CJ is not available for the small étale site of an
algebraic space.  Taking the inverse image as the realization is the convention this
development already follows in degree one, at
`AlgebraicGeometry.Space.conormalModule` (Stacks 04CN), and one category down at
`Stacks.Conormal.conormalSheaf` (Stacks 01R2); the part strings record the same split.

## What is not proved

* The **multiplication** making the pieces a sheaf of graded `𝒪_Z`-algebras, that is a
  `SheafOfModules.GradedAlgebra` whose degree-`n` piece is `conormalAlgebraPiece`.  The
  multiplication would come from the product law above through the monoidality of the inverse
  image; the monoidal pullback of a graded algebra is available for ringed *spaces*
  (`Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra`) but not for a morphism of ringed
  topoi.
* **Quasi-coherence** of the pieces, which for the same reason as in
  `AlgebraicGeometry.Space.conormalModule` needs Stacks 03DO part (6) for the inclusion.
## Proved above this file

* The identification `i_*𝒞_{Z/X, n} = 𝓘^n/𝓘^{n+1}` of Stacks 09RP is
  `AlgebraicGeometry.Space.conormalAlgebraPiecePushforwardIso`, in
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraDegreeN.lean`, which carries the 09RP
  tag.  Its route is the one this file prepares: the product law
  `Stacks.IdealPowerSheaf.smul_mem_idealPow_succ` makes `𝓘` annihilate the cokernel of
  `Stacks.IdealPowerSheaf.idealPowSuccHom`, so that cokernel is a direct image.  It does *not*
  go through the ringed-topos criterion of Stacks 08M3,
  `AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_essImage_iff_ideal_annihilates`,
  which would need the inclusion of a closed subspace of an algebraic space presented as an
  `AlgebraicGeometry.ClosedRingedImmersion` — a presentation no declaration in this development
  supplies.  It uses instead `AlgebraicGeometry.Space.essImage_modulePushforward_iff`, the same
  criterion proved directly for a closed immersion of algebraic spaces.  That file imports this
  one, which is why the statement is recorded there and not here.

## References

* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit

universe v u v' u' w

namespace Stacks.IdealPowerSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- The powers of an ideal subsheaf of the structure sheaf of a ringed site: `ℐ^0` is the
structure sheaf, and `ℐ^{n+1}` is the smallest sheaf submodule containing every product of a
section of `ℐ` with a section of `ℐ^n`. -/
noncomputable def idealPow (I : (SheafOfModules.unit R).Submodule) :
    ℕ → (SheafOfModules.unit R).Submodule
  | 0 => ⊤
  | 1 => I
  | n + 2 => sInf { P : (SheafOfModules.unit R).Submodule |
      ∀ (U : Cᵒᵖ) (a : R.obj.obj U), a ∈ I.obj U →
        ∀ m ∈ (idealPow I (n + 1)).obj U, a • m ∈ P.obj U }

/-- The module action on the structure sheaf, viewed as a sheaf of modules over itself, is
multiplication of sections. -/
theorem unit_smul_eq_mul {U : Cᵒᵖ} (a b : R.obj.obj U) :
    a • (b : (SheafOfModules.unit R).val.obj U) = (a * b : R.obj.obj U) := rfl

variable (I : (SheafOfModules.unit R).Submodule)

/-- The zeroth power of an ideal subsheaf is the whole structure sheaf. -/
theorem idealPow_zero : idealPow I 0 = ⊤ := rfl

/-- **The first power of an ideal subsheaf is the subsheaf itself.**  So the degree-one piece
of the associated graded algebra is built from `ℐ` on the nose, and agrees with the conormal
sheaf of the immersion. -/
theorem idealPow_one : idealPow I 1 = I := rfl

/-- **The product law.** A section of `ℐ` times a section of `ℐ^{n+1}` lies in `ℐ^{n+2}`. -/
theorem smul_mem_idealPow_succ (n : ℕ) (U : Cᵒᵖ) (a : R.obj.obj U) (ha : a ∈ I.obj U)
    (m : (SheafOfModules.unit R).val.obj U) (hm : m ∈ (idealPow I (n + 1)).obj U) :
    a • m ∈ (idealPow I (n + 2)).obj U := by
  simp only [idealPow, SheafOfModules.Submodule.toSubmodule_sInf,
    PresheafOfModules.Submodule.sInf_obj, Submodule.mem_iInf]
  rintro _ ⟨Q, hQ, rfl⟩
  exact hQ U a ha m hm

/-- **The product law in degree zero.** An ideal subsheaf absorbs multiplication by an
arbitrary section of the structure sheaf, so `ℐ · ℐ^0 ⊆ ℐ^1`. -/
theorem smul_mem_idealPow_one (hcomm : ∀ (V : Cᵒᵖ) (a b : R.obj.obj V), a * b = b * a)
    (U : Cᵒᵖ) (a : R.obj.obj U) (ha : a ∈ I.obj U)
    (m : (SheafOfModules.unit R).val.obj U) :
    a • m ∈ (idealPow I 1).obj U := by
  have h := Submodule.smul_mem (I.obj U) m ha
  rwa [unit_smul_eq_mul, hcomm U m a, ← unit_smul_eq_mul] at h

/-- The powers of an ideal subsheaf decrease: `ℐ^{n+1} ⊆ ℐ^n`, because `ℐ^n` is itself a
submodule and so is closed under multiplication by a section of the structure sheaf. -/
theorem idealPow_succ_le : ∀ n : ℕ, idealPow I (n + 1) ≤ idealPow I n
  | 0 => le_top
  | _ + 1 => by
      refine sInf_le ?_
      intro U a _ha m hm
      exact Submodule.smul_mem _ a hm

/-- The powers of an ideal subsheaf are antitone in the exponent. -/
theorem idealPow_antitone : Antitone (idealPow I) :=
  antitone_nat_of_succ_le (idealPow_succ_le I)

/-- Every power of an ideal subsheaf is contained in the structure sheaf. -/
theorem idealPow_le_top (n : ℕ) : idealPow I n ≤ ⊤ := le_top

/-- The inclusion `ℐ^{n+1} ⟶ ℐ^n` of consecutive powers, as a morphism of sheaves of modules.
Its cokernel is the degree-`n` piece `ℐ^n/ℐ^{n+1}` of the associated graded algebra. -/
noncomputable def idealPowSuccHom (n : ℕ) :
    (idealPow I (n + 1)).toSheafOfModules ⟶ (idealPow I n).toSheafOfModules :=
  SheafOfModules.Submodule.homOfLE (idealPow_succ_le I n)

end Stacks.IdealPowerSheaf

namespace AlgebraicGeometry.Space

open Stacks.IdealPowerSheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The homogeneous pieces of the conormal algebra of a closed subspace.**  The degree-`n`
piece `𝒞_{Z/X, n}` of the conormal algebra of a closed subspace `Z` of an algebraic space `X`
is the inverse image along the inclusion `i : Z ⟶ X` of the `n`-th power of the defining ideal
sheaf `𝓘_Z ⊆ 𝒪_X` of Stacks 03MB. -/
@[stacks 09RN
  "the homogeneous pieces, as inverse images of the ideal powers, for a closed subspace",
  ega "IV 16.1.2" "I^n/I^{n+1} pieces"]
noncomputable def conormalAlgebraPiece (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (n : ℕ) :
    Modules.{u, u} B S hS Z.1.toFunctor Z.2.1 :=
  (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
    (idealPow (definingIdealSheaf B S hS X Z) n).toSheafOfModules

/-- The degree-`n` piece of the conormal algebra is the inverse image of the `n`-th power of the
defining ideal sheaf.  This is the defining equation, stated so that consumers may rewrite with
it rather than unfold the definition. -/
theorem conormalAlgebraPiece_eq (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (n : ℕ) :
    conormalAlgebraPiece B S hS X Z n =
      (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
        (idealPow (definingIdealSheaf B S hS X Z) n).toSheafOfModules :=
  rfl

/-- **The degree-one piece of the conormal algebra is the conormal module.**  This is the
compatibility `𝒞_{Z/X, 1} = 𝒞_{Z/X}` of the source: the first power of the defining ideal
sheaf is the ideal sheaf itself, so the two inverse images agree on the nose. -/
theorem conormalAlgebraPiece_one (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    conormalAlgebraPiece B S hS X Z 1 = conormalModule B S hS X Z :=
  rfl

/-- The degree-zero piece of the conormal algebra is the inverse image of the whole structure
sheaf of `X`, which is the structure sheaf of `Z`. -/
theorem conormalAlgebraPiece_zero (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    conormalAlgebraPiece B S hS X Z 0 =
      (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
        (⊤ : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule).toSheafOfModules :=
  rfl

/-- The pieces of the conormal algebra decrease along the inclusions of the ideal powers: the
inverse image of the inclusion `𝓘^{n+1} ⟶ 𝓘^n`. -/
noncomputable def conormalAlgebraPieceSuccHom (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (n : ℕ) :
    conormalAlgebraPiece B S hS X Z (n + 1) ⟶ conormalAlgebraPiece B S hS X Z n :=
  (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
    (idealPowSuccHom (definingIdealSheaf B S hS X Z) n)

end AlgebraicGeometry.Space

end
