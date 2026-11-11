module

public import Mathlib.Algebra.DirectSum.Module
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.RationalPointExteriorProduct
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Action
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.SmoothProjectiveScheme

/-!
# Chow motives over a field and their Chow groups

Let `k` be a field. Section 0FFZ of the Stacks Project forms, for smooth projective schemes `X`
and `Y` over `k`, the `ℚ`-vector space of correspondences

  `Corrʳ(X, Y) = ⨁_d CH^{d + r}(X_d × Y) ⊗ ℚ`,

`X = ∐_d X_d` being the decomposition of `X` into its open and closed subschemes equidimensional
of dimension `d`, together with the pushforward action `c_*(α) = pr₂,*(c · pr₁^* α)` of a
correspondence on rational Chow groups and the composition
`c' ∘ c = pr₁₃,*(pr₁₂^* c · pr₂₃^* c')`. A Chow motive over `k` is a triple `M = (X, p, m)` with
`X` smooth projective over `k`, `p ∈ Corr⁰(X, X)` a projector, `p ∘ p = p`, and `m ∈ ℤ`
(Stacks 0FGA), and Stacks 0FGL defines its Chow groups

  `CH^i(M) = p(CH^{i + m}(X) ⊗ ℚ)`.

This file constructs all of this for an arbitrary smooth projective scheme over `k`, from the
equidimensional operations of
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Action`.

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.dimensionPiece`: the open and closed subscheme
  `X_d` of `X` where `X` has dimension `d`, a smooth projective scheme over `k` which is smooth of
  relative dimension `d`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.RationalCodimChowGroup`: the rational Chow group
  `CH^i(X) ⊗ ℚ = ⨁_d CH_{d - i}(X_d) ⊗ ℚ` of codimension-`i` classes.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.Corr`: the space `Corrʳ(X, Y)` of
  correspondences of degree `r`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.correspondencePushforward`: `c ↦ c_*`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.correspondenceComp`: `(c', c) ↦ c' ∘ c`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.ChowMotive`: a Chow motive `(X, p, m)` over `k`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.ChowMotive.chowGroup`: **Stacks 0FGL**, the
  Chow group `CH^i(M) = p(CH^{i + m}(X) ⊗ ℚ)`.

## Main results

* `Stacks.WeilCohomology.SmoothProjectiveScheme.ChowMotive.mem_chowGroup_iff`: the classes of
  `CH^i(M)` are the images `p_*(β)` of the classes `β ∈ CH^{i + m}(X) ⊗ ℚ`.

## Implementation notes

**The decomposition into equidimensional pieces.** `X` is smooth over `k`, so the dimension of
`X` at a point is a locally constant function of the point
(`AlgebraicGeometry.isLocallyConstant_fiberDimensionAt_of_smooth`), and its fibre over `d` is
open and closed; that is `dimensionPiece X d`, with the structure of a smooth projective scheme
over `k` from `Stacks.WeilCohomology.SmoothProjectiveScheme.clopen`. Every point of it has
dimension `d`, so it is smooth of relative dimension `d`
(`Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq`). The pieces are indexed by
all of `ℕ`, those with `d > dim X` being empty.

**Codimension grading.** Chapter 42 defines the Chow group of codimension-`p` classes of a
scheme with such a decomposition as `CH^p(X) = ∏_d CH_{d - p}(X_d)` (the paragraph after Stacks
0FE3); only finitely many pieces are nonempty, so this is the direct sum, which is how
`RationalCodimChowGroup` is written. Likewise `X_d × Y` decomposes as `∐_e X_d × Y_e`, with
`X_d × Y_e` of dimension `d + e`, so
`CH^{d + r}(X_d × Y) = ⨁_e CH_{e - r}(X_d × Y_e)` and

  `Corrʳ(X, Y) = ⨁_{(d, e)} CH_{e - r}(X_d × Y_e) ⊗ ℚ`,

the summand being `Stacks.WeilCohomology.Correspondence` of the pieces. Each operation of
Section 0FFZ is computed piece by piece, as Chapter 42 computes every operation on codimension
Chow groups: the pushforward of `c ∈ Corrʳ(X, Y)` sends the `d`-th component of `α` into the
`e`-th component of `c_*(α)` through the `(d, e)` component of `c`, and the `(d, f)` component of
`c' ∘ c` is the sum over `e` of the compositions of the `(e, f)` component of `c'` with the
`(d, e)` component of `c`, the pushforward along `pr₁₃ : X_d × Y × Z_f ⟶ X_d × Z_f` being the
sum of the pushforwards from the pieces `X_d × Y_e × Z_f`.

**Degrees.** The pushforward `CH^i(X) ⊗ ℚ ⟶ CH^j(Y) ⊗ ℚ` and the composition
`Corrˢ(Y, Z) × Corrʳ(X, Y) ⟶ Corrᵗ(X, Z)` take the target degree together with the equation
`i + r = j`, respectively `r + s = t`, that computes it; the source's maps are the instances
`j = i + r` and `t = r + s`, and for a degree-zero projector no reindexing is needed at all.

**Why a `Submodule`.** As for `Stacks.WeilCohomology.ChowMotive.chowGroup`, `CH^i(M)` is returned
as a `ℚ`-subspace of `CH^{i + m}(X) ⊗ ℚ`, the image of the action of the projector.

## References

* [Stacks Project, Tag 0FGL](https://stacks.math.columbia.edu/tag/0FGL)
* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
* [Stacks Project, Tag 0FGA](https://stacks.math.columbia.edu/tag/0FGA)
* [Stacks Project, Tag 0FE3](https://stacks.math.columbia.edu/tag/0FE3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-- A smooth projective scheme over `k` is proper over `k`. -/
instance isProper (X : (SmoothProjectiveScheme k).FullSubcategory) : IsProper X.obj.hom :=
  (isProjective X).isProper

/-! ### The equidimensional pieces -/

section Pieces

variable (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- The open and closed subset of a smooth projective scheme `X` over `k` where `X` has dimension
`d`: the points at which the fibre of `X ⟶ Spec k`, which is `X` itself, has dimension `d`. -/
def dimensionLocus (d : ℕ) : ((toScheme k).obj X).Opens where
  carrier := {x | topologicalKrullDimAt (X.obj.hom.fiber (X.obj.hom x)) (X.obj.hom.asFiber x) =
    (d : WithBot ℕ∞)}
  is_open' := (isLocallyConstant_fiberDimensionAt_of_smooth X.obj.hom).isOpen_fiber _

/-- The locus of `X` where `X` has dimension `d` is open and closed. -/
theorem isClopen_dimensionLocus (d : ℕ) :
    IsClopen (dimensionLocus X d : Set ((toScheme k).obj X)) :=
  ⟨(isLocallyConstant_fiberDimensionAt_of_smooth X.obj.hom).isClosed_fiber _,
    (dimensionLocus X d).2⟩

/-- **The piece `X_d`**: the open and closed subscheme of `X` where `X` has dimension `d`, as a
smooth projective scheme over `k`. -/
def dimensionPiece (d : ℕ) : (SmoothProjectiveScheme k).FullSubcategory :=
  clopen X (dimensionLocus X d) (isClopen_dimensionLocus X d)

/-- The piece `X_d` is smooth of relative dimension `d` over `k`. -/
instance smoothOfRelativeDimension_dimensionPiece (d : ℕ) :
    SmoothOfRelativeDimension d (dimensionPiece X d).obj.hom :=
  Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq _ d fun x => by
    refine (fiberDimensionAt_eq_of_open_square (dimensionLocus X d).ι X.obj.hom
      (dimensionPiece X d).obj.hom (𝟙 _)
      (Category.comp_id ((dimensionLocus X d).ι ≫ X.obj.hom)).symm
      x).trans ?_
    exact x.2

end Pieces

/-! ### Rational Chow groups and correspondences -/

/-- **The rational Chow group `CH^i(X) ⊗ ℚ` of codimension-`i` classes** of a smooth projective
scheme over `k`: `⨁_d CH_{d - i}(X_d) ⊗ ℚ`, over the equidimensional pieces `X_d` of `X`. -/
abbrev RationalCodimChowGroup (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ) :
    Type u :=
  DirectSum ℕ fun d =>
    RationalChowGroupCodim (fieldChowSituation k) (dimensionPiece X d).obj.hom d i

/-- **The space `Corrʳ(X, Y)` of correspondences of degree `r`** from `X` to `Y`, Section 0FFZ:
`⨁_d CH^{d + r}(X_d × Y) ⊗ ℚ`, written as `⨁_{(d, e)} CH_{e - r}(X_d × Y_e) ⊗ ℚ` over the
equidimensional pieces of `X` and `Y`. -/
abbrev Corr (X Y : (SmoothProjectiveScheme k).FullSubcategory) (r : ℤ) : Type u :=
  DirectSum (ℕ × ℕ) fun de =>
    Correspondence (fieldChowSituation k) (dimensionPiece X de.1).obj.hom
      (dimensionPiece Y de.2).obj.hom de.2 r

variable (X Y Z : (SmoothProjectiveScheme k).FullSubcategory)

/-- **The pushforward action of correspondences**, Section 0FFZ: a correspondence
`c ∈ Corrʳ(X, Y)` acts by `c_*(α) = pr₂,*(c · pr₁^* α)`, `CH^i(X) ⊗ ℚ ⟶ CH^j(Y) ⊗ ℚ` with
`j = i + r`. On the `(d, e)` component of `c` and the `d`-th component of `α` it is the action
`Stacks.WeilCohomology.correspondencePushforwardOfDimension` of a correspondence between the
equidimensional pieces `X_d` and `Y_e`, landing in the `e`-th component. -/
def correspondencePushforward (r i j : ℤ) (h : i + r = j) :
    Corr X Y r →ₗ[ℚ] RationalCodimChowGroup X i →ₗ[ℚ] RationalCodimChowGroup Y j :=
  DirectSum.toModule ℚ (ℕ × ℕ) _ fun de =>
    (LinearMap.llcomp ℚ (RationalCodimChowGroup X i) _ (RationalCodimChowGroup Y j)
        (DirectSum.lof ℚ ℕ (fun e => RationalChowGroupCodim (fieldChowSituation k)
          (dimensionPiece Y e).obj.hom e j) de.2)) ∘ₗ
      (LinearMap.lcomp ℚ _ (DirectSum.component ℚ ℕ (fun d =>
        RationalChowGroupCodim (fieldChowSituation k) (dimensionPiece X d).obj.hom d i)
          de.1)) ∘ₗ
        correspondencePushforwardOfDimension (fieldChowSituation k)
          (fieldChowSituation_dimensionFunction_of_isClosed k) (dimensionPiece X de.1).obj.hom
          (dimensionPiece Y de.2).obj.hom de.1 de.2 r i j h

/-- The `(e, f)`, `(d, e')` component of the composition of correspondences: the composition of
the `(e, f)` component of `c'` with the `(d, e)` component of the `(d, e')` summand of `c`, which
is zero unless `e' = e`, placed in the `(d, f)` summand. -/
def correspondenceCompComponent (r s t : ℤ) (h : r + s = t) (ef de : ℕ × ℕ) :
    Correspondence (fieldChowSituation k) (dimensionPiece Y ef.1).obj.hom
        (dimensionPiece Z ef.2).obj.hom ef.2 s →ₗ[ℚ]
      Correspondence (fieldChowSituation k) (dimensionPiece X de.1).obj.hom
        (dimensionPiece Y de.2).obj.hom de.2 r →ₗ[ℚ] Corr X Z t :=
  (LinearMap.llcomp ℚ _ _ (Corr X Z t) (DirectSum.lof ℚ (ℕ × ℕ) (fun df =>
      Correspondence (fieldChowSituation k) (dimensionPiece X df.1).obj.hom
        (dimensionPiece Z df.2).obj.hom df.2 t) (de.1, ef.2))) ∘ₗ
    (LinearMap.lcomp ℚ _ ((DirectSum.component ℚ (ℕ × ℕ) (fun de => Correspondence
        (fieldChowSituation k) (dimensionPiece X de.1).obj.hom (dimensionPiece Y de.2).obj.hom
          de.2 r) (de.1, ef.1)) ∘ₗ DirectSum.lof ℚ (ℕ × ℕ) (fun de => Correspondence
        (fieldChowSituation k) (dimensionPiece X de.1).obj.hom (dimensionPiece Y de.2).obj.hom
          de.2 r) de)) ∘ₗ
      correspondenceCompOfDimension (fieldChowSituation k)
        (fieldChowSituation_dimensionFunction_of_isClosed k) (dimensionPiece X de.1).obj.hom
        (dimensionPiece Y ef.1).obj.hom (dimensionPiece Z ef.2).obj.hom de.1 ef.1 ef.2 r s t h

/-- **Composition of correspondences**, Section 0FFZ:
`Corrˢ(Y, Z) × Corrʳ(X, Y) ⟶ Corrᵗ(X, Z)` with `t = r + s`,
`c' ∘ c = pr₁₃,*(pr₁₂^* c · pr₂₃^* c')`. Its `(d, f)` component is the sum over `e` of the
compositions `Stacks.WeilCohomology.correspondenceCompOfDimension` of the `(e, f)` component of
`c'` with the `(d, e)` component of `c`, correspondences between the equidimensional pieces
`X_d`, `Y_e` and `Z_f`. It is `ℚ`-bilinear. -/
def correspondenceComp (r s t : ℤ) (h : r + s = t) :
    Corr Y Z s →ₗ[ℚ] Corr X Y r →ₗ[ℚ] Corr X Z t :=
  DirectSum.toModule ℚ (ℕ × ℕ) _ fun ef =>
    (DirectSum.toModule ℚ (ℕ × ℕ) _ fun de =>
      (correspondenceCompComponent X Y Z r s t h ef de).flip).flip

/-! ### Chow motives and their Chow groups -/

/-- **A Chow motive over `k`**, Stacks 0FGA: a triple `M = (X, p, m)` of a smooth projective
scheme `X` over `k`, a correspondence `p ∈ Corr⁰(X, X)` of degree zero which is a projector for
the composition of correspondences, `p ∘ p = p`, and an integer `m`. -/
structure ChowMotive (k : Type u) [Field k] where
  /-- The smooth projective scheme `X` of the motive. -/
  X : (SmoothProjectiveScheme k).FullSubcategory
  /-- The projector `p ∈ Corr⁰(X, X)` of the motive. -/
  projector : Corr X X 0
  /-- The projector is idempotent: `p ∘ p = p`. -/
  projector_comp_projector : correspondenceComp X X X 0 0 0 (add_zero 0) projector projector =
    projector
  /-- The Tate twist `m` of the motive. -/
  twist : ℤ

namespace ChowMotive

variable (M : ChowMotive k)

/-- The action `p_*` of the projector of a Chow motive `M = (X, p, m)` on
`CH^{i + m}(X) ⊗ ℚ`: the pushforward by the degree-zero correspondence `p`. -/
def projectorAction (i : ℤ) :
    RationalCodimChowGroup M.X (i + M.twist) →ₗ[ℚ] RationalCodimChowGroup M.X (i + M.twist) :=
  correspondencePushforward M.X M.X 0 (i + M.twist) (i + M.twist) (add_zero _) M.projector

/-- **Stacks Project, Tag 0FGL.** The `i`-th Chow group of a Chow motive `M = (X, p, m)` over a
field `k`,

  `CH^i(M) = p(CH^{i + m}(X) ⊗ ℚ)`,

the image of the pushforward action `p_*` of the projector `p ∈ Corr⁰(X, X)` (Section 0FFZ) on
the rational Chow group of codimension `i + m` classes of the smooth projective scheme `X`, as a
`ℚ`-subspace of `CH^{i + m}(X) ⊗ ℚ`.

This is the complete, unconditional registration of Stacks 0FGL: the composition and the
pushforward of correspondences are the ones constructed in this file. It supersedes
`Stacks.WeilCohomology.ChowMotive.chowGroup`, which takes them as a carried
`Stacks.WeilCohomology.CorrespondenceCalculus` and no longer carries the tag. -/
@[stacks 0FGL "the i-th Chow group CH^i(M) = p(CH^{i+m}(X) ⊗ Q) of a Chow motive M = (X, p, m) \
over a field, X smooth projective and p_* the pushforward action of the projector"]
def chowGroup (i : ℤ) : Submodule ℚ (RationalCodimChowGroup M.X (i + M.twist)) :=
  LinearMap.range (M.projectorAction i)

/-- **Stacks Project, Tag 0FGL.** The classes of `CH^i(M)` are the classes `p_*(β)` for
`β ∈ CH^{i + m}(X) ⊗ ℚ`. -/
@[stacks 0FGL "membership in CH^i(M) = p(CH^{i+m}(X) ⊗ Q)"]
theorem mem_chowGroup_iff (i : ℤ) (α : RationalCodimChowGroup M.X (i + M.twist)) :
    α ∈ M.chowGroup i ↔ ∃ β, M.projectorAction i β = α :=
  LinearMap.mem_range

/-- The projector of a motive takes every rational Chow class of codimension `i + m` into
`CH^i(M)`. -/
theorem projectorAction_mem_chowGroup (i : ℤ) (β : RationalCodimChowGroup M.X (i + M.twist)) :
    M.projectorAction i β ∈ M.chowGroup i :=
  LinearMap.mem_range_self _ β

end ChowMotive

end SmoothProjectiveScheme

end Stacks.WeilCohomology

end
