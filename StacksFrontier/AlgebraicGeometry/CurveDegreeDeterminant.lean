module

public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerDegreeOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeAdditivityUnconditional
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree of the determinant of a vector bundle on a curve, after [Stacks, Tag 0DJ5]

Let `k` be a field, `X` a proper scheme of dimension at most one over `k` and `ℰ` a finite
locally free `𝒪_X`-module of constant rank `n`. Tag 0DJ5 asserts

`deg(ℰ) = deg(⋀ⁿ ℰ) = deg(det(ℰ))`.

This file holds the inputs: the dévissage form of the first equality, and the second equality
read at the determinant *line bundle*. The tag itself, both equalities in one statement with
`det` the determinant of [Stacks, Tag 0FJN], is
`AlgebraicGeometry.curveDegree_eq_curveDegree_exteriorPower_eq_invertibleCurveDegree_determinant`
of `StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeExteriorDeterminant`.

## Main definitions

* `AlgebraicGeometry.ExteriorDevissage`: the one-step dévissage input of the first equality —
  for every module of rank `m + 2` a short exact sequence with invertible quotient and
  rank-`(m + 1)` kernel, *together with* the identification of the top exterior power of the
  module with the tensor product of the top exterior power of the kernel and the quotient.

## Main results

The elided prefix throughout is `AlgebraicGeometry`.

* `Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self`: `⋀ⁿ ℰ` has rank one, so the
  degree of a rank-`n` module and the degree of its top exterior power are both degrees in the
  sense of `AlgebraicGeometry.curveDegree`.
* `Scheme.Modules.exteriorPowerOneIsoSelf`: `⋀¹ ℰ ≅ ℰ` at the scheme-level spelling of the
  exterior power.
* `curveDegree_exteriorPower_one_eq`: **the first equality at rank one**, unconditionally.
* `curveDegree_eq_curveDegree_exteriorPower_of_devissage`: **the first equality**,
  `deg(ℰ) = deg(⋀ⁿ ℰ)` for every rank `n ≥ 1`, from `ExteriorDevissage` alone.
* `curveDegree_exteriorPower_self_eq_invertibleCurveDegree`: `deg(⋀ⁿ ℰ) = deg(det(ℰ))` read in
  this repository's spelling of the determinant *line bundle*, the top exterior power itself.

## Implementation notes

### The second equality here is the near-definitional reading, said rather than dressed up

The scheme-level determinant *line bundle* of a finite locally free module of constant rank `n`
in this repository is its top exterior power:
`AlgebraicGeometry.Scheme.Modules.isInvertible_exteriorPower_self` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorPowerRank.lean`, whose docstring reads
"**The determinant line bundle.** The top exterior power `⋀^r F` ... is invertible". Read that
way, `det(ℰ)` and `⋀ⁿ ℰ` are the same object and the whole content of `deg(⋀ⁿ ℰ) = deg(det(ℰ))`
is the passage from `AlgebraicGeometry.curveDegree` at rank one to
`AlgebraicGeometry.invertibleCurveDegree`, which is
`AlgebraicGeometry.invertibleCurveDegree_eq_curveDegree`. That is what
`curveDegree_exteriorPower_self_eq_invertibleCurveDegree` below states, and it is a one-line
proof. It is a convenience, not a formalization of Tag 0DJ5's second equality, and it carries no
attribute: it assumes an invertibility instance for `⋀ⁿ ℰ` that the source does not assume.

The reading of the second equality that Tag 0DJ5 is registered at takes `det` to be the
annihilator determinant of [Stacks, Tag 0FJN],
`SheafOfModules.TensorExteriorSymmetricAlgebras.determinant` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorAlgebraDeterminant.lean` — the direct sum
over all degrees of the annihilators of the degree-one part — which is a different sheaf of
modules, compared with `⋀ⁿ ℰ` by a theorem rather than by unfolding. That comparison,
`SheafOfModules.TensorExteriorSymmetricAlgebras.determinantIsoExteriorPower` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorDeterminantTopPower.lean`, is
[Stacks, Tag 0B37] and is available; it is also what makes the invertibility of `det(ℰ)`
derivable from the rank of `ℰ` alone, so that nothing about `det(ℰ)` has to be assumed. Both
equalities of the tag in one statement, with that determinant, are
`AlgebraicGeometry.curveDegree_eq_curveDegree_exteriorPower_eq_invertibleCurveDegree_determinant`
of `StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeExteriorDeterminant`, where Tag 0DJ5 is
registered.

### What the first equality carries, and why

Two things, both named in the attribute's clause string. [Stacks, Tag 02O6] over a field is
**not** among them: both degree inputs below need it — additivity along a short exact sequence
is `AlgebraicGeometry.curveDegree_add_of_shortExact_of_isProper` (Tag 0AYS) and additivity in
a tensor product is `AlgebraicGeometry.curveDegree_tensorSheaf_eq_add` (Tag 0AYX) — but each of
those now proves it rather than assuming it, by
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper`.

1. `[IsCurve k f]`, a proper *curve*, whereas Tag 0DJ5 is stated for a proper scheme of
   dimension at most one. This is inherited verbatim from Tag 0AYX as formalized in
   `StacksFrontier/AlgebraicGeometry/CurveDegreeTensor/Cohomological.lean`, which is the tensor
   input; the reduction from dimension at most one to the curve case is [Stacks, Tag 0AYW],
   whose every form in
   `StacksFrontier/AlgebraicGeometry/ComponentMultiplicity/Devissage.lean` carries the steps of
   that reduction as hypotheses.

2. `ExteriorDevissage`, the dévissage. Its two halves have different status in this library and
   are deliberately packaged together because the induction consumes them together.

   * The short exact sequence with invertible quotient and rank-`(m + 1)` kernel is the step of
     [Stacks, Tag 0AYP], which **is** available:
     `Stacks.Divisors.exists_modification_hasInvertibleFiltration` of
     `StacksFrontier/AlgebraicGeometry/Divisors/Modification/InvertibleFiltration.lean`. It is not
     used directly for three reasons. It produces the filtration only after a *modification*
     `X' ⟶ X` and only on an *integral* `X`, so consuming it needs the degree's invariance under
     a modification ([Stacks, Tag 0AYU], formalized in
     `StacksFrontier/AlgebraicGeometry/CurveDegreeInvariance/Morphism.lean` with its own carried
     hypotheses) and the reduction to the integral components ([Stacks, Tag 0AYW], likewise);
     and `Stacks.WeilCohomology.HasInvertibleFiltration`, the record it produces, does not carry
     the rank of each stage, which the degree needs, and no lemma in this library recovers the
     rank of the kernel of a short exact sequence from the ranks of the other two terms —
     `AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact` only *relates* three ranks all of
     which are already given.
   * The identification
     `⋀^{m+1}(ℱ) ⊗ ℒ ≅ ⋀^{m+2}(ℰ)` is the isomorphism clause of [Stacks, Tag 0B38]. That clause
     **is** in this library: `Stacks.SheafOfModules.TopWedge.isIso_detComparison` of
     `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExactIso` shows the
     canonical comparison `Stacks.SheafOfModules.TopWedge.detComparison` is an isomorphism in the
     constant-rank form, taking the short exact sequence and the two ranks as its only inputs; the
     general form is in
     `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorShortExactIso`. So this
     half
     of `ExteriorDevissage` is now derivable, and only the short exact sequence of the first half
     is not. (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorPowerShortExact.lean`'s
     own note that "the assertion that the comparison is
     an **isomorphism** is not proved" describes that file, not the library.)

   So `ExteriorDevissage` is exactly the input the source's proof reads off Tags 0AYP and 0B38,
   and nothing more: it says nothing about degrees, Euler characteristics or the base field.

### Rank one, and rank zero

`curveDegree_exteriorPower_one_eq` is the rank-one case with no dévissage hypothesis at all,
since `⋀¹ ℰ ≅ ℰ`; it is also the base case of the induction. Rank zero is **not** covered: at
rank zero `ℰ` is a zero object and `⋀⁰ ℰ` has rank `binom(0,0) = 1`, so the statement compares
`deg(ℰ) = 0` with `deg(⋀⁰ ℰ)`, and closing it needs `⋀⁰ ℰ ≅ 𝒪_X`, which this library does not
have at scheme level — `SheafOfModules.GradedAlgebra` carries no degree-zero unit isomorphism.
The main theorem is therefore stated at rank `n + 1`.

## References

* [Stacks Project, Tag 0DJ5](https://stacks.math.columbia.edu/tag/0DJ5)
* [Stacks Project, Tag 0AYP](https://stacks.math.columbia.edu/tag/0AYP)
* [Stacks Project, Tag 0AYS](https://stacks.math.columbia.edu/tag/0AYS)
* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0B38](https://stacks.math.columbia.edu/tag/0B38)
* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **The top exterior power of a module of constant rank `r` has rank one.** Its rank is
`binom(r, r) = 1` by `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower`.
This is the instance that makes `AlgebraicGeometry.curveDegree` applicable to `⋀ʳ ℰ`. -/
@[sga "6 X 5.1" "special case"]
theorem isFiniteLocallyFreeOfRank_exteriorPower_self {X : Scheme.{u}} (F : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (exteriorPower F (r : ℤ)) 1 := by
  simpa only [Nat.choose_self] using isFiniteLocallyFreeOfRank_exteriorPower F r r

/-- **`⋀¹ ℰ ≅ ℰ`** at the scheme-level spelling of the exterior power. This is
`SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPowerOneIso` for the package
`SheafOfModules.algebras` that `AlgebraicGeometry.Scheme.Modules.exteriorPower` is defined
from. -/
def exteriorPowerOneIsoSelf {X : Scheme.{u}} (F : X.Modules) :
    exteriorPower F (1 : ℤ) ≅ F :=
  (_root_.SheafOfModules.algebras _ F).exteriorPowerOneIso

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- **The one-step dévissage input of [Stacks, Tag 0DJ5], with its determinant comparison.**
For every finite locally free `𝒪_X`-module `ℰ` of constant rank `m + 2` there is a short exact
sequence `0 ⟶ ℱ ⟶ ℰ ⟶ ℒ ⟶ 0` with `ℒ` of rank one and `ℱ` of rank `m + 1`, together with an
isomorphism `⋀^{m+1}(ℱ) ⊗ ℒ ≅ ⋀^{m+2}(ℰ)`.

The first half is the step of [Stacks, Tag 0AYP] with the ranks recorded; the second is the
isomorphism clause of [Stacks, Tag 0B38]. Neither half mentions a degree, a field or a proper
morphism. See this file's implementation notes for why each half is carried rather than taken
from the library. -/
def ExteriorDevissage (X : Scheme.{u}) : Prop :=
  ∀ (m : ℕ) (E : X.Modules),
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 2) →
    ∃ (F L : X.Modules) (i : F ⟶ E) (p : E ⟶ L) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (m + 1) ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 ∧
      Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
            ((Scheme.Modules.exteriorPower F ((m + 1 : ℕ) : ℤ)))).obj (L)) ≅
        Scheme.Modules.exteriorPower E ((m + 2 : ℕ) : ℤ))

/-- **The first equality of [Stacks, Tag 0DJ5] at rank one**, with no hypothesis beyond the
ones `AlgebraicGeometry.curveDegree` already carries: an invertible module is its own top
exterior power, because `⋀¹ ℰ ≅ ℰ`. -/
theorem curveDegree_exteriorPower_one_eq (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 1] :
    curveDegree k f hdim E 1 =
      @curveDegree k _ X f _ hdim (Scheme.Modules.exteriorPower E ((1 : ℕ) : ℤ)) 1
        (Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E 1) := by
  have := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E 1
  exact (curveDegree_eq_of_iso k f hdim 1
    (Scheme.Modules.exteriorPowerOneIsoSelf (X := X) E).symm)

/-- **The first equality of [Stacks, Tag 0DJ5]**: on a proper curve over a field, a finite
locally free module of constant rank `n + 1` has the same degree as its top exterior power,

`deg(ℰ) = deg(⋀^{n+1} ℰ)`.

The induction is the source's. At rank one `⋀¹ ℰ ≅ ℰ`. At rank `m + 2` the dévissage gives
`0 ⟶ ℱ ⟶ ℰ ⟶ ℒ ⟶ 0` with `ℒ` invertible and `ℱ` of rank `m + 1`; the degree is additive along
it ([Stacks, Tag 0AYS]), so `deg(ℰ) = deg(ℱ) + deg(ℒ)`, the inductive hypothesis replaces
`deg(ℱ)` by `deg(⋀^{m+1} ℱ)`, and the determinant comparison `⋀^{m+1}(ℱ) ⊗ ℒ ≅ ⋀^{m+2}(ℰ)`
turns `deg(⋀^{m+1} ℱ) + deg(ℒ)` into `deg(⋀^{m+2} ℰ)` by additivity of the degree in a tensor
product of invertible modules ([Stacks, Tag 0AYX] at ranks one and one).

See this file's implementation notes for the two hypotheses this carries that Tag 0DJ5 does
not. The first equality of the tag with neither, at every rank on a proper scheme of dimension
at most one, is `AlgebraicGeometry.curveDegree_eq_curveDegree_exteriorPower_of_isProper` of
`StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochFull`. -/
theorem curveDegree_eq_curveDegree_exteriorPower_of_devissage (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    (hdev : ExteriorDevissage X)
    (hdim : topologicalKrullDim X ≤ 1) (n : ℕ) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] :
    curveDegree k f hdim E (n + 1) =
      @curveDegree k _ X f _ hdim (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ)) 1
        (Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E (n + 1)) := by
  induction n generalizing E with
  | zero => exact curveDegree_exteriorPower_one_eq k f hdim E
  | succ m ih =>
    obtain ⟨F, L, i, p, w, hS, hF, hL, ⟨t⟩⟩ := hdev m E inferInstance
    have hF := hF
    have hL := hL
    have hdetF := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self F (m + 1)
    have hdetE := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E (m + 2)
    -- The tensor product of the two invertible modules has rank `1 * 1`, which is rank one;
    -- the instance is rebound at the literal `1` so that the three degrees below all read as
    -- degrees of rank-one modules.
    have hTen : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
              ((Scheme.Modules.exteriorPower F ((m + 1 : ℕ) : ℤ)))).obj (L))) 1 :=
      SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X
        (Scheme.Modules.exteriorPower F ((m + 1 : ℕ) : ℤ)) L 1 1
    -- `deg(ℰ) = deg(ℱ) + deg(ℒ)`, by additivity along the dévissage sequence.
    have hadd : curveDegree k f hdim E (m + 2) =
        curveDegree k f hdim F (m + 1) + curveDegree k f hdim L 1 :=
      curveDegree_add_of_shortExact_of_isProper k f hdim
        (ShortComplex.mk i p w) hS (m + 1) (m + 2) 1
    -- `deg(⋀^{m+1} ℱ ⊗ ℒ) = deg(⋀^{m+1} ℱ) + deg(ℒ)`, by additivity in the tensor product.
    have htensor : curveDegree k f hdim
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
                ((Scheme.Modules.exteriorPower F ((m + 1 : ℕ) : ℤ)))).obj (L))) 1 =
        (1 : ℤ) * curveDegree k f hdim
            (Scheme.Modules.exteriorPower F ((m + 1 : ℕ) : ℤ)) 1 +
          (1 : ℤ) * curveDegree k f hdim L 1 :=
      curveDegree_tensorSheaf_eq_add k f hdim
        (Scheme.Modules.exteriorPower F ((m + 1 : ℕ) : ℤ)) L 1 1
    -- The determinant comparison identifies that tensor product with `⋀^{m+2} ℰ`.
    have hiso : curveDegree k f hdim
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
                ((Scheme.Modules.exteriorPower F ((m + 1 : ℕ) : ℤ)))).obj (L))) 1 =
        curveDegree k f hdim (Scheme.Modules.exteriorPower E ((m + 2 : ℕ) : ℤ)) 1 :=
      curveDegree_eq_of_iso k f hdim 1 t
    rw [hadd, ih F, ← hiso, htensor]
    ring

/-- **`deg(⋀ⁿ ℰ) = deg(det(ℰ))` read at the determinant line bundle**: the top exterior power
`⋀ⁿ ℰ` of a finite locally free module of constant rank `n` *is* the determinant line bundle
(`AlgebraicGeometry.Scheme.Modules.isInvertible_exteriorPower_self`), so

`deg(⋀ⁿ ℰ) = deg(det(ℰ))`

is the passage from `AlgebraicGeometry.curveDegree` at rank one to
`AlgebraicGeometry.invertibleCurveDegree`, which is
`AlgebraicGeometry.invertibleCurveDegree_eq_curveDegree`.

This is near-definitional and stated as such, and it assumes an invertibility instance for
`⋀ⁿ ℰ` which [Stacks, Tag 0DJ5] does not assume, so it carries no attribute. The second equality
of that tag, with `det` the annihilator determinant of [Stacks, Tag 0FJN] and with nothing about
the determinant assumed, is the second conjunct of
`AlgebraicGeometry.curveDegree_eq_curveDegree_exteriorPower_eq_invertibleCurveDegree_determinant`
of `StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeExteriorDeterminant`, where the whole tag
is registered. -/
theorem curveDegree_exteriorPower_self_eq_invertibleCurveDegree (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Scheme.Modules.exteriorPower E (n : ℤ))] :
    @curveDegree k _ X f _ hdim (Scheme.Modules.exteriorPower E (n : ℤ)) 1
        (Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E n) =
      invertibleCurveDegree k f hdim (Scheme.Modules.exteriorPower E (n : ℤ)) := by
  have := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E n
  exact (invertibleCurveDegree_eq_curveDegree k f hdim
    (Scheme.Modules.exteriorPower E (n : ℤ))).symm

end AlgebraicGeometry

end
