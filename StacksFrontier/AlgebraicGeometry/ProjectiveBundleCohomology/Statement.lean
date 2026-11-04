module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.DegreeZero
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRow
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowPairing
public import StacksFrontier.AlgebraicGeometry.SymAlgebraQcohPieces.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Higher direct images of the twists on a projective bundle

Let `S` be a scheme, `n ≥ 1`, `E` a finite locally free `𝒪_S`-module of constant rank `n + 1`,
and `π : 𝐏(E) = Proj_S(Sym(E)) ⟶ S` its projective bundle, with twists `𝒪_{𝐏(E)}(d)` given by a
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` (Tag 01NR; one exists by
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` and it is unique up to
unique isomorphism). This file states the rows of [Stacks, Tag 01XX]:

* `R^q π_* 𝒪_{𝐏(E)}(d) = 0` for `q ≠ 0, n`;
* `R^0 π_* 𝒪_{𝐏(E)}(d) = Sym^d(E)`, through the canonical map `Sym^d(E) ⟶ π_* 𝒪_{𝐏(E)}(d)`
  of Tag 01NR, which is an isomorphism, and the vanishing of both sides for `d < 0`;
* `R^n π_* 𝒪_{𝐏(E)}(d) = SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)` for every integer `d`.

The graded algebra `Sym(E)` needs its pieces quasi-coherent to be an input of the relative
`Proj`; that is automatic for a finite locally free `E`, and `bundleAlgebra` is `Sym(E)` with
that quasi-coherence supplied.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.bundleAlgebra`: `Sym(E)` as the graded
  algebra of the projective bundle of a finite locally free `E`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isZero_higherDirectImage_twist`:
  `R^q π_* 𝒪(d) = 0` for `q ≠ 0, n`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isIso_symToPushforwardTwist`:
  `Sym^d(E) ⟶ π_* 𝒪(d)` is an isomorphism for `d ≥ 0`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.higherDirectImageZeroIso`:
  `R^0 π_* 𝒪(d) ≅ Sym^d(E)` for `d ≥ 0`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isZero_higherDirectImage_zero_of_neg`:
  `R^0 π_* 𝒪(d) = 0 = Sym^d(E)` for `d < 0`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.higherDirectImageTopIso`:
  `Rⁿ π_* 𝒪(d) ≅ SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)` for every integer `d`.

## References

* [Stacks Project, Tag 01XX](https://stacks.math.columbia.edu/tag/01XX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

variable {S : Scheme.{u}} (E : S.Modules) {r : ℕ}

/-- `Sym(E)`, as the quasi-coherent graded algebra whose relative `Proj` is the projective bundle
`𝐏(E)`, for `E` finite locally free of constant rank. -/
public abbrev bundleAlgebra (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E r) :
    SheafGradedAlgebra S :=
  haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  Stacks.SymGraded.schemeSheafGradedAlgebra E
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)

variable {n : ℕ} (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
  (D : TwistData (bundleAlgebra E hfree))

/-- For `E` finite locally free of constant rank `n + 1` with projective bundle `π : 𝐏(E) ⟶ S`,
`R^q π_* 𝒪_{𝐏(E)}(d) = 0` for every integer `d` and every integer `q` with `q ≠ 0` and `q ≠ n`. -/
@[stacks 01XX "the vanishing row: R^q π_* O(d) = 0 for q ≠ 0, n, every integer d and every \
integer q, for E finite locally free of constant rank n + 1 over an arbitrary scheme S",
  ega "III 2.1.15" "partial"]
public theorem isZero_higherDirectImage_twist (d q : ℤ) (hq0 : q ≠ 0) (hqn : q ≠ n) :
    IsZero (((Scheme.Modules.pushforward
        (relativeProj (bundleAlgebra E hfree)).toBase).rightDerivedPlus
      q).obj (D.algebra.piece d)) :=
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  isZero_rightDerivedPlus_pushforward_twist_of_ne E _ n hfree D d q hq0 hqn

/-- **The canonical map `Sym^d(E) ⟶ π_* 𝒪_{𝐏(E)}(d)` is an isomorphism**, for `n ≥ 1` and
`d ≥ 0`. -/
@[stacks 01XX "the q = 0 row in degrees d ≥ 0, in the canonical form: the map \
Sym^d(E) → π_* O(d) of Tag 01NR is an isomorphism, for n ≥ 1"]
public theorem isIso_symToPushforwardTwist (hn : 1 ≤ n) (d : ℕ) : IsIso (D.ψ d) :=
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  isIso_psi E _ D hn hfree d

/-- `R^0 π_* 𝒪_{𝐏(E)}(d) ≅ Sym^d(E)` for `d ≥ 0`: the comparison `R^0π_* = π_*` of
[Stacks, Tag 05TD] followed by the inverse of the canonical map of Tag 01NR. -/
@[stacks 01XX "the q = 0 row, d ≥ 0: R^0 π_* O(d) ≅ Sym^d(E), for n ≥ 1"]
public def higherDirectImageZeroIso (hn : 1 ≤ n) (d : ℕ) :
    ((Scheme.Modules.pushforward (relativeProj (bundleAlgebra E hfree)).toBase).rightDerivedPlus
      0).obj (D.algebra.piece (d : ℤ)) ≅ (bundleAlgebra E hfree).piece (d : ℤ) :=
  haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  zeroIso E _ D hn hfree d

/-- For `d < 0`, both `R^0 π_* 𝒪_{𝐏(E)}(d)` and `Sym^d(E)` vanish. -/
@[stacks 01XX "the q = 0 row, d < 0: R^0 π_* O(d) = 0 = Sym^d(E), for n ≥ 1"]
public theorem isZero_higherDirectImage_zero_of_neg (hn : 1 ≤ n) {d : ℤ} (hd : d < 0) :
    IsZero (((Scheme.Modules.pushforward
        (relativeProj (bundleAlgebra E hfree)).toBase).rightDerivedPlus
      0).obj (D.algebra.piece d)) ∧ IsZero ((bundleAlgebra E hfree).piece d) :=
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  ⟨isZero_rightDerivedPlus_zero_of_neg E _ D hn hfree hd,
    (bundleAlgebra E hfree).negative_isZero d hd⟩

/-- For `n ≥ 1` and every integer `d`,
`Rⁿ π_* 𝒪_{𝐏(E)}(d) ≅ SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)`. For `d ≤ -n - 1` it is induced
by the multiplication pairing `𝒪(d) ⊗ π^* Sym^{-n-1-d}(E) ⟶ 𝒪(-n-1)` and the trace
`Rⁿ π_* 𝒪(-n-1) ≅ (⋀ⁿ⁺¹ E)^∨`; for `d ≥ -n` both sides vanish. -/
@[stacks 01XX "the q = n row, every integer d: R^n π_* O(d) ≅ SheafHom(Sym^(-n-1-d)(E) ⊗ \
∧^(n+1) E, O_S), for E finite locally free of constant rank n + 1 over an arbitrary scheme S, \
n ≥ 1", ega "III 2.1.16" "(ii)"]
public def higherDirectImageTopIso (hn : 1 ≤ n) (d : ℤ) :
    ((Scheme.Modules.pushforward (relativeProj (bundleAlgebra E hfree)).toBase).rightDerivedPlus
      (n : ℤ)).obj (D.algebra.piece d) ≅
      Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        ((Stacks.ProjectionFormula.tensorRightInvertible S
          (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).obj
          ((bundleAlgebra E hfree).piece (-(n : ℤ) - 1 - d))) :=
  haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  topRowIso E _ D hn hfree d

/-- The row `q = n` at `d = -n - 1`:
`Rⁿ π_* 𝒪_{𝐏(E)}(-n-1) ≅ SheafHom(Sym⁰(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)`, the trace of the Koszul complex of
the tautological surjection `π^* E ⟶ 𝒪(1)`, for `n ≥ 1`. -/
public def higherDirectImageTopIsoOfEq (hn : 1 ≤ n) {d : ℤ} (hd : d = -(n : ℤ) - 1) :
    ((Scheme.Modules.pushforward (relativeProj (bundleAlgebra E hfree)).toBase).rightDerivedPlus
      (n : ℤ)).obj (D.algebra.piece d) ≅
      Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        ((Stacks.ProjectionFormula.tensorRightInvertible S
          (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).obj
          ((bundleAlgebra E hfree).piece (-(n : ℤ) - 1 - d))) :=
  haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  topRowIsoOfEq E _ D hn hfree hd

/-- The row `q = n` for `d ≥ -n`: both `Rⁿ π_* 𝒪_{𝐏(E)}(d)` and
`SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)` vanish, for `n ≥ 1`. -/
public theorem isZero_higherDirectImage_top_of_le (hn : 1 ≤ n) {d : ℤ} (hd : -(n : ℤ) ≤ d) :
    IsZero (((Scheme.Modules.pushforward
        (relativeProj (bundleAlgebra E hfree)).toBase).rightDerivedPlus
      (n : ℤ)).obj (D.algebra.piece d)) ∧
      IsZero (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        ((Stacks.ProjectionFormula.tensorRightInvertible S
          (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).obj
          ((bundleAlgebra E hfree).piece (-(n : ℤ) - 1 - d)))) :=
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  isZero_topRow_of_le E _ D hn hfree hd

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
