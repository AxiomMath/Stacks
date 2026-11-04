module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.BaseChangeRows
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.BaseChangeTopRow
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.Statement

/-!
# The identifications of Tag 01XX are compatible with base change

Let `g : S' ⟶ S` be a morphism of schemes, `E` a finite locally free `𝒪_S`-module of constant rank
`n + 1` and `E' ≅ g^*E`. The projective bundle `𝐏(E')` is the base change `S' ×_S 𝐏(E)`, with
`b : 𝐏(E') ⟶ 𝐏(E)` over `g`, and `b^* 𝒪_{𝐏(E)}(d) ⟶ 𝒪_{𝐏(E')}(d)` identifies the twists. The base
change map `g^* R^q π_* 𝒪_{𝐏(E)}(d) ⟶ R^q π'_* 𝒪_{𝐏(E')}(d)` is compatible with the
identifications of [Stacks, Tag 01XX]:

* in the row `q = 0`, `d ≥ 0`, it is `g^* Sym^d(E) = Sym^d(E')` under
  `R⁰π_* 𝒪(d) ≅ Sym^d(E)` and `R⁰π'_* 𝒪(d) ≅ Sym^d(E')`;
* in the row `q = n`, every `d`, it is the canonical map
  `g^* SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S) ⟶ SheafHom(g^*(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E), 𝒪_{S'})`
  followed by `g^*(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E) ≅ Sym^{-n-1-d}(E') ⊗ ⋀ⁿ⁺¹ E'`, under
  `Rⁿ π_* 𝒪(d) ≅ SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)` and its analogue for `E'`;
* in the rows where both sides vanish it is an isomorphism of zero modules.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.bundleTwistBaseChange`: the base change
  map on the higher direct images of the twists of the projective bundle of `E`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.bundleSymBaseChange`: the identification
  `g^* Sym^d(E) ≅ Sym^d(E')`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.bundleTopTargetBaseChange`: the base change
  map `g^* SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S) ⟶ SheafHom(Sym^{-n-1-d}(E') ⊗ ⋀ⁿ⁺¹ E', 𝒪_{S'})`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.higherDirectImageZeroIso_baseChange`:
  the row `q = 0` is compatible with base change.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.higherDirectImageTopIso_baseChange`:
  the row `q = n` is compatible with base change.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isIso_bundleTwistBaseChange_of_ne`: the
  vanishing rows are compatible with base change.

## References

* [Stacks Project, Tag 01XX](https://stacks.math.columbia.edu/tag/01XX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

variable {S S' : Scheme.{u}} (g : S' ⟶ S) (E : S.Modules) {n : ℕ}
  (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1)) (E' : S'.Modules)
  (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

include hfree hE in
/-- A module isomorphic to the pullback of a finite locally free module of constant rank `r` is
finite locally free of constant rank `r`. -/
public theorem isFiniteLocallyFreeOfRank_of_iso_pullback :
    Scheme.Modules.IsFiniteLocallyFreeOfRank E' (n + 1) :=
  Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso hE.symm
    ((Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mpr
      (have := (Scheme.Modules.isFiniteLocallyFreeOfRank_iff E (n + 1)).mp hfree
      AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g E (n + 1)))

variable (D : TwistData (bundleAlgebra E hfree))
  (D' : TwistData (bundleAlgebra E' (isFiniteLocallyFreeOfRank_of_iso_pullback g E hfree E' hE)))

/-- **The base change map on the higher direct images of the twists** of the projective bundle of
a finite locally free module: `g^* R^q π_* 𝒪_{𝐏(E)}(d) ⟶ R^q π'_*(b^* 𝒪_{𝐏(E)}(d)) ⟶
R^q π'_* 𝒪_{𝐏(E')}(d)`. -/
public def bundleTwistBaseChange (q : ℕ) (d : ℤ) :
    (Scheme.Modules.pullback g).obj
        (((Scheme.Modules.pushforward
            (relativeProj (bundleAlgebra E hfree)).toBase).rightDerivedPlus (q : ℤ)).obj
          (D.algebra.piece d)) ⟶
      ((Scheme.Modules.pushforward (relativeProj (bundleAlgebra E'
          (isFiniteLocallyFreeOfRank_of_iso_pullback g E hfree E' hE))).toBase).rightDerivedPlus
        (q : ℤ)).obj (D'.algebra.piece d) :=
  haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E'
    (isFiniteLocallyFreeOfRank_of_iso_pullback g E hfree E' hE)
  twistBaseChange g E (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E) E'
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E') hE D D' q d

/-- **The identification `g^* Sym^d(E) ≅ Sym^d(E')`**, through `E' ≅ g^*E`. -/
public def bundleSymBaseChange (d : ℤ) :
    (Scheme.Modules.pullback g).obj ((bundleAlgebra E hfree).piece d) ⟶
      (bundleAlgebra E' (isFiniteLocallyFreeOfRank_of_iso_pullback g E hfree E' hE)).piece d :=
  haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E'
    (isFiniteLocallyFreeOfRank_of_iso_pullback g E hfree E' hE)
  (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app d

/-- The identification `g^* Sym^d(E) ≅ Sym^d(E')` is an isomorphism. -/
public instance isIso_bundleSymBaseChange (d : ℤ) :
    IsIso (bundleSymBaseChange g E hfree E' hE d) :=
  haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E'
    (isFiniteLocallyFreeOfRank_of_iso_pullback g E hfree E' hE)
  Stacks.RelativeProj.isIso_symmetricSituationPullbackHom_app g E E' hE d

/-- **[Stacks, Tag 01XX], compatibility with base change, the row `q = 0`**: for a morphism of
schemes `g : S' ⟶ S`, `E` finite locally free of constant rank `n + 1` with `n ≥ 1`, `E' ≅ g^*E`
and every `d ≥ 0`, the base change map `g^* R⁰π_* 𝒪_{𝐏(E)}(d) ⟶ R⁰π'_* 𝒪_{𝐏(E')}(d)` corresponds,
under the identifications `R⁰π_* 𝒪(d) ≅ Sym^d(E)` and `R⁰π'_* 𝒪(d) ≅ Sym^d(E')`, to
`g^* Sym^d(E) ≅ Sym^d(E')`. -/
@[stacks 01XX "compatibility with base change, the q = 0 row: for g : S' → S and E' ≅ g^*E, the \
base change map g^* R^0 π_* O(d) → R^0 π'_* O(d) followed by R^0 π'_* O(d) ≅ Sym^d(E') is \
g^*(R^0 π_* O(d) ≅ Sym^d(E)) followed by g^* Sym^d(E) ≅ Sym^d(E'), for every d ≥ 0 and n ≥ 1"]
public theorem higherDirectImageZeroIso_baseChange (hn : 1 ≤ n) (d : ℕ) :
    bundleTwistBaseChange g E hfree E' hE D D' 0 (d : ℤ) ≫
        (higherDirectImageZeroIso E' (isFiniteLocallyFreeOfRank_of_iso_pullback g E hfree E' hE)
          D' hn d).hom =
      (Scheme.Modules.pullback g).map (higherDirectImageZeroIso E hfree D hn d).hom ≫
        bundleSymBaseChange g E hfree E' hE (d : ℤ) :=
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E'
    (isFiniteLocallyFreeOfRank_of_iso_pullback g E hfree E' hE)
  twistBaseChange_zeroIso g E _ E' _ hE D D' hn hfree
    (isFiniteLocallyFreeOfRank_of_iso_pullback g E hfree E' hE) d

/-- **The base change map of the target of the row `q = n`**: the canonical map
`g^* SheafHom(M, 𝒪_S) ⟶ SheafHom(g^* M, 𝒪_{S'})` for `M = Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E`, followed by
the dual of `g^*(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E) ≅ Sym^{-n-1-d}(E') ⊗ ⋀ⁿ⁺¹ E'`. -/
public def bundleTopTargetBaseChange (d : ℤ) :
    (Scheme.Modules.pullback g).obj
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
          ((Stacks.ProjectionFormula.tensorRightInvertible S
            (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).obj
            ((bundleAlgebra E hfree).piece (-(n : ℤ) - 1 - d)))) ⟶
      Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        ((Stacks.ProjectionFormula.tensorRightInvertible S'
          (Scheme.Modules.exteriorPower E' ((n + 1 : ℕ) : ℤ))).obj
          ((bundleAlgebra E' (isFiniteLocallyFreeOfRank_of_iso_pullback g E hfree E' hE)).piece
            (-(n : ℤ) - 1 - d))) :=
  haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  haveI := isQuasicoherent_of_isFiniteLocallyFreeOfRank E'
    (isFiniteLocallyFreeOfRank_of_iso_pullback g E hfree E' hE)
  topRowTargetBaseChange g E (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E) E'
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E') hE n d

/-- **[Stacks, Tag 01XX], compatibility with base change, the row `q = n`**: for a morphism of
schemes `g : S' ⟶ S`, `E` finite locally free of constant rank `n + 1` with `n ≥ 1`, `E' ≅ g^*E`
and every integer `d`, the base change map `g^* Rⁿ π_* 𝒪_{𝐏(E)}(d) ⟶ Rⁿ π'_* 𝒪_{𝐏(E')}(d)`
corresponds, under the identifications `Rⁿ π_* 𝒪(d) ≅ SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)`
and `Rⁿ π'_* 𝒪(d) ≅ SheafHom(Sym^{-n-1-d}(E') ⊗ ⋀ⁿ⁺¹ E', 𝒪_{S'})`, to the canonical map
`g^* SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S) ⟶ SheafHom(Sym^{-n-1-d}(E') ⊗ ⋀ⁿ⁺¹ E', 𝒪_{S'})`. -/
@[stacks 01XX "compatibility with base change, the q = n row: for g : S' → S and E' ≅ g^*E, the \
base change map g^* R^n π_* O(d) → R^n π'_* O(d) followed by R^n π'_* O(d) ≅ \
SheafHom(Sym^(-n-1-d)(E') ⊗ ∧^(n+1) E', O_S') is g^*(R^n π_* O(d) ≅ SheafHom(Sym^(-n-1-d)(E) ⊗ \
∧^(n+1) E, O_S)) followed by the canonical map g^* SheafHom(M, O_S) → SheafHom(g^* M, O_S') and \
g^*(Sym^(-n-1-d)(E) ⊗ ∧^(n+1) E) ≅ Sym^(-n-1-d)(E') ⊗ ∧^(n+1) E', for every integer d and n ≥ 1"]
public theorem higherDirectImageTopIso_baseChange (hn : 1 ≤ n) (d : ℤ) :
    bundleTwistBaseChange g E hfree E' hE D D' n d ≫
        (higherDirectImageTopIso E' (isFiniteLocallyFreeOfRank_of_iso_pullback g E hfree E' hE)
          D' hn d).hom =
      (Scheme.Modules.pullback g).map (higherDirectImageTopIso E hfree D hn d).hom ≫
        bundleTopTargetBaseChange g E hfree E' hE d :=
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E hfree
  have := isQuasicoherent_of_isFiniteLocallyFreeOfRank E'
    (isFiniteLocallyFreeOfRank_of_iso_pullback g E hfree E' hE)
  topRowIso_baseChange g E _ E' _ hE D D' hn hfree
    (isFiniteLocallyFreeOfRank_of_iso_pullback g E hfree E' hE) d

/-- **[Stacks, Tag 01XX], compatibility with base change, the vanishing rows**: for `q ≠ 0, n` the
base change map `g^* R^q π_* 𝒪_{𝐏(E)}(d) ⟶ R^q π'_* 𝒪_{𝐏(E')}(d)` is an isomorphism of zero
modules, for every integer `d`. -/
@[stacks 01XX "compatibility with base change, the vanishing rows: for g : S' → S, E' ≅ g^*E and \
q ≠ 0, n the base change map g^* R^q π_* O(d) → R^q π'_* O(d) is an isomorphism between zero \
modules, for every integer d"]
public theorem isIso_bundleTwistBaseChange_of_ne (q : ℕ) (d : ℤ) (hq0 : q ≠ 0) (hqn : q ≠ n) :
    IsIso (bundleTwistBaseChange g E hfree E' hE D D' q d) := by
  have h₁ := isZero_higherDirectImage_twist E hfree D d (q : ℤ) (by exact_mod_cast hq0)
    (by exact_mod_cast hqn)
  have h₂ := isZero_higherDirectImage_twist E'
    (isFiniteLocallyFreeOfRank_of_iso_pullback g E hfree E' hE) D' d (q : ℤ)
    (by exact_mod_cast hq0) (by exact_mod_cast hqn)
  exact isIso_of_source_target_iso_zero _ ((Scheme.Modules.pullback g).map_isZero h₁).isoZero
    h₂.isoZero

/-- **[Stacks, Tag 01XX], compatibility with base change, the row `q = 0` for `d < 0`**: the base
change map `g^* R⁰π_* 𝒪_{𝐏(E)}(d) ⟶ R⁰π'_* 𝒪_{𝐏(E')}(d)` is an isomorphism of zero modules. -/
@[stacks 01XX "compatibility with base change, the q = 0 row for d < 0: for g : S' → S and \
E' ≅ g^*E the base change map g^* R^0 π_* O(d) → R^0 π'_* O(d) is an isomorphism between zero \
modules, for n ≥ 1"]
public theorem isIso_bundleTwistBaseChange_zero_of_neg (hn : 1 ≤ n) {d : ℤ} (hd : d < 0) :
    IsIso (bundleTwistBaseChange g E hfree E' hE D D' 0 d) := by
  have h₁ := (isZero_higherDirectImage_zero_of_neg E hfree D hn hd).1
  have h₂ := (isZero_higherDirectImage_zero_of_neg E'
    (isFiniteLocallyFreeOfRank_of_iso_pullback g E hfree E' hE) D' hn hd).1
  exact isIso_of_source_target_iso_zero _ ((Scheme.Modules.pullback g).map_isZero h₁).isoZero
    h₂.isoZero

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
