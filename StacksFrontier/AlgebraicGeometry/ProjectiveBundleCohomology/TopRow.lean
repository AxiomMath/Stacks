module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopTrace
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.Adjunction

/-!
# The row `q = n` of the higher direct images of the twists on a projective bundle

Let `E` be finite locally free of constant rank `n + 1 ≥ 2` on a scheme `S` and `π : 𝐏(E) ⟶ S`
its projective bundle. Write `Sym^k(E)` for the degree-`k` piece of `Sym(E)`, which is zero for
`k < 0`. The row `q = n` of [Stacks, Tag 01XX] reads

`Rⁿ π_* 𝒪(d) ≅ SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)`.

This file proves it for `d ≥ -n - 1`: at `d = -n - 1` it is the trace of the Koszul filtration,
and for `d ≥ -n` both sides vanish.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isZero_dualSheaf_of_isZero`: the dual of a
  zero module is zero.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.topRowIsoOfEq`: the row at `d = -n - 1`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isZero_topRow_of_lt`: both sides vanish for
  `d ≥ -n`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf dualMap dualFunctor)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

/-- **The dual of a zero module is zero.** -/
public theorem isZero_dualSheaf_of_isZero {X : Scheme.{u}} {F : X.Modules} (hF : IsZero F) :
    IsZero (dualSheaf F) := by
  refine (IsZero.iff_id_eq_zero _).2 ?_
  have h : dualMap (𝟙 F) = dualMap (0 : F ⟶ F) := congrArg dualMap (hF.eq_of_src _ _)
  refine (Stacks.AlgebraicGeometry.ReflexiveModules.dualMap_id F).symm.trans (h.trans ?_)
  refine Stacks.AlgebraicGeometry.ReflexiveModules.hom_ext_dualSheaf fun U x W y => ?_
  rw [Stacks.AlgebraicGeometry.ReflexiveModules.dualPairing_dualMap]
  show (x.app (op W)).hom ((0 : F ⟶ F).val.app (op W.left) y) = 0
  exact (congrArg (x.app (op W)).hom (by rfl : (0 : F ⟶ F).val.app (op W.left) y = 0)).trans
    (map_zero _)

attribute [local instance 10000] HasDerivedCategory.standard

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc))

/-- **The right-hand side of the row `q = n`**: `SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)`. -/
public abbrev topRowTarget (n : ℕ) (d : ℤ) : S.Modules :=
  dualSheaf ((Stacks.ProjectionFormula.tensorRightInvertible S
    (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).obj
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (-(n : ℤ) - 1 - d)))

/-- `Sym⁰(E) ⊗ ⋀ⁿ⁺¹ E ≅ ⋀ⁿ⁺¹ E`. -/
public def symZeroTensorIso (n : ℕ) {d : ℤ} (hd : d = -(n : ℤ) - 1) :
    (Stacks.ProjectionFormula.tensorRightInvertible S
        (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).obj
        ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (-(n : ℤ) - 1 - d)) ≅
      Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ) :=
  (Stacks.ProjectionFormula.tensorRightInvertible S
      (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).mapIso
      (eqToIso (congrArg (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece
        (by rw [hd]; ring)) ≪≫ Stacks.SymGraded.pieceZeroIso E) ≪≫
    Stacks.SheafOfModules.tensorSheafLeftUnitor S.presheaf S.ringCatSheaf.2 _

variable {n : ℕ} (hn : 1 ≤ n) (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
include hn hfree

/-- **The row `q = n` at `d = -n - 1`**:
`Rⁿ π_* 𝒪(-n-1) ≅ SheafHom(Sym⁰(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)`. -/
public def topRowIsoOfEq {d : ℤ} (hd : d = -(n : ℤ) - 1) :
    ((bundlePushforward E hqc).rightDerivedPlus (n : ℤ)).obj (D.algebra.piece d) ≅
      topRowTarget E hqc n d :=
  ((bundlePushforward E hqc).rightDerivedPlus (n : ℤ)).mapIso
      (eqToIso (congrArg D.algebra.piece (by rw [hd]; push_cast; ring))) ≪≫
    ((Stacks.DerivedIndexing.rightDerivedIso (bundlePushforward E hqc) n).app _).symm ≪≫
    topTwistIsoDualDet E hqc D hn hfree ≪≫
    (dualFunctor S).mapIso (symZeroTensorIso E hqc n hd).op

/-- **The row `q = n` for `d ≥ -n`**: both `Rⁿ π_* 𝒪(d)` and
`SheafHom(Sym^{-n-1-d}(E) ⊗ ⋀ⁿ⁺¹ E, 𝒪_S)` vanish. -/
public theorem isZero_topRow_of_le {d : ℤ} (hd : -(n : ℤ) ≤ d) :
    IsZero (((bundlePushforward E hqc).rightDerivedPlus (n : ℤ)).obj (D.algebra.piece d)) ∧
      IsZero (topRowTarget E hqc n d) := by
  refine ⟨isZero_rightDerivedPlus_pushforward_twist_top E hqc hn hfree D d hd,
    isZero_dualSheaf_of_isZero ?_⟩
  have := isInvertible_det E hn hfree
  exact (Stacks.ProjectionFormula.tensorRightInvertible S _).map_isZero
    ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).negative_isZero _ (by omega))

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
