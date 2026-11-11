module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.HodgeWeilCohomologyTheory
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClassCycleClassIntegral
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassWeilThree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DivisorAmpleDegree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ZeroCycleTraceDegree

/-!
# The Hodge first Chern class of a nonzero effective Cartier divisor on a surface

Let `k` be a field of characteristic zero, let `X` be a smooth projective scheme over `k` of pure
dimension `2` and let `D ⊆ X` be a nonempty effective Cartier divisor. Then the Hodge first Chern
class

  `c₁^{Hodge}(𝒪_X(D)) ∈ H¹(X, Ω_{X/k})`

(the image of the class of `𝒪_X(D)` under `d log : H¹(X, 𝒪_X^*) ⟶ H¹(X, Ω_{X/k})`, Stacks
Section 0FLE) is nonzero.

The proof uses that Hodge cohomology is a Weil cohomology theory in characteristic zero (Remark
0FWE, `Stacks.HodgeWeil.exists_weilCohomologyTheory_hodge`). Let `γ` be its cycle class map and `∫`
its trace. By Tag 0FIF, `γ([D]) = c₁^{Hodge}(𝒪_X(D))`
(`IsCohomologicalChernCharacter.codimensionCycleClass_divisor`).
Choose an ample invertible module `𝓛` on `X` (`X` is projective) and put
`θ = c₁(𝓛) ∩ [X] ∈ CH^1(X)`. If `c₁^{Hodge}(𝒪_X(D)) = 0`, then by axiom (C)(c)
`γ([D] · θ) = γ([D]) ∪ γ(θ) = 0`, hence by Tag 0FHR `deg([D] · θ) = ∫ γ([D] · θ) = 0` in `k`.
But `deg([D] · θ) = deg_𝓛(D) > 0`
(`Stacks.WeilCohomology.codimensionDegree_closedSubschemeClass_mul_firstChernCap`, Stacks 0BEV),
and `k` has characteristic zero.

This is the input "`c₁(L) ≠ 0` for `L = 𝒪(D)`" of the obstruction calculation in the proof of
Stacks 0D1R (the stack of proper flat algebraic spaces is not algebraic).

## Main results

* `Stacks.HodgeWeil.hodgeFirstChernClassModule_divisorSheaf_ne_zero`: the statement for a smooth
  projective scheme over `k`, in the module realization of Hodge cohomology.
* `AlgebraicGeometry.Scheme.Hom.hodgeFirstChernClass_ne_zero_of_isEffectiveCartierDivisor`: the
  statement for `f : X ⟶ Spec k` smooth, projective, of relative dimension `2`, in the abelian
  realization `H¹(X, Ω_{X/k})` of Section 0FLE.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme

universe u

namespace Stacks.HodgeWeil

variable {k : Type u} [Field k]

/-- **`c₁^{Hodge}(𝒪_X(D)) ≠ 0`** for a nonempty effective Cartier divisor `D` on a smooth
projective scheme `X` of pure dimension `2` over a field of characteristic zero, the Hodge first
Chern class being read in `H¹(X, Ω¹_{X/k})` (module realization). -/
theorem hodgeFirstChernClassModule_divisorSheaf_ne_zero [CharZero k]
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (hX : AlgebraicGeometry.RelativeDimension X.obj.hom 2) (D : X.obj.left.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hD : D ≠ ⊤) :
    hodgeFirstChernClassModule X.obj.hom
        (picardClassOf X.obj.left (Stacks.Divisors.divisorSheaf D)
          (Stacks.Divisors.isInvertible_divisorSheaf D)) ≠ 0 := by
  intro h0
  obtain ⟨W, ch, h, hW⟩ := exists_weilCohomologyTheory_hodge (k := k)
  -- an ample invertible module on `X`
  have hS : HasAmpleInvertibleSheaf (Spec (.of k)) := (hasAmpleInvertibleSheaf_iff _).mpr
    ⟨Stacks.Ample.unitModule _, inferInstance, Stacks.Ample.isAmple_unitModule_of_isAffine _⟩
  obtain ⟨-, L, hLinv, hLamp⟩ :=
    (isProjective_iff_isProper_and_hasAmpleInvertibleSheaf X.obj.hom hS).mp
      (SmoothProjectiveScheme.isProjective X)
  have : SheafOfModules.IsInvertible X.obj.left.presheaf X.obj.left.ringCatSheaf.2 L := hLinv
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
      (hM := @GenuineChern.isFiniteLocallyFreeOfRank_one_of_isInvertible X.obj.left L ‹_›)
  have hdeg := codimensionDegree_closedSubschemeClass_mul_firstChernCap X hX D hD L hLamp
  have hpos := degreeWithRespectTo_pos k X.obj.hom D.subschemeι 1
    (topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor X.obj.hom 1 hX D hD) L hLamp
  have hne : IsNonemptyEquidimensional X 2 :=
    ⟨⟨D.subschemeι.base (Stacks.Divisors.nonempty_subscheme_of_ne_top D hD).some⟩, hX⟩
  -- `c₁^{Hodge}(𝒪_X(D)) = 0` gives `γ([D]) = 0`
  have hc₁ : (hodgeFirstChernClassData k).c₁ X (picardClassOf X.obj.left
      (Stacks.Divisors.divisorSheaf D) (Stacks.Divisors.isInvertible_divisorSheaf D)) = 0 := by
    have hp : hodgeFirstChernClassPiece X (picardClassOf X.obj.left
        (Stacks.Divisors.divisorSheaf D) (Stacks.Divisors.isInvertible_divisorSheaf D)) = 0 := by
      change (DirectSum.of (fun i : HodgeBidegreeInt 2 =>
        (AlgebraicGeometry.SheafOfModules.hodgeCohomologyComponent (formsAlgebras X.obj.hom)
          i.1.1 (i.1.2 : ℤ) : Type u)) bidegreeOneOne) (hodgeFirstChernClassModule X.obj.hom _) = 0
      exact (congrArg (DirectSum.of _ bidegreeOneOne) h0).trans (map_zero _)
    change hodgeFirstChernClassTw X _ = 0
    simp only [hodgeFirstChernClassTw, AddMonoidHom.coe_comp, Function.comp_apply, hp, map_zero]
  have hγ : h.codimensionCycleClass X 1 (closedSubschemeClass X.obj.hom D.subschemeι 1) = 0 :=
    (h.codimensionCycleClass_divisor (hodge_coproductAxiom k) (hodge_projectiveBundleAxiom k) X
      D).trans hc₁
  have hWγ : W.cycleClass X ((1 : ℕ) : ℤ) (closedSubschemeClass X.obj.hom D.subschemeι 1) = 0 := by
    have key₀ : ∀ V : WeilData k k, V = h.toWeilData (hodge_coproductAxiom k)
        (hodge_projectiveBundleAxiom k) (hodge_kunnethAxiom k) (hodge_traceAxiom k h) →
        V.cycleClass X ((1 : ℕ) : ℤ) (closedSubschemeClass X.obj.hom D.subschemeι 1) = 0 := by
      rintro V rfl
      apply FirstChernClassData.tateTwistMap_subtype_injective (𝔇 := hodgeFirstChernClassData k)
        X (2 * ((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ)
      exact ((h.tateTwistMap_toWeilData_cycleClass (hodge_coproductAxiom k)
        (hodge_projectiveBundleAxiom k) (hodge_kunnethAxiom k) (hodge_traceAxiom k h) X 1
        (closedSubschemeClass X.obj.hom D.subschemeι 1)).trans hγ).trans (map_zero _).symm
    exact key₀ _ hW
  -- hence `γ([D] · θ) = γ([D]) ∪ γ(θ) = 0`
  set θ := totalChowClassCapFundamental X.obj.hom
    (totalChernKClass (fieldChowSituation k) X.obj.hom (VectorBundleKZero.classOf X.obj.left L)) 1
  set β := codimensionIntersectionProduct k X.obj.hom 1 ((1 : ℕ) : ℤ)
    (closedSubschemeClass X.obj.hom D.subschemeι 1) θ
  have key : ∀ (j : ℤ) (hj : 1 + ((1 : ℕ) : ℤ) = j),
      W.cycleClass X j (codimensionChowGroupCongr X.obj.hom hj β) = 0 := by
    rintro j rfl
    refine (W.cycleClassAxiom.mul X 1 ((1 : ℕ) : ℤ) _ θ).trans ?_
    rw [show W.cycleClass X 1 (closedSubschemeClass X.obj.hom D.subschemeι 1) = 0 from hWγ,
      LinearMap.map_zero₂]
  have htr := WeilData.trace_cycleClass_eq_codimensionDegree W.poincareDuality W.kunneth
    W.cycleClassAxiom hne (codimensionChowGroupCongr X.obj.hom (by norm_num) β)
  rw [key _ _, map_zero, hdeg] at htr
  have : (degreeWithRespectTo k X.obj.hom D.subschemeι 1
      (topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor X.obj.hom 1 hX D hD) L
      hLamp : ℤ) = 0 := by exact_mod_cast htr.symm
  omega

end Stacks.HodgeWeil

namespace AlgebraicGeometry.Scheme.Hom

/-- **The Hodge first Chern class of a nonzero effective Cartier divisor on a surface does not
vanish.** Let `k` be a field of characteristic zero and `f : X ⟶ Spec k` smooth and projective of
relative dimension `2`, and let `D ⊆ X` be an effective Cartier divisor with `D ≠ ∅` (`D ≠ ⊤` as an
ideal sheaf). Then the Hodge first Chern class
`c₁^{Hodge}(𝒪_X(D)) ∈ H¹(X, Ω_{X/k})` of Section 0FLE (`d log` on `H¹(X, 𝒪_X^*) = Pic(X)`) is
nonzero; `c` is any name for the class of `𝒪_X(D)` in `Pic(X)`. -/
theorem hodgeFirstChernClass_ne_zero_of_isEffectiveCartierDivisor {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] (hf : IsProjective f)
    (hX : AlgebraicGeometry.RelativeDimension f 2) (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hD : D ≠ ⊤) (c : Stacks.Picard.ofScheme X)
    (hc : c = picardClassOf X (Stacks.Divisors.divisorSheaf D)
      (Stacks.Divisors.isInvertible_divisorSheaf D)) :
    Scheme.Hom.hodgeFirstChernClass f c ≠ 0 := by
  intro h
  let Y : (SmoothProjectiveScheme k).FullSubcategory := ⟨Over.mk f, ‹Smooth f›, hf⟩
  have : Stacks.Divisors.IsEffectiveCartierDivisor (show Y.obj.left.IdealSheafData from D) := ‹_›
  apply Stacks.HodgeWeil.hodgeFirstChernClassModule_divisorSheaf_ne_zero Y hX D hD
  subst hc
  change (Stacks.HodgeWeil.hodgeCohomologyOneIsoComponent f).hom.hom
    (Scheme.Hom.hodgeFirstChernClass f _) = 0
  exact (congrArg (Stacks.HodgeWeil.hodgeCohomologyOneIsoComponent f).hom.hom h).trans
    (map_zero _)

end AlgebraicGeometry.Scheme.Hom

end
