module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FixedPointIntersectionCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArithmeticFrobeniusInverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisEquivariantStalkComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PointCountMonotone
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RationalPointsDegreeOne
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fixed points of the geometric Frobenius of a curve are its rational points, simply

Let `k` be a finite field with `q = p ^ f` elements, `Y` a scheme over `k` and `k̄` an algebraic
closure of `k`. Write `π̄ = π_Y × id` for the base change to `Y_k̄` of the geometric Frobenius of
`Y` (Tag 03SQ). When `Y_k̄` is a smooth proper curve over `k̄`, the intersection number
`V(π̄) = (Δ · Γ_π̄)` of [Stacks, Tag 03U1] is the number of rational points of `Y`:

`V(π̄) = #Y(k)`.

This is the geometric identification used in [Stacks, Tag 03UJ] to compare the trace formula
with constant coefficients with Weil's formula. It has three parts.

* The `k̄`-points of `Y_k̄` fixed by `π̄` are the rational points of `Y`. A `k̄`-point `a` is fixed
  exactly when its projection to `Y` is fixed by the arithmetic Frobenius of `k̄`, which happens
  exactly when it comes from a rational point.
* `π̄` moves some point of `Y_k̄`. Otherwise every `k̄`-point would be fixed, a `k̄`-point being
  determined by its closed point. The curve `Y_k̄` would then have only finitely many closed
  points.
* The fixed-point locus `Γ_π̄^{-1}(Δ)` is reduced. This is the transversality `dπ̄ = 0` in a
  form that needs no differentials. Let `σ̄ = id × Spec(σ)` for the arithmetic Frobenius `σ`
  of `k̄`. Then `σ̄` is an automorphism commuting with `π̄`, and `σ̄ ∘ π̄` is the `f`-fold absolute
  Frobenius `F^f` (Tag 03SV). On the fixed-point locus `D`, where `π̄` is the identity, `F^f`
  therefore agrees with the automorphism `σ̄|_D`. A scheme whose absolute Frobenius is an
  isomorphism has no nilpotent functions.

With the fixed-point locus reduced, `AlgebraicGeometry.CurveGraph.fixedPointIntersection_eq_`
`natCard_fixedSections` counts `V(π̄)` as the number of fixed `k̄`-points.

## Main results

* `AlgebraicGeometry.isReduced_of_isIso_absoluteFrobeniusPow`: an affine scheme in
  characteristic `p` whose iterated absolute Frobenius is an isomorphism is reduced.
* `Stacks.Frobenius.fixedSectionsGeometricFrobeniusEquivRationalPoints`: the `k̄`-points of `Y_k̄`
  fixed by `π̄` are the rational points of `Y`, for any scheme `Y` over `k`.
* `Stacks.Frobenius.exists_geometricFrobeniusBaseChange_base_ne`: `π̄` moves some point of
  `Y_k̄` when `Y_k̄` is a curve.
* `Stacks.Frobenius.isReduced_fixedPointLocus_geometricFrobeniusBaseChange`: the fixed-point
  locus of `π̄` is reduced.
* `Stacks.Frobenius.fixedPointIntersection_geometricFrobeniusBaseChange_eq_natCard`:
  `V(π̄) = #Y(k)`.

## References

* [Stacks Project, Tag 03UJ](https://stacks.math.columbia.edu/tag/03UJ)
* [Stacks Project, Tag 03U1](https://stacks.math.columbia.edu/tag/03U1)
* [Stacks Project, Tag 03SV](https://stacks.math.columbia.edu/tag/03SV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

open Stacks.Frobenius in
/-- **An affine scheme whose iterated absolute Frobenius is an isomorphism is reduced.** On
global sections the `e`-fold absolute Frobenius is `a ↦ a ^ p ^ e`, and an injective `p ^ e`-th
power map leaves no nilpotents. -/
theorem isReduced_of_isIso_absoluteFrobeniusPow (X : Scheme.{u}) [IsAffine X] (p : ℕ)
    [Fact p.Prime] (hX : IsInCharacteristic X p) {e : ℕ} (he : e ≠ 0)
    [IsIso (absoluteFrobeniusPow X p hX e)] : IsReduced X := by
  have hleft : (absoluteFrobeniusPow X p hX e).appTop ≫
      (inv (absoluteFrobeniusPow X p hX e)).appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, IsIso.inv_hom_id, Scheme.Hom.id_appTop]
  have hinj : Function.Injective (absoluteFrobeniusPow X p hX e).appTop.hom :=
    Function.LeftInverse.injective (g := (inv (absoluteFrobeniusPow X p hX e)).appTop.hom)
      fun x => congrArg (fun φ => φ.hom x) hleft
  have hred : _root_.IsReduced Γ(X, ⊤) := by
    refine (isReduced_iff_pow_one_lt (p ^ e)
      (Nat.one_lt_pow he (Fact.out : p.Prime).one_lt)).2 fun x hx => hinj ?_
    show (absoluteFrobeniusPow X p hX e).appTop x = (absoluteFrobeniusPow X p hX e).appTop 0
    rw [absoluteFrobeniusPow_appTop_apply, absoluteFrobeniusPow_appTop_apply, hx, zero_pow]
    exact (pow_pos (Fact.out : p.Prime).pos e).ne'
  exact isReduced_of_isAffine_isReduced X

end AlgebraicGeometry

namespace Stacks.Frobenius

open Stacks.EtaleCohomology AlgebraicGeometry.CurveGraph

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k))) (kbar : Type u)
  [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- The arithmetic Frobenius of `k̄`, as a `k`-algebra automorphism of `k̄`. -/
abbrev arithmeticFrobeniusAlgClosure : kbar ≃ₐ[k] kbar :=
  haveI : ExpChar kbar p := ExpChar.prime (Fact.out : p.Prime)
  arithmeticFrobenius k kbar p q hcard

omit [CharP k p] in
/-- The arithmetic Frobenius of `k̄` sends `z` to `z ^ p ^ q`, where `p ^ q = #k`. -/
theorem arithmeticFrobeniusAlgClosure_apply (z : kbar) :
    arithmeticFrobeniusAlgClosure kbar p q hcard z = z ^ p ^ q := by
  have : ExpChar kbar p := ExpChar.prime (Fact.out : p.Prime)
  rw [arithmeticFrobeniusAlgClosure, arithmeticFrobenius_apply, hcard]

/-- On a `k̄`-point of `Y`, the geometric Frobenius of `Y` is the arithmetic Frobenius of `k̄`:
`a ≫ π_Y = a ≫ F_Y^q = F_{Spec k̄}^q ≫ a = Spec(σ) ≫ a`. -/
theorem comp_geometricFrobenius_left_eq_specMap_comp (a : Spec (.of kbar) ⟶ Y.left) :
    a ≫ (geometricFrobenius Y p q hcard).left =
      Spec.map (CommRingCat.ofHom
        (arithmeticFrobeniusAlgClosure kbar p q hcard).toAlgHom.toRingHom) ≫ a := by
  have hk : IsInCharacteristic (Spec (.of kbar)) p := isInCharacteristic_specAlgebraMap k kbar p
  rw [geometricFrobenius_left_eq_absoluteFrobeniusPow, ← absoluteFrobeniusPow_naturality a p hk,
    specMap_eq_absoluteFrobeniusPow _ p q hk
      (arithmeticFrobeniusAlgClosure_apply kbar p q hcard)]

/-- **The `k̄`-points of `Y_k̄` fixed by `π̄ = π_Y × id` are the rational points of `Y`**, for any
scheme `Y` over the finite field `k`. A rational point `x` gives the fixed point `(x̄, id)`, and a
fixed point projects to a `k̄`-point of `Y` fixed by the arithmetic Frobenius of `k̄`, which comes
from a unique rational point. -/
@[sga "4½ Rapport 1.1" "more general", sga "5 III 6.13" "Clause X^F = X0(F_q)"]
def fixedSectionsGeometricFrobeniusEquivRationalPoints :
    fixedSections (pullback.snd Y.hom (specAlgebraMap k kbar))
        (geometricFrobeniusBaseChange Y kbar p q hcard) ≃ rationalPoints Y.hom :=
  haveI hex : ∀ y : fixedSections (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange Y kbar p q hcard),
      ∃ x : Spec (.of k) ⟶ Y.left, x ≫ Y.hom = 𝟙 _ ∧
        specAlgebraMap k kbar ≫ x = y.1 ≫ pullback.fst Y.hom (specAlgebraMap k kbar) := by
    intro y
    refine exists_rationalPoint_of_specMap_comp_eq kbar Y.hom
      (arithmeticFrobeniusAlgClosure kbar p q hcard)
      (fun z => by rw [arithmeticFrobeniusAlgClosure_apply, hcard]) _
      (by rw [Category.assoc, pullback.condition, ← Category.assoc, y.2.1, Category.id_comp]) ?_
    rw [← comp_geometricFrobenius_left_eq_specMap_comp, Category.assoc,
      ← geometricFrobeniusBaseChange_comp_fst, ← Category.assoc, y.2.2]
  { toFun := fun y => ⟨(hex y).choose, (hex y).choose_spec.1⟩
    invFun := fun x => ⟨rationalPointBaseChangeLift Y kbar x.1 x.2,
      rationalPointBaseChangeLift_snd Y kbar x.1 x.2,
      rationalPointBaseChangeLift_comp_geometricFrobeniusBaseChange Y kbar x.1 x.2 p q hcard⟩
    left_inv := fun y => Subtype.ext (pullback.hom_ext
      ((rationalPointBaseChangeLift_fst Y kbar _ (hex y).choose_spec.1).trans
        (hex y).choose_spec.2)
      ((rationalPointBaseChangeLift_snd Y kbar _ (hex y).choose_spec.1).trans y.2.1.symm))
    right_inv := fun x => by
      have : Epi (specAlgebraMap k kbar) := Flat.epi_of_flat_of_surjective _
      exact Subtype.ext ((cancel_epi (specAlgebraMap k kbar)).1
        ((hex _).choose_spec.2.trans (rationalPointBaseChangeLift_fst Y kbar x.1 x.2))) }

variable [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsCurve kbar (pullback.snd Y.hom (specAlgebraMap k kbar))]

/-- **`π̄` moves some point of the curve `Y_k̄`.** Were every point fixed, every `k̄`-point `a`
would be fixed, since `a` and `a ≫ π̄` are `k̄`-points with the same closed point. The `k̄`-points
of `Y_k̄`, which are its closed points, would then all be rational points of `Y`, of which there
are finitely many; but a curve has infinitely many closed points. -/
theorem exists_geometricFrobeniusBaseChange_base_ne :
    ∃ c : fieldBaseChange Y kbar, (geometricFrobeniusBaseChange Y kbar p q hcard).base c ≠ c := by
  by_contra! hall
  let fC := pullback.snd Y.hom (specAlgebraMap k kbar)
  have : LocallyOfFiniteType fC := inferInstance
  have : Finite (rationalPoints Y.hom) := finite_rationalPoints Y.hom
  let ι : {s : Spec (.of kbar) ⟶ fieldBaseChange Y kbar // s ≫ fC = 𝟙 _} →
      fixedSections fC (geometricFrobeniusBaseChange Y kbar p q hcard) := fun s =>
    ⟨s.1, s.2, ext_of_apply_closedPoint_eq fC
      (by rw [Category.assoc, geometricFrobeniusBaseChange_comp_snd]; exact s.2) s.2
      (hall _)⟩
  have hinj : Function.Injective ι := fun _ _ h =>
    Subtype.ext (congrArg (fun t : fixedSections fC _ => t.1) h)
  have : Finite {s : Spec (.of kbar) ⟶ fieldBaseChange Y kbar // s ≫ fC = 𝟙 _} :=
    Finite.of_injective _
      ((fixedSectionsGeometricFrobeniusEquivRationalPoints Y kbar p q hcard).injective.comp hinj)
  exact infinite_closedPoints_of_isCurve fC
    (Set.finite_coe_iff.mp (Finite.of_equiv _ (pointEquivClosedPoint fC)))

variable [Smooth (pullback.snd Y.hom (specAlgebraMap k kbar))]
  [IsProper (pullback.snd Y.hom (specAlgebraMap k kbar))]

/-- **The fixed-point locus of `π̄` is reduced** (the transversality `dπ̄ = 0`). On it, the
`q`-fold absolute Frobenius `F^q = π̄ ∘ σ̄` agrees with the automorphism `σ̄|_D`, where
`σ̄ = id × Spec(σ)` for the arithmetic Frobenius `σ` of `k̄` (Tag 03SV). So `F^q` is an
isomorphism of `D`, and `D` is affine (finite over `k̄`), hence reduced. -/
theorem isReduced_fixedPointLocus_geometricFrobeniusBaseChange (hq : q ≠ 0) :
    IsReduced (fixedPointLocus (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange Y kbar p q hcard)
      (geometricFrobeniusBaseChange_comp_snd Y kbar p q hcard)).subscheme := by
  set fC := pullback.snd Y.hom (specAlgebraMap k kbar)
  set π := geometricFrobeniusBaseChange Y kbar p q hcard
  set w := geometricFrobeniusBaseChange_comp_snd Y kbar p q hcard
  set D := fixedPointLocus fC π w
  set σ := arithmeticFrobeniusAlgClosure kbar p q hcard
  set G := galoisBaseChange Y kbar σ
  have hσ : ∀ x : kbar, σ x = x ^ p ^ q := arithmeticFrobeniusAlgClosure_apply kbar p q hcard
  have hC : IsInCharacteristic (fieldBaseChange Y kbar) p :=
    isInCharacteristic_fieldBaseChange Y kbar p
  have hD : IsInCharacteristic D.subscheme p := isInCharacteristic_of_hom D.subschemeι p hC
  have := isPullbackDefined_graph_diagonalDivisor fC π w
    (exists_geometricFrobeniusBaseChange_base_ne Y kbar p q hcard)
  have : Stacks.Divisors.IsEffectiveCartierDivisor D :=
    ‹Stacks.Divisors.IsPullbackDefined (graph fC π w) (diagonalDivisor fC)›
  have : IsFinite (D.subschemeι ≫ fC) := isFinite_divisorSubscheme kbar fC
    (IsCurve.topologicalKrullDim_eq_one (f := fC)).le D
  have : IsAffine D.subscheme := isAffine_of_isAffineHom (D.subschemeι ≫ fC)
  -- `σ̄ ∘ π̄ = π̄ ∘ σ̄ = F^q`, so `σ̄⁻¹` commutes with `π̄`
  have hGπ : G ≫ π = absoluteFrobeniusPow _ p hC q :=
    galoisBaseChange_comp_geometricFrobeniusBaseChange Y kbar p q hcard σ hσ
  have hπG : π ≫ G = absoluteFrobeniusPow _ p hC q :=
    geometricFrobeniusBaseChange_comp_galoisBaseChange Y kbar p q hcard σ hσ
  have hGinv : inv G ≫ π = π ≫ inv G := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, hGπ, ← hπG, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hι : D.subschemeι ≫ π = D.subschemeι := fixedPointLocus_subschemeι_comp fC π w
  -- the inverse of `F^q` on `D`: the restriction of `σ̄⁻¹`
  let τ := fixedPointLocusLift fC π w (D.subschemeι ≫ inv G) (by
    rw [Category.assoc, hGinv, ← Category.assoc, hι])
  have hτ : τ ≫ D.subschemeι = D.subschemeι ≫ inv G := fixedPointLocusLift_subschemeι _ _ _ _ _
  have hF : absoluteFrobeniusPow D.subscheme p hD q ≫ D.subschemeι =
      D.subschemeι ≫ absoluteFrobeniusPow _ p hC q :=
    absoluteFrobeniusPow_naturality D.subschemeι p hD hC q
  have : IsIso (absoluteFrobeniusPow D.subscheme p hD q) := by
    refine ⟨τ, (cancel_mono D.subschemeι).1 ?_, (cancel_mono D.subschemeι).1 ?_⟩
    · rw [Category.assoc, hτ, ← Category.assoc, hF, Category.assoc, ← hπG, Category.assoc,
        IsIso.hom_inv_id, Category.comp_id, hι, Category.id_comp]
    · rw [Category.assoc, hF, ← Category.assoc, hτ, Category.assoc, ← hGπ, IsIso.inv_hom_id_assoc,
        hι, Category.id_comp]
  exact isReduced_of_isIso_absoluteFrobeniusPow D.subscheme p hD hq

/-- **`V(π̄) = #Y(k)`** ([Stacks, Tag 03UJ]): the intersection number of the diagonal of `Y_k̄`
with the graph of `π̄ = π_Y × id`, as in Weil's formula [Stacks, Tag 03U1], is the number of
rational points of `Y`. The fixed points of `π̄` are the rational points, and each has
multiplicity one because the fixed-point locus is reduced. -/
theorem fixedPointIntersection_geometricFrobeniusBaseChange_eq_natCard (hq : q ≠ 0)
    (hdim : topologicalKrullDim (fieldBaseChange Y kbar) ≤ 1) :
    fixedPointIntersection (pullback.snd Y.hom (specAlgebraMap k kbar)) hdim
        (geometricFrobeniusBaseChange Y kbar p q hcard)
        (geometricFrobeniusBaseChange_comp_snd Y kbar p q hcard) =
      Nat.card (rationalPoints Y.hom) := by
  rw [fixedPointIntersection_eq_natCard_fixedSections _ hdim _ _
    (exists_geometricFrobeniusBaseChange_base_ne Y kbar p q hcard)
    (isReduced_fixedPointLocus_geometricFrobeniusBaseChange Y kbar p q hcard hq),
    Nat.card_congr (fixedSectionsGeometricFrobeniusEquivRationalPoints Y kbar p q hcard)]

end Stacks.Frobenius

end
