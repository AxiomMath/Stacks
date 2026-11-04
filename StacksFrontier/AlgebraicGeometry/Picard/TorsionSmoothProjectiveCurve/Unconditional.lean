module

public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.Transport
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.DegreeZero.OpenSubgroupScheme
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.PicardSchemeOfCurve
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.HilbertInSite
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.AbelianVariety.DegreeZeroSmooth
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.AbelianVariety.DegreeZeroOfSmooth
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.FromCube
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.CubeRelationSiblings.PrimePowerTorsion
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# Torsion in the Picard group of a smooth projective curve

Let `k` be an algebraically closed field and `X` a smooth projective curve of genus `g` over `k`.
[Stacks, Tag 0C1Z] says:

1. if `n ≥ 1` is invertible in `k`, then `Pic(X)[n] ≅ (ℤ/nℤ)^{⊕2g}`;
2. if the characteristic of `k` is `p > 0`, then there is an integer `0 ≤ f ≤ g` with
   `Pic(X)[p^m] ≅ (ℤ/p^mℤ)^{⊕f}` for all `m ≥ 1`.

The proof is the source's. The degree gives `0 → Pic⁰(X) → Pic(X) → ℤ → 0`, and `Pic⁰(X)` is
the group of `k`-points of `Pic⁰_{X/k}`, an abelian variety of dimension `g`
([Stacks, Tag 0BA0]); the torsion of an abelian variety is [Stacks, Tag 03RP].

Concretely: a big fppf site `B` containing `X` and `Spec k` is chosen; the Picard functor of `X`
on `B` is representable by a scheme `P`
(`Stacks.PicardFunctor.isRepresentable_picardFunctor_of_isAlgClosed`); its degree-zero part is
the open subgroup scheme `Stacks.PicardFunctor.degreeZeroOpenSubgroupScheme`, whose `k`-points
are `Pic⁰(X)` (`Stacks.PicardFunctor.degreeZeroPointsAddEquiv`) and which is an abelian variety
of dimension `g` (`Stacks.PicardFunctor.isAbelianVariety_degreeZeroOpenSubgroupScheme`, from
`isAbelianVariety_and_dimension_eq_genus_of_smoothOfRelativeDimension`). The torsion of its
`k`-points is
`AlgebraicGeometry.IsAbelianVariety.nonempty_torsionBy_points_addEquiv_pi_zmod_of_isUnit` and
`AlgebraicGeometry.IsAbelianVariety.exists_rank_nonempty_torsionBy_prime_pow_addEquiv_pi_zmod`,
transported to `Pic(X)` by
`Stacks.Picard.nonempty_torsionBy_ofScheme_addEquiv_pi_zmod_of_addEquiv_points` and
`Stacks.Picard.exists_rank_torsionBy_ofScheme_prime_pow_of_addEquiv_points`.

## Main results

* `Stacks.PicardFunctor.isAbelianVariety_degreeZeroOpenSubgroupScheme`: `Pic⁰_{X/k}` is an
  abelian variety of dimension `g`.
* `Stacks.Picard.exists_jacobian`: an abelian variety of dimension `g` over `k` whose `k`-points
  are `Pic⁰(X)`.
* `Stacks.Picard.nonempty_torsionBy_addEquiv_pi_zmod_of_smoothProjectiveCurve`: Tag 0C1Z (1).
* `Stacks.Picard.exists_rank_torsionBy_prime_pow_addEquiv_pi_zmod_of_smoothProjectiveCurve`:
  Tag 0C1Z (2).

## References

* [Stacks Project, Tag 0C1Z](https://stacks.math.columbia.edu/tag/0C1Z)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

universe u

namespace Stacks.PicardFunctor

/-- **`Pic⁰_{X/k}` is an abelian variety of dimension `g`** ([Stacks, Tag 0BA0], the degree-zero
component): for a smooth projective curve of genus `g` over an algebraically closed field, the
open subgroup scheme `degreeZeroOpenSubgroupScheme` of the Picard scheme is an abelian variety of
dimension `g`. -/
theorem isAbelianVariety_degreeZeroOpenSubgroupScheme (B : BigFppfSite.{u}) {X : Scheme.{u}}
    (hX : B.Contains X) (k : Type u) [Field k] [IsAlgClosed k] {hk : B.Contains (Spec (.of k))}
    (g : B.obj hX ⟶ B.obj hk) [IsCurve k (B.inclusion.map g)]
    [IsProjectiveVariety k (B.inclusion.map g)] [Smooth (B.inclusion.map g)]
    {P : BigFppfOver B (Spec (.of k)) hk} (R : (picardFunctor B hX hk g).RepresentableBy P) :
    letI := representingGrpObj R
    IsAbelianVariety k (degreeZeroOpenSubgroupScheme B hX k g R).carrier.X ∧
      Stacks.Groupoids.abelianVarietyDimension (degreeZeroOpenSubgroupScheme B hX k g R).carrier.X =
        genus (B.inclusion.map g) := by
  let := representingGrpObj R
  have hdim : topologicalKrullDim X ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := B.inclusion.map g)).le
  exact isAbelianVariety_and_dimension_eq_genus_of_smoothOfRelativeDimension k
    (Hb := Stacks.Hilbert.hilbSiteObject B hk (B.inclusion.map g) (genus (B.inclusion.map g))) R
    (fun e => ⟨_, ⟨Stacks.Hilbert.representsHilbSiteObject B hk (B.inclusion.map g) e⟩⟩)
    (Stacks.Hilbert.representsHilbSiteObject B hk _ _) hdim _
    (exists_comp_degreeZeroOpenSubgroupScheme_iff B hX k g R hdim)
    (smoothOfRelativeDimension_degreeZeroOpenSubgroupScheme B hX k g R)

end Stacks.PicardFunctor

namespace Stacks.Picard

/-- **The Jacobian of a smooth projective curve**: over an algebraically closed field `k`, a smooth
projective curve `X` of genus `g` has an abelian variety `J` of dimension `g` whose group of
`k`-points is `Pic⁰(X)` ([Stacks, Tag 0BA0]). -/
theorem exists_jacobian (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f] :
    ∃ (J : Over (Spec (.of k))) (_ : GrpObj J) (_ : IsAbelianVariety k J),
      Stacks.Groupoids.abelianVarietyDimension J = genus f ∧
      letI : IsCommMonObj J := isCommMonObj_of_isProper_of_geometricallyIntegral J
      Nonempty (ofSchemeDegreeZero k f (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
        ≃+ Additive (𝟙_ (Over (Spec (.of k))) ⟶ J)) := by
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing ({X, Spec (.of k)} : Set Scheme.{u})
  have hX : B.Contains X := hB X (by simp)
  have hk : B.Contains (Spec (.of k)) := hB _ (by simp)
  let g : B.obj hX ⟶ B.obj hk := ObjectProperty.homMk f
  have : IsCurve k (B.inclusion.map g) := inferInstanceAs (IsCurve k f)
  have : IsProjectiveVariety k (B.inclusion.map g) := inferInstanceAs (IsProjectiveVariety k f)
  have : Smooth (B.inclusion.map g) := inferInstanceAs (Smooth f)
  obtain ⟨P, ⟨R⟩⟩ := PicardFunctor.isRepresentable_picardFunctor_of_isAlgClosed B hX hk f
  let := PicardFunctor.representingGrpObj R
  obtain ⟨hAV, hdimH⟩ := PicardFunctor.isAbelianVariety_degreeZeroOpenSubgroupScheme B hX k g R
  exact ⟨_, inferInstance, hAV, hdimH, ⟨PicardFunctor.degreeZeroPointsAddEquiv B hX k g R _⟩⟩

/-- **Stacks Project, Tag 0C1Z (1).** Let `k` be an algebraically closed field and `X` a smooth
projective curve of genus `g` over `k`. If `n ≥ 1` is invertible in `k`, then
`Pic(X)[n] ≅ (ℤ/nℤ)^{⊕2g}`. -/
@[stacks 0C1Z "clause (1)"]
theorem nonempty_torsionBy_addEquiv_pi_zmod_of_smoothProjectiveCurve (k : Type u) [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f]
    [IsProjectiveVariety k f] [Smooth f] (n : ℕ) (hn : 1 ≤ n) (hnk : IsUnit (n : k)) :
    Nonempty (Submodule.torsionBy ℤ (ofScheme X) (n : ℤ) ≃+ (Fin (2 * genus f) → ZMod n)) := by
  obtain ⟨J, _, hJ, hdimJ, ⟨e⟩⟩ := exists_jacobian k f
  let : IsCommMonObj J := isCommMonObj_of_isProper_of_geometricallyIntegral J
  exact nonempty_torsionBy_ofScheme_addEquiv_pi_zmod_of_addEquiv_points f _ J e hdimJ n
    (by omega) (IsAbelianVariety.nonempty_torsionBy_points_addEquiv_pi_zmod_of_isUnit J n hn hnk)

/-- **Stacks Project, Tag 0C1Z (2).** Let `k` be an algebraically closed field of characteristic
`p > 0` and `X` a smooth projective curve of genus `g` over `k`. Then there is an integer
`0 ≤ r ≤ g` with `Pic(X)[p^m] ≅ (ℤ/p^mℤ)^{⊕r}` for all `m ≥ 1` (the source's `f`). -/
@[stacks 0C1Z "clause (2)"]
theorem exists_rank_torsionBy_prime_pow_addEquiv_pi_zmod_of_smoothProjectiveCurve (k : Type u)
    [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f]
    [IsProjectiveVariety k f] [Smooth f] (p : ℕ) [CharP k p] (hp : 0 < p) :
    ∃ r : ℕ, r ≤ genus f ∧ ∀ m : ℕ, 1 ≤ m →
      Nonempty (Submodule.torsionBy ℤ (ofScheme X) ((p : ℤ) ^ m) ≃+ (Fin r → ZMod (p ^ m))) := by
  obtain ⟨J, _, hJ, hdimJ, ⟨e⟩⟩ := exists_jacobian k f
  let : IsCommMonObj J := isCommMonObj_of_isProper_of_geometricallyIntegral J
  exact exists_rank_torsionBy_ofScheme_prime_pow_of_addEquiv_points f _ J e hdimJ p hp
    (IsAbelianVariety.exists_rank_nonempty_torsionBy_prime_pow_addEquiv_pi_zmod J p hp)

end Stacks.Picard

end
