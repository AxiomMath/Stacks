module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AlgebraicExtensionCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveCohomologyTheorem
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs

/-!
# Classes of degree at least two on an affine curve die over a finite extension

Let `K/k` be a field extension, let `X` be an affine curve over `k`, and let `F` be an abelian
sheaf on `Spec(K)_étale` annihilated by a positive integer. This file proves the case `q > 1` of
[Stacks, Tag 0EYT]: every class `ξ ∈ H^q(X_K, (X_K → Spec K)^{-1}F)` with `q > 1` dies over a
finite extension `K'/K`. The source's argument: `ξ` dies on `X_{\bar K}` because an affine curve
over an algebraically closed field has no torsion cohomology above degree one (Theorem 03SC,
here `Stacks.EtaleCohomology.TorsionSheafSituation.isAffineVanishingAboveDegreeOne`), and then on
some `X_{K'}` with `K'/K` finite by Lemma 03Q6
(`Stacks.EtaleCohomology.exists_finiteDimensional_restriction_eq_zero_of_isAlgebraic`).

## Main results

* `Stacks.EtaleCohomology.nsmul_id_inverseImage_eq_zero` — inverse image preserves annihilation
  by an integer.
* `Stacks.EtaleCohomology.subsingleton_sheafH_scalarExtension_algebraicClosure` — the cohomology of
  a torsion sheaf on the base change of an affine curve to an algebraically closed field vanishes
  above degree one.
* `Stacks.EtaleCohomology.exists_finiteDimensional_restriction_eq_zero_of_one_lt` — the case
  `q > 1` of Tag 0EYT.

## References

* [Stacks Project, Tag 0EYT](https://stacks.math.columbia.edu/tag/0EYT)
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- Inverse image preserves annihilation by an integer: it is an additive functor. -/
theorem nsmul_id_inverseImage_eq_zero {X Y : Scheme.{u}} (g : Y ⟶ X) {n : ℕ}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hF : n • 𝟙 F = 0) :
    n • 𝟙 ((etaleAbelianInverseImage.{u, u + 1} g).obj F) = 0 := by
  rw [← (etaleAbelianInverseImage.{u, u + 1} g).map_id, ← Functor.map_nsmul, hF,
    Functor.map_zero]

/-- An abelian sheaf annihilated by a positive integer is torsion. -/
theorem torsionSheafProperty_of_pos_nsmul_id_eq_zero {C : Type*} [Category C]
    {J : GrothendieckTopology C} {F : Sheaf J AddCommGrpCat.{u + 1}} {n : ℕ} (hn : 0 < n)
    (hF : n • 𝟙 F = 0) : Stacks.Torsion.torsionSheafProperty J F :=
  Stacks.Torsion.torsionSheafProperty_of_isPrimePowerTorsion J hn
    (isPrimePowerTorsion_of_nsmul_eq_zero hF)

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The dimension of the base change of a curve along two successive field extensions is at most
one. -/
theorem topologicalKrullDim_pullback_pullback_le_one (K Ω : Type u) [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [IsCurve k f] :
    topologicalKrullDim ↥(pullback (spectrumMap K Ω) (pullback.fst (spectrumMap k K) f)) ≤ 1 := by
  rw [topologicalKrullDim_baseChange K Ω _ _ _ (IsPullback.of_hasPullback _ _).flip,
    topologicalKrullDim_baseChange k K _ _ _ (IsPullback.of_hasPullback _ _).flip]
  exact (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le

/-- **Theorem 03SC (2) on a twice base changed affine curve.** Let `X` be an affine curve over `k`,
let `K/k` be an extension and let `Ω/K` be an algebraically closed extension. For every torsion
abelian sheaf `G` on `(X_K)_Ω`, `H^q((X_K)_Ω, G) = 0` for `q > 1`. -/
theorem subsingleton_sheafH_scalarExtension_algebraicClosure (K Ω : Type u) [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [IsAlgClosed Ω] [IsCurve k f] [IsAffine X]
    (G : Sheaf (pullback (spectrumMap K Ω) (pullback.fst (spectrumMap k K) f)).smallEtaleTopology
      AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty _ G) {q : ℕ} (hq : 1 < q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} G q) :=
  let S : TorsionSheafSituation.{u, 0} :=
    { k := Ω
      X := pullback (spectrumMap K Ω) (pullback.fst (spectrumMap k K) f)
      structureMorphism := pullback.fst _ _
      dimension_le_one := topologicalKrullDim_pullback_pullback_le_one f K Ω
      F := G
      isTorsion := hG }
  S.isAffineVanishingAboveDegreeOne.subsingleton (X := S.X) hq

variable {K : Type u} [Field K] [Algebra k K]

/-- **[Stacks, Tag 0EYT], the case `q > 1`.** Let `K/k` be a field extension, let `X` be an
affine curve over `k`, let `F` be an abelian sheaf on `Spec(K)_étale` annihilated by a positive
integer `n`, and let `ξ ∈ H^q(X_K, (X_K → Spec K)^{-1}F)` with `q > 1`. Then there is a finite
extension `K'/K`, inside a fixed algebraic closure of `K`, such that `ξ` dies in
`H^q(X_{K'}, ...)`.

Here `X_K` is written `Spec K ×_{Spec k} X` and `X_{K'}` is written `Spec K' ×_{Spec K} X_K`. -/
theorem exists_finiteDimensional_restriction_eq_zero_of_one_lt [IsCurve k f] [IsAffine X]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) {n : ℕ} (hn : 0 < n)
    (hF : n • 𝟙 F = 0) {q : ℕ} (hq : 1 < q)
    (ξ : Sheaf.H.{u + 1, u + 1}
      ((etaleAbelianInverseImage.{u, u + 1} (pullback.fst (spectrumMap k K) f)).obj F) q) :
    ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧
      etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
        (pullback.snd (spectrumMap K E) (pullback.fst (spectrumMap k K) f)) _ q ξ = 0 := by
  refine exists_finiteDimensional_restriction_eq_zero_of_isAlgebraic
    (pullback.fst (spectrumMap k K) f) _ q ξ ?_
  have := subsingleton_sheafH_scalarExtension_algebraicClosure f K (AlgebraicClosure K)
    _ (torsionSheafProperty_of_pos_nsmul_id_eq_zero hn (nsmul_id_inverseImage_eq_zero
      (pullback.snd (spectrumMap K (AlgebraicClosure K)) (pullback.fst (spectrumMap k K) f))
      (nsmul_id_inverseImage_eq_zero (pullback.fst (spectrumMap k K) f) hF))) hq
  exact Subsingleton.elim _ _

end Stacks.EtaleCohomology

end
