module

public import StacksFrontier.AlgebraicGeometry.Curves.PicardTorsionBoundedExtension
public import StacksFrontier.AlgebraicGeometry.Curves.SeparableClosedPointGenus
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.Unconditional
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.DenseSeparableClosedPoints

/-!
# The `n`-torsion of the Picard group of a curve over a bounded extension

Let `k` be a field, `n` prime to the characteristic of `k`, and `X` a smooth proper curve over
`k` with `H⁰(X, 𝒪_X) = k`, of genus `g`. [Stacks, Tag 0CDU] says:

1. if `g = 1`, there is a finite separable extension `k'/k` such that `X_{k'}` has a
   `k'`-rational point and `Pic(X_{k'})[n] ≅ (ℤ/nℤ)^{⊕2}`;
2. if `g ≥ 2`, there is such an extension with `[k' : k] ≤ (2g - 2)(n^{2g})!` and
   `Pic(X_{k'})[n] ≅ (ℤ/nℤ)^{⊕2g}`.

## Main results

* `Stacks.Picard.nonempty_torsionBy_algebraicClosure_addEquiv_pi_zmod`: over an algebraic
  closure, `Pic(X_{k̄})[n] ≅ (ℤ/nℤ)^{⊕2g}` ([Stacks, Tag 0C1Z] applied to `X_{k̄}`).
* `Stacks.Picard.exists_finite_separable_torsionBy_of_genus_eq_one`: **Tag 0CDU (1).**
* `Stacks.Picard.exists_finite_separable_torsionBy_of_closedPoint`: the common step, from a
  closed point with finite separable residue field of degree at most `d`.
* `Stacks.Picard.exists_finite_separable_torsionBy_of_two_le_genus`: **Tag 0CDU (2).**

## Implementation notes

"`n` prime to the characteristic of `k`" is `(n : k) ≠ 0`: for `n ≥ 1` this says `n` is
invertible in `k`, and it excludes `n = 0`, for which the statement is false. A `k'`-rational
point of `X_{k'}` is a section of the structure morphism `X_{k'} ⟶ Spec k'`, and
`(ℤ/nℤ)^{⊕m}` is `Fin m → ZMod n`.

The proof is the source's. `X_{k̄}` is a smooth projective curve of genus `g`
(`AlgebraicGeometry.isCurve_isProjectiveVariety_genus_pullback`), so Tag 0C1Z gives
`Pic(X_{k̄})[n] ≅ (ℤ/nℤ)^{⊕2g}`; Tag 0CD5 transfers this to `k^{sep}`, and the fixed field of the
kernel of the Galois action on this finite set, enlarged by the residue field of a closed point
with finite separable residue field (Tag 056U in genus one, Tag 0CD4 in genus `≥ 2`), is `k'`
(`Stacks.Picard.exists_finite_separable_torsion_of_residueField`).

## References

* [Stacks Project, Tag 0CDU](https://stacks.math.columbia.edu/tag/0CDU)
* [Stacks Project, Tag 0C1Z](https://stacks.math.columbia.edu/tag/0C1Z)
* [Stacks Project, Tag 0CD4](https://stacks.math.columbia.edu/tag/0CD4)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Picard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **`Pic(X_{k̄})[n] ≅ (ℤ/nℤ)^{⊕2g}`.** For a smooth proper curve `X` over `k` with
`H⁰(X, 𝒪_X) = k` and of genus `g`, and `n` invertible in `k`, the `n`-torsion of the Picard group
of the base change to an algebraic closure is free of rank `2g` over `ℤ/nℤ`: `X_{k̄}` is a smooth
projective curve of genus `g`, and Tag 0C1Z applies. -/
theorem nonempty_torsionBy_algebraicClosure_addEquiv_pi_zmod [IsCurve k f] [Smooth f]
    [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (Submodule.torsionBy ℤ
      (ofScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))))
      (n : ℤ) ≃+ (Fin (2 * genus f) → ZMod n)) := by
  obtain ⟨hcurve, hproj, hgenus⟩ :=
    isCurve_isProjectiveVariety_genus_pullback f (AlgebraicClosure k)
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 fun h => hn (by rw [h, Nat.cast_zero])
  have hnK : IsUnit (n : AlgebraicClosure k) := by
    refine Ne.isUnit ?_
    rw [← map_natCast (algebraMap k (AlgebraicClosure k))]
    exact (map_ne_zero _).2 hn
  rw [← hgenus]
  exact nonempty_torsionBy_addEquiv_pi_zmod_of_smoothProjectiveCurve (AlgebraicClosure k)
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) n hn1 hnK

/-- **The proof of Tag 0CDU from a closed point.** Let `X` be a smooth proper curve over `k`
with `H⁰(X, 𝒪_X) = k` and of genus `g`, and let `n` be prime to the characteristic of `k`. If
`x ∈ X` has a residue field `κ(x)` finite separable over `k` of degree at most `d`, then there is a
finite separable extension `k'/k` with `[k' : k] ≤ d · (n^{2g})!` such that `X_{k'}` has a
`k'`-rational point and `Pic(X_{k'})[n] ≅ (ℤ/nℤ)^{⊕2g}`. -/
theorem exists_finite_separable_torsionBy_of_closedPoint [IsCurve k f] [Smooth f] [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] {n : ℕ} (hn : (n : k) ≠ 0) (x : X)
    (hfin : letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Module.Finite k (X.residueField x))
    (hsep : letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Algebra.IsSeparable k (X.residueField x)) {d : ℕ}
    (hd : letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Module.finrank k (X.residueField x) ≤ d) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
      Algebra.IsSeparable k k' ∧ Module.finrank k k' ≤ d * (n ^ (2 * genus f)).factorial ∧
      (∃ t : Spec (.of k') ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))),
        t ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) = 𝟙 _) ∧
      Nonempty (Submodule.torsionBy ℤ
        (ofScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) (n : ℤ) ≃+
        (Fin (2 * genus f) → ZMod n)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨e⟩ := nonempty_torsionBy_algebraicClosure_addEquiv_pi_zmod f hn
  exact exists_finite_separable_torsion_of_residueField f inferInstance hn e x hfin hsep hd

/-- **Stacks Project, Tag 0CDU (1).** Let `k` be a field, let `n` be prime to the characteristic
of `k`, and let `X` be a smooth proper curve over `k` with `H⁰(X, 𝒪_X) = k` and of genus `1`.
Then there is a finite separable extension `k'/k` such that `X_{k'}` has a `k'`-rational point
and `Pic(X_{k'})[n] ≅ (ℤ/nℤ)^{⊕2}`.

The point is a closed point with finite separable residue field, which exists by Tag 056U. -/
@[stacks 0CDU "(1)"]
theorem exists_finite_separable_torsionBy_of_genus_eq_one [IsCurve k f] [Smooth f] [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hg : genus f = 1) {n : ℕ}
    (hn : (n : k) ≠ 0) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
      Algebra.IsSeparable k k' ∧
      (∃ t : Spec (.of k') ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))),
        t ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) = 𝟙 _) ∧
      Nonempty (Submodule.torsionBy ℤ
        (ofScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) (n : ℤ) ≃+
        (Fin 2 → ZMod n)) := by
  have : Nonempty X := inferInstance
  obtain ⟨x, ⟨-, hfin, hsep⟩⟩ :=
    (dense_closedPoints_with_finite_separable_residueField_of_smooth f).nonempty
  obtain ⟨k', _, _, h1, h2, -, h4, h5⟩ :=
    exists_finite_separable_torsionBy_of_closedPoint f hn x hfin hsep le_rfl
  rw [hg] at h5
  exact ⟨k', _, _, h1, h2, h4, h5⟩

/-- **Stacks Project, Tag 0CDU (2).** Let `k` be a field, let `n` be prime to the characteristic
of `k`, and let `X` be a smooth proper curve over `k` with `H⁰(X, 𝒪_X) = k` and of genus
`g ≥ 2`. Then there is a finite separable extension `k'/k` with `[k' : k] ≤ (2g - 2)(n^{2g})!`
such that `X_{k'}` has a `k'`-rational point and `Pic(X_{k'})[n] ≅ (ℤ/nℤ)^{⊕2g}`.

The closed point of degree at most `2g - 2` with separable residue field is Tag 0CD4. -/
@[stacks 0CDU "(2)"]
theorem exists_finite_separable_torsionBy_of_two_le_genus [IsCurve k f] [Smooth f] [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hg : 2 ≤ genus f) {n : ℕ}
    (hn : (n : k) ≠ 0) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
      Algebra.IsSeparable k k' ∧
      Module.finrank k k' ≤ (2 * genus f - 2) * (n ^ (2 * genus f)).factorial ∧
      (∃ t : Spec (.of k') ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))),
        t ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) = 𝟙 _) ∧
      Nonempty (Submodule.torsionBy ℤ
        (ofScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) (n : ℤ) ≃+
        (Fin (2 * genus f) → ZMod n)) := by
  obtain ⟨x, -, hfin, hsep, hd⟩ :=
    exists_isClosed_isSeparable_finrank_residueField_le_two_mul_genus_sub_two k f hg
  exact exists_finite_separable_torsionBy_of_closedPoint f hn x hfin hsep hd

end Stacks.Picard

end
