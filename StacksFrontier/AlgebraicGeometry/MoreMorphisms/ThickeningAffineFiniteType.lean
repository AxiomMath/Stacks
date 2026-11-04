module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffineFiniteOrder

/-!
# A finitely generated piece of a thickening is a finite-order thickening

[Stacks Project, Tag 06AD] says that any thickening of an affine scheme is affine.
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffineFiniteOrder` reduces the
**finite-order** case to the first-order case, by the adic filtration of the defining ideal
sheaf. That reduction does not reach a general thickening: the defining ideal sheaf of a
thickening is nil but need not be nilpotent, so the adic filtration need not terminate.

This file supplies the step that closes that gap from the other side. The defining ideal sheaf
`I` of a thickening has full support, hence so does every ideal sheaf below it; and an ideal
sheaf with full support whose ideals are finitely generated on a *quasi-compact* scheme is
nilpotent, because a finitely generated ideal inside the nilradical is nilpotent and finitely
many affine opens suffice to pin a single exponent. Consequently every closed subscheme of `X'`
cut out by a finitely generated ideal sheaf below `I` is a *finite-order* thickening of `X'`, so
the finite-order reduction applies to it.

The resulting statement,
`Stacks.Thickenings.isAffine_of_isThickening_of_fg_isAffine_subscheme`, is [Stacks Project, Tag
06AD] granted two inputs: the first-order case, and the existence of **one** finitely generated
ideal sheaf below the defining ideal sheaf whose closed subscheme is affine. It therefore
records exactly what the general case still needs beyond the first-order case: an approximation
of the thickening by a finite-order one with affine source.

## Main results

* `Stacks.Thickenings.exists_pow_eq_bot_of_fg_of_support_eq_top`: an ideal sheaf with full
  support and finitely generated ideals on a quasi-compact scheme is nilpotent.
* `Stacks.Thickenings.exists_isNthOrderThickening_subschemeι_of_fg`: the inclusion of the closed
  subscheme cut out by such an ideal sheaf is a finite-order thickening.
* `Stacks.Thickenings.isAffine_of_isThickening_of_fg_isAffine_subscheme`: a thickening whose
  defining ideal sheaf dominates a finitely generated ideal sheaf with affine closed subscheme
  has affine ambient scheme, granted the first-order case of [Stacks Project, Tag 06AD].
* `Stacks.Thickenings.isAffine_of_isThickening_of_fg_isAffine_subscheme_of_surjective_appTop`:
  the same with the first-order case given in its cohomological form.

## Implementation notes

Full support is the ideal-sheaf form of nilness: by
`AlgebraicGeometry.Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal` and
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_top`, an ideal sheaf has support `⊤`
exactly when it lies below the nilradical, that is, when each of its ideals consists of
nilpotents. For a *finitely generated* ideal that upgrades to an actual vanishing power by
`Ideal.exists_pow_le_of_le_radical_of_fg`. The exponent depends on the affine open, which is why
quasi-compactness is needed: a finite subcover of the affine opens bounds all the exponents at
once, and `AlgebraicGeometry.Scheme.IdealSheafData.ext_of_iSup_eq_top` turns the chartwise
vanishing on that subcover into the equality of ideal sheaves.

The hypotheses are stated for an arbitrary ideal sheaf below the defining one rather than for a
sub-thickening, because `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι` already provides
the closed immersion and `AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι` identifies its
defining ideal sheaf.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Thickenings

variable {X X' : Scheme.{u}}

/-- **An ideal sheaf with full support and finitely generated ideals on a quasi-compact scheme is
nilpotent.**  Full support means that every ideal of the sheaf lies in the nilradical, so a
finitely generated one has a vanishing power; quasi-compactness bounds the exponents of finitely
many affine opens covering the scheme at once. -/
theorem exists_pow_eq_bot_of_fg_of_support_eq_top [CompactSpace X] {J : X.IdealSheafData}
    (hfg : ∀ U : X.affineOpens, (J.ideal U).FG) (hJ : J.support = ⊤) :
    ∃ n : ℕ, J ^ (n + 1) = ⊥ := by
  have hnil : J ≤ X.nilradical := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_top]
    exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp hJ.ge
  have hpow : ∀ U : X.affineOpens, ∃ n : ℕ, (J.ideal U) ^ (n + 1) = ⊥ := by
    intro U
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
      (J := (⊥ : Ideal Γ(X, U.1))) (Scheme.IdealSheafData.le_def.mp hnil U) (hfg U)
    exact ⟨n, le_bot_iff.mp ((Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn)⟩
  choose n hn using hpow
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens ↦ (U.1 : Set X))
    (fun U ↦ U.1.2) fun x _ ↦ by
      obtain ⟨U, hU⟩ := Opens.mem_iSup.mp ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
      exact Set.mem_iUnion.mpr ⟨U, hU⟩
  refine ⟨s.sup n, Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U : s ↦ U.1) ?_ fun U ↦ ?_⟩
  · refine top_le_iff.mp fun x _ ↦ ?_
    obtain ⟨U, hU⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨⟨U, hU.1⟩, hU.2⟩
  · simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.IdealSheafData.ideal_bot,
      Pi.bot_apply]
    exact le_bot_iff.mp (((Ideal.pow_le_pow_right
      (Nat.succ_le_succ (Finset.le_sup U.2))).trans (hn U.1).le))

/-- **The closed subscheme cut out by a finitely generated ideal sheaf with full support is a
finite-order thickening of the ambient scheme.**  The defining ideal sheaf of
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι` is the given ideal sheaf, which is nilpotent
by `Stacks.Thickenings.exists_pow_eq_bot_of_fg_of_support_eq_top`. -/
theorem exists_isNthOrderThickening_subschemeι_of_fg [CompactSpace X] {J : X.IdealSheafData}
    (hfg : ∀ U : X.affineOpens, (J.ideal U).FG) (hJ : J.support = ⊤) :
    ∃ n : ℕ, IsNthOrderThickening n J.subschemeι := by
  obtain ⟨n, hn⟩ := exists_pow_eq_bot_of_fg_of_support_eq_top hfg hJ
  exact ⟨n, inferInstance, by rw [Scheme.IdealSheafData.ker_subschemeι]; exact hn⟩

/-- **The defining ideal sheaf of a thickening has full support**, because the support of the
kernel of a quasi-compact morphism is the closure of its range, and a thickening is surjective on
points. -/
theorem IsThickening.support_ker_eq_top {i : X ⟶ X'} (hi : IsThickening i) :
    i.ker.support = ⊤ := by
  have := hi.1
  have h := i.support_ker
  refine TopologicalSpace.Closeds.ext ?_
  rw [h, Set.range_eq_univ.mpr hi.2, closure_univ, Closeds.coe_top]

/-- **Any ideal sheaf below the defining ideal sheaf of a thickening has full support.**  The
support of an ideal sheaf is antitone in the ideal sheaf, and the defining ideal sheaf of a
thickening already has full support. -/
theorem IsThickening.support_eq_top_of_le_ker {i : X ⟶ X'} (hi : IsThickening i)
    {J : X'.IdealSheafData} (hJ : J ≤ i.ker) : J.support = ⊤ :=
  top_le_iff.mp ((hi.support_ker_eq_top).ge.trans (Scheme.IdealSheafData.support_antitone hJ))

/-- **[Stacks Project, Tag 06AD] granted the first-order case and one finitely generated affine
approximation.**  Let `i : X ⟶ X'` be a thickening with `X` affine, and let `J` be an ideal sheaf
below the defining ideal sheaf of `i` whose ideals are finitely generated and whose closed
subscheme is affine.  Then `X'` is affine.

The ideal sheaf `J` cuts out a *finite-order* thickening of `X'` by
`Stacks.Thickenings.exists_isNthOrderThickening_subschemeι_of_fg`, so the reduction
`Stacks.Thickenings.isAffine_of_isNthOrderThickening_of_firstOrder` applies with its affine
closed subscheme as the source.  Note that the hypothesis `IsAffine X` is not used directly:
affineness travels up from `J.subscheme`, and `X` enters only through the thickening giving `J`
full support and `X'` quasi-compactness. -/
theorem isAffine_of_isThickening_of_fg_isAffine_subscheme
    (H : ∀ (Z Z' : Scheme.{u}) (j : Z ⟶ Z'), IsFirstOrderThickening j → IsAffine Z → IsAffine Z')
    {i : X ⟶ X'} (hi : IsThickening i) [IsAffine X] {J : X'.IdealSheafData} (hJ : J ≤ i.ker)
    (hfg : ∀ U : X'.affineOpens, (J.ideal U).FG) (hJaff : IsAffine J.subscheme) : IsAffine X' := by
  have := hi.compactSpace
  obtain ⟨n, hn⟩ :=
    exists_isNthOrderThickening_subschemeι_of_fg hfg (hi.support_eq_top_of_le_ker hJ)
  exact isAffine_of_isNthOrderThickening_of_firstOrder H hn

/-- **[Stacks Project, Tag 06AD] granted the cohomological first-order case and one finitely
generated affine approximation.**  This is
`Stacks.Thickenings.isAffine_of_isThickening_of_fg_isAffine_subscheme` with the first-order case
given as the surjectivity of the map on global sections, which is the vanishing of the first
cohomology of the defining ideal sheaf of a first-order thickening. -/
theorem isAffine_of_isThickening_of_fg_isAffine_subscheme_of_surjective_appTop
    (H : ∀ (Z Z' : Scheme.{u}) (j : Z ⟶ Z'), IsFirstOrderThickening j → IsAffine Z →
      Function.Surjective j.appTop.hom)
    {i : X ⟶ X'} (hi : IsThickening i) [IsAffine X] {J : X'.IdealSheafData} (hJ : J ≤ i.ker)
    (hfg : ∀ U : X'.affineOpens, (J.ideal U).FG) (hJaff : IsAffine J.subscheme) : IsAffine X' :=
  isAffine_of_isThickening_of_fg_isAffine_subscheme
    (fun Z Z' j hj hZ ↦ isAffine_of_isThickening_of_surjective_appTop (X := Z) hj.isThickening
      (H Z Z' j hj hZ)) hi hJ hfg hJaff

end Stacks.Thickenings

end
