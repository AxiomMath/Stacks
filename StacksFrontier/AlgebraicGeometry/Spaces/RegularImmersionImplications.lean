module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.NoetherianRegularKoszul
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty

/-!
# Koszul-regular implies `H₁`-regular implies quasi-regular, for algebraic spaces

For a representable morphism of algebraic spaces over a scheme `S`, Koszul-regularity implies
`H₁`-regularity, which in turn implies quasi-regularity.  This is Stacks tag 06BP, the analogue
for algebraic spaces of the chain of implications between the conditions of Stacks tag 063J on an
immersion of schemes, which is Stacks tag 063K.

## Main results

* `AlgebraicGeometry.Space.isH1RegularImmersion_of_isKoszulRegularImmersion`: **Stacks tag
  06BP**, the first implication.
* `AlgebraicGeometry.Space.isQuasiRegularImmersion_of_isH1RegularImmersion`: **Stacks tag 06BP**,
  the second implication.
* `AlgebraicGeometry.Space.isKoszulRegularImmersion_of_isQuasiRegularImmersion`: the converse of
  both implications over a locally Noetherian target.
* `AlgebraicGeometry.Space.isKoszulRegularImmersion_tfae`: **Stacks tag 09RW**, the three
  conditions agree for an immersion into a locally Noetherian algebraic space.

## Implementation notes

Each of the three conditions of Stacks tag 06BN is the corresponding condition of Stacks tag 063J
on the base change of the morphism to every étale scheme chart of the target, together with one
witness of representability shared by all those charts.  Both implications therefore keep that
witness, hence keep the base changes themselves, and apply the scheme-level implications of
Stacks tag 063K chart by chart.

Neither implication needs its source or target to be an algebraic space, nor the morphism to be
an immersion in the sense of Stacks tag 02YU:  representability is part of each regularity
predicate, and the base changes to étale charts are immersions of schemes by definition.  As with
the predicates themselves in
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RegularImmersion`, algebraicity is
left to the caller.

## References

* [Stacks Project, Lemma 76.44.3 (Tag 06BP)](https://stacks.math.columbia.edu/tag/06BP)
* [Stacks Project, Definition 76.44.2 (Tag 06BN)](https://stacks.math.columbia.edu/tag/06BN)
* [Stacks Project, Lemma 31.22.2 (Tag 063K)](https://stacks.math.columbia.edu/tag/063K)
* [Stacks Project, Lemma 76.44.4 (Tag 09RW)](https://stacks.math.columbia.edu/tag/09RW)
* [Stacks Project, Lemma 31.21.3 (Tag 063L)](https://stacks.math.columbia.edu/tag/063L)
-/

@[expose] public section

open CategoryTheory
open Stacks.AlgebraicGeometry

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks tag 06BP, the first implication.**  A Koszul-regular immersion of algebraic spaces
over `S` is an `H₁`-regular immersion:  degree `1` is a positive degree, so the condition on each
étale chart becomes weaker. -/
@[stacks 06BP "Koszul-regular implies H₁-regular"]
theorem isH1RegularImmersion_of_isKoszulRegularImmersion (i : Z ⟶ X)
    (h : IsKoszulRegularImmersion B S hS i) : IsH1RegularImmersion B S hS i := by
  obtain ⟨hi, hcharts⟩ := h
  refine ⟨hi, fun V q hq ↦ ?_⟩
  obtain ⟨hj, hk⟩ := hcharts V q hq
  exact ⟨hj, RegularIdealSheaf.isH1RegularImmersion_of_isKoszulRegularImmersion _ hk⟩

/-- **Stacks tag 06BP, the second implication.**  An `H₁`-regular immersion of algebraic spaces
over `S` is a quasi-regular immersion. -/
@[stacks 06BP "H₁-regular implies quasi-regular"]
theorem isQuasiRegularImmersion_of_isH1RegularImmersion (i : Z ⟶ X)
    (h : IsH1RegularImmersion B S hS i) : IsQuasiRegularImmersion B S hS i := by
  obtain ⟨hi, hcharts⟩ := h
  refine ⟨hi, fun V q hq ↦ ?_⟩
  obtain ⟨hj, hk⟩ := hcharts V q hq
  exact ⟨hj, RegularIdealSheaf.isQuasiRegularImmersion_of_isH1RegularImmersion _ hk⟩

/-- **The converse chain over a locally Noetherian target.**  A quasi-regular immersion of
algebraic spaces over `S` whose target is locally Noetherian is Koszul-regular.

Being locally Noetherian is an étale-local property of schemes, so by Stacks tag 03E8 it passes
from the atlas witnessing it to every étale scheme chart of the target; the scheme-level case of
Stacks tag 063L then upgrades each chart condition from quasi-regular to Koszul-regular. -/
theorem isKoszulRegularImmersion_of_isQuasiRegularImmersion
    (hX : IsAlgebraicSpace B S hS X) (i : Z ⟶ X)
    (hnoeth : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (h : IsQuasiRegularImmersion B S hS i) : IsKoszulRegularImmersion B S hS i := by
  obtain ⟨hi, hcharts⟩ := h
  refine ⟨hi, fun V q hq ↦ ?_⟩
  obtain ⟨hj, hk⟩ := hcharts V q hq
  have _hV : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    (exists_atlas_iff_forall_etale B S hS X
      (fun T : Scheme.{u} => IsLocallyNoetherian T) hX).1 hnoeth V q hq
  exact ⟨hj, RegularIdealSheaf.isKoszulRegularImmersion_of_isQuasiRegularImmersion _ hk⟩

/-- **Stacks tag 09RW.**  For an immersion of algebraic spaces over `S` into a locally Noetherian
algebraic space, Koszul-regularity, `H₁`-regularity and quasi-regularity agree. -/
@[stacks 09RW]
theorem isKoszulRegularImmersion_tfae (_hZ : IsAlgebraicSpace B S hS Z)
    (hX : IsAlgebraicSpace B S hS X) (i : Z ⟶ X) (_hi : IsImmersion B S hS i)
    (hnoeth : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    List.TFAE
      [IsKoszulRegularImmersion B S hS i,
        IsH1RegularImmersion B S hS i,
        IsQuasiRegularImmersion B S hS i] := by
  tfae_have 1 → 2 := isH1RegularImmersion_of_isKoszulRegularImmersion B S hS i
  tfae_have 2 → 3 := isQuasiRegularImmersion_of_isH1RegularImmersion B S hS i
  tfae_have 3 → 1 := isKoszulRegularImmersion_of_isQuasiRegularImmersion B S hS hX i hnoeth
  tfae_finish

end AlgebraicGeometry.Space

end
