module

public import StacksFrontier.AlgebraicGeometry.Conormal.SplitSequence
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.ConormalSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal sequence of an `H₁`-regular immersion of schemes, bundled

For immersions `Z --i--→ Y --j--→ X` of schemes with `i` an `H₁`-regular immersion, the conormal
sequence `0 ⟶ i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` of [Stacks Project, Tag 062S] is short exact
and splits on a neighbourhood of every point of `Z`.  Both halves are already proved, in
`StacksFrontier/AlgebraicGeometry/RegularImmersion/ConormalSequence.lean`, where they carry
[Stacks Project, Tag 063N]:
`Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSequence_shortExact` and
`Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSequence_locallySplit`.

This file packages the two into the single predicate
`Stacks.AlgebraicGeometry.IsSplitExactConormalSequence`, which is the shape in which the
conormal hypothesis is *consumed* — by the three clauses of [Stacks Project, Tag 068Z] in
`StacksDraft/AlgebraicGeometry/MoreMorphisms/RegularImmersion/SplitConormal*.lean`, and, read on
étale charts, by the three clauses of [Stacks Project, Tag 09S1] in
`StacksFrontier/AlgebraicGeometry/Spaces/RegularImmersionSplitConormal.lean`.  Before this file the
predicate occurred only as a hypothesis and nothing discharged it.

## Main results

* `Stacks.AlgebraicGeometry.isSplitExactConormalSequence_of_isH1RegularImmersion`: the conormal
  sequence of a pair of immersions whose first member is `H₁`-regular is exact and locally split.

## Implementation notes

**The two spellings of the left-hand map agree definitionally.**
`Stacks.AlgebraicGeometry.conormalSequenceLeftMap`, which the predicate is stated with, and
`Stacks.Immersion.conormalLeftMap`, which the short complex
`Stacks.Immersion.conormalSequenceShortComplex` of the exactness results is built from, are both
`Stacks.Immersion.immersionConormalSheafMap (i ≫ j) j i (𝟙 X)` applied to a proof of the same
commutation, so they differ only in a proof argument and the short complexes they generate are
equal by proof irrelevance.

**Transporting the local splitting between the two restriction functors.**  Tag 063N produces a
splitting of the sequence restricted along `SheafOfModules.overFunctor`, which is the restriction
the local lifting lemma of [Stacks Project, Tag 08C6] is stated for, whereas the predicate asks
for a retraction of the left-hand map after restriction along
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`.  The two are identified by
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`, and a retraction is carried across a
natural isomorphism of functors by conjugating with its components; the naturality square of the
inverse is what moves the left-hand map past them.

## References

* [Stacks Project, Tag 063N](https://stacks.math.columbia.edu/tag/063N)
* [Stacks Project, Tag 062S](https://stacks.math.columbia.edu/tag/062S)
* [Stacks Project, Tag 068Z](https://stacks.math.columbia.edu/tag/068Z)
* [Stacks Project, Tag 08C6](https://stacks.math.columbia.edu/tag/08C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry

variable {Z Y X : Scheme.{u}}

/-- **A retraction is carried across a natural isomorphism of functors.**  If `r` retracts
`F.map u` and `e : F ≅ G`, then conjugating `r` by the components of `e` at the two ends of `u`
retracts `G.map u`.

The naturality square of `e.inv` is what moves `G.map u` past the component at the target. -/
private theorem retraction_of_natIso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) {A Bb : C} (u : A ⟶ Bb) {r : F.obj Bb ⟶ F.obj A}
    (hr : F.map u ≫ r = 𝟙 _) :
    G.map u ≫ (e.inv.app Bb ≫ r ≫ e.hom.app A) = 𝟙 _ :=
  calc G.map u ≫ (e.inv.app Bb ≫ r ≫ e.hom.app A)
      = (G.map u ≫ e.inv.app Bb) ≫ r ≫ e.hom.app A := by simp only [Category.assoc]
    _ = (e.inv.app A ≫ F.map u) ≫ r ≫ e.hom.app A := by rw [e.inv.naturality]
    _ = e.inv.app A ≫ (F.map u ≫ r) ≫ e.hom.app A := by simp only [Category.assoc]
    _ = 𝟙 _ := by rw [hr, Category.id_comp, Iso.inv_hom_id_app]

/-- **The two spellings of the left-hand map of the conormal sequence agree.**
`Stacks.AlgebraicGeometry.conormalSequenceLeftMap` and `Stacks.Immersion.conormalLeftMap` are the
same canonical map of [Stacks Project, Tag 01R4]; they are built from proofs of the same
commutation, so they are equal. -/
theorem conormalSequenceLeftMap_eq (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    conormalSequenceLeftMap i j = Stacks.Immersion.conormalLeftMap i j := rfl

/-- **The conormal sequence of an `H₁`-regular immersion of schemes is exact and locally split.**
For immersions `Z --i--→ Y --j--→ X` of schemes with `i` an `H₁`-regular immersion, the canonical
sequence `0 ⟶ i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` of [Stacks Project, Tag 062S] is a short
exact sequence of `𝒪_Z`-modules whose left-hand map admits a retraction on a neighbourhood of
every point of `Z`.

Short exactness is `Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSequence_shortExact` and
the local splitting is
`Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSequence_locallySplit`, both
[Stacks Project, Tag 063N]; `H₁`-regularity of `i` is what each of them consumes, for injectivity
on the left and for finite local freeness of `𝒞_{Z/Y}` respectively.  The retraction produced
there is one of the sequence restricted along `SheafOfModules.overFunctor`, and is carried to the
open-subscheme restriction by `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`. -/
@[ega "IV 16.9.13" "more general",
  ega "IV 19.1.5" "more general",
  sga "6 VII 1.7" "more general",
  sga "6 VII 4.2" "partial"]
theorem isSplitExactConormalSequence_of_isH1RegularImmersion (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j]
    (hi : RegularIdealSheaf.IsH1RegularImmersion i) :
    IsSplitExactConormalSequence i j where
  comp_eq_zero := Stacks.Immersion.conormalSequence_comp_zero i j
  shortExact := RegularIdealSheaf.conormalSequence_shortExact i j hi
  locallySplit z := by
    obtain ⟨V, hzV, ⟨sp⟩⟩ := RegularIdealSheaf.conormalSequence_locallySplit i j hi z
    have hf : (_root_.SheafOfModules.overFunctor
          (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace) V).map
          (conormalSequenceLeftMap i j) ≫ sp.r = 𝟙 _ := sp.f_r
    have hGf : ((_root_.SheafOfModules.overFunctor
          (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace) V) ⋙
            (Scheme.Modules.overEquiv V).functor).map (conormalSequenceLeftMap i j) ≫
        (Scheme.Modules.overEquiv V).functor.map sp.r = 𝟙 _ :=
      ((Scheme.Modules.overEquiv V).functor.map_comp _ _).symm.trans
        ((congrArg (Scheme.Modules.overEquiv V).functor.map hf).trans
          ((Scheme.Modules.overEquiv V).functor.map_id _))
    exact ⟨V, hzV, _, retraction_of_natIso (Scheme.Modules.overFunctorEquiv V)
      (conormalSequenceLeftMap i j) hGf⟩

end Stacks.AlgebraicGeometry

end
