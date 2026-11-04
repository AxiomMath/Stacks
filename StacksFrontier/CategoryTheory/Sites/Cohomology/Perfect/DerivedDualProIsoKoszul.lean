module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DerivedDualProIsoMate
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DerivedDualProIsoDualComplexMate
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DerivedDualOfStrictlyPerfectComplex

/-!
# The mate of a chain map, read in the derived category

`Stacks.SheafOfModules.DerivedMonoidal.exactPairingQ` carries an exact pairing of complexes of
`𝒪`-modules — stated for the tensor product of [Stacks, Tag 01CA] in its strict spelling — to a
pairing for the derived tensor product of [Stacks, Tag 0FPT]. It does so in three steps: the
identity functor on complexes re-seats the monoidal structure
(`Stacks.SheafOfModules.DerivedMonoidal.exactPairingSheafTensor`), the pairing is reflected along
the inclusion of the K-flat complexes
(`Stacks.SheafOfModules.DerivedMonoidal.exactPairingKFlatComplexes`), and the monoidal
localization functor pushes it into `D(𝒪)`.

This file computes the **mate** through those three steps: the mate of `Q φ` for the pushed
pairings is `Q` of the mate of `φ` for the original ones.

## Main results

* `Stacks.SheafOfModules.DerivedMonoidal.mate_exactPairingSheafTensor`: re-seating the monoidal
  structure does not change the mate.
* `Stacks.SheafOfModules.DerivedMonoidal.mate_exactPairingQ`: **the mate for the pairings of
  `exactPairingQ` is the image of the mate.**

## Implementation notes

**Why re-seating is invisible.** `exactPairingSheafTensor` is the image of the pairing under the
identity functor on complexes, transported back along
`CategoryTheory.Functor.mapHomologicalComplexIdIso`. By
`CategoryTheory.ExactPairing.mate_exactPairingCongr` the transport conjugates the mate by that
isomorphism, and by `CategoryTheory.ExactPairing.map_mate` the image pairing has the image mate;
the two conjugations are inverse, by the naturality of `mapHomologicalComplexIdIso`, so nothing
is left. The two monoidal structures are never compared directly — which is what keeps both of
them from having to be in scope at once.

**The other two steps.** They are `CategoryTheory.ExactPairing.map_mate_ofFullyFaithful` for the
inclusion of the K-flat complexes and `CategoryTheory.ExactPairing.map_mate` for the localization
functor. Both are read through `CategoryTheory.ObjectProperty.ι_map`: a morphism of the full
subcategory is a one-field structure, so `ι.map g` is `g.hom` and
`(kFlatComplexQ R).map g` is `DerivedCategory.Q.map g.hom`, each by `rfl`.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe d u

namespace Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

/-- **Re-seating the monoidal structure does not change the mate.** The mate of `ψ` for the
pairings of `Stacks.SheafOfModules.DerivedMonoidal.exactPairingSheafTensor` — taken in the
monoidal category of complexes that the derived tensor product of [Stacks, Tag 0FPT] is built
on — is the mate of `ψ` for the given pairings, taken in the strict monoidal category of
complexes of [Stacks, Tag 0FPQ]. -/
theorem mate_exactPairingSheafTensor (F G F' G' : Complexes R)
    (p : @ExactPairing (Complexes R) _ (Strict.monoidalCategoryCochainComplex R) F G)
    (p' : @ExactPairing (Complexes R) _ (Strict.monoidalCategoryCochainComplex R) F' G')
    (ψ : F ⟶ F') :
    ExactPairing.mate (exactPairingSheafTensor R F G p) (exactPairingSheafTensor R F' G' p') ψ =
      @ExactPairing.mate (Complexes R) _ (Strict.monoidalCategoryCochainComplex R)
        F F' G G' p p' ψ := by
  have key := ExactPairing.mate_exactPairingCongr
    (@ExactPairing.map (Complexes R) (Complexes R) _ _
      (Strict.monoidalCategoryCochainComplex R) _
      ((𝟭 (Mod R)).mapHomologicalComplex (ComplexShape.up ℤ)) (idComplexMonoidal R) F G p)
    (@ExactPairing.map (Complexes R) (Complexes R) _ _
      (Strict.monoidalCategoryCochainComplex R) _
      ((𝟭 (Mod R)).mapHomologicalComplex (ComplexShape.up ℤ)) (idComplexMonoidal R) F' G' p')
    ((Functor.mapHomologicalComplexIdIso (Mod R) (ComplexShape.up ℤ)).app F).symm
    ((Functor.mapHomologicalComplexIdIso (Mod R) (ComplexShape.up ℤ)).app G).symm
    ((Functor.mapHomologicalComplexIdIso (Mod R) (ComplexShape.up ℤ)).app F').symm
    ((Functor.mapHomologicalComplexIdIso (Mod R) (ComplexShape.up ℤ)).app G').symm ψ
  have nat : ∀ {X Y : Complexes R} (f : X ⟶ Y),
      ((Functor.mapHomologicalComplexIdIso (Mod R) (ComplexShape.up ℤ)).app X).hom ≫ f ≫
        ((Functor.mapHomologicalComplexIdIso (Mod R) (ComplexShape.up ℤ)).app Y).inv =
      ((𝟭 (Mod R)).mapHomologicalComplex (ComplexShape.up ℤ)).map f := fun f => by
    ext i; simp
  have hmap := @ExactPairing.map_mate (Complexes R) (Complexes R) _ _
    (Strict.monoidalCategoryCochainComplex R) _
    ((𝟭 (Mod R)).mapHomologicalComplex (ComplexShape.up ℤ)) (idComplexMonoidal R)
    F G F' G' p p' ψ
  refine key.trans ?_
  simp only [Iso.symm_hom, Iso.symm_inv]
  rw [nat ψ, ← hmap, ← nat]
  simp

variable [HasDerivedCategory.{d} (Mod R)]

attribute [local instance] derivedMonoidal derivedSymmetric kFlatQ_isLocalization
  CochainComplex.KFlatMonoidal.homotopyMonoidal CochainComplex.KFlatMonoidal.homotopyBraided
  homQMonoidal homQBraided kFlatQMonoidal kFlatQBraided kFlatQuotientMonoidal
  kFlatQuotientLaxBraided kFlatComplexQMonoidal

/-- **The mate for the pairings pushed into the derived category is the image of the mate.** If
`𝒢^•` is a left dual of `ℱ^•` and `𝒢'^•` of `ℱ'^•` in the monoidal category of complexes of
[Stacks, Tag 0FPQ], all four complexes being K-flat, then the mate of `Q ψ` for the pairings of
`Stacks.SheafOfModules.DerivedMonoidal.exactPairingQ` is `Q` of the mate of `ψ`. -/
theorem mate_exactPairingQ (F G F' G' : Complexes R)
    (hF : KFlatComplexes R F) (hG : KFlatComplexes R G)
    (hF' : KFlatComplexes R F') (hG' : KFlatComplexes R G')
    (p : @ExactPairing (Complexes R) _ (Strict.monoidalCategoryCochainComplex R) F G)
    (p' : @ExactPairing (Complexes R) _ (Strict.monoidalCategoryCochainComplex R) F' G')
    (ψ : F ⟶ F') :
    ExactPairing.mate (exactPairingQ R F G hF hG p) (exactPairingQ R F' G' hF' hG' p')
        (DerivedCategory.Q.map ψ) =
      DerivedCategory.Q.map (@ExactPairing.mate (Complexes R) _
        (Strict.monoidalCategoryCochainComplex R) F F' G G' p p' ψ) := by
  let : ExactPairing ((KFlatComplexes R).ι.obj ⟨F, hF⟩) ((KFlatComplexes R).ι.obj ⟨G, hG⟩) :=
    exactPairingSheafTensor R F G p
  let : ExactPairing ((KFlatComplexes R).ι.obj ⟨F', hF'⟩) ((KFlatComplexes R).ι.obj ⟨G', hG'⟩) :=
    exactPairingSheafTensor R F' G' p'
  have h2 := ExactPairing.map_mate_ofFullyFaithful (KFlatComplexes R).ι
    ⟨F, hF⟩ ⟨G, hG⟩ ⟨F', hF'⟩ ⟨G', hG'⟩ (ObjectProperty.homMk ψ)
  have h3 := ExactPairing.map_mate (kFlatComplexQ R)
    (ExactPairing.ofFullyFaithful (KFlatComplexes R).ι (⟨F, hF⟩ : _) ⟨G, hG⟩)
    (ExactPairing.ofFullyFaithful (KFlatComplexes R).ι (⟨F', hF'⟩ : _) ⟨G', hG'⟩)
    (ObjectProperty.homMk ψ)
  exact h3.symm.trans
    (congrArg DerivedCategory.Q.map (h2.trans (mate_exactPairingSheafTensor R F G F' G' p p' ψ)))

end Stacks.SheafOfModules.DerivedMonoidal

end
