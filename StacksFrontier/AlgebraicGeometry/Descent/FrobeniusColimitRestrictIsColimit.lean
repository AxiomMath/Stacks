module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitDiagramIso
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitPresheafIsColimit

/-!
# The cocone of Stacks Tag 0EXB is colimiting

Let `p` be a prime, let `X` be a scheme in characteristic `p`, write `φ` for the `p`-th power
endomorphism of `𝒪_X`, `S_α` and `U_α` for extension and restriction of scalars along a morphism
`α` of sheaves of rings, and `ι_n : 𝒪_X ⟶ colim_F 𝒪_X` for the stage-`n` coprojection. **This
file proves that `AlgebraicGeometry.frobeniusStageRestrictCocone` is a colimit cocone**, that is

`U_n (S_n 𝒢) = colim_j (U_φ)^{∘j}((S_φ)^{∘j}𝒢)`,

which is the last remaining input to the full faithfulness half of Stacks Tag 0EXB.

The proof reads everything on abelian sheaves, where restriction of scalars disappears and the
forgetful functor reflects colimits
(`AlgebraicGeometry.isColimit_frobeniusStageRestrictCocone_of_toSheaf`). There the diagram is the
abelian sheafification of the objectwise one by
`AlgebraicGeometry.frobeniusRestrictExtendDiagramToSheafIso`, the apex is the sheafification of
`(colim_j 𝒪_X) ⊗_{𝒪_X} 𝒢` by `AlgebraicGeometry.frobeniusStageRestrictToSheafIso`, and the legs
match by `AlgebraicGeometry.toSheaf_map_frobeniusStageRestrictLeg`; the objectwise cocone is
colimiting by `AlgebraicGeometry.isColimit_frobeniusPresheafCocone`, and both the underlying
abelian presheaf and its sheafification preserve colimits.

## Main definitions

* `AlgebraicGeometry.frobeniusStageRestrictToSheafIso`: the abelian sheaf underlying the apex.

## Main results

* `AlgebraicGeometry.toSheaf_map_frobeniusStageRestrictLeg`: **the leg of the cocone is the
  sheafification of the objectwise base change along the stage-`n + j` coprojection.**
* `AlgebraicGeometry.isColimit_frobeniusStageRestrictCocone`: **the cocone of Stacks Tag 0EXB is
  colimiting.**

## Implementation notes

Every statement here spells the source and target of the objectwise base change
`Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj`, and the morphism whose source is
spelled the other way is kept a *variable*
(`AlgebraicGeometry.presheafToSheaf_comp_map_restrictExtendObj`). The reason is that the kernel
answers a mismatch between two spellings of the source object of
`CategoryTheory.Functor.map` by unfolding the morphism, and the leg of the objectwise cocone
unfolds through `Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo` into an adjoint transpose;
with a variable there is nothing to unfold, and the leg is substituted afterwards. A mismatch in
the *target* is harmless.

## References

* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius TopologicalSpace

universe u

namespace CategoryTheory

universe v₂ u₂

/-- **A commuting square read with the isomorphism on the other side, inverted.** -/
lemma comp_comp_inv_eq_of_comp_hom_eq {D : Type u₂} [Category.{v₂} D] {W V Y Z : D}
    {a : W ⟶ V} {b : V ⟶ Z} {i : Y ≅ Z} {L : W ⟶ Y} (h : L ≫ i.hom = a ≫ b) :
    (a ≫ b) ≫ i.inv = L := by
  rw [← h, Category.assoc, i.hom_inv_id, Category.comp_id]

end CategoryTheory

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)
  (G : _root_.SheafOfModules.{u} X.ringSheafOnOpens)

/-! ### The apex -/

/-- **The abelian sheaf underlying `U_n (S_n 𝒢)`**, the apex of the cocone of Stacks Tag 0EXB,
is the sheafification of the objectwise tensor product `(colim_j 𝒪_X) ⊗_{𝒪_X} 𝒢`. The stage-`n`
restriction of scalars disappears, and the extension of scalars is read through
`Stacks.SheafOfModules.pullbackCompToSheafIso`. -/
noncomputable def frobeniusStageRestrictToSheafIso (n : ℕ) :
    (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).obj
        ((frobeniusStageRestrictScalars X p hX n).obj
          ((frobeniusStageExtendScalars X p hX n).obj G)) ≅
      (presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u}).obj
        ((PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj).obj
          (Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
            (frobeniusRingPresheafι X p hX n) G.val)) :=
  eqToIso (Functor.congr_obj (frobeniusStageRestrictScalars_comp_toSheaf X p hX n)
      ((frobeniusStageExtendScalars X p hX n).obj G)) ≪≫
    (Stacks.SheafOfModules.pullbackCompToSheafIso (frobeniusStageStructureMap X p hX n)
      (toFrobeniusColimitRingSheaf X p hX) (frobeniusRingPresheafι X p hX n)
      (restrictScalars_frobeniusRingPresheafι_comp X p hX n)).app G

/-- The forward map of `AlgebraicGeometry.frobeniusStageRestrictToSheafIso` is the `eqToHom`
along `frobeniusStageRestrictScalars_comp_toSheaf`, followed by the component at `𝒢` of the
forward map of `Stacks.SheafOfModules.pullbackCompToSheafIso`. -/
lemma frobeniusStageRestrictToSheafIso_hom (n : ℕ) :
    (frobeniusStageRestrictToSheafIso X p hX G n).hom =
      eqToHom (Functor.congr_obj (frobeniusStageRestrictScalars_comp_toSheaf X p hX n)
          ((frobeniusStageExtendScalars X p hX n).obj G)) ≫
        (Stacks.SheafOfModules.pullbackCompToSheafIso (frobeniusStageStructureMap X p hX n)
          (toFrobeniusColimitRingSheaf X p hX) (frobeniusRingPresheafι X p hX n)
          (restrictScalars_frobeniusRingPresheafι_comp X p hX n)).hom.app G :=
  rfl

/-! ### The legs -/

/-- **The left edge of the naturality square of the legs of Stacks Tag 0EXB**: the leg of the
cocone, followed by the comparison of the apex with the sheafification, is the comparison at `j`
followed by the leg read as a morphism out of the pullback along `φ^j`. Both sides are read on
abelian sheaves, where the `j`-fold restriction of scalars along Frobenius and the one along the
stage-`n + j` coprojection both disappear. -/
theorem toSheaf_map_frobeniusStageRestrictLeg_comp (n j : ℕ) :
    (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
          (frobeniusStageRestrictLeg X p hX n j G) ≫
        eqToHom (Functor.congr_obj (frobeniusStageRestrictScalars_comp_toSheaf X p hX n)
          ((frobeniusStageExtendScalars X p hX n).obj G)) =
      eqToHom (Functor.congr_obj (endoIter_frobeniusRestrictScalars_comp_toSheaf X p hX j)
          (((frobeniusExtendScalars X p hX).endoIter j).obj G)) ≫
        (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
            ((frobeniusExtendScalarsIterIso X p hX j).hom.app G) ≫
          (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
              (frobeniusIterStageHom X p hX n j G) ≫
            eqToHom (Functor.congr_obj
              (frobeniusStageRestrictScalars_comp_toSheaf X p hX (n + j))
              ((frobeniusStageExtendScalars X p hX n).obj G)) := by
  have hL : (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
        (frobeniusStageRestrictLeg X p hX n j G) =
      (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
          (((frobeniusRestrictScalars X p hX).endoIter j).map
            ((frobeniusStageExtendScalarsAdjunction X p hX (n + j)).unit.app
                (((frobeniusExtendScalars X p hX).endoIter j).obj G) ≫
              (frobeniusStageRestrictScalars X p hX (n + j)).map
                ((Adjunction.leftAdjointUniq
                  (frobeniusStageExtendScalarsAdjunctionIter X p hX n j)
                  (frobeniusStageExtendScalarsAdjunction X p hX n)).hom.app G))) ≫
        eqToHom (congrArg (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).obj
          (Functor.congr_obj (pushforward_frobeniusStage_comp_iter X p hX n j)
            ((frobeniusStageExtendScalars X p hX n).obj G))) :=
    CategoryTheory.map_comp_eqToHom _ _ _
  exact CategoryTheory.comp_eqToHom_eq_of_transport _
    (Functor.congr_obj (frobeniusStageRestrictScalars_comp_toSheaf X p hX n)
      ((frobeniusStageExtendScalars X p hX n).obj G))
    (Functor.congr_obj (frobeniusStageRestrictScalars_comp_toSheaf X p hX (n + j))
      ((frobeniusStageExtendScalars X p hX n).obj G)) hL
    (CategoryTheory.eqToHom_comp_map_comp
      (endoIter_frobeniusRestrictScalars_comp_toSheaf X p hX j) _)
    (CategoryTheory.map_comp_eq_map_of_iso
      (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens)
      ((frobeniusExtendScalarsIterIso X p hX j).app G) _ rfl)

/-- The leg of the objectwise cocone of Stacks Tag 0EXB, with its source and target spelled as
`Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj`. See
`AlgebraicGeometry.frobeniusPresheafDiagram_map_succ'` for why that spelling is the only one
used below. -/
lemma frobeniusPresheafCocone_ι_app' (n j : ℕ) :
    (((frobeniusPresheafCocone X p hX G.val n).ι.app j) :
        Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
            (frobeniusRingSheafIter X p hX j).hom G.val ⟶
          Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
            (frobeniusRingPresheafι X p hX n) G.val) =
      Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo (frobeniusRingSheafIter X p hX j).hom
        (frobeniusRingPresheafι X p hX (n + j)) G.val (frobeniusRingPresheafι X p hX n)
        (frobeniusRingSheafIter_hom_comp_frobeniusRingPresheafι X p hX j n) :=
  frobeniusPresheafCocone_ι_app X p hX G.val n j

/-- A morphism out of the `j`-th term of the objectwise diagram of Stacks Tag 0EXB, read after
the underlying abelian presheaf and its sheafification, with its source spelled
`Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj`.

The morphism is a variable and not the leg of the cocone, and that is the whole point: the two
spellings of the source are definitionally equal, but the kernel answers the question by
unfolding the morphism, and the leg unfolds through
`Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo` into an adjoint transpose. With a variable
there is nothing to unfold, and the leg is substituted afterwards. -/
lemma presheafToSheaf_comp_map_restrictExtendObj (n j : ℕ)
    (m : (frobeniusPresheafDiagram X p hX G.val).obj j ⟶
      Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
        (frobeniusRingPresheafι X p hX n) G.val) :
    (PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj ⋙
          presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u}).map m =
      (presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u}).map
        (@CategoryTheory.Functor.map _ _ _ _
          (PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj)
          (Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
            (frobeniusRingSheafIter X p hX j).hom G.val)
          (Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
            (frobeniusRingPresheafι X p hX n) G.val) m) :=
  rfl

/-- The leg of the objectwise cocone of Stacks Tag 0EXB, read after the underlying abelian
presheaf and its sheafification. -/
lemma presheafToSheaf_map_frobeniusPresheafCocone_ι_app (n j : ℕ) :
    @CategoryTheory.Functor.map _ _ _ _
        (PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj ⋙
          presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u})
        ((frobeniusPresheafDiagram X p hX G.val).obj j)
        (Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
          (frobeniusRingPresheafι X p hX n) G.val)
        ((frobeniusPresheafCocone X p hX G.val n).ι.app j) =
      (presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u}).map
        (@CategoryTheory.Functor.map _ _ _ _
          (PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj)
          (Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
            (frobeniusRingSheafIter X p hX j).hom G.val)
          (Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
            (frobeniusRingPresheafι X p hX n) G.val)
          (Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo
            (frobeniusRingSheafIter X p hX j).hom
            (frobeniusRingPresheafι X p hX (n + j)) G.val
            (frobeniusRingPresheafι X p hX n)
            (frobeniusRingSheafIter_hom_comp_frobeniusRingPresheafι X p hX j n))) :=
  (presheafToSheaf_comp_map_restrictExtendObj X p hX G n j
      ((frobeniusPresheafCocone X p hX G.val n).ι.app j)).trans
    (congrArg (fun q ↦ (presheafToSheaf (Opens.grothendieckTopology (X : TopCat))
        AddCommGrpCat.{u}).map ((PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj).map q))
      (frobeniusPresheafCocone_ι_app' X p hX G n j))

/-- **The leg of the cocone of Stacks Tag 0EXB becomes, on the underlying abelian sheaves, the
sheafification of the objectwise base change along the stage-`n + j` coprojection.** -/
theorem toSheaf_map_frobeniusStageRestrictLeg (n j : ℕ) :
    (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
          (frobeniusStageRestrictLeg X p hX n j G) ≫
        (frobeniusStageRestrictToSheafIso X p hX G n).hom =
      (frobeniusRestrictExtendToSheafIso X p hX G j).hom ≫
        @CategoryTheory.Functor.map _ _ _ _
          (PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj ⋙
            presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u})
          ((frobeniusPresheafDiagram X p hX G.val).obj j)
          (Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
            (frobeniusRingPresheafι X p hX n) G.val)
          ((frobeniusPresheafCocone X p hX G.val n).ι.app j) := by
  rw [presheafToSheaf_map_frobeniusPresheafCocone_ι_app,
    frobeniusStageRestrictToSheafIso_hom, frobeniusRestrictExtendToSheafIso_hom]
  exact CategoryTheory.comp_comp_eq_of_square
    (pullbackCompToSheafIso_frobeniusIterStageHom X p hX n j G)
    (toSheaf_map_frobeniusStageRestrictLeg_comp X p hX G n j)

/-- The leg condition comparing the cocone of Stacks Tag 0EXB, read on abelian sheaves, with
the abelian sheafification of the objectwise cocone precomposed with the comparison of the
diagrams. This is `AlgebraicGeometry.toSheaf_map_frobeniusStageRestrictLeg` in the shape
`CategoryTheory.Limits.Cocone.ext` asks for. -/
theorem frobeniusStageRestrictCocone_precompose_ι_app (n j : ℕ) :
    ((Cocone.precompose (frobeniusRestrictExtendDiagramToSheafIso X p hX G).hom).obj
          ((PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj ⋙
              presheafToSheaf (Opens.grothendieckTopology (X : TopCat))
                AddCommGrpCat.{u}).mapCocone
            (frobeniusPresheafCocone X p hX G.val n))).ι.app j ≫
        (frobeniusStageRestrictToSheafIso X p hX G n).symm.hom =
      ((_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).mapCocone
        (frobeniusStageRestrictCocone X p hX n G)).ι.app j := by
  show ((frobeniusRestrictExtendDiagramToSheafIso X p hX G).hom.app j ≫
        @CategoryTheory.Functor.map _ _ _ _
          (PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj ⋙
            presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u})
          ((frobeniusPresheafDiagram X p hX G.val).obj j)
          (Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
            (frobeniusRingPresheafι X p hX n) G.val)
          ((frobeniusPresheafCocone X p hX G.val n).ι.app j)) ≫
      (frobeniusStageRestrictToSheafIso X p hX G n).inv =
    (_root_.SheafOfModules.toSheaf X.ringSheafOnOpens).map
      (frobeniusStageRestrictLeg X p hX n j G)
  refine CategoryTheory.comp_comp_inv_eq_of_comp_hom_eq ?_
  rw [frobeniusRestrictExtendDiagramToSheafIso_hom_app]
  exact toSheaf_map_frobeniusStageRestrictLeg X p hX G n j

/-! ### The colimit -/

/-- **The cocone of Stacks Tag 0EXB is colimiting**: the `𝒪_X`-module underlying
`𝒢 ⊗_{𝒪_X} colim_F 𝒪_X` is the filtered colimit of the `F^{j,*}𝒢`.

Both the diagram and the apex are read on abelian sheaves, where everything becomes the
sheafification of the objectwise cocone `j ↦ 𝒪_X ⊗_{φ^j, 𝒪_X} 𝒢` of
`AlgebraicGeometry.frobeniusPresheafCocone`, which is colimiting by
`AlgebraicGeometry.isColimit_frobeniusPresheafCocone`; the forgetful functor to abelian sheaves
reflects colimits, and both the underlying abelian presheaf and its sheafification preserve
them. -/
noncomputable def isColimit_frobeniusStageRestrictCocone (n : ℕ) :
    IsColimit (frobeniusStageRestrictCocone X p hX n G) :=
  isColimit_frobeniusStageRestrictCocone_of_toSheaf X p hX n G
    (IsColimit.ofIsoColimit
      ((IsColimit.precomposeHomEquiv (frobeniusRestrictExtendDiagramToSheafIso X p hX G)
            ((PresheafOfModules.toPresheaf X.ringSheafOnOpens.obj ⋙
                presheafToSheaf (Opens.grothendieckTopology (X : TopCat))
                  AddCommGrpCat.{u}).mapCocone
              (frobeniusPresheafCocone X p hX G.val n))).symm
        (isColimitOfPreserves _ (isColimit_frobeniusPresheafCocone X p hX G.val n)))
      (Cocone.ext (frobeniusStageRestrictToSheafIso X p hX G n).symm
        (fun j ↦ frobeniusStageRestrictCocone_precompose_ι_app X p hX G n j)))

end AlgebraicGeometry

end
