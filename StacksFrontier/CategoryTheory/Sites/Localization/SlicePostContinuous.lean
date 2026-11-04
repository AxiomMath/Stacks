module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable

/-!
# A continuous functor of sites stays continuous on the slices

Let `u : C ⥤ D` be a continuous functor of sites, `J` on `C` and `K` on `D`, and let `X` be an
object of `C`. Localizing at `X` gives `Over.post u : C/X ⥤ D/u(X)`, and the two slices carry the
localized topologies `J.over X` and `K.over (u X)`. This file proves that `Over.post u` is again
continuous.

Mathlib has the *cocontinuous* half as an instance
(`CategoryTheory.Functor.IsCocontinuous` of `Over.post`), and it has
`CategoryTheory.CoverPreserving.overPost`, which is the easy half of continuity; but
`Functor.IsContinuous` is strictly stronger than cover-preservation, and Mathlib leaves the
statement below as a hypothesis everywhere it is needed — in
`StacksFrontier/CategoryTheory/Sites/Cohomology/HigherDirectImage/BiggerSiteGlobalCohomology.lean`
among others. It is discharged here once and for all.

## Main results

* `CategoryTheory.Functor.isContinuous_overPost`: `Over.post u` is continuous for the localized
  topologies.

## Implementation notes

The proof is the one of Stacks 00Y1 read through the equivalence
`Sh(D/u(X)) ≌ Sh(D)/h_{u(X)}^#` of
`StacksFrontier/CategoryTheory/Sites/Localization/SheavesOverRepresentable.lean`: a sheaf `G` on
`D/u(X)` is the *fibre* of a map of sheaves on `D` over the tautological section of
`h_{u(X)}^#`, and restricting a fibre along `Over.post u` is the fibre of the restricted map,
which is a sheaf on `C/X` by `CategoryTheory.OverShriek.isSheaf_fiber` — its two hypotheses being
sheafhood and separatedness of restrictions along `u` followed by `Over.forget X`, i.e. exactly
what continuity of `u` provides. That argument needs the coefficient universe to be the morphism
universe of both sites, so it is run on the small models `AsSmall C` and `AsSmall D` with the
induced topologies and transported back along the two equivalences, whose slice functors are
continuous because an equivalence is representably flat.

## References

* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
-/

@[expose] public section

open Opposite

namespace CategoryTheory.Functor

universe v v₁ v₂ u₁ u₂

/-- `Over.post F` is continuous when both sites are small and the coefficient universe is the
common object-and-morphism universe: the small case of
`CategoryTheory.Functor.isContinuous_overPost`. -/
private theorem isContinuous_overPost_small
    {C D : Type v} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] (X : C) :
    (Over.post (X := X) F).IsContinuous (J.over X) (K.over (F.obj X)) := by
  refine ⟨fun G => ?_⟩
  let T := (OverShriek.sheafFunctorToOver (U := F.obj X) K).obj G
  let A := (presheafToSheaf K (Type v)).obj (yoneda.obj (F.obj X))
  let ρ : yoneda.obj X ⟶ F.op ⋙ A.obj :=
    { app := fun Y => ↾fun f => (toSheafify K (yoneda.obj (F.obj X))).app (F.op.obj Y) (F.map f)
      naturality := by
        intro Y Z f
        ext g
        dsimp
        simpa [A, F.map_comp] using
          (NatTrans.naturality_apply (toSheafify K (yoneda.obj (F.obj X)))
            (F.map f.unop).op (F.map g)) }
  have hF' := (Over.forget X).op_comp_isSheaf_of_types (J.over X) J
    (⟨_, (isSheaf_iff_isSheaf_of_type _ _).2 (F.op_comp_isSheaf_of_types J K T.left)⟩ :
      Sheaf J (Type v))
  have hA' := (Over.forget X).op_comp_isSheaf_of_types (J.over X) J
    (⟨_, (isSheaf_iff_isSheaf_of_type _ _).2 (F.op_comp_isSheaf_of_types J K A)⟩ :
      Sheaf J (Type v))
  have h := OverShriek.isSheaf_fiber ρ (Functor.whiskerLeft F.op T.hom.hom) hF' hA'.isSeparated
  let e := Functor.isoWhiskerLeft (Over.post (X := X) F).op
    ((sheafToPresheaf (K.over (F.obj X)) (Type v)).mapIso
      ((OverShriek.sheafUnitIso K).app G))
  rw [← isSheaf_iff_isSheaf_of_type]
  exact (Presheaf.isSheaf_of_iso_iff e).2 ((isSheaf_iff_isSheaf_of_type _ _).2 h)

/-- **A continuous functor of sites induces a continuous functor of slices.** For `u : C ⥤ D`
continuous and `X : C`, the functor `Over.post u : C/X ⥤ D/u(X)` is continuous for the localized
topologies `J.over X` and `K.over (u X)`.

Mathlib supplies the cocontinuous counterpart as an instance but takes this statement as a
hypothesis; it holds with no hypothesis beyond continuity of `u`. -/
theorem isContinuous_overPost
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] (X : C) :
    (Over.post (X := X) F).IsContinuous (J.over X) (K.over (F.obj X)) := by
  let eC := (AsSmall.equiv : C ≌ AsSmall.{max u₁ v₁ u₂ v₂} C)
  let eD := (AsSmall.equiv : D ≌ AsSmall.{max u₁ v₁ u₂ v₂} D)
  let J' := eC.inverse.inducedTopology J
  let K' := eD.inverse.inducedTopology K
  let F' := eC.inverse ⋙ F ⋙ eD.functor
  have : (F ⋙ eD.functor).IsContinuous J K' :=
    Functor.isContinuous_comp _ _ _ K _
  have : F'.IsContinuous J' K' :=
    Functor.isContinuous_comp _ _ _ J _
  have : (Over.post (X := eC.functor.obj X) F').IsContinuous
      (J'.over (eC.functor.obj X)) (K'.over (F'.obj (eC.functor.obj X))) :=
    isContinuous_overPost_small J' K' F' _
  have : (Over.post (X := X) eC.functor).IsContinuous
      (J.over X) (J'.over (eC.functor.obj X)) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous eC.functor J J').overPost X)
  have : (Over.post (X := F'.obj (eC.functor.obj X)) eD.inverse).IsContinuous
      (K'.over (F'.obj (eC.functor.obj X))) (K.over (F.obj X)) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous eD.inverse K' K).overPost _)
  have : (Over.post (X := X) eC.functor ⋙ Over.post F').IsContinuous
      (J.over X) (K'.over (F'.obj (eC.functor.obj X))) :=
    Functor.isContinuous_comp _ _ _ (J'.over (eC.functor.obj X)) _
  exact Functor.isContinuous_comp
    (Over.post (X := X) eC.functor ⋙ Over.post F') (Over.post eD.inverse)
    (J.over X) (K'.over (F'.obj (eC.functor.obj X))) (K.over (F.obj X))

end CategoryTheory.Functor

end
