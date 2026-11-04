module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfALocalizedSite
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteTypeLocality
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors

/-!
# Cohomology of a sheaf restricted to the slice over an object of a slice

Let `(C, J)` be a site, `X` an object of `C` and `W : Over X`. The slice `(C/X)/W` is identified
with `C/W.left` by the iterated slice equivalence, and restricting an abelian sheaf `F` on `C/X`
to `(C/X)/W` and transporting it to `C/W.left` is restriction along `Over.map W.hom`. Its
cohomology over an object `V` of `C/W.left` is the cohomology of `F` over `Over.map W.hom V`:
cohomology commutes with localization (Stacks 03F3, here
`Stacks.Cohomology.LocalizedSite.overPullbackRightDerivedSectionsIso`) and with the equivalence
of sites.

## Main results

* `Stacks.Cohomology.LocalizedSite.iteratedSliceRightDerivedSectionsIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.LocalizedSite

universe v u w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [UnivLE.{max u v, w}] [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{w}]

attribute [local instance] Stacks.ConstantSheaf.iteratedSliceBackward_sheafPushforward_isEquivalence
  Stacks.ConstantSheaf.hasWeakSheafify_over_over

/-- **Cohomology over an object of a slice of a slice.** For `W : Over X` and `V : Over W.left`,
the cohomology over `V` of the restriction of `F` to `(C/X)/W`, transported to `C/W.left`, is the
cohomology of `F` over `Over.map W.hom V`. -/
def iteratedSliceRightDerivedSectionsIso (X : C) (W : Over X)
    [∀ W : Over X, HasSheafify ((J.over X).over W) AddCommGrpCat.{w}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [EnoughInjectives (Sheaf (J.over X) AddCommGrpCat.{w})]
    [EnoughInjectives (Sheaf ((J.over X).over W) AddCommGrpCat.{w})]
    [EnoughInjectives (Sheaf (J.over W.left) AddCommGrpCat.{w})]
    (p : ℕ) (V : Over W.left) (F : Sheaf (J.over X) AddCommGrpCat.{w}) :
    (((sheafToPresheaf (J.over W.left) AddCommGrpCat.{w} ⋙
        (evaluation (Over W.left)ᵒᵖ AddCommGrpCat.{w}).obj (op V)).rightDerived p).obj
      ((W.iteratedSliceBackward.sheafPushforwardContinuous AddCommGrpCat.{w} (J.over W.left)
        ((J.over X).over W)).obj (((J.over X).overPullback AddCommGrpCat.{w} W).obj F))) ≅
      ((sheafToPresheaf (J.over X) AddCommGrpCat.{w} ⋙
        (evaluation (Over X)ᵒᵖ AddCommGrpCat.{w}).obj (op ((Over.map W.hom).obj V))).rightDerived
          p).obj F :=
  ((Stacks.Cohomology.SheafifiedHigherDirectImage.pushforwardRightDerivedSectionsIso
      AddCommGrpCat.{w} W.iteratedSliceBackward p V).app
    (((J.over X).overPullback AddCommGrpCat.{w} W).obj F)) ≪≫
    (overPullbackRightDerivedSectionsIso (J.over X) W p (W.iteratedSliceBackward.obj V)).app F

/-- **Vanishing of cohomology over an object lying over `W`, read on `C/W.left`.** If `g : V ⟶ W`
in `C/X`, the cohomology of `F` over `V` vanishes as soon as that of the restriction of `F` to
`(C/X)/W`, transported to `C/W.left`, vanishes over `Over.mk g.left`. -/
theorem isZero_rightDerivedSections_of_iteratedSlice (X : C) (W : Over X)
    [∀ W : Over X, HasSheafify ((J.over X).over W) AddCommGrpCat.{w}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [EnoughInjectives (Sheaf (J.over X) AddCommGrpCat.{w})]
    [EnoughInjectives (Sheaf ((J.over X).over W) AddCommGrpCat.{w})]
    [EnoughInjectives (Sheaf (J.over W.left) AddCommGrpCat.{w})]
    (p : ℕ) {V : Over X} (g : V ⟶ W) (F : Sheaf (J.over X) AddCommGrpCat.{w})
    (h : IsZero (((sheafToPresheaf (J.over W.left) AddCommGrpCat.{w} ⋙
        (evaluation (Over W.left)ᵒᵖ AddCommGrpCat.{w}).obj (op (Over.mk g.left))).rightDerived
          p).obj
      ((W.iteratedSliceBackward.sheafPushforwardContinuous AddCommGrpCat.{w} (J.over W.left)
        ((J.over X).over W)).obj (((J.over X).overPullback AddCommGrpCat.{w} W).obj F)))) :
    IsZero (((sheafToPresheaf (J.over X) AddCommGrpCat.{w} ⋙
        (evaluation (Over X)ᵒᵖ AddCommGrpCat.{w}).obj (op V)).rightDerived p).obj F) := by
  have e : V ≅ (Over.map W.hom).obj (Over.mk g.left) :=
    Over.isoMk (Iso.refl _) (by simp [Over.w g])
  exact (h.of_iso (iteratedSliceRightDerivedSectionsIso J X W p (Over.mk g.left) F).symm).of_iso
    ((Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (Functor.isoWhiskerLeft (sheafToPresheaf (J.over X) AddCommGrpCat.{w})
        ((evaluation (Over X)ᵒᵖ AddCommGrpCat.{w}).mapIso e.op)) p).symm.app F)

end Stacks.Cohomology.LocalizedSite

end
