module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomology
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCechComplex
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationDescentAb
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringCohomologicalDescent

/-!
# Global sections on the total site are global sections of the direct image

Let `C` be a site, let `K` be a simplicial semi-representable object of `C` and let
`a : Sh((C/K)_total) ⟶ Sh(C)` be the augmentation of Stacks 0D8B. The **underived** identity

`Γ(C, a_*ℱ) = Γ((C/K)_total, ℱ)`

is the datum on which the factorisation `RΓ((C/K)_total, -) = RΓ(C, -) ∘ Ra_*` of Stacks 08J6
rests, and it is what
`CategoryTheory.SimplicialSiteSituation.Augmentation.derivedGlobalSectionsPushforwardIso` takes as
its hypothesis `hΓ`. This file proves it, for every simplicial semi-representable object of every
site and with no hypothesis on `K`.

## Why it is a theorem and not an assumption

The module docstring of
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringDerivedGlobalSections.lean` says of
`hΓ`
that it "is not available in this library", on the ground that "nothing in Mathlib or in this
development says that the inverse image of a morphism of topoi carries a constant abelian sheaf to
a constant abelian sheaf". The first half of that account is the right reduction and the second
half is false. Because `CategoryTheory.Sheaf.Γ` is by definition the right adjoint of
`CategoryTheory.constantSheaf`, and `a_*` is the right adjoint of `a⁻¹`, uniqueness of right
adjoints turns `hΓ` into

`constantSheaf C ⋙ a⁻¹ ≅ constantSheaf (C/K)_total`

on abelian sheaves — and that statement is
`Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso`, which holds for an arbitrary
coefficient category, needs no terminal object and no equivalence hypothesis, and asks only that
the functor of sites be continuous and cocontinuous. The functor here is the localization functor
`j_total`, which is both, by
`CategoryTheory.SimplicialSemiRepresentable.totalForget_isContinuous` and
`.totalForget_isCocontinuous`; and `a⁻¹` on abelian sheaves *is* restriction along `j_total`, by
`CategoryTheory.SimplicialSemiRepresentable.situationTotalInverseImageAbIso`, which also needs no
condition on `K`. So every ingredient is already in the library.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.constantSheafTotalInverseImageAbIso`: **the inverse
  image of a constant abelian sheaf along the augmentation is the constant abelian sheaf**,
  `constantSheaf C ⋙ a⁻¹ ≅ constantSheaf (C/K)_total`.
* `CategoryTheory.SimplicialSemiRepresentable.abelianTotalPushforwardGammaIso`: **the underived
  identity of Stacks 08J6** for the augmentation of Stacks 0D8B,
  `a_* ⋙ Γ(C, -) ≅ Γ((C/K)_total, -)`. This is the `hΓ` of
  `.Augmentation.derivedGlobalSectionsPushforwardIso` and of
  `.Augmentation.derivedGlobalSectionsInverseImageIso`.
* `CategoryTheory.SimplicialSemiRepresentable.abelianTotalPushforwardGammaIsoOver`: the same over
  a slice site `C/X`, which is the shape Stacks 09X7 and Stacks 09X9 consume.

## Implementation notes

The total site has two spellings here: `Grothendieck (slices K)`, which is the type of the
localization functor `totalForget K`, and `↥(situation J K).totalCategory`, which is the type
`(situation J K).totalTopology` is a topology on. They are definitionally equal, but the instances
`totalForget_isContinuous`, `totalForget_isCocontinuous` and `HasWeakSheafify` are only *found* at
the first, while the expected type of the comparison forces the second. So
`constantSheafTotalInverseImageAbIso` applies `constantSheafRestrictionIso` with its site argument
given explicitly as `Grothendieck (slices K)` and every instance it cannot then find passed by
name — `hasWeakSheafifyTotalAb` and `hasLimitsStructuredArrowTotalForget` being named for exactly
that purpose. A type ascription does not do it.

The two steps are separate declarations rather than one, because each of them compares the two
spellings once and doing both in a single declaration exhausts the elaboration budget.

## References

* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialSiteSituation Opposite

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable SimplicialSiteSituation

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-! ### The instances the comparison cannot find on its own -/

/-- Abelian sheaves on the total site admit sheafification. This is `inferInstance`; it is named
because the comparison of this file needs it at the spelling `Grothendieck (slices K)` of the
total site, where instance search does not find it. See the implementation notes. -/
theorem hasWeakSheafifyTotalAb :
    HasWeakSheafify ((situation J K).totalTopology) AddCommGrpCat.{u} :=
  inferInstance

/-- `AddCommGrpCat` has limits of the shapes the right Kan extension along `j_total` needs. This is
`inferInstance`; it is named for the same reason as `hasWeakSheafifyTotalAb`. -/
theorem hasLimitsStructuredArrowTotalForget :
    ∀ X : Cᵒᵖ, HasLimitsOfShape (StructuredArrow X (totalForget K).op) AddCommGrpCat.{u} :=
  fun _ => inferInstance

/-! ### The inverse image of a constant abelian sheaf is constant -/

/-- **The inverse image along the augmentation of Stacks 0D8B carries a constant abelian sheaf to
the constant abelian sheaf:** `constantSheaf C ⋙ a⁻¹ ≅ constantSheaf (C/K)_total` on abelian
sheaves. No condition on `K` is used.

`a⁻¹` on abelian sheaves is restriction along the localization functor `j_total`, by
`situationTotalInverseImageAbIso`, and `j_total` is continuous and cocontinuous; for such a functor
of sites the restriction of a constant sheaf is the constant sheaf, with no terminal object and for
an arbitrary coefficient category, which is
`Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso`. -/
def constantSheafTotalInverseImageAbIso :
    constantSheaf J AddCommGrpCat.{u} ⋙
        Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
          (situationAugmentation J K) ≅
      constantSheaf ((situation J K).totalTopology) AddCommGrpCat.{u} :=
  Functor.isoWhiskerLeft (constantSheaf J AddCommGrpCat.{u}) (situationTotalInverseImageAbIso J K)
    ≪≫
    @Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso
      (Grothendieck (slices K)) _ C _ ((situation J K).totalTopology) J (totalForget K)
      AddCommGrpCat.{u} _ (hasWeakSheafifyTotalAb J K) _
      (totalForget_isContinuous J K) (totalForget_isCocontinuous J K)
      (hasLimitsStructuredArrowTotalForget K)

/-! ### The underived identity of Stacks 08J6 -/

/-- **The underived identity on which Stacks 08J6 rests, for the augmentation of Stacks 0D8B:**
`Γ(C, a_*ℱ) = Γ((C/K)_total, ℱ)`, as an isomorphism of functors
`a_* ⋙ Γ(C, -) ≅ Γ((C/K)_total, -)` on abelian sheaves. No condition on `K` is used.

This is the `hΓ` hypothesis of
`CategoryTheory.SimplicialSiteSituation.Augmentation.derivedGlobalSectionsPushforwardIso` and of
`.derivedGlobalSectionsInverseImageIso`, and it is a theorem rather than an assumption.

`Γ` is the right adjoint of `constantSheaf` and `a_*` is the right adjoint of `a⁻¹`, so
`a_* ⋙ Γ(C, -)` is right adjoint to `constantSheaf C ⋙ a⁻¹`, which
`constantSheafTotalInverseImageAbIso` identifies with `constantSheaf (C/K)_total`; the two
functors are therefore right adjoints of one and the same functor, and uniqueness of right
adjoints identifies them. -/
def abelianTotalPushforwardGammaIso :
    Augmentation.abelianTotalPushforward (situation J K) (Cat.of C) J
          (situationAugmentation J K) ⋙
        Sheaf.Γ J AddCommGrpCat.{u} ≅
      Sheaf.Γ ((situation J K).totalTopology) AddCommGrpCat.{u} :=
  Adjunction.rightAdjointUniq
    (Adjunction.ofNatIsoLeft
      ((constantSheafΓAdj J AddCommGrpCat.{u}).comp
        (Augmentation.abelianTotalAdjunction (situation J K) (Cat.of C) J
          (situationAugmentation J K)))
      (constantSheafTotalInverseImageAbIso J K))
    (constantSheafΓAdj ((situation J K).totalTopology) AddCommGrpCat.{u})

/-! ### The same over an object of the site -/

section Over

variable [HasPullbacks C] (P : Pretopology C) {X : C}
  (L : SimplicialObject (FormalCoproduct.{u} (Over X)))

/-- **The underived identity of Stacks 08J6 over a slice site `C/X`:**
`Γ(C/X, a_*ℱ) = Γ((C/L)_total, ℱ)` for the augmentation of Stacks 0D8B read over `C/X`. This is
the `hΓ` that Stacks 09X7 and Stacks 09X9 consume, and it holds for every simplicial
semi-representable object `L` over `X`, with no hypothesis on `L`. -/
def abelianTotalPushforwardGammaIsoOver :
    Augmentation.abelianTotalPushforward (situation (P.toGrothendieck.over X) L)
          (Cat.of (Over X)) (P.toGrothendieck.over X)
          (situationAugmentation (P.toGrothendieck.over X) L) ⋙
        Sheaf.Γ (P.toGrothendieck.over X) AddCommGrpCat.{u} ≅
      Sheaf.Γ ((situation (P.toGrothendieck.over X) L).totalTopology) AddCommGrpCat.{u} :=
  abelianTotalPushforwardGammaIso (P.toGrothendieck.over X) L

end Over

end CategoryTheory.SimplicialSemiRepresentable

end
