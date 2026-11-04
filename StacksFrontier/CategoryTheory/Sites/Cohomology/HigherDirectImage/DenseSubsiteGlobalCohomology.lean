module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.BiggerSiteGlobalCohomology

/-!
# Global cohomology does not change along a dense subsite

Let `G : C ⥤ D` be a continuous and cocontinuous functor of sites whose restriction functor
`g⁻¹ = G.sheafPushforwardContinuous` on abelian sheaves is an *equivalence* — which is the case
for the inclusion of a dense subsite, by
`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`, and in particular for a special cocontinuous
functor in the sense of [Stacks, Tag 03CG].  Then restriction along `G` does not change global
sheaf cohomology:

`g⁻¹ ⋙ H^p(C, -) ≅ H^p(D, -)`,

naturally in the abelian sheaf on `(D, K)`.

The engine for such a comparison is
`Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfConstantSheafIsoOfAcyclic`, which asks
for two data: the comparison of constant sheaves `g_! ℤ_C ≅ ℤ_D` in degree zero, and acyclicity
of the restriction of an injective abelian sheaf.  Both are supplied here, and neither needs a
terminal object: the restriction of the constant sheaf is the constant sheaf for any continuous
and cocontinuous functor, because restriction of presheaves takes a constant presheaf to the
constant presheaf and commutes with sheafification
(`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility`); and an equivalence
preserves injective objects, whose higher cohomology vanishes.

## Main definitions

* `Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso` — **the restriction of a
  constant sheaf along a continuous and cocontinuous functor is the constant sheaf.**  This holds
  with no equivalence hypothesis and is the general fact behind the degree-zero datum.
* `Stacks.Cohomology.DenseSubsiteGlobal.pullbackConstantSheafIso` — the degree-zero datum
  `g_! ℤ_C ≅ ℤ_D` in the form the engine consumes, obtained from the previous isomorphism and
  the counit of `g_! ⊣ g⁻¹`, which is invertible because `g⁻¹` is an equivalence.

## Main results

* `Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence` — **restriction along
  a continuous and cocontinuous functor whose restriction of abelian sheaves is an equivalence
  does not change global cohomology**, in every degree.

## Implementation notes

This is a variant of [Stacks, Tag 03YU] (see
`StacksFrontier/CategoryTheory/Sites/Cohomology/HigherDirectImage/BiggerSiteGlobalCohomology.lean`),
with the terminal objects in the hypotheses of that tag replaced by the invertibility of
restriction.

For sheaves of modules the degree-zero datum would instead be the comparison of structure sheaves
`g_! g^*O ≅ O`, which is not what `constantSheafRestrictionIso` provides.

## References

* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 03CG](https://stacks.math.columbia.edu/tag/03CG)
* [Stacks Project, Tag 03A0](https://stacks.math.columbia.edu/tag/03A0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.DenseSubsiteGlobal

universe w v v' u u'

section ConstantSheaf

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  (A : Type*) [Category* A] [HasWeakSheafify J A] [HasWeakSheafify K A]
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [∀ X, HasLimitsOfShape (StructuredArrow X G.op) A]

/-- **The restriction of a constant sheaf along a continuous and cocontinuous functor of sites is
the constant sheaf.**  On presheaves the restriction of a constant presheaf is the constant
presheaf on the nose, and restriction commutes with sheafification when the functor is
cocontinuous, which is
`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility`. -/
def constantSheafRestrictionIso :
    constantSheaf K A ⋙ G.sheafPushforwardContinuous A J K ≅ constantSheaf J A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.const Dᵒᵖ)
      (G.pushforwardContinuousSheafificationCompatibility A J K).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Iso.refl _) (presheafToSheaf J A)

end ConstantSheaf

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  (A : Type*) [Category* A] [HasWeakSheafify J A] [HasWeakSheafify K A]
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [∀ X, HasLimitsOfShape (StructuredArrow X G.op) A]

variable [(G.sheafPushforwardContinuous A J K).IsEquivalence]

/-- **The lower shriek takes the constant sheaf to the constant sheaf**, `g_! M_C ≅ M_D`, when
restriction is an equivalence.  Restriction takes `M_D` to `M_C` by
`constantSheafRestrictionIso`, and the counit of `g_! ⊣ g⁻¹` is invertible because `g⁻¹` is an
equivalence, so applying `g_!` to that identification and composing with the counit is the
required comparison.  This is the degree-zero datum of
`Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfConstantSheafIsoOfAcyclic`. -/
def pullbackConstantSheafIso (M : A) :
    (G.sheafPullback A J K).obj ((constantSheaf J A).obj M) ≅ (constantSheaf K A).obj M :=
  (G.sheafPullback A J K).mapIso ((constantSheafRestrictionIso J K G A).app M).symm ≪≫
    asIso ((G.sheafAdjunctionContinuous A J K).counit.app ((constantSheaf K A).obj M))

section Cohomology

variable [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{max u w} (Sheaf J AddCommGrpCat.{w})]
  [HasExt.{max u w} (Sheaf K AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{w})]
  [∀ X, HasLimitsOfShape (StructuredArrow X G.op) AddCommGrpCat.{w}]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsEquivalence]

/-- **Restriction along a continuous and cocontinuous functor of sites whose restriction of
abelian sheaves is an equivalence does not change global cohomology.**  For every degree `p`,

`H^p(C, g⁻¹ F) ≅ H^p(D, F)`

naturally in the abelian sheaf `F` on `(D, K)`, where `H^p` is `CategoryTheory.Sheaf.functorH`,
the `Ext`-groups out of the constant sheaf on `ℤ`.

Both hypotheses of the engine are available: the degree-zero datum is
`pullbackConstantSheafIso`, and the restriction of an injective abelian sheaf is injective, an
equivalence preserving injective objects, so its higher cohomology vanishes. -/
def sheafCohomologyIsoOfIsEquivalence (p : ℕ) :
    G.sheafPushforwardContinuous AddCommGrpCat.{w} J K ⋙
        Sheaf.functorH.{max u w, w, v, u} J p ≅
      Sheaf.functorH.{max u w, w, v, u} K p :=
  Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfConstantSheafIsoOfAcyclic J K G
    (pullbackConstantSheafIso J K G AddCommGrpCat.{w} (AddCommGrpCat.of (ULift.{w} ℤ)))
    (fun I hI _n a ↦
      haveI : Injective ((G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj I) :=
        (G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).injective_obj_of_injective hI
      Subsingleton.elim a 0) p

end Cohomology

end Stacks.Cohomology.DenseSubsiteGlobal

end
