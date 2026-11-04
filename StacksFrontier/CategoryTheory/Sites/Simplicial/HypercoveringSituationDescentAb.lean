module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.PresheafObjects
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.MorphismOfSites
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolution
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringEssSurjAb
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationPushforwardComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The essential image of `a⁻¹` on abelian sheaves, and Stacks 0D8K (2)

For a hypercovering, the essential image of `a⁻¹` on abelian sheaves is the cartesian abelian
sheaves (Stacks 0D8E (2)), with `a⁻¹` read as restriction of abelian sheaves along the
localization functor `j_total`. This file proves the same clause over an object `X` of `C`
(Stacks 0D8K (2)), and transports both clauses to the abelian inverse image
`CategoryTheory.Sites.abelianInverseImage` (Stacks 04JC) of the morphism of topoi which
Stacks 0D70 attaches to the augmentation of a simplicial-site situation.

The transport is a general statement: for a continuous functor `v` of sites and a morphism of
topoi `f` whose set-valued inverse image is isomorphic to restriction along `v`, the abelian
inverse image of `f` is restriction of abelian sheaves along `v`.

## Main definitions

* `CategoryTheory.Sites.abelianInverseImageIsoSheafPushforwardContinuous`: the abelian inverse
  image of a morphism of topoi whose set-valued inverse image is restriction along a continuous
  functor `v` is restriction of abelian sheaves along `v`.
* `CategoryTheory.SimplicialSemiRepresentable.situationTotalInverseImageAbIso`: the abelian
  inverse image `CategoryTheory.SimplicialSiteSituation.Augmentation.totalInverseImageAb` of the
  morphism of topoi of Stacks 0D70 is restriction of abelian sheaves along `j_total`.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable`
  `.essImage_situationTotalInverseImageAb_of_isCartesianAbSheaf` and
  `.mem_essImage_situationTotalInverseImageAb_iff_isCartesianAbSheaf`: Stacks 0D8E (2) for the
  abelian inverse image of the morphism of topoi of Stacks 0D70: every cartesian abelian sheaf on
  the total site is an `a⁻¹𝒢`, and the essential image is exactly the cartesian abelian sheaves.
* `CategoryTheory.SimplicialSemiRepresentable.essImage_of_isCartesianAbSheaf_over` and
  `.mem_essImage_abelianInverseImage_iff_isCartesianAbSheaf_over`: Stacks 0D8K (2): for a
  hypercovering of an object `X`, every cartesian abelian sheaf on the total site is an `a⁻¹𝒢` and
  the essential image of `a⁻¹` is exactly the cartesian abelian sheaves, `a⁻¹` being restriction
  along `j_total`.
* `CategoryTheory.SimplicialSemiRepresentable.isIso_abelianCounit_app_over`: Stacks 0D8K (2):
  the counit `a⁻¹a_*ℱ ⟶ ℱ` is invertible at every cartesian abelian `ℱ`.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.essImage_situationTotalInverseImageAb_of_isCartesianAbSheaf_over` and
  `.mem_essImage_situationTotalInverseImageAb_iff_isCartesianAbSheaf_over`: the same two
  statements over an object, for the abelian inverse image of the morphism of topoi of
  Stacks 0D70.

## Implementation notes

In `essImage_of_isCartesianAbSheaf_over` the sheaf is quantified inside the statement, its
category depending on the topology `P.toGrothendieck.over X`. Over `C/X` the hypothesis
`HasEqualizers C` is omitted: `C/X` has a final object and, from `HasPullbacks C`, fibre products,
hence all finite limits.

## References

* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D8C](https://stacks.math.columbia.edu/tag/0D8C)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D8K](https://stacks.math.columbia.edu/tag/0D8K)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 00YT](https://stacks.math.columbia.edu/tag/00YT)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 01G5](https://stacks.math.columbia.edu/tag/01G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryTheory.Hypercovering

namespace CategoryTheory.Sites

attribute [local instance] Stacks.Sites.AbelianPullback.cartesianMonoidalCategorySheaf
  Stacks.Sites.AbelianPullback.braidedCategorySheaf
  Stacks.Sites.AbelianPullback.preservesFiniteLimitsSheafPushforward
  Stacks.Sites.AbelianPullback.braidedSheafPushforward
  Stacks.Sites.AbelianPullback.braidedInverseImageOfTopoi

universe w u₀ v₀ u₁ v₁

/-- The abelian inverse image of a morphism of topoi `f` whose set-valued inverse image is
restriction along a continuous functor `v` is restriction of abelian sheaves along `v`. -/
def abelianInverseImageIsoSheafPushforwardContinuous {A : Type u₀} [Category.{v₀} A]
    {B : Type u₁} [Category.{v₁} B] (v : A ⥤ B) (JA : GrothendieckTopology A)
    (JB : GrothendieckTopology B) [v.IsContinuous JA JB]
    [(v.sheafPushforwardContinuous (Type w) JA JB).IsRightAdjoint]
    (f : MorphismOfTopoi (Sheaf JA (Type w)) (Sheaf JB (Type w)))
    (α : f.inverseImage ≅ v.sheafPushforwardContinuous (Type w) JA JB) :
    abelianInverseImage f ≅ v.sheafPushforwardContinuous AddCommGrpCat.{w} JA JB :=
  Functor.isoWhiskerLeft (AbelianSheaf.internalSheaf JB)
      (Functor.isoWhiskerRight (Functor.mapCommGrpNatIso α) (AbelianSheaf.externalSheaf JA)) ≪≫
    Stacks.Sites.AbelianPullback.abelianSheafPushforwardIso v JA JB

end CategoryTheory.Sites

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable SimplicialSiteSituation

variable {C : Type u} [SmallCategory C]

/-! ### The abelian inverse image of the augmentation is restriction along `j_total` -/

variable (J : GrothendieckTopology C) (K : SimplicialObject (FormalCoproduct.{u} C))
  [J.toCoverage.HasPullbacks]

/-- The abelian inverse image of the morphism of topoi which Stacks 0D70 attaches to the
augmentation of the simplicial-site situation of a simplicial semi-representable object `K` is
restriction of abelian sheaves along the localization functor `j_total`. -/
def situationTotalInverseImageAbIso :
    Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J (situationAugmentation J K) ≅
      (totalForget K).sheafPushforwardContinuous Ab.{u} ((situation J K).totalTopology) J :=
  letI : ((totalForget K).sheafPushforwardContinuous (Type u)
      ((situation J K).totalTopology) J).IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (totalForget K) (Type u)
      ((situation J K).totalTopology) J).isRightAdjoint
  Sites.abelianInverseImageIsoSheafPushforwardContinuous (totalForget K)
    ((situation J K).totalTopology) J _
    (CocontinuousSimplicialSite.Augmentation.totalInverseImageIso (augmentation J K) ≪≫
      totalInverseImageIso J K)

/-! ### Stacks 0D8E (2) for the inverse image of the morphism of topoi of Stacks 0D70 -/

variable [HasEqualizers C] [HasPullbacks C]

/-- Every cartesian abelian sheaf on the total site lies in the essential image of the abelian
inverse image of the morphism of topoi which Stacks 0D70 attaches to the augmentation of the
simplicial-site situation of a hypercovering. -/
@[stacks 0D8E "part (2): every cartesian abelian sheaf is an a^{-1}G for the a of Stacks 0D70 at \
the simplicial-site situation"]
theorem essImage_situationTotalInverseImageAb_of_isCartesianAbSheaf (P : Pretopology C)
    (H : HypercoveringOfTerminal.{u, u, u} P)
    (G : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology Ab.{u})
    (hG : (situation P.toGrothendieck H.toSimplicialObject).IsCartesianAbSheaf G) :
    (Augmentation.totalInverseImageAb (situation P.toGrothendieck H.toSimplicialObject)
      (Cat.of C) P.toGrothendieck
      (situationAugmentation P.toGrothendieck H.toSimplicialObject)).essImage G :=
  Functor.essImage.ofNatIso
    (situationTotalInverseImageAbIso P.toGrothendieck H.toSimplicialObject).symm
    (essImage_of_isCartesianAbSheaf P H G hG)

/-- The essential image of the abelian inverse image of the morphism of topoi of Stacks 0D70 at
the simplicial-site situation of a hypercovering is exactly the cartesian abelian sheaves. -/
@[stacks 0D8E "part (2): the essential image of the a^{-1} of Stacks 0D70 at the \
simplicial-site situation is exactly the cartesian abelian sheaves"]
theorem mem_essImage_situationTotalInverseImageAb_iff_isCartesianAbSheaf (P : Pretopology C)
    (H : HypercoveringOfTerminal.{u, u, u} P)
    (G : Sheaf (situation P.toGrothendieck H.toSimplicialObject).totalTopology Ab.{u}) :
    (Augmentation.totalInverseImageAb (situation P.toGrothendieck H.toSimplicialObject)
        (Cat.of C) P.toGrothendieck
        (situationAugmentation P.toGrothendieck H.toSimplicialObject)).essImage G ↔
      (situation P.toGrothendieck H.toSimplicialObject).IsCartesianAbSheaf G :=
  (Functor.essImage_eq_of_natIso
    (situationTotalInverseImageAbIso P.toGrothendieck H.toSimplicialObject)) ▸
    ⟨isCartesianAbSheaf_of_mem_essImage P.toGrothendieck H.toSimplicialObject,
      essImage_of_isCartesianAbSheaf P H G⟩

/-! ### Stacks 0D8K (2): the essential image for a hypercovering of an object -/

section Over

omit [HasEqualizers C]

variable (P : Pretopology C) {X : C} (L : SimplicialObject (FormalCoproduct.{u} (Over X)))

/-- For a hypercovering `L` of an object `X`, every cartesian sheaf of abelian groups on the
total site is isomorphic to the restriction along the localization functor `j_total` of a sheaf of
abelian groups on `C/X`. -/
@[stacks 0D8K "part (2): every cartesian abelian sheaf on the total site is an a^{-1}G"]
theorem essImage_of_isCartesianAbSheaf_over (hL : IsHypercovering P L) :
    ∀ G : Sheaf (situation (P.toGrothendieck.over X) L).totalTopology Ab.{u},
      (situation (P.toGrothendieck.over X) L).IsCartesianAbSheaf G →
        ((totalForget L).sheafPushforwardContinuous Ab.{u}
          ((situation (P.toGrothendieck.over X) L).totalTopology)
          (P.toGrothendieck.over X)).essImage G := by
  have : HasFiniteLimits (Over X) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  obtain ⟨H, hH⟩ := exists_hypercoveringOfTerminal_over_of_isHypercovering P L hL
  have hQ : ((P.toGrothendieck.over X).toPretopology).toGrothendieck =
      P.toGrothendieck.over X := (Pretopology.gi (C := Over X)).l_u_eq _
  rw [← hQ, ← hH]
  exact fun G hG => essImage_of_isCartesianAbSheaf _ H G hG

/-- For a hypercovering `L` of an object `X`, the essential image of restriction of abelian
sheaves along `j_total` is exactly the cartesian abelian sheaves. -/
@[stacks 0D8K "part (2): the essential image of a^{-1} on abelian sheaves is exactly the \
cartesian abelian sheaves"]
theorem mem_essImage_abelianInverseImage_iff_isCartesianAbSheaf_over (hL : IsHypercovering P L)
    (G : Sheaf (situation (P.toGrothendieck.over X) L).totalTopology Ab.{u}) :
    ((totalForget L).sheafPushforwardContinuous Ab.{u}
        ((situation (P.toGrothendieck.over X) L).totalTopology)
        (P.toGrothendieck.over X)).essImage G ↔
      (situation (P.toGrothendieck.over X) L).IsCartesianAbSheaf G :=
  ⟨isCartesianAbSheaf_of_mem_essImage_over L P.toGrothendieck,
    essImage_of_isCartesianAbSheaf_over P L hL G⟩

/-- For a cartesian sheaf of abelian groups `ℱ` on the total site of a hypercovering of an
object `X`, the counit `a⁻¹ a_* ℱ ⟶ ℱ` is an isomorphism. -/
@[stacks 0D8K "part (2): a^{-1} a_* F = F for cartesian F on abelian sheaves"]
theorem isIso_abelianCounit_app_over (hL : IsHypercovering P L)
    (G : Sheaf (situation (P.toGrothendieck.over X) L).totalTopology Ab.{u})
    (hG : (situation (P.toGrothendieck.over X) L).IsCartesianAbSheaf G) :
    IsIso ((abelianTotalAdjunction (P.toGrothendieck.over X) L).counit.app G) :=
  (isIso_abelianCounit_app_iff_mem_essImage_of_isLocallyFull (P.toGrothendieck.over X) L
    (isCoverDense_totalForget_over P L hL.1) (isLocallyFull_totalForget_over P L hL) G).mpr
    (essImage_of_isCartesianAbSheaf_over P L hL G hG)

/-- For a hypercovering `L` of an object `X`, every cartesian abelian sheaf on the total site
lies in the essential image of the abelian inverse image of the total augmentation which
Stacks 0D70 constructs from the simplicial-site situation of `C/X`. -/
@[stacks 0D8K "part (2): every cartesian abelian sheaf is an a^{-1}G for the a of Stacks 0D70 at \
the simplicial-site situation of C/X"]
theorem essImage_situationTotalInverseImageAb_of_isCartesianAbSheaf_over
    (hL : IsHypercovering P L)
    (G : Sheaf (situation (P.toGrothendieck.over X) L).totalTopology Ab.{u})
    (hG : (situation (P.toGrothendieck.over X) L).IsCartesianAbSheaf G) :
    (Augmentation.totalInverseImageAb (situation (P.toGrothendieck.over X) L)
      (Cat.of (Over X)) (P.toGrothendieck.over X)
      (situationAugmentation (P.toGrothendieck.over X) L)).essImage G :=
  Functor.essImage.ofNatIso
    (situationTotalInverseImageAbIso (P.toGrothendieck.over X) L).symm
    (essImage_of_isCartesianAbSheaf_over P L hL G hG)

/-- For a hypercovering `L` of an object `X`, the essential image of the abelian inverse image of
the morphism of topoi of Stacks 0D70 at the simplicial-site situation of `C/X` is exactly the
cartesian abelian sheaves. -/
@[stacks 0D8K "part (2): the essential image of the a^{-1} of Stacks 0D70 at the \
simplicial-site situation of C/X is exactly the cartesian abelian sheaves"]
theorem mem_essImage_situationTotalInverseImageAb_iff_isCartesianAbSheaf_over
    (hL : IsHypercovering P L)
    (G : Sheaf (situation (P.toGrothendieck.over X) L).totalTopology Ab.{u}) :
    (Augmentation.totalInverseImageAb (situation (P.toGrothendieck.over X) L)
        (Cat.of (Over X)) (P.toGrothendieck.over X)
        (situationAugmentation (P.toGrothendieck.over X) L)).essImage G ↔
      (situation (P.toGrothendieck.over X) L).IsCartesianAbSheaf G :=
  (Functor.essImage_eq_of_natIso (situationTotalInverseImageAbIso (P.toGrothendieck.over X) L)) ▸
    mem_essImage_abelianInverseImage_iff_isCartesianAbSheaf_over P L hL G

end Over

end CategoryTheory.SimplicialSemiRepresentable

end
