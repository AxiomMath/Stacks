module

public import Mathlib.CategoryTheory.Action.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedSubschemeSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.BaseChangeEtaleSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.ConstantInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperHenselianFirstCohomology
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperHenselianLimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction to the closed fibre is an equivalence on finite locally constant sheaves

Let `A` be a henselian local ring, `X` a proper scheme over `A` and `X₀` its closed fibre. Stacks
0A48 says that base change `FÉt_X ⥤ FÉt_{X₀}` is an equivalence of categories. This file carries
that statement across the dictionary of Stacks 03RV: the inverse image of **sheaves of sets**
restricted to the finite locally constant sheaves on the small étale site of `X` is an equivalence
onto the finite locally constant sheaves on the small étale site of `X₀`, on both presentations of
the site. It then transports a group action along each of those equivalences.

## Main definitions

* `AlgebraicGeometry.finiteLocallyConstantPullbackEquivalence` and
  `AlgebraicGeometry.etaleSiteFiniteLocallyConstantPullbackEquivalence` — inverse image on finite
  locally constant sheaves of sets as an equivalence of categories, on the site of Stacks 021B
  and on Mathlib's small étale site, given that base change of finite étale covers is one.
* `AlgebraicGeometry.finiteEtaleBaseChangeAction` and
  `AlgebraicGeometry.finiteEtaleBaseChangeActionEquivalence` — base change of finite étale covers
  on objects carrying an action of a fixed monoid, and the induced equivalence.
* `AlgebraicGeometry.properHenselianFiniteEtaleActionEquivalence` — the same for the closed-fibre
  base change of a proper scheme over a henselian local ring, that is **Stacks 0A48 with an
  action carried along**, and
  `AlgebraicGeometry.properHenselianFiniteLocallyConstantActionEquivalence` for its sheaf form.
* `AlgebraicGeometry.closedFibreBigSiteInclusion` — the closed-fibre inclusion as a morphism of a
  big étale site containing the scheme and its closed fibre.
* `Stacks.EtaleCohomology.etaleInverseImageConstantSheafIso` — the inverse image of a constant
  sheaf of sets on Mathlib's small étale site is the constant sheaf on the same set.

## Main results

* `AlgebraicGeometry.isEquivalence_etaleSiteFiniteLocallyConstantSheafPullback_of_isProper` —
  **restriction to the closed fibre is an equivalence on finite locally constant sheaves of
  sets**, for a proper scheme over a henselian local ring.

## Implementation notes

The two presentations of the small étale site are kept apart deliberately. Stacks 03RV and Stacks
0A48 are both available on the size-bounded site of Stacks 021B, so the equivalence is proved
there first, by conjugating base change of finite étale covers through
`AlgebraicGeometry.finiteLocallyConstantFiniteEtaleEquivalenceBaseChangeIso`; it is then moved to
Mathlib's `AlgebraicGeometry.Scheme.smallEtaleTopology` along
`AlgebraicGeometry.finiteLocallyConstantSheafEquivPullbackIso`. A big étale site therefore appears
in those two statements, as everywhere in this part of the library; it is set-theoretic
bookkeeping, upstream of the geometry and absent from the conclusion, and
`AlgebraicGeometry.BigEtaleSite.exists_contains_of_small` produces one containing any small set of
schemes.

The closed-fibre statement is phrased for the morphism
`Stacks.EtaleCohomology.closedFibreInclusion`, which is by definition the first projection of the
pullback of `X ⟶ Spec A` along the closed point, so that Stacks 0A48 applies to it with no
comparison.

## References

* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
* [Stacks Project, Tag 0A48](https://stacks.math.columbia.edu/tag/0A48)
* [Stacks Project, Tag 0A5G](https://stacks.math.columbia.edu/tag/0A5G)
* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf

universe u

namespace AlgebraicGeometry

section Sheaves

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : Y ⟶ X)

/-- **Inverse image on finite locally constant sheaves of sets is an equivalence as soon as base
change of finite étale covers is**, on the site of Stacks 021B. -/
theorem isEquivalence_finiteLocallyConstantSheafPullback
    (h : (finiteEtaleBaseChange f.hom).IsEquivalence) :
    (finiteLocallyConstantSheafPullback B f).IsEquivalence := by
  have := h
  have h₁ : ((finiteLocallyConstantFiniteEtaleEquivalence B X).functor ⋙
      finiteEtaleBaseChange f.hom).IsEquivalence :=
    inferInstanceAs
      ((finiteLocallyConstantFiniteEtaleEquivalence B X).functor ⋙
        finiteEtaleBaseChange f.hom).IsEquivalence
  have h₂ : (finiteLocallyConstantSheafPullback B f ⋙
      (finiteLocallyConstantFiniteEtaleEquivalence B Y).functor).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (finiteLocallyConstantFiniteEtaleEquivalenceBaseChangeIso B f)
  exact Functor.isEquivalence_of_comp_right _
    (finiteLocallyConstantFiniteEtaleEquivalence B Y).functor

/-- Inverse image on the finite locally constant sheaves of sets of the site of Stacks 021B, as
an equivalence of categories. -/
def finiteLocallyConstantPullbackEquivalence
    (h : (finiteEtaleBaseChange f.hom).IsEquivalence) :
    FiniteLocallyConstantSheaf B X ≌ FiniteLocallyConstantSheaf B Y :=
  have := isEquivalence_finiteLocallyConstantSheafPullback B f h
  (finiteLocallyConstantSheafPullback B f).asEquivalence

/-- **Inverse image on finite locally constant sheaves of sets is an equivalence as soon as base
change of finite étale covers is**, on Mathlib's small étale site. -/
theorem isEquivalence_etaleSiteFiniteLocallyConstantSheafPullback
    (h : (finiteEtaleBaseChange f.hom).IsEquivalence) :
    (etaleSiteFiniteLocallyConstantSheafPullback B f).IsEquivalence := by
  have := isEquivalence_finiteLocallyConstantSheafPullback B f h
  have h₁ : (finiteLocallyConstantSheafPullback B f ⋙
      (SmallEtale.finiteLocallyConstantSheafEquiv B Y).functor).IsEquivalence :=
    inferInstanceAs (finiteLocallyConstantSheafPullback B f ⋙
      (SmallEtale.finiteLocallyConstantSheafEquiv B Y).functor).IsEquivalence
  have h₂ : ((SmallEtale.finiteLocallyConstantSheafEquiv B X).functor ⋙
      etaleSiteFiniteLocallyConstantSheafPullback B f).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (finiteLocallyConstantSheafEquivPullbackIso B f).symm
  exact Functor.isEquivalence_of_comp_left
    (SmallEtale.finiteLocallyConstantSheafEquiv B X).functor _

/-- Inverse image on the finite locally constant sheaves of sets of Mathlib's small étale site,
as an equivalence of categories. -/
def etaleSiteFiniteLocallyConstantPullbackEquivalence
    (h : (finiteEtaleBaseChange f.hom).IsEquivalence) :
    ObjectProperty.FullSubcategory
        (fun F : Sheaf X.obj.smallEtaleTopology (Type (u + 1)) ↦
          IsFiniteLocallyConstant X.obj.smallEtaleTopology F) ≌
      ObjectProperty.FullSubcategory
        (fun F : Sheaf Y.obj.smallEtaleTopology (Type (u + 1)) ↦
          IsFiniteLocallyConstant Y.obj.smallEtaleTopology F) :=
  have := isEquivalence_etaleSiteFiniteLocallyConstantSheafPullback B f h
  (etaleSiteFiniteLocallyConstantSheafPullback B f).asEquivalence

end Sheaves

section ClosedFibre

/-- **Stacks 0A48 at the closed-fibre inclusion.** For `A` henselian local and `X` proper over
`A`, base change of finite étale covers along the inclusion of the closed fibre of `X ⟶ Spec A`
is an equivalence of categories. -/
theorem isEquivalence_finiteEtaleBaseChange_closedFibreInclusion
    (A : Type u) [CommRing A] [HenselianLocalRing A] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of A)) [IsProper g] :
    (finiteEtaleBaseChange
      (Stacks.EtaleCohomology.closedFibreInclusion A g)).IsEquivalence :=
  isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianLocalRing A g

/-- The closed-fibre inclusion, read as a morphism of a big étale site containing both the
scheme and its closed fibre. -/
def closedFibreBigSiteInclusion (B : BigEtaleSite.{u}) (A : Type u) [CommRing A] [IsLocalRing A]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of A)) (hX : B.Contains X)
    (hY : B.Contains (Stacks.EtaleCohomology.closedFibre A g)) :
    B.obj (Stacks.EtaleCohomology.closedFibre A g) hY ⟶ B.obj X hX :=
  ObjectProperty.homMk (Stacks.EtaleCohomology.closedFibreInclusion A g)

/-- **Restriction to the closed fibre is an equivalence on finite locally constant sheaves of
sets**, on Mathlib's small étale site, for a proper scheme over a henselian local ring. -/
theorem isEquivalence_etaleSiteFiniteLocallyConstantSheafPullback_of_isProper
    (B : BigEtaleSite.{u}) (A : Type u) [CommRing A] [HenselianLocalRing A] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of A)) [IsProper g] (hX : B.Contains X)
    (hY : B.Contains (Stacks.EtaleCohomology.closedFibre A g)) :
    (etaleSiteFiniteLocallyConstantSheafPullback B
      (closedFibreBigSiteInclusion B A g hX hY)).IsEquivalence :=
  isEquivalence_etaleSiteFiniteLocallyConstantSheafPullback B _
    (isEquivalence_finiteEtaleBaseChange_closedFibreInclusion A g)

end ClosedFibre

section Actions

variable (G : Type*) [Monoid G]

/-- **Base change of finite étale covers, with an action of `G` carried along.** An action of a
monoid on an object of a category is a functor out of the one-object category on that monoid, so
base change acts on objects with an action by postcomposition. -/
abbrev finiteEtaleBaseChangeAction {X Y : Scheme.{u}} (i : Y ⟶ X) :
    Action (FiniteEtaleOver X) G ⥤ Action (FiniteEtaleOver Y) G :=
  (finiteEtaleBaseChange i).mapAction G

/-- **An equivalence of categories of finite étale covers carries actions of `G` along.** -/
def finiteEtaleBaseChangeActionEquivalence {X Y : Scheme.{u}} (i : Y ⟶ X)
    (h : (finiteEtaleBaseChange i).IsEquivalence) :
    Action (FiniteEtaleOver X) G ≌ Action (FiniteEtaleOver Y) G :=
  have := h
  Equivalence.mapAction G (finiteEtaleBaseChange i).asEquivalence

/-- **Stacks 0A48 with an action carried along.** For `A` henselian local and `X` proper over
`A`, base change to the closed fibre is an equivalence between the finite étale covers of `X`
carrying an action of a monoid `G` and those of the closed fibre carrying one. -/
@[ega "IV 18.3.4" "special case",
  sga "4 XII 5.9bis" "more general",
  sga "7 XIII 1.2.1" "more general"]
def properHenselianFiniteEtaleActionEquivalence
    (A : Type u) [CommRing A] [HenselianLocalRing A] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of A)) [IsProper g] :
    Action (FiniteEtaleOver X) G ≌
      Action (FiniteEtaleOver (Stacks.EtaleCohomology.closedFibre A g)) G :=
  finiteEtaleBaseChangeActionEquivalence G _
    (isEquivalence_finiteEtaleBaseChange_closedFibreInclusion A g)

/-- **Restriction to the closed fibre is an equivalence on finite locally constant sheaves of
sets carrying an action of `G`**, on Mathlib's small étale site. -/
def properHenselianFiniteLocallyConstantActionEquivalence
    (B : BigEtaleSite.{u}) (A : Type u) [CommRing A] [HenselianLocalRing A] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of A)) [IsProper g] (hX : B.Contains X)
    (hY : B.Contains (Stacks.EtaleCohomology.closedFibre A g)) :
    Action
        (ObjectProperty.FullSubcategory
          (fun F : Sheaf X.smallEtaleTopology (Type (u + 1)) ↦
            IsFiniteLocallyConstant X.smallEtaleTopology F)) G ≌
      Action
        (ObjectProperty.FullSubcategory
          (fun F : Sheaf (Stacks.EtaleCohomology.closedFibre A g).smallEtaleTopology
              (Type (u + 1)) ↦
            IsFiniteLocallyConstant
              (Stacks.EtaleCohomology.closedFibre A g).smallEtaleTopology F)) G :=
  have := isEquivalence_etaleSiteFiniteLocallyConstantSheafPullback_of_isProper B A g hX hY
  Equivalence.mapAction G
    (etaleSiteFiniteLocallyConstantSheafPullback B
      (closedFibreBigSiteInclusion B A g hX hY)).asEquivalence

end Actions

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

/-- **The inverse image of a constant sheaf of sets is the constant sheaf**, on Mathlib's small
étale site. -/
def etaleInverseImageConstantSheafIso {X Y : Scheme.{u}} (i : Y ⟶ X) :
    constantSheaf X.smallEtaleTopology (Type (u + 1)) ⋙
        smallEtaleInverseImage.{u, 0} i ≅
      constantSheaf Y.smallEtaleTopology (Type (u + 1)) := by
  have hlan : PreservesFiniteLimits ((smallEtaleBaseChange i).op.lan :
      (X.Etaleᵒᵖ ⥤ Type (u + 1)) ⥤ _) := by
    refine Stacks.Topology.lan_preservesFiniteLimits_of_flat _ fun V => ?_
    have : IsFiltered (CostructuredArrow (smallEtaleBaseChange i).op V) :=
      IsFiltered.of_equivalence
        (structuredArrowOpEquivalence (smallEtaleBaseChange i) (Opposite.unop V))
    infer_instance
  have hlex : PreservesFiniteLimits (smallEtaleInverseImage.{u, 0} i) :=
    inferInstanceAs (PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange i)
        (Type (u + 1)) X.smallEtaleTopology Y.smallEtaleTopology))
  have hY : IsIso (Scheme.Etale.mk (𝟙 Y)).hom := inferInstanceAs (IsIso (𝟙 Y))
  have hX : IsIso (Scheme.Etale.mk (𝟙 X)).hom := inferInstanceAs (IsIso (𝟙 X))
  exact Stacks.ConstantSheaf.inverseImageConstantSheafIso
    (L := smallEtaleInverseImage.{u, 0} i)
    (R := (smallEtaleBaseChange i).sheafPushforwardContinuous (Type (u + 1))
      X.smallEtaleTopology Y.smallEtaleTopology)
    (smallEtaleInverseImageAdjunction.{u, 0} i)
    (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 Y)))
    (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 X)))

end Stacks.EtaleCohomology

end
