module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackFpqcAmalgamation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite

/-!
# Étale cohomology with support in a closed subscheme

Let `i : Z ⟶ X` be a closed immersion of schemes and let `j : U ⟶ X` be the inclusion of the
open complement.  For an abelian sheaf `F` on `X_étale`, the sections of `F` with support in
`Z` form the kernel of the restriction map `F ⟶ j_*(F|_U)`.  This kernel is supported on `Z`,
so inverse image along `i` carries it to an abelian sheaf `ℋ_Z(F)` on `Z_étale`; the resulting
left exact functor has right derived functors `ℋ^p_Z`, the cohomology sheaves with support
in `Z`.

## Main definitions

* `AlgebraicGeometry.closedComplementOpen` and
  `AlgebraicGeometry.closedComplementInclusion` — the open complement of a closed immersion
  and its inclusion.
* `AlgebraicGeometry.supportedSectionsSubsheaf` — the subsheaf of sections with support in the
  closed subscheme, as an abelian sheaf on the ambient small étale site.
* `AlgebraicGeometry.supportedSections` — the same sheaf viewed on the closed subscheme, the
  functor `ℋ_Z`.
* `AlgebraicGeometry.SmallEtaleAbelianSheaf` — abelian sheaves on a small étale site.

## Main results

* `AlgebraicGeometry.smallEtalePullback_preservesFiniteLimits_ab` — inverse image of abelian
  sheaves along a morphism of small étale sites is left exact.
* `AlgebraicGeometry.smallEtalePushforward_injective_ab` — direct image of abelian sheaves
  preserves injective objects.
* `AlgebraicGeometry.isZero_rightDerivedPlus_supportedSections_pushforward` — the cohomology
  sheaves with support in `Z` of the direct image of an injective abelian sheaf on `Z` vanish
  in positive degrees.

## Implementation notes

Viewing the supported-sections sheaf on the closed subscheme uses that inverse image along a
closed immersion inverts direct image on sheaves supported on the closed subscheme; `ℋ_Z` is
therefore the composite of the kernel functor with inverse image along `i`.

Left exactness of inverse image is obtained from the pointwise description of the presheaf
pullback as a filtered colimit: base change of small étale sites is representably flat, so the
costructured-arrow categories computing the left Kan extension are filtered, and the forgetful
functor of abelian groups preserves filtered colimits of that size.

## References

* [Stacks Project, Tag 09XR](https://stacks.math.columbia.edu/tag/09XR)
* [Stacks Project, Tag 0A45](https://stacks.math.columbia.edu/tag/0A45)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

/-- The kernel of a natural transformation out of an additive functor is additive: its
inclusion into the source is a pointwise monomorphism natural in the argument, and additivity
of a map is detected after composing with a monomorphism. -/
private theorem kernel_natTrans_additive {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Abelian D] {F G : C ⥤ D} [F.Additive] (η : F ⟶ G) :
    (kernel η).Additive where
  map_add {A A'} g g' := by
    have hmono : Mono ((kernel.ι η).app A') :=
      inferInstanceAs (Mono (((evaluation C D).obj A').map (kernel.ι η)))
    refine (cancel_mono ((kernel.ι η).app A')).1 ?_
    simp only [Preadditive.add_comp, (kernel.ι η).naturality, F.map_add,
      Preadditive.comp_add]

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- Abelian sheaves on the small étale site of an object of a big étale site. -/
public abbrev SmallEtaleAbelianSheaf (Y : B.Scheme) :=
  Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}

/-- Abelian sheaves on a small étale site form a Grothendieck abelian category: the site is
essentially small in the universe of the schemes, and abelian groups are Grothendieck
abelian. -/
public instance smallEtaleAbelianSheaf_isGrothendieckAbelian (Y : B.Scheme) :
    IsGrothendieckAbelian.{u + 1} (SmallEtaleAbelianSheaf B Y) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

/-- Injective resolutions of abelian sheaves on a small étale site exist. -/
public instance smallEtaleAbelianSheaf_enoughInjectives (Y : B.Scheme) :
    EnoughInjectives (SmallEtaleAbelianSheaf B Y) :=
  IsGrothendieckAbelian.enoughInjectives

section Exactness

variable {Y W : B.Scheme} (f : Y ⟶ W)

/-- Inverse image of abelian sheaves along a morphism of small étale sites is left exact.

The presheaf pullback is the left Kan extension along base change, which is computed pointwise
by a colimit over a costructured-arrow category; representable flatness of base change makes
that category filtered, the forgetful functor of abelian groups preserves filtered colimits,
and sheafification is left exact. -/
public instance smallEtalePullback_preservesFiniteLimits_ab :
    PreservesFiniteLimits
      ((smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{u + 1}
        (SmallEtale.topology B W.obj W.property)
        (SmallEtale.topology B Y.obj Y.property)) := by
  have hfor : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} _
  have hlan := Stacks.Topology.lan_preservesFiniteLimits_of_flat
    (E := AddCommGrpCat.{u + 1}) (F := smallEtaleBaseChange B f) (hPres := fun V => by
      have hfilt : IsFiltered (CostructuredArrow (smallEtaleBaseChange B f).op V) :=
        IsFiltered.of_equivalence
          (structuredArrowOpEquivalence (smallEtaleBaseChange B f) V.unop)
      exact hfor.preserves_filtered_colimits
        (CostructuredArrow (smallEtaleBaseChange B f).op V))
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

/-- Inverse image of abelian sheaves along a morphism of small étale sites preserves
monomorphisms, being left exact. -/
public instance smallEtalePullback_preservesMonomorphisms_ab :
    ((smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{u + 1}
        (SmallEtale.topology B W.obj W.property)
        (SmallEtale.topology B Y.obj Y.property)).PreservesMonomorphisms := by
  constructor
  intro A A' g _
  exact preserves_mono_of_preservesLimit _ g

/-- Direct image of abelian sheaves along a morphism of small étale sites carries injective
sheaves to injective sheaves: it is right adjoint to the left exact inverse image. -/
public theorem smallEtalePushforward_injective_ab
    (I : SmallEtaleAbelianSheaf B Y) [Injective I] :
    Injective
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B W.obj W.property)
        (SmallEtale.topology B Y.obj Y.property)).obj I) :=
  ((smallEtaleBaseChange B f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B W.obj W.property)
    (SmallEtale.topology B Y.obj Y.property)).map_injective I inferInstance

/-- Direct image of abelian sheaves along a morphism of small étale sites is additive. -/
public instance smallEtalePushforward_additive_ab :
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B W.obj W.property)
      (SmallEtale.topology B Y.obj Y.property)).Additive where
  map_add := by intros; rfl

/-- Inverse image of abelian sheaves along a morphism of small étale sites is additive. -/
public instance smallEtalePullback_additive_ab :
    ((smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B W.obj W.property)
      (SmallEtale.topology B Y.obj Y.property)).Additive :=
  ((smallEtaleBaseChange B f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B W.obj W.property)
    (SmallEtale.topology B Y.obj Y.property)).left_adjoint_additive

end Exactness

section ClosedComplement

variable {Z X : B.Scheme} (i : Z ⟶ X) [IsClosedImmersion (B.inclusion.map i)]

/-- The complement of the image of a closed immersion, as a Zariski open of the target. -/
public def closedComplementOpen : (B.inclusion.obj X).Opens :=
  ⟨(Set.range (B.inclusion.map i).base)ᶜ,
    (B.inclusion.map i).isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The open complement of a closed immersion, as an object of the big étale site. -/
public def closedComplement : B.Scheme :=
  BigEtaleSite.openObj B (closedComplementOpen B i)

/-- The inclusion of the open complement of a closed immersion. -/
public def closedComplementInclusion : closedComplement B i ⟶ X :=
  BigEtaleSite.openObjι B (closedComplementOpen B i)

/-- The restriction map from an abelian sheaf on `X_étale` to the direct image of its
restriction to the open complement of `Z`. -/
public def complementRestriction :
    𝟭 (SmallEtaleAbelianSheaf B X) ⟶
      (smallEtaleBaseChange B (closedComplementInclusion B i)).sheafPullback
          AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (closedComplement B i).obj (closedComplement B i).property) ⋙
        (smallEtaleBaseChange B (closedComplementInclusion B i)).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (closedComplement B i).obj (closedComplement B i).property) :=
  ((smallEtaleBaseChange B (closedComplementInclusion B i)).sheafAdjunctionContinuous
    AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B (closedComplement B i).obj
      (closedComplement B i).property)).unit

/-- Sections with support in the closed subscheme, as an abelian sheaf on the ambient small
étale site: the kernel of restriction to the open complement. -/
public def supportedSectionsSubsheaf :
    SmallEtaleAbelianSheaf B X ⥤ SmallEtaleAbelianSheaf B X :=
  kernel (complementRestriction B i)

/-- Sections with support in the closed subscheme, viewed as an abelian sheaf on that
subscheme: the functor `ℋ_Z`. -/
public def supportedSections :
    SmallEtaleAbelianSheaf B X ⥤ SmallEtaleAbelianSheaf B Z :=
  supportedSectionsSubsheaf B i ⋙
    (smallEtaleBaseChange B i).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B Z.obj Z.property)

/-- The subsheaf of sections with support in the closed subscheme is additive. -/
public instance supportedSectionsSubsheaf_additive :
    (supportedSectionsSubsheaf B i).Additive :=
  kernel_natTrans_additive (complementRestriction B i)

/-- The functor of sections with support in the closed subscheme is additive. -/
public instance supportedSections_additive : (supportedSections B i).Additive := by
  dsimp only [supportedSections]
  infer_instance

/-- **Stacks 09XR.** The cohomology sheaves with support in a closed subscheme of the direct
image of an injective abelian sheaf on that subscheme vanish in positive degrees. -/
@[stacks 09XR]
public theorem isZero_rightDerivedPlus_supportedSections_pushforward
    (G : SmallEtaleAbelianSheaf B Z) [Injective G] (p : ℤ) (hp : 0 < p) :
    IsZero (((supportedSections B i).rightDerivedPlus p).obj
      (((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Z.obj Z.property)).obj G)) :=
  have := smallEtalePushforward_injective_ab B i G
  Functor.isZero_rightDerivedPlus_obj_injective _ p hp.ne' _

end ClosedComplement

end AlgebraicGeometry

end
