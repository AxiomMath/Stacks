module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.HenselianPairEtaleSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedSubschemeSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange

/-!
# Étale global sections of a represented henselian pair

Let `(A, I)` be a henselian pair and let `B` be a big fppf site containing `Spec A`. The scheme
`Spec A` and its closed subscheme `Spec (A ⧸ I)` are objects of the big fppf site of `Spec A`, so
they represent algebraic spaces over `Spec A`, and the closed immersion represents a morphism
`q` between them. Restriction of global sections along `q` is bijective on the small étale site
of the algebraic space `Spec A`, for every sheaf of sets.

## Main definitions

* `Stacks.Sites.globalSectionsIsoOfAdjunctionOfPreservesTerminal`: for an adjunction `L ⊣ R`
  between sheaf topoi whose left adjoint preserves the final object, `R ⋙ Γ ≅ Γ`.
* `AlgebraicGeometry.Space.representedSchemeRestriction`: restriction of sheaves of sets from
  Mathlib's small étale site of the scheme underlying `T` to the small étale site of the
  algebraic space `h_T`.
* `AlgebraicGeometry.Space.representedSchemeRestrictionPushforwardIso`: it intertwines the two
  direct images along a morphism of the big fppf site.
* `AlgebraicGeometry.Space.representedSchemeRestrictionInverseImageIso`: it intertwines the two
  inverse images.
* `AlgebraicGeometry.Space.globalSectionsRepresentedIsoOfIsIso`: global sections on `h_T` are
  global sections of the inverse image on `h_Q`, when this holds for the underlying schemes.
* `AlgebraicGeometry.Space.globalSectionsRepresentedQuotientIso`: for a henselian pair `(A, I)`,
  global sections on the small étale site of `Spec A` are global sections of the inverse image on
  `Spec (A ⧸ I)`.

## References

* [Stacks Project, Tag 09ZH](https://stacks.math.columbia.edu/tag/09ZH)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.Sites

section GlobalSections

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J (Type (max u v))] [HasWeakSheafify K (Type (max u v))]

/-- The constant sheaf of sets on a singleton is a final sheaf. -/
def isTerminalConstantSheafPUnit :
    IsTerminal ((constantSheaf J (Type (max u v))).obj PUnit) :=
  (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).ofIso
    ((fullyFaithfulSheafToPresheaf J (Type (max u v))).preimageIso
      (isoSheafify J (Presheaf.isSheaf_of_isTerminal J Types.isTerminalPUnit)))

variable {J K}

/-- For an adjunction `L ⊣ R` between the categories of sheaves of sets on two sites whose left
adjoint preserves the final object, the global sections of `R G` are the global sections of `G`,
naturally in `G`. -/
def globalSectionsIsoOfAdjunctionOfPreservesTerminal
    {L : Sheaf J (Type (max u v)) ⥤ Sheaf K (Type (max u v))}
    {R : Sheaf K (Type (max u v)) ⥤ Sheaf J (Type (max u v))}
    (adj : L ⊣ R) [PreservesLimit (Functor.empty.{0} _) L] :
    R ⋙ Sheaf.Γ J (Type (max u v)) ≅ Sheaf.Γ K (Type (max u v)) :=
  Functor.isoWhiskerLeft R (Sheaf.ΓNatIsoCoyoneda J PUnit) ≪≫
    (adj.compCoyonedaIso.app (op _)).symm ≪≫
    coyoneda.mapIso
      ((isTerminalConstantSheafPUnit K).uniqueUpToIso
        ((isTerminalConstantSheafPUnit J).isTerminalObj L)).op ≪≫
    (Sheaf.ΓNatIsoCoyoneda K PUnit).symm

end GlobalSections

end Stacks.Sites

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Restriction

variable (T : BigFppfOver B S hS)

/-- Restriction along the identification of the small étale site of `h_T` with the bounded small
étale site of the scheme underlying `T` is an equivalence of the categories of sheaves of sets. -/
instance isEquivalence_representedSmallEtaleRestriction :
    ((representedSmallEtaleEquivalence B S hS T).functor.sheafPushforwardContinuous
      (Type (u + 1)) (SmallEtale.topology B S hS (yoneda.obj T))
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)).IsEquivalence :=
  inferInstanceAs (Equivalence.sheafCongr (SmallEtale.topology B S hS (yoneda.obj T))
    (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
    (representedSmallEtaleEquivalence B S hS T) (Type (u + 1))).inverse.IsEquivalence

/-- Restriction of sheaves of sets from Mathlib's small étale site of the scheme underlying `T` to
the bounded small étale site, followed by restriction along the identification of the latter with
the small étale site of the algebraic space `h_T`. -/
abbrev representedSchemeRestriction :
    Sheaf (Scheme.smallEtaleTopology T.left.obj) (Type (u + 1)) ⥤
      Sheaf (SmallEtale.topology B S hS (yoneda.obj T)) (Type (u + 1)) :=
  (_root_.AlgebraicGeometry.SmallEtale.toEtaleSite (associatedBigEtaleSite B) T.left.obj
      T.left.property).sheafPushforwardContinuous (Type (u + 1))
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B) T.left.obj
        T.left.property) (Scheme.smallEtaleTopology T.left.obj) ⋙
    (representedSmallEtaleEquivalence B S hS T).functor.sheafPushforwardContinuous
      (Type (u + 1)) (SmallEtale.topology B S hS (yoneda.obj T))
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `IsEquivalence` of the sheaf pushforward between small étale sites
/-- Restriction of sheaves of sets from the small étale site of the scheme underlying `T` to the
small étale site of the algebraic space `h_T` is an equivalence of categories. -/
instance isEquivalence_representedSchemeRestriction :
    (representedSchemeRestriction B S hS T).IsEquivalence := by
  have : ((_root_.AlgebraicGeometry.SmallEtale.toEtaleSite (associatedBigEtaleSite B) T.left.obj
      T.left.property).sheafPushforwardContinuous (Type (u + 1))
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B) T.left.obj
        T.left.property) (Scheme.smallEtaleTopology T.left.obj)).IsEquivalence :=
    inferInstanceAs (_root_.AlgebraicGeometry.SmallEtale.sheafEquiv (associatedBigEtaleSite B)
      T.left.obj T.left.property (Type (u + 1))).inverse.IsEquivalence
  infer_instance

end Restriction

section BaseChange

variable {Q T : BigFppfOver B S hS} (g : Q ⟶ T)

/-- For a morphism `g : Q ⟶ T` of the big fppf site of `S`, restriction from Mathlib's small étale
sites to the small étale sites of the represented algebraic spaces carries direct image along the
underlying morphism of schemes to direct image along the represented morphism of algebraic
spaces. -/
def representedSchemeRestrictionPushforwardIso :
    representedSchemeRestriction B S hS Q ⋙
        (smallToposMorphism B S hS (representedSpaceMap B S hS g)).pushforward ≅
      (Stacks.EtaleCohomology.smallEtaleBaseChange
          ((associatedBigEtaleSite B).inclusion.map g.left)).sheafPushforwardContinuous
          (Type (u + 1)) (Scheme.smallEtaleTopology T.left.obj)
          (Scheme.smallEtaleTopology Q.left.obj) ⋙
        representedSchemeRestriction B S hS T := by
  have hg := relativelyRepresentable_yoneda_map B S hS g
  set A := Type (u + 1)
  set E := associatedBigEtaleSite B
  set φ := representedSpaceMap B S hS g
  set e' := representedSmallEtaleEquivalence B S hS Q
  set e'' := representedSmallEtaleEquivalence B S hS T
  set L := smallBaseChange B S hS φ hg
  set R := _root_.AlgebraicGeometry.smallEtaleBaseChange E g.left
  set J := SmallEtale.topology B S hS (yoneda.obj T)
  set J' := SmallEtale.topology B S hS (yoneda.obj Q)
  set K := _root_.AlgebraicGeometry.SmallEtale.topology E
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property
  set K' := _root_.AlgebraicGeometry.SmallEtale.topology E
    ((BigFppfOver.toScheme B S hS).obj Q) Q.left.property
  haveI : L.IsContinuous J J' := isContinuous_smallBaseChange B S hS φ hg
  haveI : R.IsContinuous K K' :=
    _root_.AlgebraicGeometry.smallEtaleBaseChange_isContinuous E g.left
  haveI : (L ⋙ e'.functor).IsContinuous J K' := Functor.isContinuous_comp _ _ J J' K'
  haveI : (e''.functor ⋙ R).IsContinuous J K' := Functor.isContinuous_comp _ _ J K K'
  have hiso :
      e'.functor.sheafPushforwardContinuous A J' K' ⋙ L.sheafPushforwardContinuous A J J' ≅
        R.sheafPushforwardContinuous A K K' ⋙ e''.functor.sheafPushforwardContinuous A J K :=
    Functor.sheafPushforwardContinuousComp' (F := L) (G := e'.functor) (Iso.refl _) A J J' K' ≪≫
      Functor.sheafPushforwardContinuousIso
        (representedSmallEtaleBaseChangeIso B S hS g hg) A J K' ≪≫
      (Functor.sheafPushforwardContinuousComp' (F := e''.functor) (G := R)
        (Iso.refl _) A J K K').symm
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (smallBaseChange_topos B S hS φ hg)) ≪≫
    Functor.isoWhiskerLeft _ hiso ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (_root_.AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso E g.left A).symm _ ≪≫
    Functor.associator _ _ _

/-- The quasi-inverses of the restrictions from Mathlib's small étale sites carry inverse image
along the represented morphism of algebraic spaces to inverse image along the underlying morphism
of schemes. -/
def representedSchemeRestrictionInverseImageIso :
    (smallToposMorphism B S hS (representedSpaceMap B S hS g)).inverseImage ⋙
        (representedSchemeRestriction B S hS Q).asEquivalence.inverse ≅
      (representedSchemeRestriction B S hS T).asEquivalence.inverse ⋙
        Stacks.EtaleCohomology.smallEtaleInverseImage.{u, 0}
          ((associatedBigEtaleSite B).inclusion.map g.left) :=
  Adjunction.leftAdjointUniq
    (((smallToposMorphism B S hS (representedSpaceMap B S hS g)).adj.comp
      (representedSchemeRestriction B S hS Q).asEquivalence.symm.toAdjunction).ofNatIsoRight
        (representedSchemeRestrictionPushforwardIso B S hS g))
    ((representedSchemeRestriction B S hS T).asEquivalence.symm.toAdjunction.comp
      (Stacks.EtaleCohomology.smallEtaleInverseImageAdjunction.{u, 0}
        ((associatedBigEtaleSite B).inclusion.map g.left)))

set_option synthInstance.maxHeartbeats 400000 in
-- instance search through the composite of sheaf adjunctions on small étale sites
/-- If restriction of global sections along the morphism of schemes underlying `g : Q ⟶ T` is
bijective for every sheaf of sets on Mathlib's small étale site, then global sections of every
sheaf of sets on the small étale site of the algebraic space `h_T` are, naturally, those of its
inverse image on `h_Q`. -/
def globalSectionsRepresentedIsoOfIsIso
    (h : IsIso (Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageComparison.{u, 0}
      ((associatedBigEtaleSite B).inclusion.map g.left)).val) :
    Sheaf.Γ (SmallEtale.topology B S hS (yoneda.obj T)) (Type (u + 1)) ≅
      (smallToposMorphism B S hS (representedSpaceMap B S hS g)).inverseImage ⋙
        Sheaf.Γ (SmallEtale.topology B S hS (yoneda.obj Q)) (Type (u + 1)) :=
  (Stacks.Sites.globalSectionsIsoOfAdjunctionOfPreservesTerminal.{u, u + 1}
      (representedSchemeRestriction B S hS T).asEquivalence.toAdjunction).symm ≪≫
    Functor.isoWhiskerLeft _ (asIso
      (Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageComparison.{u, 0}
        ((associatedBigEtaleSite B).inclusion.map g.left)).val) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (representedSchemeRestrictionInverseImageIso B S hS g).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Stacks.Sites.globalSectionsIsoOfAdjunctionOfPreservesTerminal.{u, u + 1}
        (representedSchemeRestriction B S hS Q).asEquivalence.toAdjunction)

end BaseChange

section HenselianPair

variable {B} (A : Type u) [CommRing A] (I : Ideal A) (hA : B.Contains (Spec (.of A)))

/-- The closed subscheme `Spec (A ⧸ I)` of `Spec A`, as an object of the big fppf site of
`Spec A`. -/
abbrev quotientSpecOver : BigFppfOver B (Spec (.of A)) hA :=
  haveI : _root_.AlgebraicGeometry.IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  Over.mk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    B.obj (Scheme.size_lt_of_isClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) hA) ⟶ B.obj hA)

/-- The closed immersion `Spec (A ⧸ I) ⟶ Spec A`, as a morphism of the big fppf site of
`Spec A` to its final object. -/
abbrev quotientSpecOverHom : quotientSpecOver A I hA ⟶ Over.mk (𝟙 (B.obj hA)) :=
  Over.homMk (quotientSpecOver A I hA).hom (by simp)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the inverse-image and global-sections functors on small étale sites
/-- Let `(A, I)` be a henselian pair. For every sheaf of sets `ℱ` on the small étale site of the
algebraic space represented by `Spec A`, the global sections of `ℱ` are, naturally in `ℱ`, the
global sections of its inverse image on the algebraic space represented by `Spec (A ⧸ I)`. -/
def globalSectionsRepresentedQuotientIso (hI : HenselianPair A I) :
    Sheaf.Γ (SmallEtale.topology B (Spec (.of A)) hA (yoneda.obj (Over.mk (𝟙 (B.obj hA)))))
        (Type (u + 1)) ≅
      (smallToposMorphism B (Spec (.of A)) hA
          (representedSpaceMap B (Spec (.of A)) hA (quotientSpecOverHom A I hA))).inverseImage ⋙
        Sheaf.Γ (SmallEtale.topology B (Spec (.of A)) hA (yoneda.obj (quotientSpecOver A I hA)))
          (Type (u + 1)) :=
  globalSectionsRepresentedIsoOfIsIso B (Spec (.of A)) hA (quotientSpecOverHom A I hA)
    (Stacks.EtaleCohomology.isIso_globalSectionsComparison_quotient_of_henselianPair.{u, 0}
      A I hI)

end HenselianPair

end AlgebraicGeometry.Space

end
