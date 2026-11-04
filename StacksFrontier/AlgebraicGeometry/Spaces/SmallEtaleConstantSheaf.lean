module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalkRing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposRingUniverse
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.InverseImage

/-!
# Constant sheaves of rings and global sections on the small étale site of a space

For an algebraic space `X`, the small étale site `X_et` is a dense subsite of the spaces-étale
site of `X` (Stacks 03G1), which has a terminal object. This file uses that comparison to define
the global sections `Γ(X, -)` of sheaves of commutative rings on `X_et`
(`AlgebraicGeometry.Space.ringGlobalSections`), and proves:

* `AlgebraicGeometry.Space.constantSheafGlobalSectionsAdj`: the constant sheaf functor is left
  adjoint to global sections;
* `AlgebraicGeometry.Space.globalSectionsPushforwardIso`: global sections commute with the direct
  image along a morphism of algebraic spaces, `Γ(Y, f_* F) ≅ Γ(X, F)`;
* `AlgebraicGeometry.Space.constantSheafInverseImageIso`: the inverse image of a constant sheaf
  of rings is the constant sheaf, `f⁻¹ M̲ ≅ M̲`, as the uniqueness of left adjoints of global
  sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Functor.IsDenseSubsite

variable {C D : Type*} [Category* C] [Category* D] (J : GrothendieckTopology C)
  (K : GrothendieckTopology D) (G : C ⥤ D) [G.IsDenseSubsite J K] (A : Type*) [Category* A]
  [(G.sheafPushforwardContinuous A J K).IsEquivalence] [HasWeakSheafify J A]
  [HasWeakSheafify K A]

/-- **The restriction of a constant sheaf to a dense subsite is constant**, naturally in the
value. Restriction along a dense subsite commutes with sheafification
(`CategoryTheory.Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility`), and restricts
the constant presheaf to the constant presheaf. -/
def constantSheafCompSheafPushforwardContinuousIso :
    constantSheaf K A ⋙ G.sheafPushforwardContinuous A J K ≅ constantSheaf J A :=
  Functor.isoWhiskerLeft (Functor.const Dᵒᵖ) (sheafEquivSheafificationCompatibility J K G A).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (NatIso.ofComponents
      (fun M => NatIso.ofComponents (fun _ => Iso.refl M)) (fun _ => by ext; simp))
      (presheafToSheaf J A)

end CategoryTheory.Functor.IsDenseSubsite

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comma categories indexing the right Kan extension along the comparison functor of
Stacks 03G1 have limits of commutative rings in universe `u`: they are essentially small. -/
instance hasLimitsOfShape_structuredArrow_comparisonFunctor_op_commRingCat
    (X : AlgebraicSpaces B S hS) (W : (SpacesEtale B S hS X)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow W (comparisonFunctor B S hS X).op) CommRingCat.{u} :=
  have : EssentiallySmall.{u} (StructuredArrow W (comparisonFunctor B S hS X).op) :=
    inferInstance
  hasLimitsOfShape_of_essentiallySmall _ _

/-- Sheafification of presheaves of commutative rings with sections in the universe of the
schemes, on the small étale site of a presheaf over `S`. Instance search does not settle the
universes of the general instance `AlgebraicGeometry.Space.SmallEtale.instHasSheafify` at this
coefficient category. -/
instance (priority := high) hasSheafify_smallEtale_commRingCat
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    HasSheafify (SmallEtale.topology B S hS F) CommRingCat.{u} :=
  SmallEtale.instHasSheafify B S hS F CommRingCat.{u}

/-- `hasSheafify_smallEtale_commRingCat`, read as the existence of the left adjoint of the
inclusion of sheaves into presheaves, at the same priority. -/
instance (priority := high) hasWeakSheafify_smallEtale_commRingCat
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    HasWeakSheafify (SmallEtale.topology B S hS F) CommRingCat.{u} :=
  (hasSheafify_smallEtale_commRingCat B S hS F).isRightAdjoint

/-- Presheaves of commutative rings with sections in the universe of the schemes admit
sheafification on the spaces-étale site, transported along the dense subsite inclusion of
Stacks 03G1 from the small étale site. -/
instance hasSheafify_spacesEtale_commRingCat (X : AlgebraicSpaces B S hS) :
    HasSheafify (SpacesEtale.topology B S hS X) CommRingCat.{u} :=
  Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)
    (comparisonFunctor B S hS X)

section InverseImage

variable {B S hS}

/-- Restriction of sheaves of commutative rings along the comparison functor of Stacks 03G1, from
the spaces-étale site to the small étale site. -/
abbrev ringRestriction (Z : AlgebraicSpaces B S hS) :
    Sheaf (SpacesEtale.topology B S hS Z) CommRingCat.{u} ⥤
      Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u} :=
  (comparisonFunctor B S hS Z).sheafPushforwardContinuous CommRingCat.{u}
    (SmallEtale.topology B S hS Z.1) (SpacesEtale.topology B S hS Z)

/-- **Stacks 03G1 for sheaves of commutative rings**: restriction along the comparison functor is
an equivalence. -/
abbrev ringRestrictionEquiv (Z : AlgebraicSpaces B S hS) :
    Sheaf (SpacesEtale.topology B S hS Z) CommRingCat.{u} ≌
      Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u} :=
  (ringRestriction Z).asEquivalence

/-- The constant sheaf of commutative rings on the small étale site of `Z` is the restriction of
the constant sheaf on the spaces-étale site, naturally in the value. -/
def constantSheafRestrictionIso (Z : AlgebraicSpaces B S hS) :
    constantSheaf (SpacesEtale.topology B S hS Z) CommRingCat.{u} ⋙ ringRestriction Z ≅
      constantSheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u} :=
  Functor.IsDenseSubsite.constantSheafCompSheafPushforwardContinuousIso
    (SmallEtale.topology B S hS Z.1) (SpacesEtale.topology B S hS Z) (comparisonFunctor B S hS Z)
    CommRingCat.{u}

/-- **Global sections** of a sheaf of commutative rings on the small étale site of an algebraic
space `Z`: the sections over `Z` itself, the final object of the spaces-étale site, of the
corresponding spaces-étale sheaf (Stacks 03G1). -/
abbrev ringGlobalSections (Z : AlgebraicSpaces B S hS) :
    Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u} ⥤ CommRingCat.{u} :=
  (ringRestrictionEquiv Z).inverse ⋙
    (sheafSections (SpacesEtale.topology B S hS Z) CommRingCat.{u}).obj
      (Opposite.op (SpacesEtale.idObj B S hS Z))

/-- **The constant sheaf is left adjoint to global sections** on the small étale site of an
algebraic space: on the spaces-étale site `Z` is a final object, and the comparison
equivalence of Stacks 03G1 carries the constant sheaf to the constant sheaf. -/
def constantSheafGlobalSectionsAdj (Z : AlgebraicSpaces B S hS) :
    constantSheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u} ⊣ ringGlobalSections Z :=
  ((constantSheafAdj (SpacesEtale.topology B S hS Z) CommRingCat.{u}
      (SpacesEtale.isTerminal_idObj B S hS Z)).comp
    (ringRestrictionEquiv Z).toAdjunction).ofNatIsoLeft (constantSheafRestrictionIso Z)

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **Global sections commute with the small étale direct image**: for `f : X ⟶ Y` and a sheaf of
commutative rings `F` on `X_étale`, `Γ(Y, f_*F) = Γ(X, F)`, naturally in `F`. Through the
comparison equivalences of Stacks 03G1 the direct image is spaces-étale base change
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_pushforwardRing`), whose sections over the
final object `Y` are the sections over its base change `X ×_Y Y`, a final object of the
spaces-étale site of `X`. -/
def globalSectionsPushforwardIso :
    (smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing ⋙ ringGlobalSections Y ≅
      ringGlobalSections X :=
  letI := (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous
  let bc := (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous CommRingCat.{u}
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
  let e₁ : (smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing ⋙
      (ringRestrictionEquiv Y).inverse ≅ (ringRestrictionEquiv X).inverse ⋙ bc :=
    Functor.isoWhiskerRight (Functor.leftUnitor _).symm _ ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerRight (ringRestrictionEquiv X).counitIso.symm _)
        _ ≪≫
      Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft _
        (smallEtaleRingedToposHom_pushforwardRing B S hS f)) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (ringRestrictionEquiv Y).unitIso.symm) ≪≫
      Functor.isoWhiskerLeft _ (Functor.rightUnitor _)
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e₁ _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((sheafSections (SpacesEtale.topology B S hS X)
      CommRingCat.{u}).mapIso ((isTerminal_spacesBaseChange_idObj B S hS f).uniqueUpToIso
        (SpacesEtale.isTerminal_idObj B S hS X)).op.symm)

/-- **The inverse image of the constant sheaf**: `f⁻¹M̲ ≅ M̲`, naturally in `M`, as the
uniqueness of left adjoints of global sections, `f⁻¹ ∘ (constant sheaf on Y)` being left
adjoint to `Γ(Y, f_*(-)) = Γ(X, -)` (`globalSectionsPushforwardIso`). -/
def constantSheafInverseImageIso :
    constantSheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u} ≅
      constantSheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u} ⋙
        (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing :=
  (constantSheafGlobalSectionsAdj X).leftAdjointUniq
    (((constantSheafGlobalSectionsAdj Y).comp
      (smallEtaleRingedToposHom B S hS f).toToposHom.ringAdjunction).ofNatIsoRight
      (globalSectionsPushforwardIso f))

/-- **The inverse image of a constant sheaf of rings along a morphism of algebraic spaces is
constant**: for `f : X ⟶ Y` and a commutative ring `M`, the inverse image along the morphism of
small étale topoi of Stacks 03G8 of the constant sheaf `M̲` on `Y_étale` is the constant sheaf
`M̲` on `X_étale`. -/
abbrev inverseImageConstantSheafIso (M : CommRingCat.{u}) :
    (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing.obj
        ((constantSheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}).obj M) ≅
      (constantSheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}).obj M :=
  ((constantSheafInverseImageIso f).app M).symm

end InverseImage

end AlgebraicGeometry.Space
