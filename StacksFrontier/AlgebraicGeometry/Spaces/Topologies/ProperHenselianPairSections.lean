module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GlobalSectionsComparisonTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.HenselianPairRepresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeSmallEtale

/-!
# Étale global sections of a proper algebraic space over a henselian pair

Let `(A, I)` be a henselian pair, let `X` be an algebraic space over `A` whose structure morphism
`f : X ⟶ Spec A` is proper, and let `i : X₀ ⟶ X` be the inclusion of the closed fibre
`X₀ = X ×_{Spec A} Spec (A ⧸ I)`. For every sheaf of sets `ℱ` on `X_étale`, restriction of
sections `Γ(X, ℱ) ⟶ Γ(X₀, i⁻¹ℱ)` is bijective. This is [Stacks, Tag 0DFY].

The proof is the second one of the source. Proper base change for algebraic spaces,
[Stacks, Tag 0DG0] (`AlgebraicGeometry.Space.isIso_properBaseChangeMap_of_isProper`), applied to
`f` and the closed immersion `q : Spec (A ⧸ I) ⟶ Spec A`, identifies `q⁻¹ f_* ℱ` with
`f₀,* i⁻¹ ℱ`; the case of the identity of `Spec A`, which is [Stacks, Tag 09ZH], identifies
`Γ(Spec A, f_* ℱ)` with `Γ(Spec (A ⧸ I), q⁻¹ f_* ℱ)`
(`AlgebraicGeometry.Space.globalSectionsRepresentedQuotientIso`); and global sections of a direct
image are global sections on the source. These canonical identifications give an isomorphism of
functors `Γ(X, -) ≅ Γ(X₀, i⁻¹ -)`, and every natural transformation between these two functors is
the restriction map, because global sections are corepresented by the final sheaf.

## Main definitions

* `AlgebraicGeometry.Space.globalSectionsRestriction`: restriction of global sections along a
  morphism of algebraic spaces, `Γ(Y, ℱ) ⟶ Γ(Y, i_* i⁻¹ ℱ) = Γ(X, i⁻¹ ℱ)`.
* `AlgebraicGeometry.Space.closedFibre` and `AlgebraicGeometry.Space.closedFibreInclusion`: the
  closed fibre `X ×_{Spec A} Spec (A ⧸ I)` and its inclusion into `X`.
* `AlgebraicGeometry.Space.globalSectionsClosedFibreIso`: the isomorphism of global-sections
  functors.

## Main results

* `AlgebraicGeometry.Space.isIso_globalSectionsRestriction_closedFibre_of_henselianPair`:
  **[Stacks, Tag 0DFY]**.

## References

* [Stacks Project, Tag 0DFY](https://stacks.math.columbia.edu/tag/0DFY)
* [Stacks Project, Tag 0DG0](https://stacks.math.columbia.edu/tag/0DG0)
* [Stacks Project, Tag 09ZH](https://stacks.math.columbia.edu/tag/09ZH)
* [Stacks Project, Tag 0A0C](https://stacks.math.columbia.edu/tag/0A0C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section Restriction

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of sheaves of sets on the small étale sites exceeds the
-- default budget
/-- **Restriction of global sections along a morphism of algebraic spaces.** For `i : X ⟶ Y`
and a sheaf of sets `ℱ` on `Y_étale`, the map `Γ(Y, ℱ) ⟶ Γ(Y, i_* i⁻¹ ℱ) = Γ(X, i⁻¹ ℱ)` induced
by the unit of the adjunction `i⁻¹ ⊣ i_*`, natural in `ℱ`. -/
def globalSectionsRestriction {X Y : AlgebraicSpaces B S hS} (i : X ⟶ Y) :
    Sheaf.Γ (SmallEtale.topology B S hS Y.1) (Type (u + 1)) ⟶
      (smallToposMorphism B S hS i).inverseImage ⋙
        Sheaf.Γ (SmallEtale.topology B S hS X.1) (Type (u + 1)) :=
  letI := (smallToposMorphism B S hS i).preservesFiniteLimits
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (smallToposMorphism B S hS i).adj.unit
      (Sheaf.Γ (SmallEtale.topology B S hS Y.1) (Type (u + 1))) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (smallToposMorphism B S hS i).inverseImage
      (Stacks.Sites.globalSectionsIsoOfAdjunctionOfPreservesTerminal.{u, u + 1}
        (smallToposMorphism B S hS i).adj).hom

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of sheaves of sets on the small étale sites exceeds the
-- default budget
/-- Every natural transformation `Γ(Y, -) ⟶ Γ(X, i⁻¹ -)` is restriction of global sections: the
inverse image carries the final sheaf to a final sheaf, whose global sections are a single
point, and global sections are corepresented by the final sheaf. -/
theorem eq_globalSectionsRestriction {X Y : AlgebraicSpaces B S hS} (i : X ⟶ Y)
    (α : Sheaf.Γ (SmallEtale.topology B S hS Y.1) (Type (u + 1)) ⟶
      (smallToposMorphism B S hS i).inverseImage ⋙
        Sheaf.Γ (SmallEtale.topology B S hS X.1) (Type (u + 1))) :
    α = globalSectionsRestriction B S hS i := by
  let := (smallToposMorphism B S hS i).preservesFiniteLimits
  refine Stacks.EtaleCohomology.natTrans_Γ_ext.{u + 1} (SmallEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS X.1) (smallToposMorphism B S hS i).inverseImage ?_ _ _
  have hT := (Stacks.Sites.isTerminalConstantSheafPUnit.{u, u + 1}
    (SmallEtale.topology B S hS Y.1)).isTerminalObj (smallToposMorphism B S hS i).inverseImage
  refine ⟨fun x y ↦
    (Sheaf.ΓObjEquivHom (SmallEtale.topology B S hS X.1) _ PUnit.{u + 2}).injective ?_⟩
  exact hT.hom_ext _ _

end Restriction

section HenselianPair

variable {B : BigFppfSite.{u}} (A : Type u) [CommRing A] (I : Ideal A)
  (hA : B.Contains (Spec (.of A))) (X : AlgebraicSpaces B (Spec (.of A)) hA)
  (f : X ⟶ ⟨yoneda.obj (Over.mk (𝟙 (B.obj hA))),
    isAlgebraicSpace_yoneda B (Spec (.of A)) hA (Over.mk (𝟙 (B.obj hA)))⟩)

/-- The closed fibre `X₀ = X ×_{Spec A} Spec (A ⧸ I)` of an algebraic space `X` over `Spec A`. -/
abbrev closedFibre : AlgebraicSpaces B (Spec (.of A)) hA :=
  AlgebraicSpaces.fiberProduct B (Spec (.of A)) hA f
    (schemeSpaceMap (quotientSpecOverHom A I hA))

/-- The inclusion `i : X₀ ⟶ X` of the closed fibre. -/
abbrev closedFibreInclusion : closedFibre A I hA X f ⟶ X :=
  ObjectProperty.homMk (pullback.fst f.hom
    (schemeSpaceMap (quotientSpecOverHom A I hA)).hom)

/-- The structure morphism `f₀ : X₀ ⟶ Spec (A ⧸ I)` of the closed fibre. -/
abbrev closedFibreProjection :
    closedFibre A I hA X f ⟶ schemeSpace (quotientSpecOver A I hA) :=
  ObjectProperty.homMk (pullback.snd f.hom
    (schemeSpaceMap (quotientSpecOverHom A I hA)).hom)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of sheaves of sets on the small étale sites exceeds the
-- default budget
/-- **Global sections of a proper algebraic space over a henselian pair are those of its closed
fibre**, as an isomorphism of functors `Γ(X, -) ≅ Γ(X₀, i⁻¹ -)` on sheaves of sets on
`X_étale`. It is the composite of the identification of global sections of `f_* ℱ` with those of
`ℱ`, of [Stacks, Tag 09ZH] for `Spec A` applied to `f_* ℱ`, of proper base change
[Stacks, Tag 0DG0] `q⁻¹ f_* ℱ ≅ f₀,* i⁻¹ ℱ`, and of the identification of global sections of
`f₀,* i⁻¹ ℱ` with those of `i⁻¹ ℱ`. -/
def globalSectionsClosedFibreIso (hI : HenselianPair A I)
    (hf : IsProper B (Spec (.of A)) hA f.hom) :
    Sheaf.Γ (SmallEtale.topology B (Spec (.of A)) hA X.1) (Type (u + 1)) ≅
      (smallToposMorphism B (Spec (.of A)) hA (closedFibreInclusion A I hA X f)).inverseImage ⋙
        Sheaf.Γ (SmallEtale.topology B (Spec (.of A)) hA (closedFibre A I hA X f).1)
          (Type (u + 1)) :=
  letI := (smallToposMorphism B (Spec (.of A)) hA f).preservesFiniteLimits
  letI := (smallToposMorphism B (Spec (.of A)) hA
    (closedFibreProjection A I hA X f)).preservesFiniteLimits
  letI := isIso_properBaseChangeMap_of_isProper B (Spec (.of A)) hA f hf
    (schemeSpaceMap (quotientSpecOverHom A I hA))
    (closedFibreProjection A I hA X f) (closedFibreInclusion A I hA X f)
    (AlgebraicSpaces.isPullback_fiberProduct B (Spec (.of A)) hA f
      (schemeSpaceMap (quotientSpecOverHom A I hA)))
  (Stacks.Sites.globalSectionsIsoOfAdjunctionOfPreservesTerminal.{u, u + 1}
      (smallToposMorphism B (Spec (.of A)) hA f).adj).symm ≪≫
    Functor.isoWhiskerLeft _ (globalSectionsRepresentedQuotientIso A I hA hI) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (properBaseChangeMap B (Spec (.of A)) hA f
      (schemeSpaceMap (quotientSpecOverHom A I hA))
      (closedFibreProjection A I hA X f) (closedFibreInclusion A I hA X f)
      (AlgebraicSpaces.isPullback_fiberProduct B (Spec (.of A)) hA f
        (schemeSpaceMap (quotientSpecOverHom A I hA))))) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Stacks.Sites.globalSectionsIsoOfAdjunctionOfPreservesTerminal.{u, u + 1}
        (smallToposMorphism B (Spec (.of A)) hA (closedFibreProjection A I hA X f)).adj)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of sheaves of sets on the small étale sites exceeds the
-- default budget
/-- **[Stacks, Tag 0DFY].** Let `(A, I)` be a henselian pair, let `X` be an algebraic space over
`A` whose structure morphism `f : X ⟶ Spec A` is proper, and let `i : X₀ ⟶ X` be the inclusion of
`X₀ = X ×_{Spec A} Spec (A ⧸ I)`. For every sheaf of sets `ℱ` on `X_étale`,
`Γ(X, ℱ) = Γ(X₀, i⁻¹ ℱ)`: restriction of global sections along `i`, natural in `ℱ`, is an
isomorphism. -/
@[stacks 0DFY]
theorem isIso_globalSectionsRestriction_closedFibre_of_henselianPair (hI : HenselianPair A I)
    (hf : IsProper B (Spec (.of A)) hA f.hom) :
    IsIso (globalSectionsRestriction B (Spec (.of A)) hA (closedFibreInclusion A I hA X f)) := by
  rw [← eq_globalSectionsRestriction B (Spec (.of A)) hA (closedFibreInclusion A I hA X f)
    (globalSectionsClosedFibreIso A I hA X f hI hf).hom]
  infer_instance

end HenselianPair

end AlgebraicGeometry.Space

end
