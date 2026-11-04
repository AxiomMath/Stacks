module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleBaseChangeMate
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleBaseChangeUnitors
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartCoverDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartLocalFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePushforwardFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ComplexesWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyInjectiveSetEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.CategoryTheory.Adjunction.ModificationGlueing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Glueing spaces-étale sheaves along a modification

Let

```
E --j--> Y
|g       |f
v        v
Z --i--> X
```

be a commutative square of algebraic spaces over `S`. This file instantiates the abstract glueing
of `CategoryTheory.Adjunction.ModificationGlueing` on the spaces-étale topoi of sheaves of sets:
the restriction functor `F ↦ (f⁻¹F, i⁻¹F)` to the categorical pullback of `j⁻¹` and `g⁻¹`, its
right adjoint `(G', G, α) ↦ f_*G' ×_{i_*g_*j⁻¹G'} i_*G`, and the criterion for the restriction to
be an equivalence (Stacks, Tag 0GFY).

The base-change input of the criterion is the spaces-étale base-change 2-cell
`AlgebraicGeometry.Space.spacesToposBaseChangeSquare` of the square, whose invertibility is the
conclusion of Stacks 0DG0 for `f` proper and the square cartesian. The open part is the open
complement `u : U ⟶ X` of the closed immersion `i`, with a cartesian square `w ≫ f = fU ≫ u` in
which `fU` is an isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.spacesPushforwardCompSquareIso`: the comparison of the two composite
  direct images of a commutative square, as an isomorphism.
* `AlgebraicGeometry.Space.spacesModificationRestriction`,
  `AlgebraicGeometry.Space.spacesModificationGlue` and
  `AlgebraicGeometry.Space.spacesModificationAdjunction`: restriction, glueing, and the adjunction
  between them.

## Main results

* `AlgebraicGeometry.Space.reflectsIsomorphisms_spacesEtaleInverseImage_of_isIso`: inverse image
  along an isomorphism of algebraic spaces reflects isomorphisms.
* `AlgebraicGeometry.Space.isIso_spacesToposAdjunction_counit_of_isClosedImmersion`: for a closed
  immersion `i` the counit `i⁻¹ i_* ⟶ 𝟭` of spaces-étale sheaves of sets is an isomorphism.
* `AlgebraicGeometry.Space.isTerminal_spacesInverseImage_closedImmersionComplement`: the
  restriction of a direct image along a closed immersion to the open complement is terminal.
* `AlgebraicGeometry.Space.isIso_spacesInverseImage_map_counit_of_isPullback`: over an étale `U`
  above which `f` is an isomorphism, restriction to the preimage inverts the counit of `f`.
* `AlgebraicGeometry.Space.isIso_of_isIso_spacesInverseImage_map`: restrictions to an open and a
  closed part covering the points jointly reflect isomorphisms.
* `AlgebraicGeometry.Space.isEquivalence_spacesModificationRestriction`: the restriction functor
  is an equivalence, given the Stacks 0DG0 base-change isomorphism for the square.

## References

* [Stacks Project, Tag 0GFY](https://stacks.math.columbia.edu/tag/0GFY)
* [Stacks Project, Tag 0DG0](https://stacks.math.columbia.edu/tag/0DG0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison `i_* ⋙ f_* ≅ f'_* ⋙ g_*` of the composite spaces-étale direct images of a
commutative square, as an isomorphism; its underlying morphism is
`AlgebraicGeometry.Space.spacesPushforwardCompSquare`. -/
def spacesPushforwardCompSquareIso {X Y X' Y' : AlgebraicSpaces B S hS}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (w : i ≫ f = f' ≫ g) :
    (spacesBaseChange B S hS i).functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS X') ⋙
      (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ≅
    (spacesBaseChange B S hS f').functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X') ⋙
      (spacesBaseChange B S hS g).functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS Y') :=
  spacesBaseChange_pushforward_comp B S hS i f ≪≫
    eqToIso (congrArg (fun k : X' ⟶ Y =>
      (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X')) w) ≪≫
    (spacesBaseChange_pushforward_comp B S hS f' g).symm

/-- The underlying morphism of `AlgebraicGeometry.Space.spacesPushforwardCompSquareIso` is
`AlgebraicGeometry.Space.spacesPushforwardCompSquare`. -/
theorem spacesPushforwardCompSquareIso_hom {X Y X' Y' : AlgebraicSpaces B S hS}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (w : i ≫ f = f' ≫ g) :
    (spacesPushforwardCompSquareIso B S hS i f' f g w).hom =
      spacesPushforwardCompSquare B S hS i f' f g w := rfl

/-- The identification `h⁻¹ ⋙ (inv h)⁻¹ ≅ 𝟭` for an isomorphism `h` of algebraic spaces, conjugate
to the composite of the direct-image comparisons `(inv h)_* ⋙ h_* ≅ (𝟙 _)_* ≅ 𝟭`. -/
def spacesEtaleInverseImageInvIso {U V : AlgebraicSpaces B S hS} (h : U ⟶ V) [IsIso h] :
    𝟭 (Sheaf (SpacesEtale.topology B S hS V) (Type (u + 1))) ≅
      ((spacesBaseChange_isMorphismOfSites B S hS h).morphismOfTopoi).inverseImage ⋙
        ((spacesBaseChange_isMorphismOfSites B S hS (inv h)).morphismOfTopoi).inverseImage :=
  (conjugateIsoEquiv ((spacesToposAdjunction B S hS h).comp
      (spacesToposAdjunction B S hS (inv h))) Adjunction.id).symm
    (spacesBaseChange_pushforward_comp B S hS (inv h) h ≪≫
      eqToIso (congrArg (fun k : V ⟶ V =>
        (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS V) (SpacesEtale.topology B S hS V))
          (IsIso.inv_hom_id h)) ≪≫
      spacesEtaleSheafPushforwardId B S hS V)

/-- Inverse image along an isomorphism of algebraic spaces reflects isomorphisms. -/
theorem reflectsIsomorphisms_spacesEtaleInverseImage_of_isIso {U V : AlgebraicSpaces B S hS}
    (h : U ⟶ V) [IsIso h] :
    Functor.ReflectsIsomorphisms
      ((spacesBaseChange_isMorphismOfSites B S hS h).morphismOfTopoi).inverseImage where
  reflects {F F'} φ _ := by
    have : IsIso ((((spacesBaseChange_isMorphismOfSites B S hS h).morphismOfTopoi).inverseImage ⋙
        ((spacesBaseChange_isMorphismOfSites B S hS (inv h)).morphismOfTopoi).inverseImage).map
          φ) :=
      Functor.map_isIso _
        (((spacesBaseChange_isMorphismOfSites B S hS h).morphismOfTopoi).inverseImage.map φ)
    exact (NatIso.isIso_map_iff (spacesEtaleInverseImageInvIso B S hS h) φ).mpr this

/-- **Stacks 04E5, part (1), full faithfulness, on the spaces-étale topos.** For a closed
immersion `i : Z ⟶ X` the spaces-étale direct image of sheaves of sets (at `Type (u + 1)`) is
fully faithful. -/
@[sga "4 VIII 6.3" "more general"]
def fullyFaithfulSpacesPushforwardOfIsClosedImmersion {Z X : AlgebraicSpaces B S hS}
    (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    ((spacesBaseChange B S hS i).functor.sheafPushforwardContinuous (Type (u + 1))
      (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Z)).FullyFaithful :=
  letI := isContinuous_smallBaseChange B S hS i hi.rep
  have h := ((smallEtaleToposEquiv B S hS Z).fullyFaithfulFunctor.comp
    (fullyFaithfulSmallEtaleRestriction B S hS (Type (u + 1)) i hi.rep
      (smallBaseChange_isCoverDense_of_isClosedImmersion B S hS i hi)
      (smallBaseChange_isLocallyFull_of_isClosedImmersion B S hS i hi))).ofIso
    (smallBaseChange_pushforward_comparison B S hS i hi.rep)
  Functor.FullyFaithful.ofCompFaithful (G := (smallEtaleToposEquiv B S hS X).functor) h

/-- The counit of an adjunction is an isomorphism when the right adjoint is fully faithful. -/
private theorem isIso_counit_of_fullyFaithful {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (h : R.FullyFaithful) : IsIso adj.counit :=
  haveI := h.full
  haveI := h.faithful
  adj.counit_isIso_of_R_fully_faithful

/-- **Stacks 04E5, part (1), left inverse, on the spaces-étale topos.** For a closed immersion
`i` the counit `i⁻¹ i_* ⟶ 𝟭` of spaces-étale sheaves of sets is an isomorphism. -/
theorem isIso_spacesToposAdjunction_counit_of_isClosedImmersion {Z X : AlgebraicSpaces B S hS}
    (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    IsIso (spacesToposAdjunction B S hS i).counit := by
  exact isIso_counit_of_fullyFaithful _
    (fullyFaithfulSpacesPushforwardOfIsClosedImmersion B S hS i hi)

/-- The spaces-étale direct image along an isomorphism of algebraic spaces is an equivalence,
with inverse the direct image along the inverse. -/
def spacesPushforwardEquivalenceOfIsIso {U V : AlgebraicSpaces B S hS} (h : U ⟶ V) [IsIso h] :
    Sheaf (SpacesEtale.topology B S hS U) (Type (u + 1)) ≌
      Sheaf (SpacesEtale.topology B S hS V) (Type (u + 1)) :=
  CategoryTheory.Equivalence.mk
    ((spacesBaseChange B S hS h).functor.sheafPushforwardContinuous (Type (u + 1))
      (SpacesEtale.topology B S hS V) (SpacesEtale.topology B S hS U))
    ((spacesBaseChange B S hS (inv h)).functor.sheafPushforwardContinuous (Type (u + 1))
      (SpacesEtale.topology B S hS U) (SpacesEtale.topology B S hS V))
    (spacesBaseChange_pushforward_comp B S hS h (inv h) ≪≫
      eqToIso (congrArg (fun k : U ⟶ U =>
        (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS U) (SpacesEtale.topology B S hS U))
        (IsIso.hom_inv_id h)) ≪≫ spacesEtaleSheafPushforwardId B S hS U).symm
    (spacesBaseChange_pushforward_comp B S hS (inv h) h ≪≫
      eqToIso (congrArg (fun k : V ⟶ V =>
        (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS V) (SpacesEtale.topology B S hS V))
        (IsIso.inv_hom_id h)) ≪≫ spacesEtaleSheafPushforwardId B S hS V)

/-- Along an isomorphism of algebraic spaces the counit of the spaces-étale inverse and direct
images is an isomorphism. -/
theorem isIso_spacesToposAdjunction_counit_of_isIso {U V : AlgebraicSpaces B S hS} (h : U ⟶ V)
    [IsIso h] : IsIso (spacesToposAdjunction B S hS h).counit := by
  exact isIso_counit_of_fullyFaithful _
    (spacesPushforwardEquivalenceOfIsIso B S hS h).fullyFaithfulFunctor

/-- **A modification which is an isomorphism over an étale `U`.** For a cartesian square
`w ≫ f = fU ≫ u` with `u` étale and `fU` an isomorphism, `w⁻¹` inverts the counit
`f⁻¹ f_* ⟶ 𝟭` of spaces-étale sheaves of sets. -/
theorem isIso_spacesInverseImage_map_counit_of_isPullback {X Y U V : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (u : U ⟶ X) (w : V ⟶ Y) (fU : V ⟶ U) [IsIso fU] (sq : IsPullback w fU f u)
    (hu : IsEtale B S hS u.hom) (G : Sheaf (SpacesEtale.topology B S hS Y) (Type (u + 1))) :
    IsIso (((spacesBaseChange_isMorphismOfSites B S hS w).morphismOfTopoi).inverseImage.map
      ((spacesToposAdjunction B S hS f).counit.app G)) := by
  have := isIso_spacesToposAdjunction_counit_of_isIso B S hS fU
  exact Adjunction.ModificationGlueing.isIso_map_counit_of_isIso_baseChange
    (spacesToposAdjunction B S hS f) (spacesToposAdjunction B S hS u)
    (spacesToposAdjunction B S hS w) (spacesToposAdjunction B S hS fU)
    (spacesPushforwardCompSquareIso B S hS w fU f u sq.w)
    (isIso_spacesToposBaseChangeSquare B S hS w fU f u sq hu) G

/-- A sheaf of sets all of whose values are terminal is terminal. -/
def _root_.CategoryTheory.Sheaf.isTerminalOfIsTerminalVal {C : Type*} [Category C]
    {J : GrothendieckTopology C} {A : Type*} [Category A] (F : Sheaf J A)
    (h : ∀ W, IsTerminal (F.val.obj W)) : IsTerminal F :=
  IsTerminal.ofUniqueHom
    (fun _ => ⟨{ app := fun W => (h W).from _, naturality := fun _ _ _ => (h _).hom_ext _ _ }⟩)
    (fun _ _ => Sheaf.hom_ext (NatTrans.ext (funext fun W => (h W).hom_ext _ _)))

section OpenComplement

variable {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)

/-- The inclusion of the open complement of a closed immersion is étale. -/
theorem isEtale_closedImmersionComplementHom :
    IsEtale B S hS (closedImmersionComplementHom B S hS i hi).hom :=
  isEtale_of_isOpenImmersion B S hS (isOpenImmersion_closedImmersionComplementHom B S hS i hi)

/-- An object of the spaces-étale site of the open complement `X ∖ Z`, pushed to `X` and base
changed along `i`, has no points. -/
theorem isEmpty_points_spacesBaseChange_spacesEtalePostcomp
    (W : SpacesEtale B S hS (closedImmersionComplement B S hS i hi)) :
    IsEmpty (points B S hS ((SpacesEtale.toSpaces B S hS Z).obj
      ((spacesBaseChange B S hS i).functor.obj
        ((spacesEtalePostcomp B S hS (closedImmersionComplementHom B S hS i hi)
          (isEtale_closedImmersionComplementHom B S hS i hi)).obj W))).obj) := by
  refine ⟨fun x => ?_⟩
  let P := (spacesEtalePostcomp B S hS (closedImmersionComplementHom B S hS i hi)
    (isEtale_closedImmersionComplementHom B S hS i hi)).obj W
  change points B S hS (pullback P.1.hom i).1 at x
  have hw : pointsMap B S hS _ ((pullback.fst P.1.hom i).hom ≫ P.1.hom.hom) x =
      pointsMap B S hS _ ((pullback.snd P.1.hom i).hom ≫ i.hom) x :=
    congrArg (fun k => pointsMap B S hS _ k.hom x) (pullback.condition (f := P.1.hom) (g := i))
  rw [pointsMap_comp_apply, pointsMap_comp_apply] at hw
  have hu : pointsMap B S hS _ P.1.hom.hom (pointsMap B S hS _ (pullback.fst P.1.hom i).hom x) ∈
      Set.range (pointsMap B S hS (closedImmersionComplement B S hS i hi).1
        (closedImmersionComplementHom B S hS i hi).hom) :=
    ⟨_, (pointsMap_comp_apply B S hS W.1.hom.hom
      (closedImmersionComplementHom B S hS i hi).hom _).symm⟩
  rw [range_pointsMap_closedImmersionComplementHom, hw] at hu
  exact hu ⟨_, rfl⟩

/-- **Stacks 04E5, part (1), the easy half of the essential image, on the spaces-étale topos.**
The restriction of a direct image along a closed immersion `i` to the open complement of `Z` is
terminal. -/
@[sga "4 VIII 6.3" "partial"]
def isTerminal_spacesInverseImage_closedImmersionComplement
    (M : Sheaf (SpacesEtale.topology B S hS Z) (Type (u + 1))) :
    IsTerminal
      (((spacesBaseChange_isMorphismOfSites B S hS
          (closedImmersionComplementHom B S hS i hi)).morphismOfTopoi).inverseImage.obj
        (((spacesBaseChange B S hS i).functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Z)).obj M)) :=
  IsTerminal.ofIso
    (Sheaf.isTerminalOfIsTerminalVal _ fun W =>
      M.isTerminalOfBotCover _ (SpacesEtale.bot_mem_topology B S hS Z _
        (isEmpty_points_spacesBaseChange_spacesEtalePostcomp B S hS i hi W.unop)))
    ((spacesToposMorphism_inverseImageIso B S hS (closedImmersionComplementHom B S hS i hi)
      (isEtale_closedImmersionComplementHom B S hS i hi)).app _).symm

end OpenComplement

section Conservativity

/-- If the small étale inverse image along `f` inverts `a`, then `a` is a bijection on the stalk
at the image of every geometric point of the source (Stacks 04K2, part (4)). -/
theorem bijective_stalkSetMap_of_isIso_map {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (x : GeometricPoint B S hS X.1)
    {F G : Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1))} (a : F ⟶ G)
    (ha : IsIso ((smallToposMorphism B S hS f).inverseImage.map a)) :
    Function.Bijective (stalkSetMap (geometricPointMap f.hom x) a.hom) := by
  have h₁ : IsIso ((sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)) ⋙
      stalkSetFunctor x).map ((smallToposMorphism B S hS f).inverseImage.map a)) :=
    Functor.map_isIso _ _
  exact (isIso_iff_bijective _).mp
    ((NatIso.isIso_map_iff (smallEtaleInverseImageStalkIso B S hS f x) a).mp h₁)

/-- **Restrictions to an open and a closed part covering the points jointly reflect
isomorphisms**, for small étale sheaves of sets. -/
theorem isIso_of_isIso_smallInverseImage_map {X O Z : AlgebraicSpaces B S hS} (o : O ⟶ X)
    (i : Z ⟶ X) (ho : IsOpenImmersion B S hS o.hom) (hi : IsClosedImmersion B S hS i.hom)
    (hcover : ∀ x : points B S hS X.1, x ∈ Set.range (pointsMap B S hS O.1 o.hom) ∨
      x ∈ Set.range (pointsMap B S hS Z.1 i.hom))
    {F G : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))} (a : F ⟶ G)
    (h₁ : IsIso ((smallToposMorphism B S hS o).inverseImage.map a))
    (h₂ : IsIso ((smallToposMorphism B S hS i).inverseImage.map a)) : IsIso a := by
  refine isIso_of_bijective_stalkSetMap B S hS X.property a fun x => ?_
  rcases hcover x.image with hx | hx
  · obtain ⟨y, rfl⟩ :=
      exists_geometricPoint_map_eq_of_mem_range_of_isOpenImmersion B S hS o ho x hx
    exact bijective_stalkSetMap_of_isIso_map B S hS o y a h₁
  · obtain ⟨z, rfl⟩ := exists_geometricPoint_map_eq_of_mem_range B S hS i hi x hx
    exact bijective_stalkSetMap_of_isIso_map B S hS i z a h₂

/-- **Restrictions to an open and a closed part covering the points jointly reflect
isomorphisms**, for spaces-étale sheaves of sets. -/
theorem isIso_of_isIso_spacesInverseImage_map {X O Z : AlgebraicSpaces B S hS} (o : O ⟶ X)
    (i : Z ⟶ X) (ho : IsOpenImmersion B S hS o.hom) (hi : IsClosedImmersion B S hS i.hom)
    (hcover : ∀ x : points B S hS X.1, x ∈ Set.range (pointsMap B S hS O.1 o.hom) ∨
      x ∈ Set.range (pointsMap B S hS Z.1 i.hom))
    {F F' : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1))} (φ : F ⟶ F')
    (h₁ : IsIso
      (((spacesBaseChange_isMorphismOfSites B S hS o).morphismOfTopoi).inverseImage.map φ))
    (h₂ : IsIso
      (((spacesBaseChange_isMorphismOfSites B S hS i).morphismOfTopoi).inverseImage.map φ)) :
    IsIso φ := by
  have key : ∀ {P : AlgebraicSpaces B S hS} (p : P ⟶ X)
      [IsIso (((spacesBaseChange_isMorphismOfSites B S hS p).morphismOfTopoi).inverseImage.map φ)],
      IsIso ((smallToposMorphism B S hS p).inverseImage.map
        ((smallEtaleToposEquiv B S hS X).functor.map φ)) := fun p =>
    (NatIso.isIso_map_iff (smallToposMorphism_inverseImage_comparison B S hS p) φ).mpr
      (Functor.map_isIso (smallEtaleToposEquiv B S hS _).functor _)
  have : IsIso ((smallEtaleToposEquiv B S hS X).functor.map φ) :=
    isIso_of_isIso_smallInverseImage_map B S hS o i ho hi hcover _ (key o) (key i)
  exact isIso_of_reflects_iso φ (smallEtaleToposEquiv B S hS X).functor

end Conservativity

variable {X Y Z E : AlgebraicSpaces B S hS} (f : Y ⟶ X) (i : Z ⟶ X) (j : E ⟶ Y) (g : E ⟶ Z)
  (w : j ≫ f = g ≫ i)

/-- The restriction functor `F ↦ (f⁻¹F, i⁻¹F)` from spaces-étale sheaves on `X` to the categorical
pullback of `j⁻¹` and `g⁻¹`, with the identification `j⁻¹f⁻¹F ≅ g⁻¹i⁻¹F` conjugate to the
direct-image comparison of the square. -/
def spacesModificationRestriction :
    Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)) ⥤
      CategoricalPullback
        ((spacesBaseChange_isMorphismOfSites B S hS j).morphismOfTopoi).inverseImage
        ((spacesBaseChange_isMorphismOfSites B S hS g).morphismOfTopoi).inverseImage :=
  Adjunction.ModificationGlueing.restriction (spacesToposAdjunction B S hS f)
    (spacesToposAdjunction B S hS i) (spacesToposAdjunction B S hS j)
    (spacesToposAdjunction B S hS g) (spacesPushforwardCompSquareIso B S hS j g f i w)

/-- The glueing functor `(G', G, α) ↦ f_*G' ×_{i_*g_*j⁻¹G'} i_*G`. -/
def spacesModificationGlue :
    CategoricalPullback
        ((spacesBaseChange_isMorphismOfSites B S hS j).morphismOfTopoi).inverseImage
        ((spacesBaseChange_isMorphismOfSites B S hS g).morphismOfTopoi).inverseImage ⥤
      Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)) :=
  Adjunction.ModificationGlueing.glue (spacesToposAdjunction B S hS j)
    (spacesToposAdjunction B S hS g) (spacesPushforwardCompSquareIso B S hS j g f i w)

/-- Restriction is left adjoint to glueing. -/
def spacesModificationAdjunction :
    spacesModificationRestriction B S hS f i j g w ⊣ spacesModificationGlue B S hS f i j g w :=
  Adjunction.ModificationGlueing.adjunction _ _ _ _ _

/-- **Glueing spaces-étale sheaves along a modification, granted Stacks 0DG0.** Let
`j ≫ f = g ≫ i` be a cartesian square of algebraic spaces with `i : Z ⟶ X` a closed immersion,
let `u : U ⟶ X` be the open complement of `Z`, and let `w ≫ f = fU ≫ u` be a cartesian square
with `fU` an isomorphism (`f` is an isomorphism over `U`). If the spaces-étale base-change
2-cell of the first square is invertible (`h0DG0`, the conclusion of Stacks 0DG0 when `f` is
proper), the restriction functor `F ↦ (f⁻¹F, i⁻¹F)` is an equivalence onto the categorical
pullback of `j⁻¹` and `g⁻¹`; its inverse is `AlgebraicGeometry.Space.spacesModificationGlue`. -/
theorem isEquivalence_spacesModificationRestriction (sq : IsPullback j g f i)
    (h0DG0 : IsIso (spacesToposBaseChangeSquare B S hS j g f i sq))
    (hi : IsClosedImmersion B S hS i.hom)
    {V : AlgebraicSpaces B S hS} (w' : V ⟶ Y)
    (fU : V ⟶ closedImmersionComplement B S hS i hi) [IsIso fU]
    (sqU : IsPullback w' fU f (closedImmersionComplementHom B S hS i hi)) :
    (spacesModificationRestriction B S hS f i j g sq.w).IsEquivalence := by
  have ho := isOpenImmersion_closedImmersionComplementHom B S hS i hi
  have hcoverX : ∀ x : points B S hS X.1,
      x ∈ Set.range (pointsMap B S hS (closedImmersionComplement B S hS i hi).1
        (closedImmersionComplementHom B S hS i hi).hom) ∨
      x ∈ Set.range (pointsMap B S hS Z.1 i.hom) := fun x => by
    rw [range_pointsMap_closedImmersionComplementHom]
    exact (em _).symm
  have hcoverY : ∀ y : points B S hS Y.1, y ∈ Set.range (pointsMap B S hS V.1 w'.hom) ∨
      y ∈ Set.range (pointsMap B S hS E.1 j.hom) := fun y => by
    rcases hcoverX (pointsMap B S hS Y.1 f.hom y) with ⟨v, hv⟩ | ⟨z, hz⟩
    · obtain ⟨e, -, he⟩ := exists_point_of_isPullback B S hS sqU.flip v y hv
      exact Or.inl ⟨e, he⟩
    · obtain ⟨e, -, he⟩ := exists_point_of_isPullback B S hS sq.flip z y hz
      exact Or.inr ⟨e, he⟩
  have := ((spacesBaseChange_isMorphismOfSites B S hS i).morphismOfTopoi).preservesFiniteLimits
  have := ((spacesBaseChange_isMorphismOfSites B S hS
    (closedImmersionComplementHom B S hS i hi)).morphismOfTopoi).preservesFiniteLimits
  have := reflectsIsomorphisms_spacesEtaleInverseImage_of_isIso B S hS fU
  have := isIso_spacesToposAdjunction_counit_of_isClosedImmersion B S hS i hi
  exact Adjunction.ModificationGlueing.isEquivalence_restriction _ _ _ _ _ h0DG0 _
    (isTerminal_spacesInverseImage_closedImmersionComplement B S hS i hi) _ _
    (Adjunction.ModificationGlueing.inverseImageIso (spacesToposAdjunction B S hS f)
      (spacesToposAdjunction B S hS (closedImmersionComplementHom B S hS i hi))
      (spacesToposAdjunction B S hS w') (spacesToposAdjunction B S hS fU)
      (spacesPushforwardCompSquareIso B S hS w' fU f _ sqU.w))
    (isIso_spacesInverseImage_map_counit_of_isPullback B S hS f _ w' fU sqU
      (isEtale_closedImmersionComplementHom B S hS i hi))
    (fun φ h₁ h₂ => isIso_of_isIso_spacesInverseImage_map B S hS _ i ho hi hcoverX φ h₁ h₂)
    (fun ψ h₁ h₂ => isIso_of_isIso_spacesInverseImage_map B S hS w' j
      (isOpenImmersion_of_isPullback B S hS sqU.flip ho)
      (isClosedImmersion_of_isPullback B S hS sq.flip hi) hcoverY ψ h₁ h₂)

end AlgebraicGeometry.Space
