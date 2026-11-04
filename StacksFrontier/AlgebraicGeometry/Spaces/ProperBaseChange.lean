module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStack
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Properness of morphisms of algebraic spaces is stable under base change

Properness of a morphism of algebraic spaces over `S` is the conjunction of being separated,
being of finite type, and being universally closed (Stacks 03ZM). Each of the three conditions
is stable under base change, and hence so is properness.

## Main definitions

* `AlgebraicGeometry.Space.pointsMapHomeomorph`: the homeomorphism on points induced by an
  isomorphism of algebraic spaces.
* `AlgebraicGeometry.Space.isClosedMorphismProperty`: being a closed morphism, as a property of
  morphisms in the category of algebraic spaces over `S`.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_isStableUnderBaseChange`: quasi-compactness is
  stable under base change.
* `AlgebraicGeometry.Space.isFiniteType_isStableUnderBaseChange`: being of finite type is
  stable under base change.
* `AlgebraicGeometry.Space.universallyClosed_iff_universally_isClosedMorphism`: being
  universally closed is being universally a closed morphism.
* `AlgebraicGeometry.Space.isProper_isStableUnderBaseChange`: properness is stable under base
  change.

## Implementation notes

The statements are `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` on the category of
algebraic spaces over `S` (Stacks 02X2), so they apply to an arbitrary cartesian square rather
than to a chosen fibre product.

## References

* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
* [Stacks Project, Tag 04WP](https://stacks.math.columbia.edu/tag/04WP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Quasi-compactness of a morphism of algebraic spaces over `S` is stable under base change. -/
instance isQuasiCompact_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsQuasiCompact B S hS f.hom) where
  of_isPullback sq hg :=
    isQuasiCompact_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sq) hg

/-- Being of finite type is stable under base change for morphisms of algebraic spaces over
`S`. -/
@[stacks 03XH "finite type"]
instance isFiniteType_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsFiniteType B S hS f.hom) := by
  have := isLocallyOfFiniteType_isStableUnderBaseChange B S hS
  exact MorphismProperty.IsStableUnderBaseChange.inf
    (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsLocallyOfFiniteType B S hS f.hom)
    (Q := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsQuasiCompact B S hS f.hom)

/-- The homeomorphism on points induced by an isomorphism of algebraic spaces over `S`, for the
topology of Stacks 03BX. -/
noncomputable def pointsMapHomeomorph {F G : AlgebraicSpaces B S hS} (e : F ≅ G) :
    @Homeomorph (points B S hS F.obj) (points B S hS G.obj)
      (pointTopology B S hS F.obj) (pointTopology B S hS G.obj) :=
  letI := pointTopology B S hS F.obj
  letI := pointTopology B S hS G.obj
  { toFun := pointsMap B S hS F.obj e.hom.hom
    invFun := pointsMap B S hS G.obj e.inv.hom
    left_inv := fun p => by
      have h := congrFun (pointsMap_comp B S hS F.obj e.hom.hom e.inv.hom) p
      rw [show e.hom.hom ≫ e.inv.hom = 𝟙 F.obj from congrArg (fun k => k.hom) e.hom_inv_id,
        pointsMap_id] at h
      exact h.symm
    right_inv := fun p => by
      have h := congrFun (pointsMap_comp B S hS G.obj e.inv.hom e.hom.hom) p
      rw [show e.inv.hom ≫ e.hom.hom = 𝟙 G.obj from congrArg (fun k => k.hom) e.inv_hom_id,
        pointsMap_id] at h
      exact h.symm
    continuous_toFun := continuous_pointsMap B S hS e.hom.hom
    continuous_invFun := continuous_pointsMap B S hS e.inv.hom }

/-- The underlying morphism of an isomorphism of algebraic spaces over `S` is a closed
morphism. -/
private theorem isClosedMorphism_iso_hom {F G : AlgebraicSpaces B S hS} (e : F ≅ G) :
    IsClosedMorphism B S hS e.hom.hom := by
  let _ := pointTopology B S hS F.obj
  let _ := pointTopology B S hS G.obj
  exact (pointsMapHomeomorph B S hS e).isClosedMap

/-- The composition of closed morphisms of algebraic spaces over `S` is a closed morphism. -/
private theorem isClosedMorphism_hom_comp {F G H : AlgebraicSpaces B S hS} (f : F ⟶ G) (g : G ⟶ H)
    (hf : IsClosedMorphism B S hS f.hom) (hg : IsClosedMorphism B S hS g.hom) :
    IsClosedMorphism B S hS (f ≫ g).hom := by
  let _ := pointTopology B S hS F.obj
  let _ := pointTopology B S hS G.obj
  let _ := pointTopology B S hS H.obj
  have key : IsClosedMap (pointsMap B S hS G.obj g.hom ∘ pointsMap B S hS F.obj f.hom) :=
    IsClosedMap.comp hg hf
  rw [← pointsMap_comp] at key
  exact key

/-- Being a closed morphism of algebraic spaces over `S` is unchanged by precomposing with an
isomorphism. -/
theorem isClosedMorphism_iso_hom_comp {F G H : AlgebraicSpaces B S hS} (e : F ≅ G) (f : G ⟶ H)
    (hf : IsClosedMorphism B S hS f.hom) :
    IsClosedMorphism B S hS (e.hom ≫ f).hom :=
  isClosedMorphism_hom_comp B S hS _ _ (isClosedMorphism_iso_hom B S hS e) hf

/-- Being a closed morphism of algebraic spaces over `S` is unchanged by postcomposing with an
isomorphism. -/
theorem isClosedMorphism_comp_iso_hom {F G H : AlgebraicSpaces B S hS} (e : G ≅ H) (f : F ⟶ G)
    (hf : IsClosedMorphism B S hS f.hom) :
    IsClosedMorphism B S hS (f ≫ e.hom).hom :=
  isClosedMorphism_hom_comp B S hS _ _ hf (isClosedMorphism_iso_hom B S hS e)

/-- Being a closed morphism, as a property of morphisms in the category of algebraic spaces over
`S`. -/
abbrev isClosedMorphismProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => IsClosedMorphism B S hS f.hom

/-- Being a closed morphism of algebraic spaces over `S` respects isomorphisms. -/
instance isClosedMorphismProperty_respectsIso :
    (isClosedMorphismProperty B S hS).RespectsIso :=
  MorphismProperty.RespectsIso.mk _
    (fun e f hf => isClosedMorphism_iso_hom_comp B S hS e f hf)
    (fun e f hf => isClosedMorphism_comp_iso_hom B S hS e f hf)

/-- A morphism of algebraic spaces over `S` is universally closed if and only if it is
universally a closed morphism in the category of algebraic spaces over `S`. -/
theorem universallyClosed_iff_universally_isClosedMorphism {X T : AlgebraicSpaces B S hS}
    (g : X ⟶ T) :
    UniversallyClosed B S hS g.hom ↔ (isClosedMorphismProperty B S hS).universally g := by
  refine ⟨fun hg Y' T' i₁ i₂ k sq => ?_, fun hg Z hZ k => hg _ _ _
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk (X := (⟨Z, hZ⟩ : AlgebraicSpaces B S hS)) k) g)⟩
  have hcan : isClosedMorphismProperty B S hS
      (ObjectProperty.homMk (pullback.fst i₂.hom g.hom) :
        AlgebraicSpaces.fiberProduct B S hS i₂ g ⟶ T') :=
    hg T'.obj T'.property i₂.hom
  refine ((isClosedMorphismProperty B S hS).arrow_mk_iso_iff
    (Arrow.isoMk (f := Arrow.mk (ObjectProperty.homMk (pullback.fst i₂.hom g.hom)))
      (g := Arrow.mk k)
      ((AlgebraicSpaces.isPullback_fiberProduct B S hS i₂ g).isoIsPullback T' X sq)
      (Iso.refl _) ?_)).mp hcan
  exact (AlgebraicSpaces.isPullback_fiberProduct B S hS i₂ g).isoIsPullback_hom_fst T' X sq

/-- Properness of morphisms of algebraic spaces over `S` is stable under base
change. -/
@[stacks 04WP]
instance isProper_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsProper B S hS f.hom) := by
  constructor
  rintro X Y Y' T f g f' g' hpb ⟨hsep, hft, huc⟩
  let R : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
  have : (MorphismProperty.presheaf R).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange R
  have : (MorphismProperty.presheaf R).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact ⟨(MorphismProperty.IsStableUnderBaseChange.diagonal
      (P := MorphismProperty.presheaf R)).of_isPullback
        (AlgebraicSpaces.isPullback_hom B S hS hpb) hsep,
    (isFiniteType_isStableUnderBaseChange B S hS).of_isPullback hpb hft,
    (universallyClosed_iff_universally_isClosedMorphism B S hS g').mpr
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb
        ((universallyClosed_iff_universally_isClosedMorphism B S hS g).mp huc))⟩

end AlgebraicGeometry.Space

end
