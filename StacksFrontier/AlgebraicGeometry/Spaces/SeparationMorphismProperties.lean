module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange

/-!
# Separatedness, properness, universal closedness and quasi-compactness as morphism properties

Let `S` be a scheme contained in a big fppf site `B`. Being quasi-compact, separated, universally
closed, locally of finite type, of finite type, proper and quasi-separated are packaged as
`CategoryTheory.MorphismProperty` on the category `AlgebraicGeometry.AlgebraicSpaces` of
algebraic spaces over `S`, with their stability under base change and, for closedness,
universal closedness and quasi-compactness, under composition.

## Main definitions

* `AlgebraicGeometry.Space.quasiCompactProperty`, `.separatedProperty`,
  `.universallyClosedProperty`, `.properProperty`, `.finiteTypeProperty`,
  `.locallyOfFiniteTypeProperty` and `.quasiSeparatedProperty`.

## Main results

* `AlgebraicGeometry.Space.isSeparated_pullback` and
  `AlgebraicGeometry.Space.isLocallySeparated_pullback`: a base change of a separated, resp.
  locally separated, morphism of algebraic spaces is separated, resp. locally separated.
* `AlgebraicGeometry.Space.universallyClosed_pullback`: a base change of a universally closed
  morphism of algebraic spaces is universally closed.
* `AlgebraicGeometry.Space.isClosedMorphism_comp` and
  `AlgebraicGeometry.Space.universallyClosed_comp`: a composition of closed, resp. universally
  closed, morphisms of algebraic spaces is closed, resp. universally closed.
* `AlgebraicGeometry.Space.isQuasiCompact_comp`: a composition of quasi-compact morphisms of
  algebraic spaces is quasi-compact.
* `AlgebraicGeometry.Space.properProperty_eq_inf` and
  `AlgebraicGeometry.Space.finiteTypeProperty_eq_inf`: the two conjunctive decompositions.
* `AlgebraicGeometry.Space.properProperty_isLocalAtTarget` and
  `.finiteTypeProperty_isLocalAtTarget`: properness, resp. finite type, is local at the target
  for a precoverage as soon as the conditions it is built from are.

## Implementation notes

The seven properties are abbreviations, so an instance proved for the unfolded property is found
by instance search through the abbreviation; base-change instances are declared here only for
separatedness, universal closedness and local finite type.

## References

* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HG](https://stacks.math.columbia.edu/tag/03HG)
* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03IS](https://stacks.math.columbia.edu/tag/03IS)
* [Stacks Project, Tag 03IU](https://stacks.math.columbia.edu/tag/03IU)
* [Stacks Project, Tag 03KL](https://stacks.math.columbia.edu/tag/03KL)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Base change of separated and locally separated morphisms -/

/-- If `P` is stable under base change, so is `P.diagonal`, for the second projection of a pullback
of presheaves on the big fppf site of `S`. -/
private theorem diagonal_pullback_snd (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    [P.IsStableUnderBaseChange] {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hf : P.diagonal f) : P.diagonal (pullback.snd f g) := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (MorphismProperty.IsStableUnderBaseChange.diagonal (P := P)).of_isPullback
    (IsPullback.of_hasPullback f g) hf

/-- A base change of a separated morphism of algebraic spaces over `S` is separated. -/
@[stacks 03KL "separated_base_change"]
theorem isSeparated_pullback {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hf : IsSeparated B S hS f) :
    IsSeparated B S hS (pullback.snd f g) := by
  have : (closedImmersionPresheafProperty B S hS).IsStableUnderBaseChange :=
    isClosedImmersion_isStableUnderBaseChange B S hS
  exact diagonal_pullback_snd B S hS (closedImmersionPresheafProperty B S hS) f g hf

/-- A base change of a locally separated morphism of algebraic spaces over `S` is locally
separated. -/
@[stacks 03KL "locally_separated_base_change"]
theorem isLocallySeparated_pullback {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hf : IsLocallySeparated B S hS f) :
    IsLocallySeparated B S hS (pullback.snd f g) := by
  have : (immersionPresheafProperty B S hS).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact diagonal_pullback_snd B S hS (immersionPresheafProperty B S hS) f g hf

/-! ### Closed and universally closed morphisms -/

/-- A morphism of presheaves on the big fppf site of `S` is closed as soon as its precomposition
with an isomorphism is. -/
private theorem isClosedMorphism_of_iso_comp
    {A D E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : A ≅ D) (f : D ⟶ E)
    (hf : IsClosedMorphism B S hS (e.hom ≫ f)) :
    IsClosedMorphism B S hS f := by
  let _ := pointTopology B S hS A
  let _ := pointTopology B S hS D
  let _ := pointTopology B S hS E
  have hinv : IsClosedMap (pointsMap B S hS D e.inv) := by
    refine IsClosedMap.of_inverse (continuous_pointsMap B S hS e.hom) ?_ ?_
    · intro x
      have h := congrArg (pointsMap B S hS A) e.hom_inv_id
      rw [pointsMap_comp, pointsMap_id] at h
      exact congrFun h x
    · intro x
      have h := congrArg (pointsMap B S hS D) e.inv_hom_id
      rw [pointsMap_comp, pointsMap_id] at h
      exact congrFun h x
  have hmap : pointsMap B S hS D f =
      pointsMap B S hS A (e.hom ≫ f) ∘ pointsMap B S hS D e.inv := by
    rw [← pointsMap_comp, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  change IsClosedMap (pointsMap B S hS D f)
  rw [hmap]
  exact IsClosedMap.comp hf hinv

/-- A composition of closed morphisms of algebraic spaces over `S` is closed. -/
@[stacks 03IU "closed"]
theorem isClosedMorphism_comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsClosedMorphism B S hS f)
    (hg : IsClosedMorphism B S hS g) :
    IsClosedMorphism B S hS (f ≫ g) := by
  let _ := pointTopology B S hS X
  let _ := pointTopology B S hS Y
  let _ := pointTopology B S hS Z
  change IsClosedMap (pointsMap B S hS X (f ≫ g))
  rw [pointsMap_comp]
  exact IsClosedMap.comp hg hf

/-- A base change of a universally closed morphism of algebraic spaces over `S` is universally
closed. -/
@[stacks 03IS]
theorem universallyClosed_pullback {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Z ⟶ Y) (hf : UniversallyClosed B S hS f) :
    UniversallyClosed B S hS (pullback.fst g f) := by
  intro W hW k
  refine isClosedMorphism_of_iso_comp B S hS
    (pullbackRightPullbackFstIso g f k).symm (pullback.fst k (pullback.fst g f)) ?_
  have hmap : (pullbackRightPullbackFstIso g f k).symm.hom ≫
      pullback.fst k (pullback.fst g f) = pullback.fst (k ≫ g) f := by
    rw [Iso.symm_hom, Iso.inv_comp_eq, pullbackRightPullbackFstIso_hom_fst]
  rw [hmap]
  exact hf W hW (k ≫ g)

/-- A composition of universally closed morphisms of algebraic spaces over `S` is universally
closed. -/
@[stacks 03IU "universally closed"]
theorem universallyClosed_comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : UniversallyClosed B S hS f)
    (hg : UniversallyClosed B S hS g) :
    UniversallyClosed B S hS (f ≫ g) := by
  intro T hT k
  refine isClosedMorphism_of_iso_comp B S hS
    (pullbackLeftPullbackSndIso k g f) (pullback.fst k (f ≫ g)) ?_
  have hmap : (pullbackLeftPullbackSndIso k g f).hom ≫ pullback.fst k (f ≫ g) =
      pullback.fst (pullback.snd k g) f ≫ pullback.fst k g :=
    pullbackLeftPullbackSndIso_hom_fst k g f
  rw [hmap]
  exact isClosedMorphism_comp B S hS _ _
    (hf _ (isAlgebraicSpace_pullback B S hS k g hT hY hZ) (pullback.snd k g))
    (hg T hT k)

/-! ### The seven properties, and their stability under base change and composition -/

/-- Being quasi-compact, as a property of morphisms in the category of
algebraic spaces over `S`. -/
abbrev quasiCompactProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => IsQuasiCompact B S hS f.hom

/-- Being separated, as a property of morphisms in the category of
algebraic spaces over `S`. -/
abbrev separatedProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => IsSeparated B S hS f.hom

/-- Being universally closed, as a property of morphisms in the category of algebraic spaces
over `S`. -/
abbrev universallyClosedProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => UniversallyClosed B S hS f.hom

/-- Being locally of finite type, as a property of morphisms in the category of algebraic spaces
over `S`. -/
abbrev locallyOfFiniteTypeProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => IsLocallyOfFiniteType B S hS f.hom

/-- Being of finite type, as a property of morphisms in the category of algebraic spaces over
`S`. -/
abbrev finiteTypeProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => IsFiniteType B S hS f.hom

/-- Being proper, as a property of morphisms in the category of algebraic
spaces over `S`. -/
abbrev properProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => IsProper B S hS f.hom

/-- Being quasi-separated, as a property of morphisms in the category of algebraic spaces over
`S`. -/
abbrev quasiSeparatedProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f => IsQuasiSeparated B S hS f.hom

/-- Being locally of finite type is stable under base change. -/
instance locallyOfFiniteTypeProperty_isStableUnderBaseChange :
    (locallyOfFiniteTypeProperty B S hS).IsStableUnderBaseChange :=
  isLocallyOfFiniteType_isStableUnderBaseChange B S hS

/-- Separatedness of a morphism of algebraic spaces over `S` is stable under base change, for an
arbitrary cartesian square in the category of algebraic spaces over `S`. -/
instance separatedProperty_isStableUnderBaseChange :
    (separatedProperty B S hS).IsStableUnderBaseChange where
  of_isPullback sq hg := by
    have : (closedImmersionPresheafProperty B S hS).IsStableUnderBaseChange :=
      isClosedImmersion_isStableUnderBaseChange B S hS
    have : (closedImmersionPresheafProperty B S hS).RespectsIso :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.IsStableUnderBaseChange.diagonal
      (P := closedImmersionPresheafProperty B S hS)).of_isPullback
        (AlgebraicSpaces.isPullback_hom B S hS sq) hg

/-- Universal closedness of a morphism of algebraic spaces over `S` is stable under base change,
for an arbitrary cartesian square in the category of algebraic spaces over `S`. -/
instance universallyClosedProperty_isStableUnderBaseChange :
    (universallyClosedProperty B S hS).IsStableUnderBaseChange where
  of_isPullback {_ _ _ _ _ g _ g'} sq hg :=
    (universallyClosed_iff_universally_isClosedMorphism B S hS g').mpr
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback sq
        ((universallyClosed_iff_universally_isClosedMorphism B S hS g).mp hg))

/-- Being a closed morphism of algebraic spaces over `S` is stable under composition. -/
instance isClosedMorphismProperty_isStableUnderComposition :
    (isClosedMorphismProperty B S hS).IsStableUnderComposition where
  comp_mem f g hf hg := isClosedMorphism_comp B S hS f.hom g.hom hf hg

/-- Universal closedness of a morphism of algebraic spaces over `S` is stable under
composition. -/
instance universallyClosedProperty_isStableUnderComposition :
    (universallyClosedProperty B S hS).IsStableUnderComposition where
  comp_mem {_ Y Z} f g hf hg :=
    universallyClosed_comp B S hS Y.property Z.property f.hom g.hom hf hg

/-- A composition of quasi-compact morphisms of algebraic spaces over `S` is quasi-compact. -/
theorem isQuasiCompact_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : IsAlgebraicSpace B S hS G) (hH : IsAlgebraicSpace B S hS H)
    (f : F ⟶ G) (g : G ⟶ H) (hf : IsQuasiCompact B S hS f)
    (hg : IsQuasiCompact B S hS g) :
    IsQuasiCompact B S hS (f ≫ g) := by
  intro Z hZ hZqc k
  exact isQuasiCompactSpace_of_iso B S hS (pullbackLeftPullbackSndIso k g f)
    (hf (pullback k g) (isAlgebraicSpace_pullback B S hS k g hZ hG hH)
      (hg Z hZ hZqc k) (pullback.snd k g))

/-- Quasi-compactness of a morphism of algebraic spaces over `S` is stable under
composition. -/
instance quasiCompactProperty_isStableUnderComposition :
    (quasiCompactProperty B S hS).IsStableUnderComposition where
  comp_mem {_ Y Z} f g hf hg :=
    isQuasiCompact_comp B S hS Y.property Z.property f.hom g.hom hf hg

/-! ### The two conjunctive decompositions -/

/-- Being of finite type is being locally of finite type and quasi-compact, as an equality of
properties of morphisms of algebraic spaces over `S`. -/
theorem finiteTypeProperty_eq_inf :
    finiteTypeProperty B S hS =
      locallyOfFiniteTypeProperty B S hS ⊓ quasiCompactProperty B S hS := rfl

/-- Being proper is being separated, of finite type and universally closed, as an equality of
properties of morphisms of algebraic spaces over `S`. -/
theorem properProperty_eq_inf :
    properProperty B S hS =
      separatedProperty B S hS ⊓
        (finiteTypeProperty B S hS ⊓ universallyClosedProperty B S hS) := rfl

/-- Being of finite type is local at the target for a precoverage of the algebraic spaces over
`S` as soon as being locally of finite type and being quasi-compact are. -/
theorem finiteTypeProperty_isLocalAtTarget {K : Precoverage (AlgebraicSpaces B S hS)}
    (hlft : (locallyOfFiniteTypeProperty B S hS).IsLocalAtTarget K)
    (hqc : (quasiCompactProperty B S hS).IsLocalAtTarget K) :
    (finiteTypeProperty B S hS).IsLocalAtTarget K := by
  rw [finiteTypeProperty_eq_inf]
  exact MorphismProperty.IsLocalAtTarget.inf _ _

/-- Being proper is local at the target for a precoverage of the algebraic spaces over `S` as
soon as being separated, being of finite type and being universally closed are. -/
theorem properProperty_isLocalAtTarget {K : Precoverage (AlgebraicSpaces B S hS)}
    (hsep : (separatedProperty B S hS).IsLocalAtTarget K)
    (hft : (finiteTypeProperty B S hS).IsLocalAtTarget K)
    (huc : (universallyClosedProperty B S hS).IsLocalAtTarget K) :
    (properProperty B S hS).IsLocalAtTarget K := by
  rw [properProperty_eq_inf]
  exact MorphismProperty.IsLocalAtTarget.inf _ _

end AlgebraicGeometry.Space

end
