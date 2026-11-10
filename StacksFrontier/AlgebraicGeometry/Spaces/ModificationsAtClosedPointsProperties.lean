module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationExcisionProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers

/-!
# Properties and fibres of a modification at finitely many closed points

Let `X` be a decent algebraic space over a scheme `S`, let `x₁, …, xₙ ∈ |X|` be pairwise
distinct closed points and let `(Uᵢ, uᵢ) → (X, xᵢ)` be the chosen elementary étale
neighborhoods, so that the functor `F` of Stacks 0BHA restricts a modification `f : Y ⟶ X` of
`X` away from `{x₁, …, xₙ}` to modifications `gᵢ : Yᵢ ⟶ Uᵢ` of `Uᵢ` away from `uᵢ`.

Two comparisons between `f` and the family `gᵢ` are proved here.

**Stacks 0BHC**: `f` has each of ten standard properties — quasi-compact, quasi-separated,
separated, locally of finite presentation, of finite presentation, locally of finite type, of
finite type, proper, integral, finite — exactly when every `gᵢ` does.

**Stacks 0BHD**: the distinguished point `uᵢ` is represented by a monomorphism
`Spec κ(uᵢ) ⟶ Uᵢ` whose composite with `Uᵢ ⟶ X` is a monomorphism representing `xᵢ`; in other
words `uᵢ ⟶ xᵢ` is an isomorphism. Consequently the fibre of `f` over `xᵢ` and the fibre of
`gᵢ` over `uᵢ` are the same algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.residuePoint` is the canonical field-valued
  representative of `uᵢ`, and
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.residuePointToNeighborhood` and
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.residuePointToSpace` are the induced
  monomorphisms `Spec κ(uᵢ) ⟶ Uᵢ` and `Spec κ(uᵢ) ⟶ X`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.fibreAtPoint` and
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.fibreAtNeighborhoodPoint` are the fibres
  `Y_{xᵢ}` and `(Yᵢ)_{uᵢ}`.

## Main results

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.mono_residuePointToSpace`: the composite
  `Spec κ(uᵢ) ⟶ Uᵢ ⟶ X` is a monomorphism, and
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.pointsMap_toSpaceHom_neighborhoodPoint`:
  the point it represents is `xᵢ`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.fibreAtPointIso`: **Stacks 0BHD**, the
  fibre of `f` over `xᵢ` is isomorphic to the fibre of `gᵢ` over `uᵢ`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_openImages_isZariskiCover`: the
  open subspace `X ∖ {x₁, …, xₙ}` together with the open images of the chosen neighborhoods is
  a Zariski covering of `X`.
* **Stacks 0BHC**, one theorem per property, in the namespace
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods`:
  `…isQuasiCompact_iff_forall_restrictionComponent`,
  `…isQuasiSeparated_iff_forall_restrictionComponent`,
  `…isSeparated_iff_forall_restrictionComponent`,
  `…isLocallyOfFinitePresentation_iff_forall_restrictionComponent`,
  `…isFinitePresentation_iff_forall_restrictionComponent`,
  `…isLocallyOfFiniteType_iff_forall_restrictionComponent`,
  `…isFiniteType_iff_forall_restrictionComponent`,
  `…isProper_iff_forall_restrictionComponent`,
  `…isIntegralHom_iff_forall_restrictionComponent`,
  `…isFinite_iff_forall_restrictionComponent`.

## Implementation notes

A point of an algebraic space over `S` is an equivalence class of sections over spectra of
fields, and the morphism it presents is `AlgebraicGeometry.Space.fieldMorphism` of a
representative. For the distinguished point of an elementary étale neighborhood the canonical
representative is the one used by `AlgebraicGeometry.Space.presheafPoint`, whose section is the
canonical morphism `Spec κ(uᵢ) ⟶ Uᵢ`; monicity of its composite with `Uᵢ ⟶ X` is the field
`ElementaryEtaleNeighborhood.mono_residueField` of the chosen neighborhood.

The fibre of a morphism over a point is the fibre product with the morphism the point presents,
as elsewhere in the development. Since `gᵢ` is literally the second projection of the fibre
product of `f` with `Uᵢ ⟶ X`, the isomorphism of fibres is the pasting isomorphism
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`; no hypothesis beyond the shape of the
morphisms is used, which is the sense in which the source's "clear because `uᵢ ⟶ xᵢ` is an
isomorphism" holds. Both fibres are algebraic spaces over `S`, and the isomorphism is produced
at that level through `CategoryTheory.ObjectProperty.isoMk`, the inclusion of a full
subcategory being fully faithful.

The source deduces 0BHC from Stacks 0BGZ, which compares the two sides of the base change of
Stacks 0BGY along a single étale morphism `V ⟶ W` carrying the preimage of a closed subspace
isomorphically onto it. For `n > 1` no single `Uᵢ` satisfies that hypothesis — the preimage of
`{x₁, …, xₙ}` in `Uᵢ` is only `{uᵢ}` — so the argument is run again here with the whole family
at once. The "only if" direction of each property is base-change stability along the Cartesian
square `…isPullback_restrictionComponent_obj`. The "if" direction of all ten runs through one
argument, the private `prop_of_prop_restrictionComponent`, whose four hypotheses are those of
the corresponding step for a single morphism in
`StacksFrontier/AlgebraicGeometry/Spaces/ModificationExcisionProperties.lean`: base change along
a Cartesian square of algebraic spaces, the property for isomorphisms, the surjective-étale
chart criterion and the Zariski criterion. The source's étale covering
`{X ∖ {x₁, …, xₙ} → X, U₁ → X, …, Uₙ → X}` is replaced by the Zariski covering of
`…exists_openImages_isZariskiCover` by `X ∖ {x₁, …, xₙ}` and the open images of the `Uᵢ`, since
the library states each property's locality as a Zariski criterion together with a scheme chart
criterion; the chart of the `i`th image is `Uᵢ` itself, which is already a scheme. The generic
transport lemmas that argument uses — `AlgebraicGeometry.Space.prop_comp_iso`,
`…prop_of_isPullback_of_isPullback` and `…prop_pullback_fst_of_snd`, for a property satisfying
`AlgebraicGeometry.Space.StableUnderAlgebraicBaseChange` — are imported from the file above,
and `…isPullback_homMk` from `Spaces.Morphisms.FiniteType`.

## References

* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
* [Stacks Project, Tag 0BGZ](https://stacks.math.columbia.edu/tag/0BGZ)
* [Stacks Project, Tag 0BHA](https://stacks.math.columbia.edu/tag/0BHA)
* [Stacks Project, Tag 0BHC](https://stacks.math.columbia.edu/tag/0BHC)
* [Stacks Project, Tag 0BHD](https://stacks.math.columbia.edu/tag/0BHD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace ClosedPointNeighborhoods

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {n : ℕ}
  (D : ClosedPointNeighborhoods B S hS n)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` on presheaves on the big fppf site exceeds the default limit
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_ModificationsAtClosedPointsProperties :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ModificationsAtClosedPointsProperties
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The residue field of the distinguished point of a neighborhood -/

/-- The canonical field-valued representative of the distinguished point `uᵢ` of the `i`th
chosen neighborhood: the residue field of `uᵢ`, with the canonical morphism to `Uᵢ`. -/
def residuePoint (i : Fin n) : FieldValuedPoint B S hS (D.neighborhoodSpace i).obj :=
  ⟨(D.neighborhood i).scheme.left.1.residueField (D.neighborhood i).point,
    (D.neighborhood i).residueField_contained,
    (D.neighborhood i).scheme.left.1.fromSpecResidueField (D.neighborhood i).point ≫
      (D.neighborhood i).scheme.hom.1,
    residueFieldMap B S hS (D.neighborhood i).scheme (D.neighborhood i).point
      (D.neighborhood i).residueField_contained⟩

/-- The canonical representative presents the distinguished point `uᵢ`. -/
theorem class_residuePoint (i : Fin n) :
    (D.residuePoint i).class B S hS (D.neighborhoodSpace i).obj = D.neighborhoodPoint i :=
  rfl

/-- The spectrum `Spec κ(uᵢ)` of the residue field of the distinguished point of the `i`th
chosen neighborhood, as an algebraic space over the base. -/
def residuePointSpace (i : Fin n) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (residueFieldObject B S hS (D.neighborhood i).scheme (D.neighborhood i).point
      (D.neighborhood i).residueField_contained),
    isAlgebraicSpace_yoneda B S hS _⟩

/-- The canonical morphism `Spec κ(uᵢ) ⟶ Uᵢ` presenting the distinguished point of the `i`th
chosen neighborhood. -/
def residuePointToNeighborhood (i : Fin n) : D.residuePointSpace i ⟶ D.neighborhoodSpace i :=
  ObjectProperty.homMk
    (yoneda.map (residueFieldMap B S hS (D.neighborhood i).scheme (D.neighborhood i).point
      (D.neighborhood i).residueField_contained))

/-- The canonical morphism `Spec κ(uᵢ) ⟶ X` presenting the chosen point `xᵢ`, obtained from
`Spec κ(uᵢ) ⟶ Uᵢ` by composing with the `i`th neighborhood. -/
def residuePointToSpace (i : Fin n) : D.residuePointSpace i ⟶ D.space :=
  D.residuePointToNeighborhood i ≫ D.toSpaceHom i

/-- The canonical morphism `Spec κ(uᵢ) ⟶ Uᵢ` of schemes over the base, with its source written
as the site object of the canonical representative of `uᵢ`. -/
def residuePointMap (i : Fin n) :
    (D.residuePoint i).siteObject B S hS (D.neighborhoodSpace i).obj ⟶
      (D.neighborhood i).scheme :=
  residueFieldMap B S hS (D.neighborhood i).scheme (D.neighborhood i).point
    (D.neighborhood i).residueField_contained

/-- The morphism `Spec κ(uᵢ) ⟶ Uᵢ` is the one presented by the canonical representative of the
distinguished point `uᵢ`. -/
theorem residuePointToNeighborhood_hom (i : Fin n) :
    (D.residuePointToNeighborhood i).hom =
      fieldMorphism B S hS (D.neighborhoodSpace i).obj (D.residuePoint i) :=
  ((Equiv.symm_apply_eq yonedaEquiv).2
    (yonedaEquiv_yoneda_map (D.residuePointMap i)).symm).symm

/-- The composite `Spec κ(uᵢ) ⟶ Uᵢ ⟶ X` is a monomorphism: this is one of the defining
properties of an elementary étale neighborhood, and it is what makes `uᵢ ⟶ xᵢ` an
isomorphism. -/
theorem mono_residuePointToSpace (i : Fin n) : Mono (D.residuePointToSpace i).hom :=
  (D.neighborhood i).mono_residueField

/-- The distinguished point `uᵢ` of the `i`th chosen neighborhood lies above the chosen
point `xᵢ`. -/
theorem pointsMap_toSpaceHom_neighborhoodPoint (i : Fin n) :
    pointsMap B S hS (D.neighborhoodSpace i).obj (D.toSpaceHom i).hom
        (D.neighborhoodPoint i) = D.point i :=
  (D.neighborhood i).map_point

/-! ### The fibres of a modification and of its restrictions -/

variable {D}

/-- The fibre `Y_{xᵢ}` over the chosen point `xᵢ` of a modification `f : Y ⟶ X` of `X` away
from `{x₁, …, xₙ}`. -/
def fibreAtPoint (M : D.modificationsAwayFromPoints) (i : Fin n) : AlgebraicSpaces B S hS :=
  ⟨pullback M.obj.hom (D.residuePointToSpace i).hom,
    isAlgebraicSpace_pullback B S hS M.obj.hom (D.residuePointToSpace i).hom M.property.1
      (D.residuePointSpace i).property D.space.property⟩

/-- The fibre `(Yᵢ)_{uᵢ}` over the distinguished point `uᵢ` of the restriction `gᵢ : Yᵢ ⟶ Uᵢ`
of a modification under the functor `F` of Stacks 0BHA. -/
def fibreAtNeighborhoodPoint (M : D.modificationsAwayFromPoints) (i : Fin n) :
    AlgebraicSpaces B S hS :=
  ⟨pullback ((D.restrictionComponent i).obj M).obj.hom (D.residuePointToNeighborhood i).hom,
    isAlgebraicSpace_pullback B S hS _ (D.residuePointToNeighborhood i).hom
      ((D.restrictionComponent i).obj M).property.1 (D.residuePointSpace i).property
      (D.neighborhoodSpace i).property⟩

/-- **Stacks 0BHD.** If `f : Y ⟶ X` corresponds to `gᵢ : Yᵢ ⟶ Uᵢ` under the functor `F` of
Stacks 0BHA, then `Y_{xᵢ} ≅ (Yᵢ)_{uᵢ}` as algebraic spaces: both are the fibre product of `f`
with the monomorphism `Spec κ(uᵢ) ⟶ X`. -/
@[stacks 0BHD "the fibres agree"]
def fibreAtPointIso (M : D.modificationsAwayFromPoints) (i : Fin n) :
    fibreAtPoint M i ≅ fibreAtNeighborhoodPoint M i :=
  ObjectProperty.isoMk _
    (pullbackLeftPullbackSndIso M.obj.hom (D.toSpaceHom i).hom
      (D.residuePointToNeighborhood i).hom).symm

/-! ### The Zariski covering by the open complement and the open images -/

variable (D)

/-- **The Zariski covering replacing the étale covering `{X ∖ {x₁, …, xₙ} → X, Uᵢ → X}`.** The
open subspace `X ∖ {x₁, …, xₙ}` together with the open images of the chosen neighborhoods is a
Zariski covering of `X`, and the `i`th image carries the surjective étale chart through which
`Uᵢ` factors. Covering holds because `xᵢ` is the image of the distinguished point `uᵢ`. -/
theorem exists_openImages_isZariskiCover :
    ∃ I : Fin n → Subfunctor D.space.obj, (∀ i, IsOpenSubspace B S hS (I i)) ∧
      (∃ q : ∀ i, (D.neighborhoodSpace i).obj ⟶ (I i).toFunctor,
        (∀ i, q i ≫ (I i).ι = (D.toSpaceHom i).hom) ∧
          (∀ i, IsSurjective B S hS (q i)) ∧ ∀ i, IsEtale B S hS (q i)) ∧
      IsZariskiCover B S hS (ULift.{u} (Option (Fin n)))
        (fun o ↦ Option.elim o.down D.openAwayFromPoints I) := by
  classical
  have hdata : ∀ i : Fin n, ∃ (I : Subfunctor D.space.obj)
      (q : (D.neighborhoodSpace i).obj ⟶ I.toFunctor), IsOpenSubspace B S hS I ∧
        q ≫ I.ι = (D.toSpaceHom i).hom ∧ IsSurjective B S hS q ∧ IsEtale B S hS q ∧
          Set.range (pointsMap B S hS I.toFunctor I.ι) =
            Set.range (pointsMap B S hS (D.neighborhoodSpace i).obj (D.toSpaceHom i).hom) := by
    intro i
    obtain ⟨I, q, hIopen, hq, hqsurj, hqetale, hIimage⟩ :=
      exists_isOpenSubspace_etaleImage B S hS D.space.property (D.neighborhood i).scheme
        (D.toSpaceHom i).hom
        (presheaf_etale_of_isEtale B S hS (D.neighborhood i).etale_toSpace)
    exact ⟨I, q, hIopen, hq,
      (presheafSurjective_iff_isSurjective_yoneda B S hS I.toFunctor hIopen.1
        (D.neighborhood i).scheme q).mp hqsurj,
      isEtale_of_presheaf_etale B S hS hqetale, hIimage⟩
  choose I q hIopen hq hqsurj hqetale hIimage using hdata
  refine ⟨I, hIopen, ⟨q, hq, hqsurj, hqetale⟩, ?_⟩
  have hopen : ∀ o : ULift.{u} (Option (Fin n)), IsOpenSubspace B S hS
      (Option.elim o.down D.openAwayFromPoints I) := by
    rintro ⟨o⟩
    cases o with
    | none => exact D.isOpenSubspace_openAwayFromPoints
    | some i => exact hIopen i
  refine (isZariskiCover_iff_iUnion_points B S hS D.space.obj D.space.property _ _ hopen).mpr ?_
  refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ?_
  by_cases hx : x ∈ Set.range D.point
  · obtain ⟨i, rfl⟩ := hx
    refine ⟨ULift.up (some i), ?_⟩
    have hmem : D.point i ∈
        Set.range (pointsMap B S hS (D.neighborhoodSpace i).obj (D.toSpaceHom i).hom) :=
      ⟨D.neighborhoodPoint i, D.pointsMap_toSpaceHom_neighborhoodPoint i⟩
    rw [← hIimage i] at hmem
    exact hmem
  · refine ⟨ULift.up none, ?_⟩
    have hmem : x ∈ Set.range (pointsMap B S hS D.openAwayFromPoints.toFunctor
        D.openAwayFromPoints.ι) := by
      rw [D.range_pointsMap_ι_openAwayFromPoints]
      exact hx
    exact hmem

/-! ### Comparison of the ten standard properties -/

variable {D}

/-- The restriction of a modification under the functor `F` of Stacks 0BHA is its base change
along the chosen neighborhood: the structure morphism of the `i`th component is the second
projection of the fibre product with `Uᵢ ⟶ X`. -/
theorem restrictionComponent_obj_hom (i : Fin n) (M : D.modificationsAwayFromPoints) :
    ((D.restrictionComponent i).obj M).obj.hom = pullback.snd M.obj.hom (D.toSpaceHom i).hom :=
  rfl

/-- The restriction of a modification under the functor `F` of Stacks 0BHA sits in a Cartesian
square over the modification. -/
theorem isPullback_restrictionComponent_obj (i : Fin n) (M : D.modificationsAwayFromPoints) :
    IsPullback (pullback.fst M.obj.hom (D.toSpaceHom i).hom)
      ((D.restrictionComponent i).obj M).obj.hom M.obj.hom (D.toSpaceHom i).hom :=
  IsPullback.of_hasPullback _ _

/-- A base-change stable property of morphisms of presheaves holds for each restriction of a
modification under the functor `F` of Stacks 0BHA as soon as it holds for the modification. -/
private theorem prop_restrictionComponent_of_prop
    {P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (hbc : StableUnderAlgebraicBaseChange B S hS P) (M : D.modificationsAwayFromPoints)
    (i : Fin n) (hf : P M.obj.hom) : P ((D.restrictionComponent i).obj M).obj.hom :=
  hbc M.property.1 D.space.property ((D.restrictionComponent i).obj M).property.1
    (D.neighborhoodSpace i).property (isPullback_restrictionComponent_obj i M) hf

/-- A property of morphisms of presheaves whose induced property on algebraic spaces is stable
under base change is stable under base change along Cartesian squares of algebraic spaces. -/
private theorem stableUnderAlgebraicBaseChange_of_algebraicSpaces
    {P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    [MorphismProperty.IsStableUnderBaseChange
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (φ : X ⟶ Y) => P φ.hom)] :
    StableUnderAlgebraicBaseChange B S hS P :=
  fun hF hG hF' hG' sq hk => MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun ⦃X Y : AlgebraicSpaces B S hS⦄ (φ : X ⟶ Y) => P φ.hom)
    (isPullback_homMk B S hS hF hG' hG hF' sq) hk

/-- **The "if" half of Stacks 0BHC, for an arbitrary property.** A property of morphisms of
presheaves which is stable under base change, holds for isomorphisms, can be checked on a
surjective étale scheme chart of the target and is Zariski local on the target holds for a
modification of `X` away from `{x₁, …, xₙ}` as soon as it holds for each of its restrictions
under the functor `F` of Stacks 0BHA. -/
private theorem prop_of_prop_restrictionComponent
    {P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (hbc : StableUnderAlgebraicBaseChange B S hS P)
    (hiso : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ G),
      IsAlgebraicSpace B S hS F → IsAlgebraicSpace B S hS G → IsIso k → P k)
    (hchart : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ G),
      IsAlgebraicSpace B S hS F → IsAlgebraicSpace B S hS G →
      ∀ (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ G), IsSurjective B S hS q →
        IsEtale B S hS q → P (pullback.snd k q) → P k)
    (hzar : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ G),
      IsAlgebraicSpace B S hS F → IsAlgebraicSpace B S hS G →
      ∀ (J : Type u) (Uj : J → Subfunctor G), IsZariskiCover B S hS J Uj →
        (∀ j, P (pullback.snd k (Uj j).ι)) → P k)
    (M : D.modificationsAwayFromPoints)
    (hh : ∀ i, P ((D.restrictionComponent i).obj M).obj.hom) :
    P M.obj.hom := by
  obtain ⟨I, hIopen, ⟨q, hq, hqsurj, hqetale⟩, hcover⟩ := D.exists_openImages_isZariskiCover
  have hX : IsAlgebraicSpace B S hS M.obj.left := M.property.1
  have hW₀ : IsOpenSubspace B S hS D.openAwayFromPoints :=
    D.isOpenSubspace_openAwayFromPoints
  have hoverAway : P (pullback.snd M.obj.hom D.openAwayFromPoints.ι) :=
    hiso _ (isAlgebraicSpace_pullback B S hS M.obj.hom D.openAwayFromPoints.ι hX hW₀.1
      D.space.property) hW₀.1 M.property.2
  have hoverI : ∀ i, P (pullback.snd M.obj.hom (I i).ι) := by
    intro i
    have hIalg : IsAlgebraicSpace B S hS (pullback M.obj.hom (I i).ι) :=
      isAlgebraicSpace_pullback B S hS M.obj.hom (I i).ι hX (hIopen i).1 D.space.property
    refine hchart _ hIalg (hIopen i).1 (D.neighborhood i).scheme (q i) (hqsurj i)
      (hqetale i) ?_
    have hbig : IsPullback
        (pullback.fst (pullback.snd M.obj.hom (I i).ι) (q i) ≫
          pullback.fst M.obj.hom (I i).ι)
        (pullback.snd (pullback.snd M.obj.hom (I i).ι) (q i)) M.obj.hom (q i ≫ (I i).ι) :=
      (IsPullback.of_hasPullback (pullback.snd M.obj.hom (I i).ι) (q i)).paste_horiz
        (IsPullback.of_hasPullback M.obj.hom (I i).ι)
    rw [hq i] at hbig
    exact prop_of_isPullback_of_isPullback hbc
      (isAlgebraicSpace_pullback B S hS M.obj.hom (D.toSpaceHom i).hom hX
        (D.neighborhoodSpace i).property D.space.property)
      (isAlgebraicSpace_pullback B S hS (pullback.snd M.obj.hom (I i).ι) (q i) hIalg
        (isAlgebraicSpace_yoneda B S hS (D.neighborhood i).scheme) (hIopen i).1)
      (D.neighborhoodSpace i).property (isPullback_restrictionComponent_obj i M) hbig (hh i)
  refine hzar _ hX D.space.property (ULift.{u} (Option (Fin n))) _ hcover ?_
  rintro ⟨o⟩
  cases o with
  | none => exact hoverAway
  | some i => exact hoverI i

variable (M : D.modificationsAwayFromPoints)

/-- **Stacks 0BHC, quasi-compactness.** A modification of `X` away from `{x₁, …, xₙ}` is
quasi-compact exactly when each of its restrictions under the functor `F` of Stacks 0BHA is. -/
@[stacks 0BHC "quasi-compactness"]
theorem isQuasiCompact_iff_forall_restrictionComponent :
    IsQuasiCompact B S hS M.obj.hom ↔
      ∀ i, IsQuasiCompact B S hS ((D.restrictionComponent i).obj M).obj.hom := by
  have hbc : StableUnderAlgebraicBaseChange B S hS (fun _ _ k => IsQuasiCompact B S hS k) :=
    fun _ _ _ _ sq hk => IsQuasiCompact.of_isPullback B S hS sq hk
  refine ⟨fun hf i => prop_restrictionComponent_of_prop hbc M i hf, fun hh => ?_⟩
  refine prop_of_prop_restrictionComponent hbc ?_ ?_ ?_ M hh
  · intro F G k _ _ hk
    have := hk
    exact isQuasiCompact_of_isClosedImmersion' B S hS (isClosedImmersion_of_isIso B S hS k)
  · intro F G k hF hG U q hqs hqe h
    refine ((isQuasiCompact_tfae B S hS hF hG k).out 4 1).mp (by
      exact ⟨U, q, hqs, hqe, prop_pullback_fst_of_snd hbc k q hF hG
        (isAlgebraicSpace_yoneda B S hS U) h⟩)
  · intro F G k hF hG J Uj hU h
    refine ((isQuasiCompact_tfae B S hS hF hG k).out 6 1).mp (by
      exact ⟨J, Uj, hU,
        fun j => prop_pullback_fst_of_snd hbc k (Uj j).ι hF hG (hU.1 j).1 (h j)⟩)

/-- **Stacks 0BHC, quasi-separatedness.** A modification of `X` away from `{x₁, …, xₙ}` is
quasi-separated exactly when each of its restrictions under the functor `F` of Stacks 0BHA
is. -/
@[stacks 0BHC "quasi-separatedness"]
theorem isQuasiSeparated_iff_forall_restrictionComponent :
    IsQuasiSeparated B S hS M.obj.hom ↔
      ∀ i, IsQuasiSeparated B S hS ((D.restrictionComponent i).obj M).obj.hom := by
  have hbc : StableUnderAlgebraicBaseChange B S hS (fun _ _ k => IsQuasiSeparated B S hS k) :=
    fun _ _ _ _ sq hk => (MorphismProperty.IsStableUnderBaseChange.diagonal
      (P := quasiCompactPresheafProperty B S hS)).of_isPullback sq hk
  refine ⟨fun hf i => prop_restrictionComponent_of_prop hbc M i hf, fun hh => ?_⟩
  refine prop_of_prop_restrictionComponent hbc ?_ ?_ ?_ M hh
  · intro F G k _ _ hk
    have := hk
    have : IsIso (pullback.diagonal k) := (pullback.isIso_diagonal_iff k).2 (IsIso.mono_of_iso k)
    exact isQuasiCompact_of_isClosedImmersion' B S hS
      (isClosedImmersion_of_isIso B S hS (pullback.diagonal k))
  · intro F G k hF hG U q hqs hqe h
    exact isQuasiSeparated_of_etaleChart B S hS hF
      ((presheafSurjective_iff_isSurjective_yoneda B S hS G hG U q).mpr hqs)
      (presheaf_etale_of_isEtale B S hS hqe) h
  · intro F G k hF _ J Uj hU h
    exact isQuasiSeparated_of_zariskiCover B S hS hF hU h

/-- **Stacks 0BHC, separatedness.** A modification of `X` away from `{x₁, …, xₙ}` is separated
exactly when each of its restrictions under the functor `F` of Stacks 0BHA is. -/
@[stacks 0BHC "separatedness"]
theorem isSeparated_iff_forall_restrictionComponent :
    IsSeparated B S hS M.obj.hom ↔
      ∀ i, IsSeparated B S hS ((D.restrictionComponent i).obj M).obj.hom := by
  have _hci : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hbc : StableUnderAlgebraicBaseChange B S hS (fun _ _ k => IsSeparated B S hS k) :=
    fun _ _ _ _ sq hk => (MorphismProperty.IsStableUnderBaseChange.diagonal
      (P := MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)))).of_isPullback sq hk
  refine ⟨fun hf i => prop_restrictionComponent_of_prop hbc M i hf, fun hh => ?_⟩
  refine prop_of_prop_restrictionComponent hbc ?_ ?_ ?_ M hh
  · intro F G k _ _ hk
    have := hk
    exact isSeparated_of_isIso B S hS k
  · intro F G k hF hG U q hqs hqe h
    exact isSeparated_of_etaleChart B S hS hF
      ((presheafSurjective_iff_isSurjective_yoneda B S hS G hG U q).mpr hqs)
      (presheaf_etale_of_isEtale B S hS hqe) h
  · intro F G k hF _ J Uj hU h
    exact isSeparated_of_zariskiCover B S hS hF hU h

/-- **Stacks 0BHC, local finite presentation.** A modification of `X` away from `{x₁, …, xₙ}`
is locally of finite presentation exactly when each of its restrictions under the functor `F`
of Stacks 0BHA is. -/
@[stacks 0BHC "local finite presentation"]
theorem isLocallyOfFinitePresentation_iff_forall_restrictionComponent :
    IsLocallyOfFinitePresentation B S hS M.obj.hom ↔
      ∀ i, IsLocallyOfFinitePresentation B S hS
        ((D.restrictionComponent i).obj M).obj.hom := by
  have _hsb := isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  have hbc : StableUnderAlgebraicBaseChange B S hS
      (fun _ _ k => IsLocallyOfFinitePresentation B S hS k) :=
    stableUnderAlgebraicBaseChange_of_algebraicSpaces
  refine ⟨fun hf i => prop_restrictionComponent_of_prop hbc M i hf, fun hh => ?_⟩
  refine prop_of_prop_restrictionComponent hbc ?_ ?_ ?_ M hh
  · intro F G k _ hG hk
    have := hk
    exact isLocallyOfFinitePresentation_of_isEtale B S hS (isEtale_of_isIso B S hS k)
  · intro F G k hF hG U q hqs hqe h
    refine ((isLocallyOfFinitePresentation_tfae B S hS hF hG k).out 5 1).mp (by
      exact ⟨U, q, hqs, hqe, prop_pullback_fst_of_snd hbc k q hF hG
        (isAlgebraicSpace_yoneda B S hS U) h⟩)
  · intro F G k hF hG J Uj hU h
    have hPB : ∀ j, IsAlgebraicSpace B S hS (pullback k (Uj j).ι) := fun j =>
      isAlgebraicSpace_pullback B S hS k (Uj j).ι hF (hU.1 j).1 hG
    refine ((isLocallyOfFinitePresentation_tfae B S hS hF hG k).out 9 1).mp (by
      refine ⟨J, Uj, fun _ => PUnit.{u + 1}, fun _ _ => ⊤, hU,
        fun j => isZariskiCover_top (hPB j), fun j _ => ?_⟩
      exact isLocallyOfFinitePresentation_comp B S hS (isOpenSubspace_top (hPB j)).1 (hPB j)
        (hU.1 j).1 _ _
        (isLocallyOfFinitePresentation_of_isEtale B S hS (isEtale_of_isIso B S hS _))
        (h j))

/-- **Stacks 0BHC, local finite type.** A modification of `X` away from `{x₁, …, xₙ}` is
locally of finite type exactly when each of its restrictions under the functor `F` of
Stacks 0BHA is. -/
@[stacks 0BHC "local finite type"]
theorem isLocallyOfFiniteType_iff_forall_restrictionComponent :
    IsLocallyOfFiniteType B S hS M.obj.hom ↔
      ∀ i, IsLocallyOfFiniteType B S hS ((D.restrictionComponent i).obj M).obj.hom := by
  have _hsb := isLocallyOfFiniteType_isStableUnderBaseChange B S hS
  have hbc : StableUnderAlgebraicBaseChange B S hS (fun _ _ k => IsLocallyOfFiniteType B S hS k) :=
    stableUnderAlgebraicBaseChange_of_algebraicSpaces
  refine ⟨fun hf i => prop_restrictionComponent_of_prop hbc M i hf, fun hh => ?_⟩
  refine prop_of_prop_restrictionComponent hbc ?_ ?_ ?_ M hh
  · intro F G k _ hG hk
    have := hk
    exact isLocallyOfFiniteType_of_isEtale B S hS hG (isEtale_of_isIso B S hS k)
  · intro F G k hF hG U q hqs hqe h
    refine ((isLocallyOfFiniteType_tfae B S hS hF hG k).out 5 1).mp (by
      exact ⟨U, q, hqs, hqe, prop_pullback_fst_of_snd hbc k q hF hG
        (isAlgebraicSpace_yoneda B S hS U) h⟩)
  · intro F G k hF hG J Uj hU h
    refine ((isLocallyOfFiniteType_tfae B S hS hF hG k).out 9 1).mp (by
      refine ⟨J, Uj, hU, fun j => ?_⟩
      have hsq := Subfunctor.isPullback_preimage k (Uj j)
      have hP : IsAlgebraicSpace B S hS ((Uj j).preimage k).toFunctor :=
        (isAlgebraicSpace_pullback B S hS (Uj j).ι k (hU.1 j).1 hF hG).of_iso
          hsq.isoPullback.symm
      refine ⟨PUnit.{u + 1}, fun _ => ⊤, isZariskiCover_top hP, fun _ => ?_⟩
      refine isLocallyOfFiniteType_comp B S hS (isOpenSubspace_top hP).1 hP (hU.1 j).1 _ _
        (isLocallyOfFiniteType_of_isEtale B S hS hP (isEtale_of_isIso B S hS _)) ?_
      exact prop_of_isPullback_of_isPullback hbc
        (isAlgebraicSpace_pullback B S hS k (Uj j).ι hF (hU.1 j).1 hG) hP (hU.1 j).1
        (IsPullback.of_hasPullback k (Uj j).ι) hsq.flip (h j))

/-- **Stacks 0BHC, finite type.** A modification of `X` away from `{x₁, …, xₙ}` is of finite
type exactly when each of its restrictions under the functor `F` of Stacks 0BHA is. -/
@[stacks 0BHC "finite type"]
theorem isFiniteType_iff_forall_restrictionComponent :
    IsFiniteType B S hS M.obj.hom ↔
      ∀ i, IsFiniteType B S hS ((D.restrictionComponent i).obj M).obj.hom := by
  have hlft := isLocallyOfFiniteType_iff_forall_restrictionComponent M
  have hqc := isQuasiCompact_iff_forall_restrictionComponent M
  exact ⟨fun hf i => ⟨hlft.mp hf.1 i, hqc.mp hf.2 i⟩,
    fun hh => ⟨hlft.mpr fun i => (hh i).1, hqc.mpr fun i => (hh i).2⟩⟩

/-- **Stacks 0BHC, finite presentation.** A modification of `X` away from `{x₁, …, xₙ}` is of
finite presentation exactly when each of its restrictions under the functor `F` of
Stacks 0BHA is. -/
@[stacks 0BHC "finite presentation"]
theorem isFinitePresentation_iff_forall_restrictionComponent :
    IsFinitePresentation B S hS M.obj.hom ↔
      ∀ i, IsFinitePresentation B S hS ((D.restrictionComponent i).obj M).obj.hom := by
  have hlfp := isLocallyOfFinitePresentation_iff_forall_restrictionComponent M
  have hqc := isQuasiCompact_iff_forall_restrictionComponent M
  have hqs := isQuasiSeparated_iff_forall_restrictionComponent M
  exact ⟨fun hf i => ⟨hlfp.mp hf.1 i, hqc.mp hf.2.1 i, hqs.mp hf.2.2 i⟩,
    fun hh => ⟨hlfp.mpr fun i => (hh i).1, hqc.mpr fun i => (hh i).2.1,
      hqs.mpr fun i => (hh i).2.2⟩⟩

/-- **Stacks 0BHC, properness.** A modification of `X` away from `{x₁, …, xₙ}` is proper
exactly when each of its restrictions under the functor `F` of Stacks 0BHA is. -/
@[stacks 0BHC "properness"]
theorem isProper_iff_forall_restrictionComponent :
    IsProper B S hS M.obj.hom ↔
      ∀ i, IsProper B S hS ((D.restrictionComponent i).obj M).obj.hom := by
  have hbc : StableUnderAlgebraicBaseChange B S hS (fun _ _ k => IsProper B S hS k) :=
    stableUnderAlgebraicBaseChange_of_algebraicSpaces
  refine ⟨fun hf i => prop_restrictionComponent_of_prop hbc M i hf, fun hh => ?_⟩
  refine prop_of_prop_restrictionComponent hbc ?_ ?_ ?_ M hh
  · intro F G k hF hG hk
    have := hk
    exact isProper_of_isClosedImmersion B S hS hF hG k (isClosedImmersion_of_isIso B S hS k)
  · intro F G k hF hG U q hqs hqe h
    refine ((isProper_tfae B S hS hF hG k).out 4 1).mp (by
      exact ⟨U, q, hqs, hqe, prop_pullback_fst_of_snd hbc k q hF hG
        (isAlgebraicSpace_yoneda B S hS U) h⟩)
  · intro F G k hF hG J Uj hU h
    refine ((isProper_tfae B S hS hF hG k).out 5 1).mp (by
      exact ⟨J, Uj, hU,
        fun j => prop_pullback_fst_of_snd hbc k (Uj j).ι hF hG (hU.1 j).1 (h j)⟩)

/-- **Stacks 0BHC, integrality.** A modification of `X` away from `{x₁, …, xₙ}` is integral
exactly when each of its restrictions under the functor `F` of Stacks 0BHA is. -/
@[stacks 0BHC "integrality"]
theorem isIntegralHom_iff_forall_restrictionComponent :
    IsIntegralHom B S hS M.obj.hom ↔
      ∀ i, IsIntegralHom B S hS ((D.restrictionComponent i).obj M).obj.hom := by
  have hbc : StableUnderAlgebraicBaseChange B S hS (fun _ _ k => IsIntegralHom B S hS k) :=
    fun _ _ _ _ sq hk => isIntegralHom_of_isPullback B S hS sq hk
  refine ⟨fun hf i => prop_restrictionComponent_of_prop hbc M i hf, fun hh => ?_⟩
  refine prop_of_prop_restrictionComponent hbc ?_ ?_ ?_ M hh
  · intro F G k _ _ hk
    have := hk
    exact isIntegralHom_of_isClosedImmersion B S hS k (isClosedImmersion_of_isIso B S hS k)
  · intro F G k hF hG U q hqs hqe h
    exact isIntegralHom_of_surjectiveEtaleChart B S hS hF hG k hqs hqe h
  · intro F G k hF hG J Uj hU h
    exact (isIntegralHom_iff_zariskiCover B S hS k hF hG).mpr ⟨J, Uj, hU, h⟩

/-- **Stacks 0BHC, finiteness.** A modification of `X` away from `{x₁, …, xₙ}` is finite
exactly when each of its restrictions under the functor `F` of Stacks 0BHA is. -/
@[stacks 0BHC "finiteness"]
theorem isFinite_iff_forall_restrictionComponent :
    IsFinite B S hS M.obj.hom ↔
      ∀ i, IsFinite B S hS ((D.restrictionComponent i).obj M).obj.hom := by
  have hbc : StableUnderAlgebraicBaseChange B S hS (fun _ _ k => IsFinite B S hS k) :=
    fun _ _ _ _ sq hk => isFinite_of_isPullback B S hS sq hk
  refine ⟨fun hf i => prop_restrictionComponent_of_prop hbc M i hf, fun hh => ?_⟩
  refine prop_of_prop_restrictionComponent hbc ?_ ?_ ?_ M hh
  · intro F G k _ _ hk
    have := hk
    exact isFinite_of_isClosedImmersion B S hS k (isClosedImmersion_of_isIso B S hS k)
  · intro F G k hF hG U q hqs hqe h
    exact isFinite_of_surjectiveEtaleChart B S hS hF hG k hqs hqe h
  · intro F G k hF hG J Uj hU h
    exact (isFinite_iff_zariskiCover B S hS k hF hG).mpr ⟨J, Uj, hU, h⟩

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
