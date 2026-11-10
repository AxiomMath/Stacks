module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.AlgebraicGeometry.Quot.CartesianFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.SpacesDefoThickeningTower
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedClosedSubspaceIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtInfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AlgebraExtensionEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FirstOrderAlgebraExtension
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.TangentSpace.Functor

/-!
# The first-order thickening of a deformation of a proper flat algebraic space

Let `x₀ = (X₀ ⟶ Spec k)` be an object of `Spaces'_{fp, flat, proper}` over `Spec k`, and let
`x = (X' ⟶ Spec A)` be a deformation of `x₀` over an object `A` of `𝒞_Λ` whose maximal ideal
has square zero (for instance `A = k[V]`). The arrow `x₀ ⟶ x` lies over the closed immersion
`Spec k ⟶ Spec A`, which is then a square-zero closed immersion of the big fppf site, and the
inverse image `Z = X' ×_{Spec A} Spec k` of `Spec k` in `X'` is a first-order thickening
`Z ⊆ X'`. Because `X' ⟶ Spec A` is flat, the conormal module of `Z ⊆ X'` is the pullback of
the conormal module of `Spec k ⊆ Spec A` (the flat clause of [Stacks Project, Tag 04CQ]), and
`𝒪_{X'}` restricted to `Z` is an extension of `𝒪_Z` by that pullback.

This is the geometric input of the proof of [Stacks Project, Tag 0D1K]: the identification
of first-order deformations of `X₀` over `k[V]` with extensions of `𝒪_{X₀}` by `𝒪_{X₀} ⊗_k V`
(the discussion of [Stacks Project, Tag 0D17]).

## Main results

* `Deformation.Artin.isSquareZeroClosedImmersion_map_arrow`: the arrow of a deformation over
  an algebra with square-zero maximal ideal lies over a square-zero closed immersion.
* `AlgebraicGeometry.Space.deformationThickening`: the closed subspace `Z ⊆ X'` attached to a
  deformation of a proper flat algebraic space, with
  `AlgebraicGeometry.Space.isFirstOrderThickening_deformationThickening`.
* `AlgebraicGeometry.Space.deformationAlgebraExtension`: the extension of `𝒪_Z` by the
  pullback of the conormal module of `Spec k ⊆ Spec A`.

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v w

namespace Deformation.Artin

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {iΛ : Spec (.of Λ) ⟶ S}
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) {x₀ : X}
  {hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

/-- The residue map of an object of `𝒞_Λ` is surjective. -/
theorem residueMap_surjective' (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Function.Surjective (residueMap A) :=
  A.residueEquiv.surjective.comp IsLocalRing.residue_surjective

/-- The base morphism of the arrow of a deformation is the spectrum of the residue map, up to
the identifications of the bases. -/
private theorem left_map_arrow (x : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀) :
    ((p ⋙ Over.post B.inclusion).map x.arrow).left =
      eqToHom (congrArg Over.left hx₀) ≫ Spec.map (CommRingCat.ofHom (residueMap x.algebra)) ≫
        eqToHom (congrArg Over.left x.base).symm := by
  rw [← x.arrow_base]
  simp only [Functor.comp_map, Over.post_map, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  rw [eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- **The arrow of a deformation over an algebra with square-zero residue kernel lies over a
square-zero closed immersion.** The arrow `x₀ ⟶ x` of a deformation over `A` lies over
`Spec k ⟶ Spec A`, the spectrum of the residue map; when the kernel of the residue map squares
to zero, this is a square-zero closed immersion of the big fppf site. -/
theorem isSquareZeroClosedImmersion_map_arrow
    (x : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (hsq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥) :
    Space.IsSquareZeroClosedImmersion B S hS (p.map x.arrow) := by
  refine Space.isSquareZeroClosedImmersion_of_specMap B S hS
    (CommRingCat.ofHom (residueMap x.algebra)) (residueMap_surjective' x.algebra) hsq _ _ _
    (eqToIso (congrArg Over.left hx₀)) (eqToIso (congrArg Over.left x.base)) ?_
  exact left_map_arrow p x

/-- **A retraction of `Spec k ⟶ Spec A` from a section of the residue map.** A ring map
`σ : k ⟶ A` under `Λ` gives a morphism `Spec A ⟶ Spec k` of the big fppf site from the base of
a deformation over `A` to the base of `x₀`. -/
def baseRetraction (x : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (σ : k →+* x.algebra) (hσΛ : σ.comp (algebraMap Λ k) = algebraMap Λ x.algebra) :
    p.obj x.point ⟶ p.obj x₀ :=
  (Over.post B.inclusion).preimage (eqToHom x.base ≫
    Over.homMk (V := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
      (Spec.map (CommRingCat.ofHom σ)) (by
      change Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
        Spec.map (CommRingCat.ofHom (algebraMap Λ x.algebra)) ≫ iΛ
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hσΛ]) ≫
    eqToHom hx₀.symm)

/-- The retraction attached to a section of the residue map is a retraction of the arrow of
the deformation. -/
theorem map_arrow_comp_baseRetraction (x : DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (σ : k →+* x.algebra) (hσΛ : σ.comp (algebraMap Λ k) = algebraMap Λ x.algebra)
    (hσ : (residueMap x.algebra).comp σ = RingHom.id k) :
    p.map x.arrow ≫ baseRetraction p x σ hσΛ = 𝟙 _ := by
  apply (Over.post B.inclusion).map_injective
  rw [Functor.map_comp, baseRetraction, Functor.map_preimage, CategoryTheory.Functor.map_id]
  ext1
  change ((p ⋙ Over.post B.inclusion).map x.arrow).left ≫ _ = _
  rw [left_map_arrow]
  simp only [Over.comp_left, Over.eqToHom_left, Over.homMk_left, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Over.id_left]
  rw [← Category.assoc (Spec.map _), ← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ]
  simp

/-! ### The algebras `k[V]` -/

section SquareZero

/-- The right action of `k` on a `k`-module, the one through which `k[V]` is formed. -/
local instance (M : ModuleCat.{u} k) : Module kᵐᵒᵖ M :=
  Module.oppositeOfCommSemiring k M

local instance (M : ModuleCat.{u} k) : IsCentralScalar k M :=
  Module.isCentralScalar_oppositeOfCommSemiring k M

variable (Λ k) in
/-- The residue kernel of `k[V]` squares to zero. -/
theorem ker_residueMap_sq_artinianSquareZero (V : FGModuleCat.{u} k) :
    RingHom.ker (residueMap ((artinianSquareZeroExtensionFunctor Λ k).obj V)) ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  have hx' : TrivSqZeroExt.fst (R := k) (M := V.obj) x = 0 := hx
  have hy' : TrivSqZeroExt.fst (R := k) (M := V.obj) y = 0 := hy
  change x * y = 0
  refine TrivSqZeroExt.ext ?_ ?_
  · exact (TrivSqZeroExt.fst_mul _ _).trans (by rw [hx', zero_mul]; rfl)
  · refine (TrivSqZeroExt.snd_mul _ _).trans ?_
    simp only [hx', hy', zero_smul, MulOpposite.op_zero, add_zero]
    rfl

variable (Λ k) in
/-- The inclusion `k ⟶ k[V]` of constants. -/
def squareZeroSection (V : FGModuleCat.{u} k) :
    k →+* ((artinianSquareZeroExtensionFunctor Λ k).obj V) where
  toFun a := (TrivSqZeroExt.inl a :
    TrivSqZeroExt k ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V))
  map_one' := rfl
  map_zero' := rfl
  map_add' a b := (TrivSqZeroExt.inl_add (M := (forget₂ (FGModuleCat.{u} k)
    (ModuleCat.{u} k)).obj V) a b)
  map_mul' a b := (TrivSqZeroExt.inl_mul (M := (forget₂ (FGModuleCat.{u} k)
    (ModuleCat.{u} k)).obj V) a b)

theorem squareZeroSection_comp_algebraMap (V : FGModuleCat.{u} k) :
    (squareZeroSection Λ k V).comp (algebraMap Λ k) =
      algebraMap Λ ((artinianSquareZeroExtensionFunctor Λ k).obj V) :=
  RingHom.ext fun _ => rfl

theorem residueMap_comp_squareZeroSection (V : FGModuleCat.{u} k) :
    (residueMap ((artinianSquareZeroExtensionFunctor Λ k).obj V)).comp
      (squareZeroSection Λ k V) = RingHom.id k :=
  RingHom.ext fun _ => rfl

end SquareZero

end Deformation.Artin


namespace AlgebraicGeometry.Space

open Deformation.Artin

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {y₀ : CartesianProperFlatSpaces B S hS}
  {hy₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj y₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  (x : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) y₀ hy₀)

/-- The total space `X'` of a deformation `X' ⟶ Spec A` of a proper flat algebraic space. -/
abbrev deformationSpace : AlgebraicSpaces B S hS :=
  x.point.obj.obj.left

/-- The structure morphism `X' ⟶ Spec A` of a deformation, as a morphism of algebraic spaces
into the algebraic space represented by the base. -/
abbrev deformationStructureMap :
    deformationSpace B S hS x ⟶
      (schemeSpaceFunctor B S hS).obj ((cartesianProperFlatProjection B S hS).obj x.point) :=
  commaHomAsSpaceMap x.point.obj.obj

/-- The structure morphism of a deformation is flat. -/
theorem isFlat_deformationStructureMap : IsFlat B S hS (deformationStructureMap B S hS x).hom :=
  x.point.obj.property.2.1

variable (hsq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥)

/-- **The closed fibre of a deformation, as a closed subspace of its total space.** For a
deformation `X' ⟶ Spec A` over an algebra whose residue kernel squares to zero, the inverse
image `X' ×_{Spec A} Spec k` of the closed point `Spec k ⊆ Spec A`. -/
abbrev deformationThickening : ClosedSubspaces B S hS (deformationSpace B S hS x).1 :=
  preimageSubspace B S hS (deformationStructureMap B S hS x)
    (squareZeroSubspace B S hS _
      (isSquareZeroClosedImmersion_map_arrow (cartesianProperFlatProjection B S hS) x hsq))

/-- The closed fibre of a deformation over an algebra with square-zero residue kernel is a
first-order thickening of its total space. -/
theorem isFirstOrderThickening_deformationThickening :
    IsFirstOrderThickening B S hS (deformationSpace B S hS x)
      (deformationThickening B S hS x hsq).1 :=
  isFirstOrderThickening_preimage_squareZeroSubspace B S hS _
    (isSquareZeroClosedImmersion_map_arrow (cartesianProperFlatProjection B S hS) x hsq)
    (deformationStructureMap B S hS x)

/-- **The extension of a deformation.** For a deformation `X' ⟶ Spec A` over an algebra with
square-zero residue kernel, with closed fibre `Z = X' ×_{Spec A} Spec k ⊆ X'` and projection
`f : Z ⟶ Spec k`, and for any morphism `g : X' ⟶ Y`, the inverse image `i^{-1}𝒪_{X'}` is an
extension of `(i ≫ g)^{-1}𝒪_Y`-algebras of `𝒪_Z` by `f^*𝒞_{Spec k/Spec A}`: the extension of
the first-order thickening `Z ⊆ X'` with its kernel identified, by flatness of `X' ⟶ Spec A`
and the flat clause of Stacks 04CQ, with the pullback of the conormal module of the base. -/
def deformationAlgebraExtension {Y : AlgebraicSpaces B S hS}
    (g : deformationSpace B S hS x ⟶ Y) :
    Deformation.AlgebraExtension
      (J := SmallEtale.topology B S hS (deformationThickening B S hS x hsq).1.toFunctor)
      (structureSharpInverseImage B S hS
        (subspaceInclusion B S hS _ (deformationThickening B S hS x hsq) ≫ g))
      ((modulePullback B S hS (preimageProjection B S hS (deformationStructureMap B S hS x)
          (squareZeroSubspace B S hS _
            (isSquareZeroClosedImmersion_map_arrow (cartesianProperFlatProjection B S hS) x
              hsq)))).obj
        (conormalModule B S hS _ (squareZeroSubspace B S hS _
          (isSquareZeroClosedImmersion_map_arrow (cartesianProperFlatProjection B S hS) x
            hsq)))) :=
  haveI := isIso_conormalMap_preimage_squareZeroSubspace B S hS _
    (isSquareZeroClosedImmersion_map_arrow (cartesianProperFlatProjection B S hS) x hsq)
    (deformationStructureMap B S hS x) (isFlat_deformationStructureMap B S hS x)
  (firstOrderAlgebraExtension B S hS (deformationThickening B S hS x hsq)
      (isFirstOrderThickening_deformationThickening B S hS x hsq) g).transportKernel
    (asIso (conormalMap B S hS (deformationThickening B S hS x hsq) _
      (deformationStructureMap B S hS x) _
      (conormalEtaleRestrictionSquare B S hS (deformationStructureMap B S hS x) _))).symm

/-- The underlying comma morphism `x₀ ⟶ x` of the arrow of a deformation, and the space map
`X₀ ⟶ X'` it carries. -/
abbrev deformationArrow : y₀.obj.obj ⟶ x.point.obj.obj :=
  x.arrow.1.hom

/-- The arrow of a deformation is strongly cartesian over the base. -/
theorem isStronglyCartesian_deformationArrow :
    (spacesProjection B S hS).IsStronglyCartesian (deformationArrow B S hS x).right
      (deformationArrow B S hS x) :=
  x.arrow.2

/-- **The closed fibre of a deformation is the space it deforms.** The fibre square of the arrow
`x₀ ⟶ x` and the inverse-image square of the closed fibre are both fibre products of
`X' ⟶ Spec A` and `Spec k ⟶ Spec A`, so the space `X₀` of `x₀` is identified with the closed
fibre, compatibly with the maps into `X'`. -/
def deformationThickeningIsoPresheaf :
    y₀.obj.obj.left.obj ≅ (deformationThickening B S hS x hsq).1.toFunctor := by
  let i := (cartesianProperFlatProjection B S hS).map x.arrow
  have hi := isSquareZeroClosedImmersion_map_arrow (cartesianProperFlatProjection B S hS) x hsq
  have hA := (isPullback_hom_of_isStronglyCartesian B S hS (deformationArrow B S hS x)
    (isStronglyCartesian_deformationArrow B S hS x)).flip
  have hB := isPullback_preimageSubspace B S hS (deformationStructureMap B S hS x)
    (squareZeroSubspace B S hS i hi)
  have key : (rangeIsoPresheaf B S hS i hi.1).inv ≫ yoneda.map i =
      (Subfunctor.range (yoneda.map i)).ι := by
    rw [Iso.inv_comp_eq, rangeIsoPresheaf_hom, Subfunctor.toRange_ι]
  have hB' : IsPullback (deformationThickening B S hS x hsq).1.ι
      ((preimageProjection B S hS (deformationStructureMap B S hS x)
        (squareZeroSubspace B S hS i hi)).hom ≫ (rangeIsoPresheaf B S hS i hi.1).inv)
      (deformationStructureMap B S hS x).hom (yoneda.map i) :=
    hB.of_iso (Iso.refl _) (Iso.refl _) (rangeIsoPresheaf B S hS i hi.1).symm
      (Iso.refl _) (Category.id_comp _).symm (Category.id_comp _).symm
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id]; exact key.symm)
  exact hA.isoIsPullback _ _ hB'

/-- The identification of the space of `x₀` with the closed fibre of a deformation is
compatible with the maps into the total space `X'`. -/
theorem deformationThickeningIsoPresheaf_hom_ι :
    (deformationThickeningIsoPresheaf B S hS x hsq).hom ≫ (deformationThickening B S hS x hsq).1.ι =
      (deformationArrow B S hS x).left.hom :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- **The closed fibre of a deformation is the space it deforms**, as an isomorphism of algebraic
spaces. -/
def deformationThickeningIso :
    y₀.obj.obj.left ≅ (⟨(deformationThickening B S hS x hsq).1.toFunctor,
      (deformationThickening B S hS x hsq).2.1⟩ : AlgebraicSpaces B S hS) :=
  (ObjectProperty.fullyFaithfulι _).preimageIso (deformationThickeningIsoPresheaf B S hS x hsq)

/-- The identification of the space of `x₀` with the closed fibre, followed by the inclusion of
the closed fibre, is the map `X₀ ⟶ X'` of the arrow of the deformation. -/
theorem deformationThickeningIso_hom_comp_subspaceInclusion :
    (deformationThickeningIso B S hS x hsq).hom ≫
        subspaceInclusion B S hS _ (deformationThickening B S hS x hsq) =
      (deformationArrow B S hS x).left := by
  apply ObjectProperty.hom_ext
  exact deformationThickeningIsoPresheaf_hom_ι B S hS x hsq

/-! ### The extension on the space of `x₀` -/

/-- The structure morphism `X₀ ⟶ Spec k` of the object `x₀` being deformed. -/
abbrev baseStructureMap :
    y₀.obj.obj.left ⟶
      (schemeSpaceFunctor B S hS).obj ((cartesianProperFlatProjection B S hS).obj y₀) :=
  commaHomAsSpaceMap y₀.obj.obj

variable {x} (r : (cartesianProperFlatProjection B S hS).obj x.point ⟶
    (cartesianProperFlatProjection B S hS).obj y₀)
  (hr : (cartesianProperFlatProjection B S hS).map x.arrow ≫ r = 𝟙 _)

/-- The composite `X' ⟶ Spec A ⟶ Spec k` of the structure morphism of a deformation with a
retraction `r` of `Spec k ⟶ Spec A`. -/
abbrev deformationRetractedStructureMap :
    deformationSpace B S hS x ⟶
      (schemeSpaceFunctor B S hS).obj ((cartesianProperFlatProjection B S hS).obj y₀) :=
  deformationStructureMap B S hS x ≫ (schemeSpaceFunctor B S hS).map r

include hr in
/-- Restricted to `X₀` through the closed fibre, the retracted structure morphism of a
deformation is the structure morphism of `x₀`. -/
theorem deformationThickeningIso_hom_comp_retractedStructureMap :
    (deformationThickeningIso B S hS x hsq).hom ≫
        (subspaceInclusion B S hS _ (deformationThickening B S hS x hsq) ≫
          deformationRetractedStructureMap B S hS r) =
      baseStructureMap B S hS (y₀ := y₀) := by
  rw [← Category.assoc, deformationThickeningIso_hom_comp_subspaceInclusion]
  have hw : (deformationArrow B S hS x).left ≫ deformationStructureMap B S hS x =
      baseStructureMap B S hS (y₀ := y₀) ≫
        (schemeSpaceFunctor B S hS).map ((cartesianProperFlatProjection B S hS).map x.arrow) := by
    apply ObjectProperty.hom_ext
    exact (deformationArrow B S hS x).w
  rw [← Category.assoc, hw, Category.assoc, ← Functor.map_comp, hr,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The extension of a deformation, on the space it deforms.** For a deformation `X' ⟶ Spec A`
of `x₀ = (X₀ ⟶ Spec k)` over an algebra with square-zero residue kernel, and a retraction `r` of
`Spec k ⟶ Spec A`, the structure sheaf of `X'` read on the small étale site of `X₀` (through the
closed fibre `Z ≅ X₀`) is an extension of `f₀⁻¹𝒪_{Spec k}`-algebras of `𝒪_{X₀}`, `f₀` the
structure morphism of `x₀`; its ideal is the restriction to `X₀` of the pullback of the conormal
module of `Spec k ⊆ Spec A`. -/
def deformationBaseExtension :
    Deformation.AlgebraExtension (J := SmallEtale.topology B S hS y₀.obj.obj.left.1)
      (structureSharpInverseImage B S hS (baseStructureMap B S hS (y₀ := y₀)))
      ((etaleRestrictionModule B S hS (deformationThickeningIso B S hS x hsq).hom
        (isEtale_hom_of_iso B S hS _)).obj
        ((modulePullback B S hS (preimageProjection B S hS (deformationStructureMap B S hS x)
          (squareZeroSubspace B S hS _
            (isSquareZeroClosedImmersion_map_arrow (cartesianProperFlatProjection B S hS) x
              hsq)))).obj
        (conormalModule B S hS _ (squareZeroSubspace B S hS _
          (isSquareZeroClosedImmersion_map_arrow (cartesianProperFlatProjection B S hS) x
            hsq))))) :=
  castBase B S hS (deformationThickeningIso_hom_comp_retractedStructureMap B S hS hsq r hr)
    ((etaleRestrictionFunctor B S hS (deformationThickeningIso B S hS x hsq).hom
      (isEtale_hom_of_iso B S hS _) _ _).obj
      (deformationAlgebraExtension B S hS x hsq (deformationRetractedStructureMap B S hS r)))

end AlgebraicGeometry.Space

end
