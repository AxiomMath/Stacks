module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# The points in a fibre of a cartesian diagram of schemes

Let `D` be a cartesian square of algebraic spaces over `S` as in Tag 0AC1, with corners `W`,
`Z`, `X`, `Y`, and suppose that `X`, `Y` and `Z` are *schemes*, that is, that the three
presheaves are represented by objects of the big fppf site compatibly with the two morphisms
to `Y`. The fourth corner is then represented too, by the fibre product of schemes, and the
set of Tag 0AC2 attached to two points `x` and `z` with a common image `y` is in bijection
with the spectrum of `κ(x) ⊗_{κ(y)} κ(z)`.

Consequently that set is finite as soon as one of the two residue-field extensions
`κ(y) ⊂ κ(x)`, `κ(y) ⊂ κ(z)` is finite, because then the tensor product is an Artinian ring;
and that happens in particular when `g` is quasi-finite at `z`.

## Main definitions

* `AlgebraicGeometry.Space.pointsEquivOfIso` transports the point set of Tag 03BU along an
  isomorphism of presheaves.
* `AlgebraicGeometry.Space.PointsFibresDiagram.SchemeRepresentation` records a representation
  of the three non-pullback corners of a diagram of Tag 0AC1 by site objects.
* `AlgebraicGeometry.Space.PointsFibresDiagram.SchemePointsPresentation` records bijections
  identifying the four point sets of a diagram of Tag 0AC1 with the point sets of a cartesian
  square of schemes, compatibly with all four morphisms.
* `AlgebraicGeometry.Space.PointsFibresDiagram.schemePointsPresentation` constructs the
  presentation determined by a representation.
* `AlgebraicGeometry.Space.fibreSpectrumEquiv` is the bijection of Tag 0AC3 between the set
  of Tag 0AC2 and the spectrum of the residue-field tensor product.

## Main results

* `AlgebraicGeometry.Space.fibreSpectrumEquiv_symm_apply` identifies the inverse bijection
  with the canonical map `AlgebraicGeometry.Scheme.Pullback.Triplet.SpecTensorTo`.
* `AlgebraicGeometry.Space.finite_fibrePoints_of_finite_residueField_left` and
  `AlgebraicGeometry.Space.finite_fibrePoints_of_finite_residueField_right` are the two
  finiteness criteria.
* `AlgebraicGeometry.Space.finite_fibrePoints_of_quasiFiniteAt` is the quasi-finite case.

## References

* [Stacks Project, Tag 0AC3](https://stacks.math.columbia.edu/tag/0AC3)
* [Stacks Project, Tag 0AC1](https://stacks.math.columbia.edu/tag/0AC1)
* [Stacks Project, Tag 0AC2](https://stacks.math.columbia.edu/tag/0AC2)
* [Stacks Project, Tag 01JT](https://stacks.math.columbia.edu/tag/01JT)
* [Stacks Project, Tag 01TG](https://stacks.math.columbia.edu/tag/01TG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Transporting points along an isomorphism -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An isomorphism of presheaves induces a bijection of the point sets of Tag 03BU, with
inverse the map on points of the inverse isomorphism. -/
noncomputable def pointsEquivOfIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
    points B S hS F ≃ points B S hS G where
  toFun := pointsMap B S hS F e.hom
  invFun := pointsMap B S hS G e.inv
  left_inv w := by
    rw [← pointsMap_comp_apply, e.hom_inv_id]
    exact congrFun (pointsMap_id B S hS F) w
  right_inv w := by
    rw [← pointsMap_comp_apply, e.inv_hom_id]
    exact congrFun (pointsMap_id B S hS G) w

/-- The bijection `AlgebraicGeometry.Space.pointsEquivOfIso` is the map on points of the
isomorphism. -/
@[simp]
theorem pointsEquivOfIso_apply {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (w : points B S hS F) :
    pointsEquivOfIso B S hS e w = pointsMap B S hS F e.hom w := rfl

/-- Naturality of `AlgebraicGeometry.Space.pointsEquivScheme` in the site object: the
bijection of clause (1) of Tag 03BX commutes with the map on points of the Yoneda image of a
morphism of the site. -/
theorem pointsEquivScheme_pointsMap_yoneda {U V : BigFppfOver B S hS} (α : U ⟶ V)
    (w : points B S hS (yoneda.obj U)) :
    pointsEquivScheme B S hS V (pointsMap B S hS (yoneda.obj U) (yoneda.map α) w) =
      (BigFppfOver.toScheme B S hS).map α (pointsEquivScheme B S hS U w) :=
  pointsToScheme_pointsMap_yoneda B S hS α w

namespace PointsFibresDiagram

/-! ### Diagrams whose three non-pullback corners are schemes -/

variable {B S hS}

/-- A representation of the three non-pullback corners of a cartesian square of Tag 0AC1 by
objects of the big fppf site, compatibly with its two morphisms to the lower-right corner. -/
structure SchemeRepresentation (D : PointsFibresDiagram B S hS) where
  /-- The site object representing the upper-right corner. -/
  X : BigFppfOver B S hS
  /-- The site object representing the lower-right corner. -/
  Y : BigFppfOver B S hS
  /-- The site object representing the lower-left corner. -/
  Z : BigFppfOver B S hS
  /-- The morphism of the site representing the right vertical morphism. -/
  f : X ⟶ Y
  /-- The morphism of the site representing the lower horizontal morphism. -/
  g : Z ⟶ Y
  /-- The representation of the upper-right corner. -/
  iX : D.X ≅ yoneda.obj X
  /-- The representation of the lower-right corner. -/
  iY : D.Y ≅ yoneda.obj Y
  /-- The representation of the lower-left corner. -/
  iZ : D.Z ≅ yoneda.obj Z
  /-- The right vertical morphism is represented by `f`. -/
  f_compat : D.f ≫ iY.hom = iX.hom ≫ yoneda.map f
  /-- The lower horizontal morphism is represented by `g`. -/
  g_compat : D.g ≫ iY.hom = iZ.hom ≫ yoneda.map g

namespace SchemeRepresentation

variable {D : PointsFibresDiagram B S hS}

/-- The scheme representing the upper-right corner. -/
abbrev schemeX (R : SchemeRepresentation D) : Scheme.{u} :=
  (BigFppfOver.toScheme B S hS).obj R.X

/-- The scheme representing the lower-right corner. -/
abbrev schemeY (R : SchemeRepresentation D) : Scheme.{u} :=
  (BigFppfOver.toScheme B S hS).obj R.Y

/-- The scheme representing the lower-left corner. -/
abbrev schemeZ (R : SchemeRepresentation D) : Scheme.{u} :=
  (BigFppfOver.toScheme B S hS).obj R.Z

/-- The morphism of schemes representing the right vertical morphism. -/
abbrev schemeF (R : SchemeRepresentation D) : R.schemeX ⟶ R.schemeY :=
  (BigFppfOver.toScheme B S hS).map R.f

/-- The morphism of schemes representing the lower horizontal morphism. -/
abbrev schemeG (R : SchemeRepresentation D) : R.schemeZ ⟶ R.schemeY :=
  (BigFppfOver.toScheme B S hS).map R.g

end SchemeRepresentation

/-- Bijections identifying the four point sets of a cartesian square of Tag 0AC1 with the
point sets of a cartesian square of schemes, compatibly with all four morphisms. -/
structure SchemePointsPresentation (D : PointsFibresDiagram B S hS) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) where
  /-- The points of the upper-left corner are the points of the fibre product. -/
  eW : points B S hS D.W ≃ (pullback f g : Scheme.{u})
  /-- The points of the upper-right corner are the points of `X`. -/
  eX : points B S hS D.X ≃ X
  /-- The points of the lower-right corner are the points of `Y`. -/
  eY : points B S hS D.Y ≃ Y
  /-- The points of the lower-left corner are the points of `Z`. -/
  eZ : points B S hS D.Z ≃ Z
  /-- Compatibility with the upper horizontal morphism. -/
  p_compat : ∀ w, pullback.fst f g (eW w) = eX (pointsMap B S hS D.W D.p w)
  /-- Compatibility with the left vertical morphism. -/
  q_compat : ∀ w, pullback.snd f g (eW w) = eZ (pointsMap B S hS D.W D.q w)
  /-- Compatibility with the right vertical morphism. -/
  f_compat : ∀ x, f (eX x) = eY (pointsMap B S hS D.X D.f x)
  /-- Compatibility with the lower horizontal morphism. -/
  g_compat : ∀ z, g (eZ z) = eY (pointsMap B S hS D.Z D.g z)

variable {D : PointsFibresDiagram B S hS}

/-- The point presentation determined by a representation of the three non-pullback corners
of a cartesian square of Tag 0AC1 by site objects. -/
noncomputable def schemePointsPresentation (R : SchemeRepresentation D) :
    SchemePointsPresentation D R.schemeF R.schemeG := by
  have hsq : IsPullback (D.p ≫ R.iX.hom) (D.q ≫ R.iZ.hom)
      (yoneda.map R.f) (yoneda.map R.g) :=
    D.isPullback.of_iso (Iso.refl D.W) R.iX R.iZ R.iY (by simp) (by simp)
      R.f_compat R.g_compat
  let eObj : D.W ≅ yoneda.obj (pullback R.f R.g) :=
    hsq.isoPullback ≪≫ (PreservesPullback.iso yoneda R.f R.g).symm
  have hfst : eObj.hom ≫ yoneda.map (pullback.fst R.f R.g) = D.p ≫ R.iX.hom := by
    dsimp only [eObj, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, PreservesPullback.iso_inv_fst, hsq.isoPullback_hom_fst]
  have hsnd : eObj.hom ≫ yoneda.map (pullback.snd R.f R.g) = D.q ≫ R.iZ.hom := by
    dsimp only [eObj, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, PreservesPullback.iso_inv_snd, hsq.isoPullback_hom_snd]
  let eScheme := PreservesPullback.iso (BigFppfOver.toScheme B S hS) R.f R.g
  refine
    { eW := ((pointsEquivOfIso B S hS eObj).trans
        (pointsEquivScheme B S hS (pullback R.f R.g))).trans
          (Scheme.homeoOfIso eScheme).toEquiv
      eX := (pointsEquivOfIso B S hS R.iX).trans (pointsEquivScheme B S hS R.X)
      eY := (pointsEquivOfIso B S hS R.iY).trans (pointsEquivScheme B S hS R.Y)
      eZ := (pointsEquivOfIso B S hS R.iZ).trans (pointsEquivScheme B S hS R.Z)
      p_compat := fun w ↦ ?_
      q_compat := fun w ↦ ?_
      f_compat := fun x ↦ ?_
      g_compat := fun z ↦ ?_ }
  · simp only [Equiv.trans_apply, Homeomorph.coe_toEquiv, Scheme.coe_homeoOfIso,
      pointsEquivOfIso_apply]
    calc pullback.fst R.schemeF R.schemeG
          (eScheme.hom (pointsEquivScheme B S hS _ (pointsMap B S hS D.W eObj.hom w)))
        = (BigFppfOver.toScheme B S hS).map (pullback.fst R.f R.g)
            (pointsEquivScheme B S hS _ (pointsMap B S hS D.W eObj.hom w)) :=
          congrFun (congrArg (fun k : _ ⟶ _ ↦ (k : _ → _))
            (PreservesPullback.iso_hom_fst (BigFppfOver.toScheme B S hS) R.f R.g)) _
      _ = pointsEquivScheme B S hS R.X (pointsMap B S hS _ (yoneda.map (pullback.fst R.f R.g))
            (pointsMap B S hS D.W eObj.hom w)) :=
          (pointsEquivScheme_pointsMap_yoneda B S hS _ _).symm
      _ = pointsEquivScheme B S hS R.X (pointsMap B S hS D.X R.iX.hom
            (pointsMap B S hS D.W D.p w)) := by
          rw [← pointsMap_comp_apply, hfst, pointsMap_comp_apply]
  · simp only [Equiv.trans_apply, Homeomorph.coe_toEquiv, Scheme.coe_homeoOfIso,
      pointsEquivOfIso_apply]
    calc pullback.snd R.schemeF R.schemeG
          (eScheme.hom (pointsEquivScheme B S hS _ (pointsMap B S hS D.W eObj.hom w)))
        = (BigFppfOver.toScheme B S hS).map (pullback.snd R.f R.g)
            (pointsEquivScheme B S hS _ (pointsMap B S hS D.W eObj.hom w)) :=
          congrFun (congrArg (fun k : _ ⟶ _ ↦ (k : _ → _))
            (PreservesPullback.iso_hom_snd (BigFppfOver.toScheme B S hS) R.f R.g)) _
      _ = pointsEquivScheme B S hS R.Z (pointsMap B S hS _ (yoneda.map (pullback.snd R.f R.g))
            (pointsMap B S hS D.W eObj.hom w)) :=
          (pointsEquivScheme_pointsMap_yoneda B S hS _ _).symm
      _ = pointsEquivScheme B S hS R.Z (pointsMap B S hS D.Z R.iZ.hom
            (pointsMap B S hS D.W D.q w)) := by
          rw [← pointsMap_comp_apply, hsnd, pointsMap_comp_apply]
  · simp only [Equiv.trans_apply, pointsEquivOfIso_apply]
    calc R.schemeF (pointsEquivScheme B S hS R.X (pointsMap B S hS D.X R.iX.hom x))
        = pointsEquivScheme B S hS R.Y
            (pointsMap B S hS _ (yoneda.map R.f) (pointsMap B S hS D.X R.iX.hom x)) :=
          (pointsEquivScheme_pointsMap_yoneda B S hS _ _).symm
      _ = pointsEquivScheme B S hS R.Y
            (pointsMap B S hS D.Y R.iY.hom (pointsMap B S hS D.X D.f x)) := by
          rw [← pointsMap_comp_apply, ← R.f_compat, pointsMap_comp_apply]
  · simp only [Equiv.trans_apply, pointsEquivOfIso_apply]
    calc R.schemeG (pointsEquivScheme B S hS R.Z (pointsMap B S hS D.Z R.iZ.hom z))
        = pointsEquivScheme B S hS R.Y
            (pointsMap B S hS _ (yoneda.map R.g) (pointsMap B S hS D.Z R.iZ.hom z)) :=
          (pointsEquivScheme_pointsMap_yoneda B S hS _ _).symm
      _ = pointsEquivScheme B S hS R.Y
            (pointsMap B S hS D.Y R.iY.hom (pointsMap B S hS D.Z D.g z)) := by
          rw [← pointsMap_comp_apply, ← R.g_compat, pointsMap_comp_apply]

end PointsFibresDiagram

/-! ### The fibre of a fibre product of schemes over two points -/

/-- The part of a fibre product of schemes lying over a fixed point of each factor is the
spectrum of the tensor product of their residue fields over the residue field of their common
image. -/
@[ega "I 3.4.9" "partial"]
noncomputable def pullbackFibreEquivSpecTensor {X Z Y : Scheme.{u}} (φ : X ⟶ Y) (ψ : Z ⟶ Y)
    (a : X) (b : Z) (hab : φ a = ψ b) :
    {t : ↑(pullback φ ψ) | pullback.fst φ ψ t = a ∧ pullback.snd φ ψ t = b} ≃
      Spec (Scheme.Pullback.Triplet.mk' a b hab).tensor :=
  (Scheme.Pullback.carrierEquiv.subtypeEquiv fun t ↦ by
    change (pullback.fst φ ψ t = a ∧ pullback.snd φ ψ t = b) ↔
      (Scheme.Pullback.carrierEquiv t).1 = Scheme.Pullback.Triplet.mk' a b hab
    refine ⟨fun ht ↦ Scheme.Pullback.Triplet.ext ht.1 ht.2, fun ht ↦ ⟨?_, ?_⟩⟩
    · simpa [Scheme.Pullback.carrierEquiv, Scheme.Pullback.Triplet.ofPoint] using
        congrArg Scheme.Pullback.Triplet.x ht
    · simpa [Scheme.Pullback.carrierEquiv, Scheme.Pullback.Triplet.ofPoint] using
        congrArg Scheme.Pullback.Triplet.y ht).trans
      (Equiv.sigmaSubtype (β := fun T ↦ Spec T.tensor) (Scheme.Pullback.Triplet.mk' a b hab))

/-- The inverse of `AlgebraicGeometry.Space.pullbackFibreEquivSpecTensor` is the canonical map
`AlgebraicGeometry.Scheme.Pullback.Triplet.SpecTensorTo`. -/
theorem pullbackFibreEquivSpecTensor_symm_coe {X Z Y : Scheme.{u}} (φ : X ⟶ Y) (ψ : Z ⟶ Y)
    (a : X) (b : Z) (hab : φ a = ψ b)
    (p : Spec (Scheme.Pullback.Triplet.mk' a b hab).tensor) :
    ((pullbackFibreEquivSpecTensor φ ψ a b hab).symm p).1 =
      (Scheme.Pullback.Triplet.mk' a b hab).SpecTensorTo p := by
  simp [pullbackFibreEquivSpecTensor, Equiv.sigmaSubtype, Scheme.Pullback.carrierEquiv]

/-! ### Finiteness of the spectrum of a residue-field tensor product -/

/-- The spectrum of a pushout of two field extensions of `k` is finite when one of the two
extensions is finite. -/
private theorem finite_primeSpectrum_of_isPushout
    {k K L T : Type u} [Field k] [Field K] [Field L] [CommRing T] [Algebra k K] [Algebra k L]
    (a : K →+* T) (b : L →+* T)
    (H : IsPushout (CommRingCat.ofHom (algebraMap k K)) (CommRingCat.ofHom (algebraMap k L))
      (CommRingCat.ofHom a) (CommRingCat.ofHom b))
    (hfin : (algebraMap k K).Finite ∨ (algebraMap k L).Finite) : Finite (PrimeSpectrum T) := by
  have : IsArtinianRing (TensorProduct k K L) := by
    rcases hfin with hf | hg
    · have : Module.Finite k K := RingHom.finite_algebraMap.mp hf
      let : Algebra L (TensorProduct k K L) := Algebra.TensorProduct.rightAlgebra
      have : Module.Finite L (TensorProduct k L K) := inferInstance
      have : Module.Finite L (TensorProduct k K L) :=
        Module.Finite.equiv (Algebra.TensorProduct.commRight k L K).toLinearEquiv
      exact IsArtinianRing.of_finite L _
    · have : Module.Finite k L := RingHom.finite_algebraMap.mp hg
      exact IsArtinianRing.of_finite K _
  let : IsArtinianRing T :=
    (IsPushout.isoIsPushout (X := CommRingCat.of K) (Y := CommRingCat.of L)
      (CommRingCat.isPushout_tensorProduct k K L) H).commRingCatIsoToRingEquiv.isArtinianRing
  infer_instance

/-- A quasi-finite local homomorphism has finite residue-field extension. This is the
ring-theoretic content of Tag 01TG. -/
private theorem finite_residueField_of_quasiFinite {A C : Type u} [CommRing A] [CommRing C]
    [IsLocalRing A] [IsLocalRing C] (φ : A →+* C) [IsLocalHom φ] (hφ : φ.QuasiFinite) :
    letI : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C) :=
      (IsLocalRing.ResidueField.map φ).toAlgebra
    Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C) := by
  let : Algebra A (IsLocalRing.ResidueField A) := (IsLocalRing.residue A).toAlgebra
  let : Algebra C (IsLocalRing.ResidueField C) := (IsLocalRing.residue C).toAlgebra
  let : Algebra A (IsLocalRing.ResidueField C) :=
    ((IsLocalRing.residue C).comp φ).toAlgebra
  let : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C) :=
    (IsLocalRing.ResidueField.map φ).toAlgebra
  let : IsScalarTower A (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C) :=
    .of_algebraMap_eq' (IsLocalRing.ResidueField.map_comp_residue φ)
  have hfiniteC : Module.Finite C (IsLocalRing.ResidueField C) :=
    Module.Finite.of_surjective (Algebra.linearMap C (IsLocalRing.ResidueField C))
      IsLocalRing.residue_surjective
  have : Algebra.QuasiFinite A (IsLocalRing.ResidueField C) :=
    RingHom.quasiFinite_algebraMap.mp
      (RingHom.QuasiFinite.comp
        (RingHom.QuasiFinite.of_finite (RingHom.finite_algebraMap.mpr hfiniteC)) hφ)
  have : Algebra.QuasiFinite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C) :=
    Algebra.QuasiFinite.of_restrictScalars A _ _
  exact Module.Finite.of_quasiFinite

/-! ### The points in a fibre of a diagram of schemes -/

variable {B S hS} {D : PointsFibresDiagram B S hS} (R : D.SchemeRepresentation)
  (x : points B S hS D.X) (z : points B S hS D.Z)

/-- Two points of the lower-left and upper-right corners with a common image in the
lower-right corner have, under the point presentation, a common image in the representing
scheme of the lower-right corner. -/
theorem schemeF_eq_schemeG_of_pointsMap_eq
    (h : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z) :
    R.schemeF ((D.schemePointsPresentation R).eX x) =
      R.schemeG ((D.schemePointsPresentation R).eZ z) := by
  rw [(D.schemePointsPresentation R).f_compat, (D.schemePointsPresentation R).g_compat, h]

/-- In a cartesian square of Tag 0AC1 whose three non-pullback corners are schemes, the set of
Tag 0AC2 attached to two points `x` and `z` with a common image `y` is in bijection with the
spectrum of `κ(x) ⊗_{κ(y)} κ(z)`. -/
@[stacks 0AC3 "spectrum of the fibre"]
noncomputable def fibreSpectrumEquiv
    (h : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z) :
    (fibrePoints D x z h) ≃
      Spec (Scheme.Pullback.Triplet.mk' ((D.schemePointsPresentation R).eX x)
        ((D.schemePointsPresentation R).eZ z)
        (schemeF_eq_schemeG_of_pointsMap_eq R x z h)).tensor :=
  ((D.schemePointsPresentation R).eW.subtypeEquiv fun w ↦ by
    change (pointsMap B S hS D.W D.p w = x ∧ pointsMap B S hS D.W D.q w = z) ↔
      (pullback.fst R.schemeF R.schemeG ((D.schemePointsPresentation R).eW w) =
          (D.schemePointsPresentation R).eX x ∧
        pullback.snd R.schemeF R.schemeG ((D.schemePointsPresentation R).eW w) =
          (D.schemePointsPresentation R).eZ z)
    refine ⟨fun hw ↦ ⟨by rw [(D.schemePointsPresentation R).p_compat, hw.1],
        by rw [(D.schemePointsPresentation R).q_compat, hw.2]⟩, fun hw ↦ ⟨?_, ?_⟩⟩
    · exact (D.schemePointsPresentation R).eX.injective
        (((D.schemePointsPresentation R).p_compat w).symm.trans hw.1)
    · exact (D.schemePointsPresentation R).eZ.injective
        (((D.schemePointsPresentation R).q_compat w).symm.trans hw.2)).trans
      (pullbackFibreEquivSpecTensor R.schemeF R.schemeG _ _
        (schemeF_eq_schemeG_of_pointsMap_eq R x z h))

/-- The inverse of `AlgebraicGeometry.Space.fibreSpectrumEquiv` is the canonical map
`AlgebraicGeometry.Scheme.Pullback.Triplet.SpecTensorTo`, read through the point presentation. -/
@[stacks 0AC3 "canonical correspondence"]
theorem fibreSpectrumEquiv_symm_apply
    (h : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z)
    (p : Spec (Scheme.Pullback.Triplet.mk' ((D.schemePointsPresentation R).eX x)
      ((D.schemePointsPresentation R).eZ z)
      (schemeF_eq_schemeG_of_pointsMap_eq R x z h)).tensor) :
    (D.schemePointsPresentation R).eW ((fibreSpectrumEquiv R x z h).symm p).1 =
      (Scheme.Pullback.Triplet.mk' ((D.schemePointsPresentation R).eX x)
        ((D.schemePointsPresentation R).eZ z)
        (schemeF_eq_schemeG_of_pointsMap_eq R x z h)).SpecTensorTo p := by
  rw [fibreSpectrumEquiv, Equiv.symm_trans_apply, Equiv.subtypeEquiv_symm,
    Equiv.subtypeEquiv_apply, Equiv.apply_symm_apply]
  exact pullbackFibreEquivSpecTensor_symm_coe R.schemeF R.schemeG _ _
    (schemeF_eq_schemeG_of_pointsMap_eq R x z h) p

/-- The set of Tag 0AC2 is finite when one of the residue field extensions `κ(y) ⊂ κ(x)`,
`κ(y) ⊂ κ(z)` is finite, the two being viewed as algebras over `κ(y)` through `g z`. -/
private theorem finite_fibrePoints_of_finite_algebraMap
    (h : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z)
    (hfin : letI := (((R.schemeY.residueFieldCongr
        (schemeF_eq_schemeG_of_pointsMap_eq R x z h)).inv ≫
          R.schemeF.residueFieldMap ((D.schemePointsPresentation R).eX x)).hom).toAlgebra
      letI := (((R.schemeY.residueFieldCongr rfl).inv ≫
          R.schemeG.residueFieldMap ((D.schemePointsPresentation R).eZ z)).hom).toAlgebra
      (algebraMap (R.schemeY.residueField (R.schemeG ((D.schemePointsPresentation R).eZ z)))
          (R.schemeX.residueField ((D.schemePointsPresentation R).eX x))).Finite ∨
        (algebraMap (R.schemeY.residueField (R.schemeG ((D.schemePointsPresentation R).eZ z)))
          (R.schemeZ.residueField ((D.schemePointsPresentation R).eZ z))).Finite) :
    (fibrePoints D x z h).Finite := by
  set a := (D.schemePointsPresentation R).eX x
  set b := (D.schemePointsPresentation R).eZ z
  have hy := schemeF_eq_schemeG_of_pointsMap_eq R x z h
  let : Algebra (R.schemeY.residueField (R.schemeG b)) (R.schemeX.residueField a) :=
    (((R.schemeY.residueFieldCongr hy).inv ≫ R.schemeF.residueFieldMap a).hom).toAlgebra
  let : Algebra (R.schemeY.residueField (R.schemeG b)) (R.schemeZ.residueField b) :=
    (((R.schemeY.residueFieldCongr rfl).inv ≫ R.schemeG.residueFieldMap b).hom).toAlgebra
  have : Finite (Spec (Scheme.Pullback.Triplet.mk' a b hy).tensor) :=
    finite_primeSpectrum_of_isPushout _ _
      (IsPushout.of_hasPushout
        (CommRingCat.ofHom (algebraMap (R.schemeY.residueField (R.schemeG b))
          (R.schemeX.residueField a)))
        (CommRingCat.ofHom (algebraMap (R.schemeY.residueField (R.schemeG b))
          (R.schemeZ.residueField b)))) hfin
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ (fibreSpectrumEquiv R x z h).symm)

/-- The set of Tag 0AC2 is finite when the residue field extension `κ(y) ⊂ κ(x)` is finite. -/
@[stacks 0AC3 "finite left residue extension"]
theorem finite_fibrePoints_of_finite_residueField_left
    (h : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z)
    (hfin : letI := (R.schemeF.residueFieldMap ((D.schemePointsPresentation R).eX x)).hom.toAlgebra
      Module.Finite
        (R.schemeY.residueField (R.schemeF ((D.schemePointsPresentation R).eX x)))
        (R.schemeX.residueField ((D.schemePointsPresentation R).eX x))) :
    (fibrePoints D x z h).Finite := by
  refine finite_fibrePoints_of_finite_algebraMap R x z h (Or.inl ?_)
  let : Algebra (R.schemeY.residueField (R.schemeF ((D.schemePointsPresentation R).eX x)))
      (R.schemeX.residueField ((D.schemePointsPresentation R).eX x)) :=
    (R.schemeF.residueFieldMap ((D.schemePointsPresentation R).eX x)).hom.toAlgebra
  exact (RingHom.finite_algebraMap.mpr hfin).comp
    (R.schemeY.residueFieldCongr
      (schemeF_eq_schemeG_of_pointsMap_eq R x z h)).symm.commRingCatIsoToRingEquiv.finite

/-- The set of Tag 0AC2 is finite when the residue field extension `κ(y) ⊂ κ(z)` is finite. -/
@[stacks 0AC3 "finite right residue extension"]
theorem finite_fibrePoints_of_finite_residueField_right
    (h : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z)
    (hfin : letI := (R.schemeG.residueFieldMap ((D.schemePointsPresentation R).eZ z)).hom.toAlgebra
      Module.Finite
        (R.schemeY.residueField (R.schemeG ((D.schemePointsPresentation R).eZ z)))
        (R.schemeZ.residueField ((D.schemePointsPresentation R).eZ z))) :
    (fibrePoints D x z h).Finite := by
  refine finite_fibrePoints_of_finite_algebraMap R x z h (Or.inr ?_)
  let : Algebra (R.schemeY.residueField (R.schemeG ((D.schemePointsPresentation R).eZ z)))
      (R.schemeZ.residueField ((D.schemePointsPresentation R).eZ z)) :=
    (((R.schemeY.residueFieldCongr rfl).inv ≫
      R.schemeG.residueFieldMap ((D.schemePointsPresentation R).eZ z)).hom).toAlgebra
  exact RingHom.finite_algebraMap.mpr hfin

/-- The set of Tag 0AC2 is finite whenever the lower horizontal morphism is quasi-finite at
`z`. -/
@[stacks 0AC3 "quasi-finite case"]
theorem finite_fibrePoints_of_quasiFiniteAt
    (h : pointsMap B S hS D.X D.f x = pointsMap B S hS D.Z D.g z)
    (hg : quasiFiniteAt R.schemeG ((D.schemePointsPresentation R).eZ z)) :
    (fibrePoints D x z h).Finite := by
  set b := (D.schemePointsPresentation R).eZ z
  let : Algebra (R.schemeY.residueField (R.schemeG b)) (R.schemeZ.residueField b) :=
    (R.schemeG.residueFieldMap b).hom.toAlgebra
  exact finite_fibrePoints_of_finite_residueField_right R x z h
    (finite_residueField_of_quasiFinite (R.schemeG.stalkMap b).hom hg.2)

end AlgebraicGeometry.Space

end
