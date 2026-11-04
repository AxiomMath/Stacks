module

public import StacksFrontier.AlgebraicGeometry.Conormal.IdealLift
public import StacksFrontier.AlgebraicGeometry.Conormal.RestrictSquareUnit

/-!
# The conormal sections over an affine open of the ambient scheme

Let `i : Z ⟶ X` be an immersion of schemes, let `V ⊆ X` be an **affine open of `X` itself** and
suppose the scheme-theoretic intersection `Z ∩ V` is `Spec (Γ(X, V) ⧸ I)` for an ideal
`I ⊆ Γ(X, V)`. The sections over `V` of the pushforward `i_* 𝒞_{Z/X}` are `I/I²`, as
`Γ(X, V)`-modules; that is the shape [Stacks Project, Tag 01R3] part (2) asks for, and the
identification is `Stacks.Conormal.affineConormalIsoCotangent`. This file transports the conormal
sheaf across the restriction square of `i` over `V` and across the affine square
`V ≅ Spec Γ(X, V)`, and proves the compatibility of the canonical conormal quotient map of `i`
with the restriction square.

## Main definitions

* `Stacks.Immersion.morphismRestrictShHom`, `Stacks.Immersion.isoSpecRestrict` and
  `Stacks.Immersion.isoQuotRestrict`: the restricted morphism and the two isomorphisms of the
  affine square, with their ringed spaces spelled as restrictions.
* `Stacks.Immersion.conormalSheafSelfRestrictIso`: `𝒞_{Z/X}|_{i⁻¹V} ≅ 𝒞_{i ∣_ V}`.
* `Stacks.Immersion.ambientConormalSquareIso`: the pushforward conormal sheaf of `i ∣_ V`,
  transported across the isomorphism square `V ≅ Spec Γ(X, V)`, `i⁻¹V ≅ Spec (Γ(X, V) ⧸ I)`.

## Main results

* `Stacks.Immersion.canonicalConormalQuotientMap_comp_restrictConormal`: the factorization-free
  conormal quotient map of `i`, followed by the canonical restriction-of-sections comparison into
  `(ι_V)_* ((i ∣_ V)_* 𝒞_{i ∣_ V})`, is the unit square of
  `Stacks.ClosedImmersion.restrictConormalSheafIso_comp_unit` read at the conormal sheaf of `i`
  itself.
* `Stacks.Immersion.canonicalConormalQuotientMap_comp_restrictConormal_eq_unit`: the canonical
  quotient map of `i`, followed by the restriction-of-sections comparison, is the unit of
  `(ι_V)^* ⊣ (ι_V)_*` at `ℐ_i` followed by the ideal-sheaf transport and the conormal quotient map
  of `i ∣_ V`.

## Implementation notes

Every ringed space and preimage open that meets the restriction square is written
`Z.toSheafedSpace` and `(Opens.map i.toLRSHom.toShHom.hom.base).obj V`; do not re-spell them as
`Z.toLocallyRingedSpace.toRingedSpace` or `i ⁻¹ᵁ V`, which are only reducibly equal, because the
kernel then times out. Likewise keep `Stacks.Immersion.ambientConormalSquareIso_eq` an identity
of isomorphisms: projecting `.hom` on both sides times out in the kernel.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01C2](https://stacks.math.columbia.edu/tag/01C2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction 
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.ClosedImmersion Stacks.ClosedImmersion.AffineConormal
open Stacks.ClosedImmersion.IdealSheafAffine

universe v u

namespace ModuleCat

/-- **Two equal morphisms of modules agree on every element.** -/
theorem hom_apply_congr {R : Type u} [Ring R] {A B : ModuleCat.{v} R} {f g : A ⟶ B} (h : f = g)
    (x : A) : f.hom x = g.hom x :=
  congrArg (fun k : A ⟶ B => k.hom x) h

/-- **Composition of morphisms of modules on an element**, through the `hom` projection. -/
theorem hom_comp_apply {R : Type u} [Ring R] {A B C : ModuleCat.{v} R} (f : A ⟶ B) (g : B ⟶ C)
    (x : A) : (f ≫ g).hom x = g.hom (f.hom x) := rfl

end ModuleCat

namespace Stacks.Immersion

variable {Z X : Scheme.{u}}

/-! ### The restriction square and the affine square with the same ringed spaces

The restricted morphism and the two isomorphisms of the affine square, with their ringed spaces
spelled as restrictions of `Z.toSheafedSpace` and `X.toSheafedSpace`, as for
`AlgebraicGeometry.RingedSpace.restrictHom`. -/

/-- **`i ∣_ V` on underlying ringed spaces, with its source and target spelled as restrictions.**
This is `(i ∣_ V).toLRSHom.toShHom`. -/
abbrev morphismRestrictShHom (i : Z ⟶ X) (V : X.Opens) :
    Z.toSheafedSpace.restrict ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding ⟶
      X.toSheafedSpace.restrict V.isOpenEmbedding :=
  (i ∣_ V).toLRSHom.toShHom

/-- **`X|_V ≅ Spec Γ(X, V)` for an affine open `V`, with its source spelled as a restriction.**
`AlgebraicGeometry.IsAffineOpen.isoSpec` on underlying ringed spaces, ascribed at
`X.toSheafedSpace.restrict V.isOpenEmbedding` rather than at `V.toScheme`. -/
abbrev isoSpecRestrict (V : X.Opens) (hV : IsAffineOpen V) :
    X.toSheafedSpace.restrict V.isOpenEmbedding ≅ (Spec Γ(X, V)).toSheafedSpace :=
  ringedSpaceIso hV.isoSpec

/-- **`Z|_{i⁻¹V} ≅ Spec (Γ(X, V) ⧸ I)`, with its source spelled as a restriction.** The hypothesis
of [Stacks Project, Tag 01R3] part (2) identifies `Z ∩ V` with `Spec (Γ(X, V) ⧸ I)` through
`CategoryTheory.Limits.pullback`; `AlgebraicGeometry.pullbackRestrictIsoRestrict` turns that into
an isomorphism out of `i⁻¹V`, ascribed here at
`Z.toSheafedSpace.restrict ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding`. -/
abbrev isoQuotRestrict (i : Z ⟶ X) (V : X.Opens) (I : Ideal Γ(X, V))
    (e : pullback i V.ι ≅ Spec (quotRing I)) :
    Z.toSheafedSpace.restrict ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding ≅
      (Spec (quotRing I)).toSheafedSpace :=
  ringedSpaceIso ((pullbackRestrictIsoRestrict i V).symm ≪≫ e)

/-- The affine square commutes: `i ∣_ V` followed by `V ≅ Spec Γ(X, V)` is
`Z|_{i⁻¹V} ≅ Spec (Γ(X, V) ⧸ I)` followed by the closed immersion
`Spec (Γ(X, V) ⧸ I) ⟶ Spec Γ(X, V)`, on ringed spaces spelled as restrictions. -/
theorem morphismRestrictShHom_comp_isoSpecRestrict (i : Z ⟶ X) (V : X.Opens)
    (hV : IsAffineOpen V) (I : Ideal Γ(X, V)) (e : pullback i V.ι ≅ Spec (quotRing I))
    (he : pullback.snd i V.ι ≫ hV.isoSpec.hom = e.hom ≫ quotImmersion Γ(X, V) I) :
    morphismRestrictShHom i V ≫ (isoSpecRestrict V hV).hom =
      (isoQuotRestrict i V I e).hom ≫ (quotImmersion Γ(X, V) I).toLRSHom.toShHom :=
  morphismRestrict_comp_isoSpec_toShHom i V hV I e he

/-- The restriction of `i` to `i⁻¹V ⟶ V` is `Stacks.Immersion.morphismRestrictShHom i V`. -/
theorem restrictHom_eq_morphismRestrictShHom (i : Z ⟶ X) (V : X.Opens) :
    restrictHom i.toLRSHom.toShHom V = morphismRestrictShHom i V :=
  restrictHom_eq_morphismRestrict i V

/-! ### The conormal sheaf of a restriction of the immersion itself -/

/-- **`𝒞_{Z/X}|_{i⁻¹V} ≅ 𝒞_{i ∣_ V}`.** For an immersion of schemes `i : Z ⟶ X` and an open `V`
of `X`, the conormal sheaf of `i` restricted to `i⁻¹V` is the conormal sheaf of the restricted
morphism `i ∣_ V`. -/
def conormalSheafSelfRestrictIso (i : Z ⟶ X) [IsImmersion i] (V : X.Opens) :
    (moduleRestrict Z.toSheafedSpace ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).obj
        (conormalSheaf i.liftCoborder.toLRSHom.toShHom) ≅
      conormalSheaf (morphismRestrictShHom i V) :=
  (moduleRestrict Z.toSheafedSpace ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).mapIso
      (conormalSheafSelfIso i).symm ≪≫
    restrictConormalSheafIso i.toLRSHom.toShHom V ≪≫
    eqToIso (congrArg (fun p => conormalSheaf p) (restrictHom_eq_morphismRestrictShHom i V))

/-- **`Stacks.Immersion.conormalSheafSelfRestrictIso` as a morphism, right-associated.** -/
theorem conormalSheafSelfRestrictIso_hom (i : Z ⟶ X) [IsImmersion i] (V : X.Opens) :
    (conormalSheafSelfRestrictIso i V).hom =
      ((moduleRestrict Z.toSheafedSpace ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).map
          (conormalSheafSelfIso i).inv ≫ (restrictConormalSheafIso i.toLRSHom.toShHom V).hom) ≫
        eqToHom (congrArg (fun p => conormalSheaf p)
          (restrictHom_eq_morphismRestrictShHom i V)) :=
  (Category.assoc _ _ _).symm

/-! ### Transport across the affine isomorphism square -/

/-- **The pushforward conormal sheaf of `i ∣_ V`, read on `Spec Γ(X, V)`.** Transporting
`Stacks.Immersion.conormalSheafSelfRestrictIso` along the isomorphism square
`V ≅ Spec Γ(X, V)`, `i⁻¹V ≅ Spec (Γ(X, V) ⧸ I)` of
`Stacks.Immersion.morphismRestrictShHom_comp_isoSpecRestrict` lands at the closed immersion
`Spec (Γ(X, V) ⧸ I) ⟶ Spec Γ(X, V)`, whose pushforward conormal sheaf
`Stacks.ClosedImmersion.AffineConormal.conormalΓIso` computes. -/
def ambientConormalSquareIso (i : Z ⟶ X) [IsImmersion i] (V : X.Opens) (hV : IsAffineOpen V)
    (I : Ideal Γ(X, V)) (e : pullback i V.ι ≅ Spec (quotRing I))
    (he : pullback.snd i V.ι ≫ hV.isoSpec.hom = e.hom ≫ quotImmersion Γ(X, V) I) :
    (modulePushforward (isoSpecRestrict V hV).hom).obj
        ((modulePushforward (morphismRestrictShHom i V)).obj
          ((moduleRestrict Z.toSheafedSpace ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).obj
            (conormalSheaf i.liftCoborder.toLRSHom.toShHom))) ≅
      (modulePushforward (quotImmersion Γ(X, V) I).toLRSHom.toShHom).obj
        (conormalSheaf (quotImmersion Γ(X, V) I).toLRSHom.toShHom) :=
  (modulePushforward (isoSpecRestrict V hV).hom).mapIso
      ((modulePushforward (morphismRestrictShHom i V)).mapIso
        (conormalSheafSelfRestrictIso i V)) ≪≫
    ambientPushforwardConormalIsoOfSquare (isoQuotRestrict i V I e) (isoSpecRestrict V hV)
      (morphismRestrictShHom i V) (quotImmersion Γ(X, V) I).toLRSHom.toShHom
      (morphismRestrictShHom_comp_isoSpecRestrict i V hV I e he)

/-- **`Stacks.Immersion.ambientConormalSquareIso` unfolded**, as an identity of isomorphisms. -/
theorem ambientConormalSquareIso_eq (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
    (hV : IsAffineOpen V) (I : Ideal Γ(X, V)) (e : pullback i V.ι ≅ Spec (quotRing I))
    (he : pullback.snd i V.ι ≫ hV.isoSpec.hom = e.hom ≫ quotImmersion Γ(X, V) I) :
    ambientConormalSquareIso i V hV I e he =
      (modulePushforward (isoSpecRestrict V hV).hom).mapIso
          ((modulePushforward (morphismRestrictShHom i V)).mapIso
            (conormalSheafSelfRestrictIso i V)) ≪≫
        ambientPushforwardConormalIsoOfSquare (isoQuotRestrict i V I e) (isoSpecRestrict V hV)
          (morphismRestrictShHom i V) (quotImmersion Γ(X, V) I).toLRSHom.toShHom
          (morphismRestrictShHom_comp_isoSpecRestrict i V hV I e he) := rfl

/-! ### The conormal quotient map across the restriction square -/

/-- Restricting `Stacks.Immersion.conormalSheafSelfIso` and then its inverse does nothing. -/
theorem moduleRestrict_conormalSheafSelfIso_cancel (i : Z ⟶ X) [IsImmersion i] (V : X.Opens) :
    (moduleRestrict Z.toSheafedSpace ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).map
        (conormalSheafSelfIso i).hom ≫
      ((moduleRestrict Z.toSheafedSpace ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).map
          (conormalSheafSelfIso i).inv ≫
        (restrictConormalSheafIso i.toLRSHom.toShHom V).hom) =
      (restrictConormalSheafIso i.toLRSHom.toShHom V).hom :=
  Iso.hom_inv_id_assoc (
    (moduleRestrict Z.toSheafedSpace ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).mapIso
      (conormalSheafSelfIso i)) _

/-- **The pullback of `Stacks.Immersion.conormalSheafSelfIso` is absorbed by
`Stacks.Immersion.conormalSheafSelfRestrictIso`.** -/
theorem modulePullbackRestrictIso_hom_app_conormalSheafSelfIso (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) :
    (modulePullback (Z.toSheafedSpace.ofRestrict
          ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).map
            (conormalSheafSelfIso i).hom ≫
        ((modulePullbackRestrictIso Z.toSheafedSpace
            ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).hom.app
              (conormalSheaf i.liftCoborder.toLRSHom.toShHom) ≫
          ((moduleRestrict Z.toSheafedSpace ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).map
              (conormalSheafSelfIso i).inv ≫
            (restrictConormalSheafIso i.toLRSHom.toShHom V).hom)) =
      (modulePullbackRestrictIso Z.toSheafedSpace
          ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).hom.app
            (conormalSheaf i.toLRSHom.toShHom) ≫
        (restrictConormalSheafIso i.toLRSHom.toShHom V).hom :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (
      (moduleRestrict Z.toSheafedSpace ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).map
        (conormalSheafSelfIso i).inv ≫
        (restrictConormalSheafIso i.toLRSHom.toShHom V).hom))
      ((modulePullbackRestrictIso Z.toSheafedSpace
        ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).hom.naturality
          (conormalSheafSelfIso i).hom)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun z => (modulePullbackRestrictIso Z.toSheafedSpace
            ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).hom.app
              (conormalSheaf i.toLRSHom.toShHom) ≫ z)
          (moduleRestrict_conormalSheafSelfIso_cancel i V))))

/-- `Stacks.Immersion.modulePullbackRestrictIso_hom_app_conormalSheafSelfIso` pushed forward to
`X` along `(i ∣_ V)` and `ι_V`. -/
theorem pushforward_modulePullbackRestrictIso_hom_app_conormalSheafSelfIso (i : Z ⟶ X)
    [IsImmersion i] (V : X.Opens) :
    (modulePushforward (X.toSheafedSpace.ofRestrict
          V.isOpenEmbedding)).map
        ((modulePushforward (restrictHom i.toLRSHom.toShHom V)).map
          ((modulePullback (Z.toSheafedSpace.ofRestrict
            ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).map
              (conormalSheafSelfIso i).hom)) ≫
      (modulePushforward (X.toSheafedSpace.ofRestrict
          V.isOpenEmbedding)).map
        ((modulePushforward (restrictHom i.toLRSHom.toShHom V)).map
          ((modulePullbackRestrictIso Z.toSheafedSpace
              ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).hom.app
                (conormalSheaf i.liftCoborder.toLRSHom.toShHom) ≫
            ((moduleRestrict Z.toSheafedSpace ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).map
                (conormalSheafSelfIso i).inv ≫
              (restrictConormalSheafIso i.toLRSHom.toShHom V).hom))) =
    (modulePushforward (X.toSheafedSpace.ofRestrict
        V.isOpenEmbedding)).map
      ((modulePushforward (restrictHom i.toLRSHom.toShHom V)).map
        ((modulePullbackRestrictIso Z.toSheafedSpace
            ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).hom.app
              (conormalSheaf i.toLRSHom.toShHom) ≫
          (restrictConormalSheafIso i.toLRSHom.toShHom V).hom)) :=
  ((modulePushforward (X.toSheafedSpace.ofRestrict
      V.isOpenEmbedding)).map_comp _ _).symm.trans
    (congrArg (modulePushforward (X.toSheafedSpace.ofRestrict
        V.isOpenEmbedding)).map
      (((modulePushforward (restrictHom i.toLRSHom.toShHom V)).map_comp _ _).symm.trans
        (congrArg (modulePushforward (restrictHom i.toLRSHom.toShHom V)).map
          (modulePullbackRestrictIso_hom_app_conormalSheafSelfIso i V))))

/-- Naturality of the unit of `ι_{i⁻¹V}^* ⊣ (ι_{i⁻¹V})_*` in its argument, pushed forward along
`i`: it moves `Stacks.Immersion.conormalSheafSelfIso` past the unit. -/
theorem modulePushforward_unit_app_conormalSheafSelfIso (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) :
    (modulePushforward i.toLRSHom.toShHom).map (conormalSheafSelfIso i).hom ≫
        (modulePushforward i.toLRSHom.toShHom).map
          ((modulePullbackPushforwardAdjunction
            (Z.toSheafedSpace.ofRestrict
              ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).unit.app
            (conormalSheaf i.liftCoborder.toLRSHom.toShHom)) =
      (modulePushforward i.toLRSHom.toShHom).map
          ((modulePullbackPushforwardAdjunction
            (Z.toSheafedSpace.ofRestrict
              ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).unit.app
            (conormalSheaf i.toLRSHom.toShHom)) ≫
        (modulePushforward i.toLRSHom.toShHom).map
          ((modulePushforward (Z.toSheafedSpace.ofRestrict
            ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).map
            ((modulePullback (Z.toSheafedSpace.ofRestrict
              ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).map
                (conormalSheafSelfIso i).hom)) := by
  have h := (modulePullbackPushforwardAdjunction
    (Z.toSheafedSpace.ofRestrict
      ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).unit.naturality
        (conormalSheafSelfIso i).hom
  simp only [Functor.id_map, Functor.comp_map] at h
  have h2 := congrArg (modulePushforward i.toLRSHom.toShHom).map h
  rwa [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h2

/-- Naturality of the pushforward comparison of the restriction square in its argument: it moves
`Stacks.Immersion.conormalSheafSelfIso` past
`RingedSpaceModuleAdjunction.modulePushforwardSquareIso`. -/
theorem modulePushforwardSquareIso_inv_app_conormalSheafSelfIso (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) :
    (modulePushforward i.toLRSHom.toShHom).map
          ((modulePushforward (Z.toSheafedSpace.ofRestrict
            ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).map
            ((modulePullback (Z.toSheafedSpace.ofRestrict
              ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).map
                (conormalSheafSelfIso i).hom)) ≫
        (modulePushforwardSquareIso
            (Z.toSheafedSpace.ofRestrict
              ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)
            (X.toSheafedSpace.ofRestrict V.isOpenEmbedding)
            (restrictHom i.toLRSHom.toShHom V) i.toLRSHom.toShHom
            (restrictHom_comp_ofRestrict i.toLRSHom.toShHom V)).inv.app
          ((modulePullback (Z.toSheafedSpace.ofRestrict
            ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).obj
              (conormalSheaf i.liftCoborder.toLRSHom.toShHom)) =
      (modulePushforwardSquareIso
            (Z.toSheafedSpace.ofRestrict
              ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)
            (X.toSheafedSpace.ofRestrict V.isOpenEmbedding)
            (restrictHom i.toLRSHom.toShHom V) i.toLRSHom.toShHom
            (restrictHom_comp_ofRestrict i.toLRSHom.toShHom V)).inv.app
          ((modulePullback (Z.toSheafedSpace.ofRestrict
            ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).obj
              (conormalSheaf i.toLRSHom.toShHom)) ≫
        (modulePushforward (X.toSheafedSpace.ofRestrict
            V.isOpenEmbedding)).map
          ((modulePushforward (restrictHom i.toLRSHom.toShHom V)).map
            ((modulePullback (Z.toSheafedSpace.ofRestrict
              ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).map
                (conormalSheafSelfIso i).hom)) := by
  have h := (modulePushforwardSquareIso
      (Z.toSheafedSpace.ofRestrict ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)
      (X.toSheafedSpace.ofRestrict V.isOpenEmbedding)
      (restrictHom i.toLRSHom.toShHom V) i.toLRSHom.toShHom
      (restrictHom_comp_ofRestrict i.toLRSHom.toShHom V)).inv.naturality
    ((modulePullback (Z.toSheafedSpace.ofRestrict
      ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).map
        (conormalSheafSelfIso i).hom)
  exact h

/-- **`Stacks.Immersion.conormalSheafSelfIso` passes through the whole restriction comparison.**
Composing the identification of the conormal sheaf of the defining factorization with the
canonical restriction-of-sections comparison into `(ι_V)_* ((i ∣_ V)_* 𝒞_{i ∣_ V})` gives back the
same comparison read at the conormal sheaf of `i` itself. -/
theorem conormalSheafSelfIso_hom_comp_restrictConormalUnit (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) :
    (modulePushforward i.toLRSHom.toShHom).map (conormalSheafSelfIso i).hom ≫
        (modulePushforward i.toLRSHom.toShHom).map
            ((modulePullbackPushforwardAdjunction
              (Z.toSheafedSpace.ofRestrict
                ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).unit.app
              (conormalSheaf i.liftCoborder.toLRSHom.toShHom)) ≫
          (modulePushforwardSquareIso
              (Z.toSheafedSpace.ofRestrict
                ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)
              (X.toSheafedSpace.ofRestrict V.isOpenEmbedding)
              (restrictHom i.toLRSHom.toShHom V) i.toLRSHom.toShHom
              (restrictHom_comp_ofRestrict i.toLRSHom.toShHom V)).inv.app
            ((modulePullback (Z.toSheafedSpace.ofRestrict
              ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).obj
                (conormalSheaf i.liftCoborder.toLRSHom.toShHom)) ≫
          (modulePushforward (X.toSheafedSpace.ofRestrict
            V.isOpenEmbedding)).map
            ((modulePushforward (restrictHom i.toLRSHom.toShHom V)).map
              ((modulePullbackRestrictIso Z.toSheafedSpace
                  ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).hom.app
                    (conormalSheaf i.liftCoborder.toLRSHom.toShHom) ≫
                ((moduleRestrict Z.toSheafedSpace
                      ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).map
                    (conormalSheafSelfIso i).inv ≫
                  (restrictConormalSheafIso i.toLRSHom.toShHom V).hom))) =
      (modulePushforward i.toLRSHom.toShHom).map
          ((modulePullbackPushforwardAdjunction
            (Z.toSheafedSpace.ofRestrict
              ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).unit.app
            (conormalSheaf i.toLRSHom.toShHom)) ≫
        (modulePushforwardSquareIso
              (Z.toSheafedSpace.ofRestrict
                ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)
              (X.toSheafedSpace.ofRestrict V.isOpenEmbedding)
              (restrictHom i.toLRSHom.toShHom V) i.toLRSHom.toShHom
              (restrictHom_comp_ofRestrict i.toLRSHom.toShHom V)).inv.app
            ((modulePullback (Z.toSheafedSpace.ofRestrict
              ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).obj
                (conormalSheaf i.toLRSHom.toShHom)) ≫
          (modulePushforward (X.toSheafedSpace.ofRestrict
            V.isOpenEmbedding)).map
            ((modulePushforward (restrictHom i.toLRSHom.toShHom V)).map
              ((modulePullbackRestrictIso Z.toSheafedSpace
                  ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).hom.app
                    (conormalSheaf i.toLRSHom.toShHom) ≫
                (restrictConormalSheafIso i.toLRSHom.toShHom V).hom)) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ _) (modulePushforward_unit_app_conormalSheafSelfIso i V)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun z => _ ≫ z)
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun z => z ≫ _)
                (modulePushforwardSquareIso_inv_app_conormalSheafSelfIso i V)).trans
              ((Category.assoc _ _ _).trans
                (congrArg (fun z => _ ≫ z)
                  (pushforward_modulePullbackRestrictIso_hom_app_conormalSheafSelfIso
                    i V))))))))

/-- **The factorization-free conormal quotient map across the restriction square.** The canonical
quotient map `ℐ_i ⟶ i_* 𝒞_{Z/X}` of `Stacks.Immersion.canonicalConormalQuotientMap`, followed by
the canonical restriction-of-sections comparison into `(ι_V)_* ((i ∣_ V)_* 𝒞_{i ∣_ V})`, is the
right-hand side of the unit square
`Stacks.ClosedImmersion.restrictConormalSheafIso_comp_unit`, read at the conormal sheaf of `i`
itself rather than at that of its defining factorization. -/
theorem canonicalConormalQuotientMap_comp_restrictConormal (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) :
    canonicalConormalQuotientMap i ≫
        (modulePushforward i.toLRSHom.toShHom).map
          ((modulePullbackPushforwardAdjunction
            (Z.toSheafedSpace.ofRestrict
              ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).unit.app
            (conormalSheaf i.liftCoborder.toLRSHom.toShHom)) ≫
        (modulePushforwardSquareIso
            (Z.toSheafedSpace.ofRestrict
              ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)
            (X.toSheafedSpace.ofRestrict V.isOpenEmbedding)
            (restrictHom i.toLRSHom.toShHom V) i.toLRSHom.toShHom
            (restrictHom_comp_ofRestrict i.toLRSHom.toShHom V)).inv.app
          ((modulePullback (Z.toSheafedSpace.ofRestrict
            ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).obj
              (conormalSheaf i.liftCoborder.toLRSHom.toShHom)) ≫
        (modulePushforward (X.toSheafedSpace.ofRestrict
          V.isOpenEmbedding)).map
          ((modulePushforward (restrictHom i.toLRSHom.toShHom V)).map
            ((modulePullbackRestrictIso Z.toSheafedSpace
                ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).hom.app
                  (conormalSheaf i.liftCoborder.toLRSHom.toShHom) ≫
              ((moduleRestrict Z.toSheafedSpace ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).map
                  (conormalSheafSelfIso i).inv ≫
                (restrictConormalSheafIso i.toLRSHom.toShHom V).hom))) =
      (modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
          (idealSheaf i.toLRSHom.toShHom) ≫
        (modulePushforward i.toLRSHom.toShHom).map
            ((modulePullbackPushforwardAdjunction
              (Z.toSheafedSpace.ofRestrict
                ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).unit.app
              (conormalSheaf i.toLRSHom.toShHom)) ≫
          (modulePushforwardSquareIso
                (Z.toSheafedSpace.ofRestrict
                  ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)
                (X.toSheafedSpace.ofRestrict V.isOpenEmbedding)
                (restrictHom i.toLRSHom.toShHom V) i.toLRSHom.toShHom
                (restrictHom_comp_ofRestrict i.toLRSHom.toShHom V)).inv.app
              ((modulePullback (Z.toSheafedSpace.ofRestrict
                ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).obj
                  (conormalSheaf i.toLRSHom.toShHom)) ≫
            (modulePushforward (X.toSheafedSpace.ofRestrict
              V.isOpenEmbedding)).map
              ((modulePushforward (restrictHom i.toLRSHom.toShHom V)).map
                ((modulePullbackRestrictIso Z.toSheafedSpace
                    ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).hom.app
                      (conormalSheaf i.toLRSHom.toShHom) ≫
                  (restrictConormalSheafIso i.toLRSHom.toShHom V).hom)) :=
  (Category.assoc _ _ _).trans
    (congrArg (fun z => _ ≫ z) (conormalSheafSelfIso_hom_comp_restrictConormalUnit i V))

/-- **Stacks Project, Tag 01R3 part (2), the half that lives on `X`: the canonical quotient map
of `i` restricts to the conormal quotient map of `i ∣_ V`.** The factorization-free quotient map
`ℐ_i ⟶ i_* 𝒞_{Z/X}` of `Stacks.Immersion.canonicalConormalQuotientMap`, followed by the canonical
restriction-of-sections comparison into `(ι_V)_* ((i ∣_ V)_* 𝒞_{i ∣_ V})`, is the unit of
`(ι_V)^* ⊣ (ι_V)_*` at `ℐ_i` followed by `(ι_V)_*` of the ideal-sheaf transport
`Stacks.ClosedImmersion.restrictIdealSheafIso` and of the conormal quotient map of `i ∣_ V`.

So the two sides of
```
ℐ_i ---------η_i--------→ i_* 𝒞_{Z/X}
|                              |
↓                              ↓
(ι_V)_* ℐ_{i ∣_ V} --→ (ι_V)_*((i ∣_ V)_* 𝒞_{i ∣_ V})
```
agree, the bottom edge being the conormal quotient map of the restricted morphism. -/
theorem canonicalConormalQuotientMap_comp_restrictConormal_eq_unit (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) :
    canonicalConormalQuotientMap i ≫
        (modulePushforward i.toLRSHom.toShHom).map
          ((modulePullbackPushforwardAdjunction
            (Z.toSheafedSpace.ofRestrict
              ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).unit.app
            (conormalSheaf i.liftCoborder.toLRSHom.toShHom)) ≫
        (modulePushforwardSquareIso
            (Z.toSheafedSpace.ofRestrict
              ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)
            (X.toSheafedSpace.ofRestrict V.isOpenEmbedding)
            (restrictHom i.toLRSHom.toShHom V) i.toLRSHom.toShHom
            (restrictHom_comp_ofRestrict i.toLRSHom.toShHom V)).inv.app
          ((modulePullback (Z.toSheafedSpace.ofRestrict
            ((Opens.map i.toLRSHom.toShHom.hom.base).obj V).isOpenEmbedding)).obj
              (conormalSheaf i.liftCoborder.toLRSHom.toShHom)) ≫
        (modulePushforward (X.toSheafedSpace.ofRestrict
          V.isOpenEmbedding)).map
          ((modulePushforward (restrictHom i.toLRSHom.toShHom V)).map
            ((modulePullbackRestrictIso Z.toSheafedSpace
                ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).hom.app
                  (conormalSheaf i.liftCoborder.toLRSHom.toShHom) ≫
              ((moduleRestrict Z.toSheafedSpace ((Opens.map i.toLRSHom.toShHom.hom.base).obj V)).map
                  (conormalSheafSelfIso i).inv ≫
                (restrictConormalSheafIso i.toLRSHom.toShHom V).hom))) =
      (modulePullbackPushforwardAdjunction (X.toSheafedSpace.ofRestrict
            V.isOpenEmbedding)).unit.app (idealSheaf i.toLRSHom.toShHom) ≫
        (modulePushforward (X.toSheafedSpace.ofRestrict V.isOpenEmbedding)).map
          ((modulePullbackRestrictIso X.toSheafedSpace V).hom.app
              (idealSheaf i.toLRSHom.toShHom) ≫
            (restrictIdealSheafIso i.toLRSHom.toShHom V).hom ≫
              (modulePullbackPushforwardAdjunction
                (restrictHom i.toLRSHom.toShHom V)).unit.app
                (idealSheaf (restrictHom i.toLRSHom.toShHom V))) :=
  (canonicalConormalQuotientMap_comp_restrictConormal i V).trans
    (restrictConormalSheafIso_comp_unit_scheme i V).symm


end Stacks.Immersion

end
