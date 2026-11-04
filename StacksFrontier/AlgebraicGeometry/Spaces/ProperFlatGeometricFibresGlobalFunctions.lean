module

import all StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.RestrictedFibreRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGeometricallyConnectedGlobalFunctions

/-!
# Global functions on the fibres of a morphism with reduced connected geometric fibres

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` whose geometric fibres are
reduced and connected. For a field-valued point `Spec k ⟶ Y`, the base change of the fibre
`X_k` to an algebraically closed extension `K` of `k` is the geometric fibre of `f` over the
composite `Spec K ⟶ Y`. So `X_k` satisfies the hypotheses of
`AlgebraicGeometry.Space.bijective_algebraMap_globalFunctions_of_isProper`, and when `X_k` is
proper over `k` its global functions are `k`. This is the reduction of Stacks 0E0S to
Stacks 0E6B carried out in the source's proof, through Spaces over Fields, Lemma 72.14.3.

## Main definitions

* `AlgebraicGeometry.Space.FieldValuedPoint.extend`: the field-valued point
  `Spec K ⟶ Spec k ⟶ Y` attached to a field-valued point `Spec k ⟶ Y` and an extension `K/k`.

## Main results

* `AlgebraicGeometry.Space.fibreOverFieldValuedPointExtendIso`: the fibre over the extended
  point is the base change of the fibre along `K/k`.
* `AlgebraicGeometry.Space.bijective_algebraMap_globalFunctions_fibre_of_geometricFibres`:
  the global functions of the fibre of `f` over a field-valued point are the field, when the
  fibre is proper and the geometric fibres of `f` are reduced and connected.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The field-valued point `Spec K ⟶ Spec k ⟶ Y` attached to a field-valued point `p` of `Y` with
field `k` and a field extension `K/k` whose spectrum lies in the site. -/
noncomputable def FieldValuedPoint.extend (p : FieldValuedPoint B S hS Y) (K : Type u) [Field K]
    [Algebra p.carrier K] (hK : B.Contains (Spec (.of K))) : FieldValuedPoint B S hS Y where
  carrier := K
  contained := hK
  toBase := (specMapOfExtension B p.carrier p.contained K hK ≫
    (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hS)).hom
  value := Y.map (Over.homMk (specMapOfExtension B p.carrier p.contained K hK) rfl).op p.value

/-- The field of the extended point `p.extend B S hS K hK` is `K`. -/
@[simp]
theorem FieldValuedPoint.extend_carrier (p : FieldValuedPoint B S hS Y) (K : Type u) [Field K]
    [Algebra p.carrier K] (hK : B.Contains (Spec (.of K))) : (p.extend B S hS K hK).carrier = K :=
  rfl

/-- **The fibre over an extended point is the base change of the fibre.** For a field-valued
point `p` of `Y` with field `k` and an extension `K/k`, the fibre of `f` over `Spec K ⟶ Y` is the
base change along `K/k` of the fibre of `f` over `p`. -/
noncomputable def fibreOverFieldValuedPointExtendIso (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y)
    (K : Type u) [Field K] [Algebra p.carrier K] (hK : B.Contains (Spec (.of K))) :
    (fibreOverFieldValuedPoint B S hS f (p.extend B S hS K hK) :
        (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u) ≅
      fieldBaseChange B p.carrier p.contained (fibreOverFieldValuedPoint B S hS f p) K hK :=
  (nonempty_restrictedFibre_iso_relocalizeRestrict B S hS f p.contained hK ⟨p.toBase⟩
    (specMapOfExtension B p.carrier p.contained K hK) p.value).some

/-- **The global functions of a fibre with reduced connected geometric fibres.** Let
`f : X ⟶ Y` be a morphism of algebraic spaces whose geometric fibres are reduced and connected,
and let `p : Spec k ⟶ Y` be a field-valued point whose fibre `X_k` is proper over `k`. Then
`k = H⁰(X_k, 𝒪_{X_k})`. -/
theorem bijective_algebraMap_globalFunctions_fibre_of_geometricFibres (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hred : ∀ y : GeometricPoint B S hS Y,
      HasEtaleLocalProperty B (Spec (.of y.1.carrier)) y.1.contained
        (fibreOverFieldValuedPoint B S hS f y.1)
        (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T))
    (hconn : ∀ y : GeometricPoint B S hS Y,
      ConnectedPoints B (Spec (.of y.1.carrier)) y.1.contained
        (fibreOverFieldValuedPoint B S hS f y.1))
    (p : FieldValuedPoint B S hS Y)
    (z : fibreOverFieldValuedPoint B S hS f p ⟶ yoneda.obj (Over.mk (𝟙 (B.obj p.contained))))
    (hz : IsProper B (Spec (.of p.carrier)) p.contained z) :
    Function.Bijective (algebraMap p.carrier
      (globalFunctions B (Spec (.of p.carrier)) p.contained
        (fibreOverFieldValuedPoint B S hS f p))) := by
  refine bijective_algebraMap_globalFunctions_of_isProper B p.carrier p.contained _
    (isAlgebraicSpace_fibreOverFieldValuedPoint B S hS f hX hY p) z hz
    (fun K _ _ _ hK => ?_) (fun K _ _ _ hK => ?_)
  · exact (hasEtaleLocalProperty_iff_of_iso B (Spec (.of K)) hK _
      (fibreOverFieldValuedPointExtendIso B S hS f p K hK)).mp (hred ⟨p.extend B S hS K hK, ‹_›⟩)
  · exact connectedSpace_of_presheafIso B (Spec (.of K)) hK
      (fibreOverFieldValuedPointExtendIso B S hS f p K hK) (hconn ⟨p.extend B S hS K hK, ‹_›⟩)

end AlgebraicGeometry.Space
