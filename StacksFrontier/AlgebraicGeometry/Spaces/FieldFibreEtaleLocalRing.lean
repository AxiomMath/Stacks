module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFieldSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreSourceSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing

/-!
# The maximal ideal of the base dies in the étale local ring of a field fibre

Let `h : Y ⟶ Z` be a morphism of algebraic spaces and let `z` be a field-valued point of `Z`
with field of definition `K`.  The field fibre `Y_z = Spec(K) ×_{z, Z} Y` maps to `Spec(K)`, and
the étale local ring of `Spec(K)` at any geometric point is a field.  Since the canonical
homomorphisms of étale local rings of Stacks 04NG compose and are local, the maximal ideal
`𝔪_{z̄}` of `𝒪_{Z, z̄}` therefore extends to `⊥` in `𝒪_{Y_z, ȳ_z}`.

This is the step that makes `𝒪_{Y_z, ȳ_z}` an algebra over the fibre
`𝒪_{Z, z̄}/𝔪_{z̄} = κ(z̄)`, and thence an algebra over
`𝒪_{Y, ȳ}/𝔪_{z̄}𝒪_{Y, ȳ}`, which is what
`Module.Flat.quotSMul_iff_tensor_of_isPushout` requires of its `R'` in the comparison of
conditions (1) and (2) of Stacks 05WY.

## Main results

* `AlgebraicGeometry.Space.map_maximalIdeal_etaleLocalRingMap_comp_eq_bot`: the general
  statement — a morphism factoring through a space whose étale local ring at the intermediate
  geometric point is a field kills the maximal ideal of the target.
* `AlgebraicGeometry.Space.map_maximalIdeal_etaleLocalRingMap_fieldFibreSpace_eq_bot`: the
  case of a field fibre, where the intermediate space is `Spec(K)`.

## Implementation notes

The general statement is the one with content; the field-fibre case is it applied to the
projection `Y_z ⟶ Spec(K)` of
`AlgebraicGeometry.Space.isPullback_fieldFibreSpace_snd`, with the field hypothesis supplied by
`AlgebraicGeometry.Space.isField_etaleLocalRing_yoneda` together with
`AlgebraicGeometry.isField_stalk_Spec_field`.

Both are stated for the composite `p.hom ≫ q.hom` of the underlying morphisms of presheaves
rather than for `(p ≫ q).hom`, which is the spelling `AlgebraicGeometry.Space.etaleLocalRingMap`
consumes.

## References

* [Stacks Project, Tag 05WY](https://stacks.math.columbia.edu/tag/05WY)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism into a space whose étale local ring at a geometric point is a field kills the
maximal ideal of the target.**  For `q : V ⟶ Z` and a geometric point `v̄` of `V` at which the
étale local ring of `V` is a field, the maximal ideal of `𝒪_{Z, z̄}` extends to `⊥` along the
canonical homomorphism `𝒪_{Z, z̄} → 𝒪_{V, v̄}` of Stacks 04NG.

The homomorphism is local, so it carries `𝔪_{z̄}` into the maximal ideal of `𝒪_{V, v̄}`, and that
is `⊥` because the ring is a field. -/
theorem map_maximalIdeal_etaleLocalRingMap_eq_bot_of_isField {V Z : AlgebraicSpaces B S hS}
    (q : V ⟶ Z) (v : GeometricPoint B S hS V.1)
    (hfield : IsField ↥(etaleLocalRing B S hS V.1 v)) :
    letI : IsLocalRing ↥(etaleLocalRing B S hS Z.1 (geometricPointMap q.hom v)) :=
      isLocalRing_etaleLocalRing B S hS Z.1 Z.2 _
    (maximalIdeal ↥(etaleLocalRing B S hS Z.1 (geometricPointMap q.hom v))).map
      (etaleLocalRingMap V.2 q.hom v) = ⊥ := by
  let instZ : IsLocalRing ↥(etaleLocalRing B S hS Z.1 (geometricPointMap q.hom v)) :=
    isLocalRing_etaleLocalRing B S hS Z.1 Z.2 _
  let instV : IsLocalRing ↥(etaleLocalRing B S hS V.1 v) :=
    isLocalRing_etaleLocalRing B S hS V.1 V.2 _
  have := isLocalHom_etaleLocalRingMap B S hS V.2 Z.2 q.hom v
  exact le_bot_iff.mp ((map_maximalIdeal_le _).trans
    (IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield).le)

/-- **A morphism factoring through a space with field étale local ring kills the maximal ideal
of the target.**  Let `p : W ⟶ V` and `q : V ⟶ Z` be morphisms of algebraic spaces and let `w`
be a geometric point of `W` at which the étale local ring of `V` is a field.  Then the maximal
ideal of `𝒪_{Z, z̄}`, for `z̄` the image of `w` in `Z`, extends to `⊥` along the canonical
homomorphism `𝒪_{Z, z̄} → 𝒪_{W, w}` of Stacks 04NG.

The canonical homomorphisms compose, so `𝒪_{Z, z̄} → 𝒪_{W, w}` factors through `𝒪_{V, v̄}`; the
first factor is a local homomorphism, so it carries `𝔪_{z̄}` into the maximal ideal of
`𝒪_{V, v̄}`, which is `⊥` because that ring is a field. -/
theorem map_maximalIdeal_etaleLocalRingMap_comp_eq_bot {W V Z : AlgebraicSpaces B S hS}
    (p : W ⟶ V) (q : V ⟶ Z) (w : GeometricPoint B S hS W.1)
    (hfield : IsField ↥(etaleLocalRing B S hS V.1 (geometricPointMap p.hom w))) :
    letI : IsLocalRing ↥(etaleLocalRing B S hS Z.1
        (geometricPointMap (p.hom ≫ q.hom) w)) :=
      isLocalRing_etaleLocalRing B S hS Z.1 Z.2 _
    (maximalIdeal ↥(etaleLocalRing B S hS Z.1
        (geometricPointMap (p.hom ≫ q.hom) w))).map
      (etaleLocalRingMap W.2 (p.hom ≫ q.hom) w) = ⊥ := by
  have h := congrArg (Ideal.map (etaleLocalRingMap W.2 p.hom w))
    (map_maximalIdeal_etaleLocalRingMap_eq_bot_of_isField B S hS q _ hfield)
  rwa [Ideal.map_map, etaleLocalRingMap_comp, Ideal.map_bot] at h

/-- The étale local ring of `Spec(K)` at any geometric point is a field. -/
private theorem isField_etaleLocalRing_fieldPoint {Z : AlgebraicSpaces B S hS}
    (z : FieldValuedPoint B S hS Z.1)
    (k : GeometricPoint B S hS (schemeSpace (z.siteObject B S hS Z.1)).1) :
    IsField ↥(etaleLocalRing B S hS (schemeSpace (z.siteObject B S hS Z.1)).1 k) :=
  isField_etaleLocalRing_yoneda (z.siteObject B S hS Z.1)
    (fun x => AlgebraicGeometry.isField_stalk_Spec_field z.carrier x) k

/-- **The maximal ideal of the base dies in the étale local ring of `Spec(K)`.**  For a
field-valued point `z` of `Z` with field of definition `K` and a geometric point `k̄` of
`Spec(K)`, the maximal ideal of `𝒪_{Z, z̄}` extends to `⊥` along `𝒪_{Z, z̄} → 𝒪_{Spec(K), k̄}`.

The étale local ring of `Spec(K)` at any geometric point is a field, by
`AlgebraicGeometry.Space.isField_etaleLocalRing_yoneda` applied to
`AlgebraicGeometry.isField_stalk_Spec_field`.  This is the input that makes `𝒪_{Spec(K), k̄}` an
algebra over the residue field of `𝒪_{Z, z̄}`, which is what
`Module.Flat.quotient_of_isPushout` needs of its `R'` in the flatness step for a field fibre. -/
theorem map_maximalIdeal_etaleLocalRingMap_fieldPoint_eq_bot {Z : AlgebraicSpaces B S hS}
    (z : FieldValuedPoint B S hS Z.1)
    (k : GeometricPoint B S hS (schemeSpace (z.siteObject B S hS Z.1)).1) :
    letI : IsLocalRing ↥(etaleLocalRing B S hS Z.1
        (geometricPointMap (fieldPointSpaceHom B S hS z).hom k)) :=
      isLocalRing_etaleLocalRing B S hS Z.1 Z.2 _
    (maximalIdeal ↥(etaleLocalRing B S hS Z.1
        (geometricPointMap (fieldPointSpaceHom B S hS z).hom k))).map
      (etaleLocalRingMap (schemeSpace (z.siteObject B S hS Z.1)).2
        (fieldPointSpaceHom B S hS z).hom k) = ⊥ :=
  map_maximalIdeal_etaleLocalRingMap_eq_bot_of_isField B S hS (fieldPointSpaceHom B S hS z) k
    (isField_etaleLocalRing_fieldPoint B S hS z k)

/-- **The maximal ideal of the base dies in the étale local ring of a field fibre.**  For
`h : Y ⟶ Z` and a field-valued point `z` of `Z`, and for a geometric point `ȳ_z` of the field
fibre `Y_z = Spec(K) ×_{z, Z} Y`, the maximal ideal of `𝒪_{Z, z̄}` extends to `⊥` along the
canonical homomorphism `𝒪_{Z, z̄} → 𝒪_{Y_z, ȳ_z}` which the projection `Y_z ⟶ Spec(K)` followed
by `z : Spec(K) ⟶ Z` induces.

The étale local ring of `Spec(K)` at any geometric point is a field, so this is
`AlgebraicGeometry.Space.map_maximalIdeal_etaleLocalRingMap_comp_eq_bot` applied to the
projection of the defining square of the field fibre. -/
theorem map_maximalIdeal_etaleLocalRingMap_fieldFibreSpace_eq_bot
    {Y Z : AlgebraicSpaces B S hS} (h : Y ⟶ Z) (z : FieldValuedPoint B S hS Z.1)
    (ybar : GeometricPoint B S hS (fieldFibreSpace h z).1) :
    letI : IsLocalRing ↥(etaleLocalRing B S hS Z.1
        (geometricPointMap (pullback.snd h.hom (yonedaEquiv.symm z.value) ≫
          (fieldPointSpaceHom B S hS z).hom) ybar)) :=
      isLocalRing_etaleLocalRing B S hS Z.1 Z.2 _
    (maximalIdeal ↥(etaleLocalRing B S hS Z.1
        (geometricPointMap (pullback.snd h.hom (yonedaEquiv.symm z.value) ≫
          (fieldPointSpaceHom B S hS z).hom) ybar))).map
      (etaleLocalRingMap (fieldFibreSpace h z).2
        (pullback.snd h.hom (yonedaEquiv.symm z.value) ≫
          (fieldPointSpaceHom B S hS z).hom) ybar) = ⊥ :=
  map_maximalIdeal_etaleLocalRingMap_comp_eq_bot B S hS
    (ObjectProperty.homMk (pullback.snd h.hom (yonedaEquiv.symm z.value)) :
      fieldFibreSpace h z ⟶ schemeSpace (z.siteObject B S hS Z.1))
    (fieldPointSpaceHom B S hS z) ybar
    (isField_etaleLocalRing_fieldPoint B S hS z _)

end AlgebraicGeometry.Space

end
