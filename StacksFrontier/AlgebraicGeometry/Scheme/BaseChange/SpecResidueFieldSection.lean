module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ResidueFieldFactor

/-!
# The section from the residue field of the base point

Let `f : X ⟶ S` carry a point `x` to `s` and induce an *isomorphism* of residue fields there.
Then the canonical morphism `Spec κ(s) ⟶ X` obtained by inverting that isomorphism is a section
of `f` over `Spec κ(s) ⟶ S`, and it depends only on `f` and `x`: for a factorization
`X ⟶ D ⟶ S` the section of the composite, followed by `X ⟶ D`, is the section of `D ⟶ S` at the
image of `x`.

The consequence this file is built for: if two morphisms `A ⟶ D` and `B ⟶ D` over `S` carry points
`α` and `β` to one and the same point of `D`, and both composites to `S` are trivial on residue
fields at those points, then the two sections `Spec κ(s) ⟶ D` agree. In the proof of Stacks Tag
0GDX this is what identifies the two maps `Spec κ(s) ⟶ T` — one through
`Spec(𝒪^∧_{S,s})` and `σ`, one through the slice `V` and `τ` — and hence makes the fibres
`(Y_σ)_s` and `(Y ×_{T,τ} V)_v` the same scheme, which is the identification under which the
source's point `y_τ` corresponds to `y_σ`.

## Main definitions

* `AlgebraicGeometry.specResidueFieldSection`: the morphism `Spec κ(s) ⟶ X`.

## Main results

* `AlgebraicGeometry.specResidueFieldSection_congr`,
  `AlgebraicGeometry.specResidueFieldSection_congr_hom`: it depends only on the morphism and the
  point.
* `AlgebraicGeometry.specResidueFieldSection_comp_eq`: the section of a composite, followed by the
  first factor, is the section of the second factor.
* `AlgebraicGeometry.specResidueFieldSection_comp_eq_comp`: two such sections into a common target
  agree.
* `AlgebraicGeometry.specResidueFieldSection_comp_self`,
  `AlgebraicGeometry.specResidueFieldSection_apply`: it is a section, and it hits `x`.

## Implementation notes

The residue field map is transported along `f x = s` with
`AlgebraicGeometry.Scheme.residueFieldCongr`, exactly as
`AlgebraicGeometry.EtaleNeighborhood.residueFieldMap` does. The computation
`specResidueFieldSection_comp_eq` is pure `Spec.map` bookkeeping on top of the naturality
`AlgebraicGeometry.Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`; the only step with
content is that `IsIso` of the residue field map of a composite gives `IsIso` for the second
factor at the image point, which is
`AlgebraicGeometry.isIso_residueFieldMap_of_isIso_residueFieldMap_comp`.

## References

* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The isomorphism `κ(s) ≅ κ(x)` attached to a point `x` over `s` at which `f` is trivial on
residue fields. -/
public abbrev residueFieldSectionIso {X S : Scheme.{u}} (f : X ⟶ S) {x : X} {s : S}
    (hfx : f x = s) : S.residueField s ⟶ X.residueField x :=
  (S.residueFieldCongr hfx).inv ≫ f.residueFieldMap x

/-- The map `κ(s) ⟶ κ(x)` of `residueFieldSectionIso` is an isomorphism when `f` is trivial on
residue fields at `x`. -/
public instance isIso_residueFieldSectionIso {X S : Scheme.{u}} (f : X ⟶ S) {x : X} {s : S}
    (hfx : f x = s) [IsIso (f.residueFieldMap x)] :
    IsIso (residueFieldSectionIso f hfx) :=
  IsIso.comp_isIso' inferInstance inferInstance

/-- The canonical morphism `Spec κ(s) ⟶ X` attached to a point `x` over `s` at which `f` is
trivial on residue fields. -/
public def specResidueFieldSection {X S : Scheme.{u}} (f : X ⟶ S) {x : X} {s : S}
    (hfx : f x = s) (h : IsIso (f.residueFieldMap x)) : Spec (S.residueField s) ⟶ X :=
  haveI := h
  Spec.map (inv (residueFieldSectionIso f hfx)) ≫ X.fromSpecResidueField x

/-- The section carries the unique point of `Spec κ(s)` to `x`. -/
@[simp]
public lemma specResidueFieldSection_apply {X S : Scheme.{u}} (f : X ⟶ S) {x : X} {s : S}
    (hfx : f x = s) (h : IsIso (f.residueFieldMap x)) (z : Spec (S.residueField s)) :
    specResidueFieldSection f hfx h z = x := by
  show X.fromSpecResidueField x (Spec.map (inv (residueFieldSectionIso f hfx)) z) = x
  exact Scheme.fromSpecResidueField_apply x _

/-- The section depends on the point only through the point itself: the hypotheses are
propositions, so they are irrelevant. -/
public theorem specResidueFieldSection_congr {X S : Scheme.{u}} (f : X ⟶ S) {x x' : X} {s : S}
    (hxx : x = x') (hfx : f x = s) (hfx' : f x' = s)
    (h : IsIso (f.residueFieldMap x)) (h' : IsIso (f.residueFieldMap x')) :
    specResidueFieldSection f hfx h = specResidueFieldSection f hfx' h' := by
  cases hxx
  rfl

/-- The section depends on the morphism only through the morphism itself. -/
public theorem specResidueFieldSection_congr_hom {X S : Scheme.{u}} {f f' : X ⟶ S}
    (hff : f = f') {x : X} {s : S} (hfx : f x = s) (hfx' : f' x = s)
    (h : IsIso (f.residueFieldMap x)) (h' : IsIso (f'.residueFieldMap x)) :
    specResidueFieldSection f hfx h = specResidueFieldSection f' hfx' h' := by
  cases hff
  rfl

/-- Postcomposing the section with `a` is `Spec` of a residue field map followed by the canonical
morphism at `a x`. -/
private theorem specResidueFieldSection_comp_hom {X D S : Scheme.{u}} (f : X ⟶ S) (a : X ⟶ D)
    {x : X} {s : S} (hfx : f x = s) (h : IsIso (f.residueFieldMap x)) :
    specResidueFieldSection f hfx h ≫ a =
      Spec.map (a.residueFieldMap x ≫ inv (residueFieldSectionIso f hfx)) ≫
        D.fromSpecResidueField (a x) := by
  have := h
  show Spec.map (inv (residueFieldSectionIso f hfx)) ≫ X.fromSpecResidueField x ≫ a = _
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField a x, ← Spec.map_comp_assoc]

/-- **The section of a composite, followed by the first factor, is the section of the second
factor.** -/
public theorem specResidueFieldSection_comp_eq {X D S : Scheme.{u}} (a : X ⟶ D) (q : D ⟶ S)
    {x : X} {s : S} (hx : (a ≫ q) x = s) (h : IsIso ((a ≫ q).residueFieldMap x)) :
    specResidueFieldSection (a ≫ q) hx h ≫ a =
      specResidueFieldSection q (hx : q (a x) = s)
        (isIso_residueFieldMap_of_isIso_residueFieldMap_comp a q x h) := by
  have := h
  have hq : IsIso (q.residueFieldMap (a x)) :=
    isIso_residueFieldMap_of_isIso_residueFieldMap_comp a q x h
  have hfac : residueFieldSectionIso (a ≫ q) hx =
      residueFieldSectionIso q (hx : q (a x) = s) ≫ a.residueFieldMap x :=
    by simp [residueFieldSectionIso, Scheme.residueFieldMap_comp]; rfl
  have hring : a.residueFieldMap x ≫ inv (residueFieldSectionIso (a ≫ q) hx) =
      inv (residueFieldSectionIso q (hx : q (a x) = s)) := by
    rw [IsIso.comp_inv_eq, hfac, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [specResidueFieldSection_comp_hom (a ≫ q) a hx h, hring]
  rfl

/-- **Two sections from the residue field of the base point into a common target agree.** -/
public theorem specResidueFieldSection_comp_eq_comp {A B D S : Scheme.{u}}
    (a : A ⟶ D) (b : B ⟶ D) (q : D ⟶ S) {α : A} {β : B} {s : S}
    (hd : a α = b β)
    (hα : (a ≫ q) α = s) (hβ : (b ≫ q) β = s)
    (ha : IsIso ((a ≫ q).residueFieldMap α)) (hb : IsIso ((b ≫ q).residueFieldMap β)) :
    specResidueFieldSection (a ≫ q) hα ha ≫ a =
      specResidueFieldSection (b ≫ q) hβ hb ≫ b := by
  rw [specResidueFieldSection_comp_eq a q hα ha, specResidueFieldSection_comp_eq b q hβ hb]
  exact specResidueFieldSection_congr q hd _ _ _ _

/-- The section is a section of `f` over the canonical morphism from the residue field of `s`. -/
public theorem specResidueFieldSection_comp_self {X S : Scheme.{u}} (f : X ⟶ S) {x : X} {s : S}
    (hfx : f x = s) (h : IsIso (f.residueFieldMap x)) :
    specResidueFieldSection f hfx h ≫ f = S.fromSpecResidueField s := by
  have := h
  have hring : f.residueFieldMap x ≫ inv (residueFieldSectionIso f hfx) =
      (S.residueFieldCongr hfx).hom := by
    show f.residueFieldMap x ≫ inv ((S.residueFieldCongr hfx).inv ≫ f.residueFieldMap x) = _
    rw [IsIso.comp_inv_eq, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [specResidueFieldSection_comp_hom f f hfx h, hring]
  exact Scheme.residueFieldCongr_fromSpecResidueField hfx

end AlgebraicGeometry

end
