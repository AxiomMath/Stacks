module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksCore.Tactic.StacksAttribute

/-!
# Limits of diagrams of affine schemes

A diagram of affine schemes has a limit in the category of schemes, and that limit is the
spectrum of the colimit of the rings of global sections.

No cofiltration and no affineness of the transition morphisms is needed: the statement holds for
an arbitrary small diagram of affine schemes.

## Main definitions

* `AlgebraicGeometry.Scheme.affineLimitCone` is the limit cone of a diagram of affine schemes,
  with apex `Spec` of the limit of the rings of global sections.

## Main results

* `AlgebraicGeometry.Scheme.hasLimit_of_isAffine` is the resulting existence statement.
* `AlgebraicGeometry.Scheme.affineLimitCone_pt` identifies the apex of that cone.

## Implementation notes

That the limit is again affine is Mathlib's `AlgebraicGeometry.Scheme.isAffine_of_isLimit`, which
holds for any limit cone of a diagram of affine schemes; it is restated here as
`AlgebraicGeometry.Scheme.isAffine_affineLimitCone_pt` for the cone constructed here.

`AlgebraicGeometry.Scheme.hasLimit_of_isAffine` is deliberately *not* an instance: the hypothesis
`∀ i, IsAffine (D.obj i)` would make instance search for `HasLimit` on an arbitrary diagram of
schemes try to prove that every object of it is affine.

## References

* [Stacks Project, Tag 01YW](https://stacks.math.columbia.edu/tag/01YW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]

/-- The limit cone of a diagram of affine schemes, with apex `Spec` applied to the limit in
`CommRingCatᵒᵖ` of the diagram of rings of global sections. -/
@[stacks 01YW "the limit cone, as Spec of the colimit of global sections",
  sga "4 VII 5.1" "all schemes affine"]
noncomputable def affineLimitCone : LimitCone D :=
  letI e : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec := Functor.whiskerLeft D ΓSpec.adjunction.unit
  haveI (i : I) : IsIso (e.app i) := IsAffine.affine
  haveI : IsIso e := NatIso.isIso_of_isIso_app e
  ⟨_, (IsLimit.postcomposeInvEquiv (asIso e) _).symm
    (isLimitOfPreserves Scheme.Spec (limit.isLimit (D ⋙ Scheme.Γ.rightOp)))⟩

/-- The apex of `AlgebraicGeometry.Scheme.affineLimitCone` is the spectrum of the limit of the
rings of global sections of the diagram, that is, of their colimit as rings. -/
theorem affineLimitCone_pt :
    (affineLimitCone D).cone.pt = Scheme.Spec.obj (limit (D ⋙ Scheme.Γ.rightOp)) :=
  rfl

/-- A diagram of affine schemes has a limit in the category of schemes. -/
@[stacks 01YW "existence of the limit", sga "4 VII 5.1" "all schemes affine"]
theorem hasLimit_of_isAffine : HasLimit D := ⟨⟨affineLimitCone D⟩⟩

/-- The limit of a diagram of affine schemes is affine. -/
theorem isAffine_affineLimitCone_pt : IsAffine (affineLimitCone D).cone.pt :=
  Scheme.isAffine_of_isLimit _ (affineLimitCone D).isLimit

omit [∀ i, IsAffine (D.obj i)] in
/-- Let `D` be a diagram of schemes with affine transition morphisms and let `U` be an affine open
of `D i`. Then the diagram `j ↦ (D j ⟶ D i)⁻¹ U` of inverse images of `U`, indexed by the objects
of `D` over `i`, consists of affine schemes and therefore has a limit. -/
theorem hasLimit_opensDiagram [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (i : I)
    {U : (D.obj i).Opens} (hU : IsAffineOpen U) : HasLimit (opensDiagram D i U) :=
  have (j : Over i) : IsAffine ((opensDiagram D i U).obj j) := hU.preimage (D.map j.hom)
  hasLimit_of_isAffine _

/-! ### The affine stage of section 01YV

Section 01YV constructs the limit of an inverse system of schemes with affine transition
morphisms. Its first step, Lemma 01YW, is the case of a system of affine schemes, carried here. -/

add_to_stacks 01YV "the construction of the limit when all the schemes of the system are affine: \
the limit cone is `Spec` of the colimit of the rings of global sections (Lemma 01YW)"
  AlgebraicGeometry.Scheme.affineLimitCone
add_to_stacks 01YV "existence of the limit when all the schemes of the system are affine \
(Lemma 01YW)" AlgebraicGeometry.Scheme.hasLimit_of_isAffine

end AlgebraicGeometry.Scheme

end
