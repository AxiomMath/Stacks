module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.RingTheory.Syntomic.Defs
public import StacksFrontier.RingTheory.CompleteIntersection.Relative
public import StacksCore.Tactic.StacksAttribute

/-!
# Syntomic morphisms of schemes

A morphism of schemes is *syntomic at* a point when, on suitable affine open neighbourhoods in
the source and target, its induced map on coordinate rings is syntomic; it is *syntomic* when it
is syntomic at every point of its source. A morphism of affine schemes is *standard syntomic*
when its induced map on global sections is a relative global complete intersection. A scheme
over a field is a *local complete intersection* over that field when its structure morphism is
syntomic.

## Main definitions

* `AlgebraicGeometry.SyntomicAt`: a scheme morphism is syntomic at a specified point.
* `AlgebraicGeometry.Syntomic`: a morphism of schemes is syntomic.
* `AlgebraicGeometry.IsStandardSyntomic`: a morphism of affine schemes is standard syntomic.
* `AlgebraicGeometry.IsLocalCompleteIntersectionOverField`: the local complete intersection
  condition for a scheme over a field.

## Main results

* `AlgebraicGeometry.syntomicAt_iff`: the affine-neighbourhood characterization of syntomicity at
  a point.
* `AlgebraicGeometry.isStandardSyntomic_iff_exists_arrowIso_spec`: a standard syntomic morphism is
  isomorphic to the spectrum of a relative global complete intersection ring map.

## References

* [Stacks Project, Tag 01UC](https://stacks.math.columbia.edu/tag/01UC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes `f : X ⟶ S` is *syntomic at* `x : X` if there are affine open
neighbourhoods `U` of `x` and `V` of `f(x)`, with `f(U) ⊆ V`, for which the induced map
`Γ(S, V) → Γ(X, U)` is syntomic. -/
@[stacks 01UC "syntomic_at_point"]
def SyntomicAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ V : S.affineOpens, ∃ hUV : U.1 ≤ f ⁻¹ᵁ V.1,
    letI := (f.appLE V.1 U.1 hUV).hom.toAlgebra
    Algebra.Syntomic Γ(S, V.1) Γ(X, U.1)

/-- A morphism is syntomic at a point exactly when it is represented by a syntomic ring map on some
affine neighbourhood of that point and an affine neighbourhood of its image. -/
theorem syntomicAt_iff {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    SyntomicAt f x ↔ ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ V : S.affineOpens,
      ∃ hUV : U.1 ≤ f ⁻¹ᵁ V.1,
        letI := (f.appLE V.1 U.1 hUV).hom.toAlgebra
        Algebra.Syntomic Γ(S, V.1) Γ(X, U.1) := Iff.rfl

/-- A morphism of schemes is syntomic if it is syntomic at every point of its source. -/
@[stacks 01UC "syntomic_morphism"] abbrev Syntomic {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ x : X, SyntomicAt f x

/-- A morphism `f : X ⟶ S` of affine schemes is **standard syntomic** if the induced ring map
`Γ(S, ⊤) → Γ(X, ⊤)` is a relative global complete intersection. Via the canonical isomorphisms of
affine schemes with the spectra of their global sections, this says precisely that `f` is
isomorphic to the spectrum of a relative global complete intersection. -/
@[stacks 01UC "standard_syntomic_morphism"]
abbrev IsStandardSyntomic {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) : Prop :=
  letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  Algebra.IsRelativeGlobalCompleteIntersection Γ(S, ⊤) Γ(X, ⊤)

/-- A morphism `f` of affine schemes is standard syntomic exactly when there is a relative global
complete intersection ring map `g : Γ(S, ⊤) → A` with `A ≃ₐ[Γ(S, ⊤)] Γ(X, ⊤)` and `f` isomorphic,
as an arrow, to `Spec.map g`. -/
theorem isStandardSyntomic_iff_exists_arrowIso_spec
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) :
    IsStandardSyntomic f ↔
      letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
      ∃ (A : Type u) (_ : CommRing A) (g : Γ(S, ⊤) →+* A),
        letI : Algebra Γ(S, ⊤) A := g.toAlgebra
        Algebra.IsRelativeGlobalCompleteIntersection Γ(S, ⊤) A ∧
          Nonempty (A ≃ₐ[Γ(S, ⊤)] Γ(X, ⊤)) ∧
          Nonempty (Arrow.mk f ≅ Arrow.mk (Spec.map (CommRingCat.ofHom g))) := by
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  refine ⟨fun h ↦ ⟨Γ(X, ⊤), inferInstance, f.appTop.hom, h, ⟨AlgEquiv.refl⟩,
      ⟨arrowIsoSpecΓOfIsAffine f⟩⟩, ?_⟩
  rintro ⟨A, _, g, hA, ⟨e⟩, _⟩
  let : Algebra Γ(S, ⊤) A := g.toAlgebra
  exact Algebra.IsRelativeGlobalCompleteIntersection.of_algEquiv e

/-- A scheme over a field is a **local complete intersection over the field** if its structure
morphism to the spectrum of the field is syntomic. -/
@[stacks 01UC "local_complete_intersection_over_field"]
abbrev IsLocalCompleteIntersectionOverField {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : Prop :=
  Syntomic f

end AlgebraicGeometry
