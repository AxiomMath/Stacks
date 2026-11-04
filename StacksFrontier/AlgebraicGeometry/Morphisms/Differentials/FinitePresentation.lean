module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Surjective
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationFromAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteType

/-!
# The differentials of a morphism locally of finite presentation are of finite presentation

For a morphism of schemes `f : X ⟶ S` which is locally of finite presentation, the sheaf of
relative differentials `Ω_{X/S}` is an `𝒪_X`-module of finite presentation.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isFinitePresentation_relativeDifferentials`: for a morphism
  locally of finite presentation the sheaf of relative differentials is of finite presentation.

## Implementation notes

The argument is the finite-presentation analogue of
`AlgebraicGeometry.Scheme.Hom.isFiniteType_relativeDifferentials`, Stacks 01V2, and runs on the
same chart.  Finite presentation of a quasi-coherent module is detected by the sections over the
members of an affine open cover, which is
`Stacks.AlgebraicGeometry.FinitePresentationLocal.isFinitePresentation_of_affineCover`;
quasi-coherence of `Ω_{X/S}` holds for every morphism and is available as the instance
`AlgebraicGeometry.Scheme.Hom.instIsQuasicoherentRelativeDifferentials`.

The cover is chosen one point at a time: an affine open `V` of `S` around the image of the
point, then an affine open `U ⊆ f ⁻¹ V` of `X` around the point itself.  On such a chart
[Stacks, Tag 01UT] — `Stacks.AlgebraicGeometry.AffineDifferentialsIso.
existsUnique_affineDifferentialsIso` — identifies the sections of `Ω_{X/S}` on `U` with the
Kähler differentials of `Γ(S, V) ⟶ Γ(X, U)`, and that ring map is of finite presentation
because `f` is, so Mathlib's instance `Module.FinitePresentation S Ω[S⁄R]` for a finitely
presented algebra applies.  The chart is indexed by the points of `X`, so no refinement of the
cover is needed and the covering condition is read off the choice directly.

Unlike the finite type statement of Stacks 01V2, the chart step cannot be routed through an
*essentially* of finite presentation hypothesis: Mathlib's instance for `Ω[S⁄R]` asks for
`Algebra.FinitePresentation R S` on the nose (its source carries a `TODO` to generalize).  That
costs nothing here, because `AlgebraicGeometry.LocallyOfFinitePresentation` delivers finite
presentation of `Γ(S, V) ⟶ Γ(X, U)` for an affine `U` inside the preimage of an affine `V`,
which is exactly the chart the cover is built from.

## References

* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 01V3](https://stacks.math.columbia.edu/tag/01V3)
* [Stacks Project, Tag 01V2](https://stacks.math.columbia.edu/tag/01V2), the finite type
  statement this mirrors.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **On an affine chart of a morphism locally of finite presentation the sections of the sheaf
of relative differentials are a finitely presented module.** On an affine open `U` of `X`
contained in the preimage of an affine open `V` of `S`, those sections are the Kähler
differentials of `Γ(S, V) ⟶ Γ(X, U)` by [Stacks, Tag 01UT], and that ring map is of finite
presentation. -/
@[ega "IV 16.4.22" "special case", sga "3 III 0.14" "partial"]
private theorem finitePresentation_sections_relativeDifferentials (f : X ⟶ S)
    [LocallyOfFinitePresentation f] {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens}
    (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) :
    Module.FinitePresentation Γ(X, U) Γ(Scheme.Hom.relativeDifferentials f, U) := by
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have : Algebra.FinitePresentation Γ(S, V) Γ(X, U) :=
    RingHom.finitePresentation_algebraMap.mp (f.finitePresentation_appLE hV hU hUV)
  let el : Ω[Γ(X, U)⁄Γ(S, V)] ≃ₗ[Γ(X, U)] Γ(Scheme.Hom.relativeDifferentials f, U) :=
    (Stacks.AlgebraicGeometry.AffineDifferentialsIso.existsUnique_affineDifferentialsIso
      f hU hUV hV).choose.symm.toLinearEquiv
  exact Module.FinitePresentation.of_equiv el

/-- **Stacks Project, Tag 01V3.** The sheaf of relative differentials of a morphism of schemes
which is locally of finite presentation is an `𝒪_X`-module of finite presentation. -/
@[stacks 01V3, ega "IV 16.4.22", ega "IV 17.4.1.2" "special case", sga "3 III 0.14" "more general"]
instance Scheme.Hom.isFinitePresentation_relativeDifferentials (f : X ⟶ S)
    [LocallyOfFinitePresentation f] :
    (Scheme.Hom.relativeDifferentials f).IsFinitePresentation := by
  choose A W hxA hAW using Scheme.exists_affineOpen_le_preimage_affineOpen f
  refine Stacks.AlgebraicGeometry.FinitePresentationLocal.isFinitePresentation_of_affineCover
    _ (fun x => (A x).1) ?_ (fun x => (A x).2) fun x =>
      finitePresentation_sections_relativeDifferentials f (A x).2 (W x).2 (hAW x)
  refine IsOpenCover.mk (top_le_iff.mp fun x _ => ?_)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxA x⟩

end AlgebraicGeometry

end
