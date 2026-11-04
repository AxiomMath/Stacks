module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Surjective
public import StacksFrontier.AlgebraicGeometry.Coherent.IdealSheafFiniteTypeBridge
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas

/-!
# The differentials of a morphism locally of finite type are of finite type

For a morphism of schemes `f : X ⟶ S` which is locally of finite type, the sheaf of relative
differentials `Ω_{X/S}` is an `𝒪_X`-module of finite type.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isFiniteType_relativeDifferentials`: for a morphism locally of
  finite type the sheaf of relative differentials is of finite type.

## Implementation notes

Finite type of a quasi-coherent module is detected by the sections over the members of an
affine open cover, which is
`Stacks.AlgebraicGeometry.FiniteTypeBridge.isFiniteType_of_finite_sections_affineOpens`;
quasi-coherence of `Ω_{X/S}` holds for every morphism and is
`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentials`, recorded here as an
instance so that the criterion applies by inference.

The cover is chosen one point at a time: an affine open `V` of `S` around the image of the
point, then an affine open `U ⊆ f ⁻¹ V` of `X` around the point itself. On such a chart
[Stacks, Tag 01UT] — `Stacks.AlgebraicGeometry.AffineDifferentialsIso.
existsUnique_affineDifferentialsIso` — identifies the sections of `Ω_{X/S}` on `U` with the
Kähler differentials of `Γ(S, V) ⟶ Γ(X, U)`, and that ring map is of finite type because `f`
is, so `KaehlerDifferential.finite` applies. The chart is indexed by the points of `X`, so no
refinement of the cover is needed and the covering condition is read off the choice directly.

Only *local* finiteness of type is used, so the statement is not an instance about
`AlgebraicGeometry.LocallyOfFinitePresentation`, which would be the weaker
[Stacks, Tag 01V3] about finite presentation.

## References

* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 01V2](https://stacks.math.columbia.edu/tag/01V2)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The sheaf of relative differentials of a morphism of schemes is quasi-coherent, with no
hypothesis on the morphism. This is
`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentials` as an instance. -/
instance Scheme.Hom.instIsQuasicoherentRelativeDifferentials (f : X ⟶ S) :
    (Scheme.Hom.relativeDifferentials f).IsQuasicoherent :=
  Scheme.Hom.isQuasicoherent_relativeDifferentials f

/-- **On an affine chart of a morphism locally of finite type the sections of the sheaf of
relative differentials are a finite module.** On an affine open `U` of `X` contained in the
preimage of an affine open `V` of `S`, those sections are the Kähler differentials of
`Γ(S, V) ⟶ Γ(X, U)` by [Stacks, Tag 01UT], and that ring map is of finite type, hence
essentially of finite type. -/
private theorem moduleFinite_sections_relativeDifferentials (f : X ⟶ S)
    [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens}
    (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) :
    Module.Finite Γ(X, U) Γ(Scheme.Hom.relativeDifferentials f, U) := by
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have hft : (algebraMap Γ(S, V) Γ(X, U)).FiniteType := f.finiteType_appLE hV hU hUV
  have : Algebra.EssFiniteType Γ(S, V) Γ(X, U) :=
    RingHom.essFiniteType_algebraMap.mp hft.essFiniteType
  let e := (Stacks.AlgebraicGeometry.AffineDifferentialsIso.existsUnique_affineDifferentialsIso
    f hU hUV hV).choose
  let φ : Ω[Γ(X, U)⁄Γ(S, V)] →ₗ[Γ(X, U)] Γ(Scheme.Hom.relativeDifferentials f, U) := e.inv.hom
  exact Module.Finite.of_surjective φ fun y => ⟨e.hom.hom y, congr($(e.hom_inv_id).hom y)⟩

/-- **Stacks Project, Tag 01V2.** The sheaf of relative differentials of a morphism of schemes
which is locally of finite type is an `𝒪_X`-module of finite type. -/
@[stacks 01V2, ega "IV 17.4.1.2"]
instance Scheme.Hom.isFiniteType_relativeDifferentials (f : X ⟶ S) [LocallyOfFiniteType f] :
    (Scheme.Hom.relativeDifferentials f).IsFiniteType := by
  choose A W hxA hAW using Scheme.exists_affineOpen_le_preimage_affineOpen f
  exact Stacks.AlgebraicGeometry.FiniteTypeBridge.isFiniteType_of_finite_sections_affineOpens
    _ (fun x => (A x).1) (IsOpenCover.mk (top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ⟨x, hxA x⟩))
    (fun x => (A x).2) fun x =>
      moduleFinite_sections_relativeDifferentials f (A x).2 (W x).2 (hAW x)

end AlgebraicGeometry

end
