module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistGradedTheta
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.Generic

/-!
# Clause (1) of Tag 02NC in the source's direction

[Stacks, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC) states its canonical isomorphism as
a morphism

`g : P = Proj 𝒜 ⟶ Proj ℬ = P'`

*out of* the homogeneous spectrum of the untwisted algebra, and its clause (1) as a family of
comparisons

`θ_n : g^*𝒪_{P'}(n) ⟶ 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`

on `P`. The comparison built in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjInvertibleTwistGradedTheta.lean` runs the other
way: its `Stacks.GradedRing.InvertibleTwist.thetaGradedIso` has source the pullback along
`r_ψ : U(ψ) ⟶ Proj 𝒜` of the twists of `Proj 𝒜` and target the twists of `Proj ℬ`, so both of
its sides are sheaves on an open of `Proj ℬ = P'` rather than on `P`. Each `θ_n` is invertible,
so the two readings carry the same data; they are nevertheless not the same statement, because
the two sides live on different schemes.

**This file states clause (1) on `P`, in the source's direction**, for a twisting module with a
global generator — which is the case the source's own proof calls "the identity map when
`ℒ ≅ 𝒪_S`". Nothing new has to be proved about twists: for a generator the comparison
`ψ = (x ↦ x ⊗ ℓ ^ d)` is an *isomorphism* of graded rings, with inverse
`Stacks.GradedRing.InvertibleTwist.twistHomInv`, and the whole Tag 01MY apparatus applied to that
inverse produces exactly the source's `g` and the source's `θ`. The morphism
`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom ℬ 𝒜 ψ⁻¹` has source an open of `Proj 𝒜` and
target `Proj ℬ`, that open is everything, and the morphism is an isomorphism of schemes.

## Main definitions

* `Stacks.GradedRing.InvertibleTwist.thetaGradedIsoSource`: **clause (1) of Tag 02NC in the
  source's direction**, as one isomorphism of sheaves of `ℤ`-graded algebras
  `g^*(⨁_{n ∈ ℤ} 𝒪_{P'}(n)) ≅ ⨁_{n ∈ ℤ} 𝒪_P(n)` on `P = Proj 𝒜`.

## Main results

* `Stacks.GradedRing.InvertibleTwist.bijective_gradedAddHom_twistHomInv`: the inverse comparison
  is bijective in every degree, which is the one input the Tag 01MY machinery wants.
* `Stacks.GradedRing.InvertibleTwist.isIso_twistMap_twistHomInv`: clause (1) componentwise in the
  source's direction, `θ_n : g^*𝒪_{P'}(n) ≅ 𝒪_P(n)`.
* `Stacks.GradedRing.InvertibleTwist.mapDomain_twistHomInv_eq_top`: the source `U(ψ⁻¹)` of `g` is
  the whole of `Proj 𝒜`, so the statement is about `P` itself and not an open part of it.
* `Stacks.GradedRing.InvertibleTwist.isIso_mapHom_twistHomInv`: `g` is an isomorphism of schemes.
* `Stacks.GradedRing.InvertibleTwist.ι_comp_mapHom_twistHomInv`: `g` is the inverse of the
  canonical isomorphism `Stacks.GradedRing.InvertibleTwist.projTwistIso`, restricted along the
  inclusion of its source. This is what identifies it with the source's `g` and not merely with
  some morphism `P ⟶ P'`.

## How the tag's target object is read

The tag's `𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` appears here as `𝒪_P(n)`: the generator `ℓ` trivializes `𝓛 n`
for every `n` (`Stacks.GradedRing.IsTensorPowerFamily.bijective_toSpanSingleton_pow`), hence
trivializes `π^*ℒ^{⊗ n}`, and the source's proof reads this case as the one where the tensor
factor is the structure sheaf. The factor is *not* carried as an object; writing it out requires
an isomorphism `π^*ℒ^{⊗ n} ≅ 𝒪_P`, which this library does not have — see the paragraph "What
assembling the chartwise comparisons actually needs" of
`StacksFrontier/AlgebraicGeometry/Constructions/ProjInvertibleTwist.lean`.

## What is not proved here

Without a global generator there is no inverse graded ring homomorphism, and so no `ψ⁻¹` to feed
the Tag 01MY apparatus: the canonical isomorphism is then
`Stacks.GradedRing.InvertibleTwist.projTwistIsoGeneral`, glued from the chart morphisms, and its
inverse is not `Proj` of a homomorphism of graded rings. So clause (1) in the source's direction
is proved here only for a twisting module with a global generator.

The unit is not addressed, for the reason recorded in the module docstring of
`StacksFrontier/AlgebraicGeometry/Constructions/ProjInvertibleTwistGradedTheta.lean`.

## References

* [Stacks Project, Tag 02NB](https://stacks.math.columbia.edu/tag/02NB)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry DirectSum Graded HomogeneousIdeal
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistGradedAlgebra (pullbackTwistAlgebra)
open scoped TensorProduct

/-- The inclusion of an open subscheme that equals `⊤` is an isomorphism. -/
private theorem isIso_ι_of_eq_top {X : Scheme.{u}} (U : X.Opens) (h : U = ⊤) : IsIso U.ι := by
  subst h
  rw [← Scheme.topIso_hom]
  infer_instance

namespace Stacks.GradedRing.InvertibleTwist

attribute [local instance] ProjectiveSpectrum.isPrime

variable {R A B T : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
  [Algebra R A] [Algebra R B] [Algebra R T]
  {𝒜 : ℕ → Submodule R A} [_root_.GradedAlgebra 𝒜] {𝓛 : ℕ → Submodule R T}
  {ℬ : ℕ → Submodule R B} [_root_.GradedAlgebra ℬ] (tw : InvertibleTwist 𝒜 𝓛 ℬ)
  (h𝓛 : IsTensorPowerFamily 𝓛) {ℓ : T} {hℓ : ℓ ∈ 𝓛 1}
  (hgen : Function.Bijective (LinearMap.toSpanSingleton R (𝓛 1) ⟨ℓ, hℓ⟩))

include tw h𝓛 hgen

/-! ### The inverse comparison is degreewise bijective -/

/-- The degree-`d` component of the inverse comparison homomorphism is the inverse of the
comparison of homogeneous pieces. -/
theorem gradedAddHom_twistHomInv (d : ℕ) (y : ℬ d) :
    GradedRingHom.gradedAddHom (tw.twistHomInv h𝓛 hgen) d y =
      (tw.pieceEquiv h𝓛 hgen d).symm y :=
  Subtype.ext (tw.twistHomInv_coe h𝓛 hgen d y)

/-- **The inverse comparison homomorphism is bijective in every degree.** -/
theorem bijective_gradedAddHom_twistHomInv (d : ℕ) :
    Function.Bijective (GradedRingHom.gradedAddHom (tw.twistHomInv h𝓛 hgen) d) := by
  have h : (GradedRingHom.gradedAddHom (tw.twistHomInv h𝓛 hgen) d : (ℬ d) → (𝒜 d)) =
      ((tw.pieceEquiv h𝓛 hgen d).symm : (ℬ d) → (𝒜 d)) :=
    funext (tw.gradedAddHom_twistHomInv h𝓛 hgen d)
  rw [h]
  exact (tw.pieceEquiv h𝓛 hgen d).symm.bijective

/-! ### The source's morphism `g : P ⟶ P'` -/

/-- **The source `U(ψ⁻¹)` of the source's `g` is the whole of `Proj 𝒜`.** The inverse comparison
homomorphism is surjective, so its Tag 01MY domain of definition is everything; clause (1) in the
source's direction is therefore a statement about `P = Proj 𝒜` itself. -/
theorem mapDomain_twistHomInv_eq_top :
    mapDomain ℬ 𝒜 (tw.twistHomInv h𝓛 hgen) = ⊤ :=
  mapDomain_eq_top_of_surjective ℬ 𝒜 _ (tw.surjective_twistHomInv h𝓛 hgen)

/-- **The source `U(ψ⁻¹)` of the source's `g` is `Proj 𝒜` as a scheme, and not merely as an
open.** The inclusion of an open that is everything is a split epimorphism, by
`Stacks.AlgebraicGeometry.RelativeProj.topIso_inv_isoOfEq_hom_ι`, and it is a monomorphism, being
an open immersion. -/
theorem isIso_ι_mapDomain_twistHomInv :
    IsIso (mapDomain ℬ 𝒜 (tw.twistHomInv h𝓛 hgen)).ι :=
  isIso_ι_of_eq_top _ (tw.mapDomain_twistHomInv_eq_top h𝓛 hgen)

/-- **The open `U(ψ)` carrying `Stacks.GradedRing.InvertibleTwist.thetaGradedIso` is `Proj ℬ` as a
scheme.** `Stacks.GradedRing.InvertibleTwist.mapDomain_twistHom_eq_top` says the open is
everything; this says the inclusion is an isomorphism of schemes, which is what makes the graded
assembly a statement about `Proj ℬ` itself. -/
theorem isIso_ι_mapDomain_twistHom :
    IsIso (mapDomain 𝒜 ℬ (tw.twistHom h𝓛 hgen)).ι :=
  isIso_ι_of_eq_top _ (tw.mapDomain_twistHom_eq_top h𝓛 hgen)

/-- **The source's `g : P ⟶ P'` is an isomorphism of schemes.** -/
theorem isIso_mapHom_twistHomInv :
    IsIso (mapHom ℬ 𝒜 (tw.twistHomInv h𝓛 hgen)) :=
  Stacks.AlgebraicGeometry.RelativeProjChain.isIso_mapHom_of_eventually_bijective ℬ 𝒜 _
    (Filter.Eventually.of_forall (tw.bijective_gradedAddHom_twistHomInv h𝓛 hgen))

/-- **The source's `g` is the inverse of the canonical isomorphism**
`Stacks.GradedRing.InvertibleTwist.projTwistIso`, read along the inclusion of its source. This is
what makes `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom ℬ 𝒜 ψ⁻¹` the tag's `g` and not merely
some morphism `Proj 𝒜 ⟶ Proj ℬ`. -/
theorem ι_comp_mapHom_twistHomInv :
    (mapDomain ℬ 𝒜 (tw.twistHomInv h𝓛 hgen)).ι ≫ (tw.projTwistIso h𝓛 hgen).inv =
      mapHom ℬ 𝒜 (tw.twistHomInv h𝓛 hgen) :=
  Stacks.AlgebraicGeometry.ProjBaseChange.ι_comp_projMap ℬ 𝒜 _
    (tw.irrelevant_le_map_twistHomInv h𝓛 hgen)

/-! ### Clause (1) in the source's direction -/

/-- **Clause (1) of Tag 02NC componentwise, in the source's direction.** The comparison
`θ_n : g^*𝒪_{P'}(n) ⟶ 𝒪_P(n)` attached to the inverse comparison homomorphism is an isomorphism,
for every `n : ℤ`. -/
theorem isIso_twistMap_twistHomInv (n : ℤ) :
    IsIso (twistMap ℬ 𝒜 (tw.twistHomInv h𝓛 hgen) n) :=
  Stacks.AlgebraicGeometry.RelativeProjChain.isIso_projMapData_twistMap_of_eventually_bijective
    ℬ 𝒜 _ (Filter.Eventually.of_forall (tw.bijective_gradedAddHom_twistHomInv h𝓛 hgen)) n

/-- **Clause (1) of Stacks Tag 02NC in the source's direction, for a twisting module with a global
generator.** The comparisons `θ_n` attached to the inverse comparison homomorphism fit together
into a single isomorphism of sheaves of `ℤ`-graded algebras

`θ : g^*(⨁_{n ∈ ℤ} 𝒪_{Proj ℬ}(n)) ≅ ⨁_{n ∈ ℤ} 𝒪_{Proj 𝒜}(n)`,

both sides being sheaves on `P = Proj 𝒜`, which is the shape the source states clause (1) in.
Its degree-`n` component is the comparison map of
`Stacks.GradedRing.InvertibleTwist.isIso_twistMap_twistHomInv`. The source of `g` is the whole of
`Proj 𝒜` by `Stacks.GradedRing.InvertibleTwist.mapDomain_twistHomInv_eq_top`, and `g` is the
inverse of the canonical isomorphism by
`Stacks.GradedRing.InvertibleTwist.ι_comp_mapHom_twistHomInv`.

For the same statement read on `Proj ℬ`, which is the direction the comparison on twists runs in
this library, see `Stacks.GradedRing.InvertibleTwist.thetaGradedIso`. -/
def thetaGradedIsoSource :
    pullbackTwistAlgebra ℬ (mapHom ℬ 𝒜 (tw.twistHomInv h𝓛 hgen)) ≅
      pullbackTwistAlgebra 𝒜 (mapDomain ℬ 𝒜 (tw.twistHomInv h𝓛 hgen)).ι :=
  Stacks.AlgebraicGeometry.ProjTwistGradedAlgebra.thetaGradedIso ℬ 𝒜 (tw.twistHomInv h𝓛 hgen)
    (tw.isIso_twistMap_twistHomInv h𝓛 hgen)

/-- The degree-`n` component of the graded assembly in the source's direction is the comparison
map on the `n`-th twist attached to the inverse comparison. -/
theorem thetaGradedIsoSource_hom_app (n : ℤ) :
    (tw.thetaGradedIsoSource h𝓛 hgen).hom.app n = twistMap ℬ 𝒜 (tw.twistHomInv h𝓛 hgen) n := rfl

end Stacks.GradedRing.InvertibleTwist

end
