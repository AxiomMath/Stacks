module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.Twist
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Comparison

/-!
# The two comparison maps on twists agree on sections

Tag 01MY attaches to a homomorphism `ψ : 𝒜 →+*ᵍ ℬ` of nonnegatively graded rings a comparison
map `θ n` on the `n`-th twisting sheaves. This library builds `θ` **twice**:

* `Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap`, indexed by the domain of definition
  `U(ψ) ⊆ Proj ℬ` and the induced morphism `mapHom : U(ψ) ⟶ Proj 𝒜`; and
* `Stacks.ProjTwistComparison.twistMap`, indexed by `AlgebraicGeometry.Proj.map ψ hψ`, which is
  defined on all of `Proj ℬ` and needs Mathlib's hypothesis `ℬ₊ ≤ 𝒜₊.map ψ`.

Both are the adjoint transpose of an explicit map on sections, and both of those maps are given
pointwise by a comparison of module fibres — the localization of `ψ` at a homogeneous prime of
`ℬ` and its `ψ`-preimage. **This file identifies the two maps on sections**, pointwise, which is
the content of the identification of the two `θ`s.

## Main results

* `Stacks.AlgebraicGeometry.ProjThetaCompare.basePoint_eq_comapFun`: the point of `Proj 𝒜` at
  which the two constructions read a section is the same point. On the `U(ψ)` side it is the
  image of the point under `mapHom`; on the `Proj.map` side it is Mathlib's
  `ProjectiveSpectrum.comapFun`.
* `Stacks.AlgebraicGeometry.ProjThetaCompare.fibreMap_apply_eq_of_eq`: **the two fibre
  comparisons agree**, applied to the value of one dependent family of module fibres at the two
  points.
* `Stacks.AlgebraicGeometry.ProjThetaCompare.twistFibreMap_apply_eq`: the same at the two points
  the constructions actually use.
* `Stacks.AlgebraicGeometry.ProjThetaCompare.twistFamily_eq_sectionFun`: **the two maps on
  sections agree**, at every point of the image of the preimage of an open of `Proj 𝒜`, for every
  section of the `n`-th twist over it and every integer `n`.

## Why the statements are applied to a family rather than equated as maps

The two fibre comparisons have the same source *module* only after the two points of `Proj 𝒜` are
identified, and that identification is propositional: one point is `(mapHom 𝒜 ℬ ψ).base y`, the
other is `ProjectiveSpectrum.comapFun ψ hψ y`, and they agree because both homogeneous ideals are
the `ψ`-preimage of the one at `y`. So an equation between the two maps does not typecheck as it
stands, and transporting one side along the point equality puts an `Eq.rec` in the statement.

The route taken here is the one `Stacks.ProjTwistComparison.fibreMap_comp_of_eq` takes for the
composition law: the statement quantifies over a dependent family `f` of module fibres and reads
it at the two points, so that **both sides live in the fibre at `y`** and no transport appears;
the point of `Proj 𝒜` is a variable and the identification a hypothesis, which `subst` removes,
after which the two maps are the same instance of `Localization.localRingHom`, and the two
membership proofs and the two hypotheses are identified by proof irrelevance.

## What is not proved here

The identification of the two **morphisms** `θ n` is not proved, and no clause of any tag is
claimed. Both morphisms are adjoint transposes, and passing from the agreement of the transposes
on sections to an equation between the morphisms needs, besides this file: the identification
`mapHomOfTop 𝒜 ℬ ψ hdom = Proj.map ψ hψ`
(`Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map`), the identification of the two opens
`U.comap (ProjectiveSpectrum.comap ψ hψ)` and `(mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)`
over a `ψ` whose domain of definition is everything, and the naturality of the
pullback--pushforward adjunction in the morphism.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal TopologicalSpace CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain

namespace Stacks.AlgebraicGeometry.ProjThetaCompare

universe u

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **The two constructions read a section of `𝒪_{Proj 𝒜}(n)` at the same point.** Tag 01MY's
comparison over the domain of definition reads it at the image of the point under `mapHom`,
`Stacks.AlgebraicGeometry.ProjTwistCompare.basePoint`; the comparison indexed by
`AlgebraicGeometry.Proj.map` reads it at Mathlib's `ProjectiveSpectrum.comapFun`. The two
homogeneous ideals are both the `ψ`-preimage of the one at the point. -/
public theorem basePoint_eq_comapFun (ψ : 𝒜 →+*ᵍ ℬ) (hψ : ℬ₊ ≤ 𝒜₊.map ψ)
    (y : (mapDomain 𝒜 ℬ ψ).toScheme) :
    ProjTwistCompare.basePoint 𝒜 ℬ ψ y = ProjectiveSpectrum.comapFun ψ hψ y.1 :=
  ProjectiveSpectrum.ext (ProjTwistCompare.basePoint_asHomogeneousIdeal 𝒜 ℬ ψ y)

/-- **The two fibre comparisons agree.** Both are the localization of `ψ` at a homogeneous prime
of `ℬ` and its `ψ`-preimage, so once the two points of `Proj 𝒜` are identified they are the same
instance of `Localization.localRingHom`.

The point `x` is a variable and the identification is a hypothesis, so that it can be substituted
away; the two sides are read off one dependent family of module fibres, so that both live in the
fibre at `y` and no transport appears. See the module docstring. -/
public theorem fibreMap_apply_eq_of_eq (ψ : 𝒜 →+*ᵍ ℬ) (hψ : ℬ₊ ≤ 𝒜₊.map ψ)
    (y : ProjectiveSpectrum ℬ) (x : ProjectiveSpectrum 𝒜)
    (hx : x.asHomogeneousIdeal = y.asHomogeneousIdeal.comap ψ)
    (hxeq : x = ProjectiveSpectrum.comapFun ψ hψ y)
    {P : ProjectiveSpectrum 𝒜 → Prop} (f : ∀ q : Subtype P, ModuleFiber (M := A) 𝒜 q.1)
    (h₁ : P x) (h₂ : P (ProjectiveSpectrum.comapFun ψ hψ y)) :
    ProjTwistCompare.fibreMap 𝒜 ℬ ψ x y hx (f ⟨x, h₁⟩) =
      Stacks.ProjTwistComparison.fibreMap ψ hψ y (f ⟨_, h₂⟩) := by
  subst hxeq
  rfl

/-- **Tag 01MY's fibre comparison over the domain of definition is the fibre comparison of the
map indexed by `AlgebraicGeometry.Proj.map`**, at the two points the two constructions use. -/
public theorem twistFibreMap_apply_eq (ψ : 𝒜 →+*ᵍ ℬ) (hψ : ℬ₊ ≤ 𝒜₊.map ψ)
    (y : (mapDomain 𝒜 ℬ ψ).toScheme)
    {P : ProjectiveSpectrum 𝒜 → Prop} (f : ∀ q : Subtype P, ModuleFiber (M := A) 𝒜 q.1)
    (h₁ : P (ProjTwistCompare.basePoint 𝒜 ℬ ψ y))
    (h₂ : P (ProjectiveSpectrum.comapFun ψ hψ y.1)) :
    ProjTwistCompare.twistFibreMap 𝒜 ℬ ψ y (f ⟨_, h₁⟩) =
      Stacks.ProjTwistComparison.fibreMap ψ hψ y.1 (f ⟨_, h₂⟩) :=
  fibreMap_apply_eq_of_eq 𝒜 ℬ ψ hψ y.1 (ProjTwistCompare.basePoint 𝒜 ℬ ψ y)
    (ProjTwistCompare.basePoint_asHomogeneousIdeal 𝒜 ℬ ψ y)
    (basePoint_eq_comapFun 𝒜 ℬ ψ hψ y) f h₁ h₂

/-- **The two maps on sections of the `n`-th twist agree.**

Over an open `U` of `Proj 𝒜`, Tag 01MY's comparison over the domain of definition
(`Stacks.AlgebraicGeometry.ProjTwistCompare.twistFamily`) and the comparison indexed by
`AlgebraicGeometry.Proj.map` (`Stacks.ProjTwistComparison.sectionFun`) take the same value at
every point of the image of the preimage of `U`: both apply the localization of `ψ` to the value
of the section at the point below, and that point is the same point. -/
public theorem twistFamily_eq_sectionFun (ψ : 𝒜 →+*ᵍ ℬ) (hψ : ℬ₊ ≤ 𝒜₊.map ψ) (n : ℤ)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (a : (twistingSheaf 𝒜 n).val.obj (.op U))
    (V : Opens (ProjectiveSpectrum.top ℬ))
    (hUV : V.1 ⊆ ProjectiveSpectrum.comap ψ hψ ⁻¹' U.1)
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)))
    (hz : (z.1 : ProjectiveSpectrum ℬ) ∈ V) :
    ProjTwistCompare.twistFamily 𝒜 ℬ ψ n U a z =
      Stacks.ProjTwistComparison.sectionFun ψ hψ U V hUV a.1 ⟨z.1, hz⟩ :=
  twistFibreMap_apply_eq 𝒜 ℬ ψ hψ (ProjTwistCompare.liftPt 𝒜 ℬ ψ z) a.1
    (ProjTwistCompare.liftPt_mem 𝒜 ℬ ψ z) (hUV hz)

end Stacks.AlgebraicGeometry.ProjThetaCompare

end
