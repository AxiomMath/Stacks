module

public import StacksFrontier.AlgebraicGeometry.ThetaMultiplicative.Basic
public import StacksFrontier.AlgebraicGeometry.ThetaMultiplicative.ScalarTwistProduct

/-!
# Tag 01MY's comparison intertwines the homogeneous scalar actions

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings and let
`ρ_n := Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap 𝒜 ℬ ψ n` be the adjoint
form of [Stacks, Tag 01MY]'s comparison `θ` on the `n`-th twist,
`𝒪_{Proj 𝒜}(n) ⟶ (Proj ψ)_*(𝒪_{Proj ℬ}(n)|_{U(ψ)})`.

This file proves that `ρ` intertwines multiplication by a homogeneous element `a` of degree `i`
with multiplication by `ψ a`:

`ρ_{i + n} (a · s) = (ψ a) · ρ_n s`,

on the sections over an arbitrary open and in every integer degree `n`, where both scalar
multiplications are
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap` — the action the graded
module of twisted global sections, and hence the finiteness statements of [Stacks, Tag 01YS]
clause (5), is built from.

## Why this is the square that was missing

The graded assembly these finiteness statements need is a comparison of the *whole* graded
module `⨁_n Γ(Proj 𝒜, 𝒪(n))` with `⨁_n Γ(Proj ℬ, 𝒪(n))`, compatible with the degree-one action
in every degree at once. The module docstring of
`StacksFrontier/AlgebraicGeometry/Blowup/ProjectivePushforwardGradedSections.lean` records that the
*pullback* spelling of `θ` — `Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso`
— cannot supply it, because its five structural inverse-image factors defeat the transport of
the product formula, and that the *adjoint* spelling can, because
`Stacks.AlgebraicGeometry.ThetaMultiplicative.twistPushforwardMap_absoluteTwistProduct` holds
over every open and in all integer degrees with no structural factors at all. It also records
the one input that was genuinely absent: a comparison between the product
`Stacks.AlgebraicGeometry.RelativeProjTwists.absoluteTwistProduct` that formula is stated with
and the scalar action `twistScalarSheafMap` the finiteness statements use. That comparison is
`StacksFrontier/AlgebraicGeometry/ThetaMultiplicative/ScalarTwistProduct.lean`; this file is what it
was for.

Nothing here is a transport through structural factors, and nothing here is restricted to
sections of the form `degreeSection d a`: the identity holds for an arbitrary section `s` of
`𝒪(n)` over an arbitrary open, which is exactly the strength the assembly was found to need and
the elementwise `pullbackTwistIso_degreeSection` was found not to have.

## Main results

* `Stacks.AlgebraicGeometry.ThetaMultiplicative.twistPushforwardMap_degreeSectionOn`: the
  comparison carries the restriction to an open of the global section attached to `a` to the
  one attached to `ψ a`. This is
  `Stacks.AlgebraicGeometry.ProjTwistTheta.twistPushforwardMap_degreeSection_val` at an
  arbitrary open rather than only at `⊤`.
* `Stacks.AlgebraicGeometry.ThetaMultiplicative.twistPushforwardMap_twistScalarSheafMap`:
  **the multiplicativity square**, `ρ_{i + n} (a · s) = (ψ a) · ρ_n s`.
* `Stacks.AlgebraicGeometry.ThetaMultiplicative.twistSection_twistScalarSheafMap`: the same
  square written with `Stacks.AlgebraicGeometry.ProjTwistCompare.twistSection`.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.ProjTwistTheta
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap
  twistScalarSheafMap_app_eq_absoluteTwistProduct absoluteTwistProduct_degreeSectionOn_eq)
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.TwistRigidity (degreeSectionOn degreeSectionOn_apply)

namespace Stacks.AlgebraicGeometry.ThetaMultiplicative

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-! ### The homogeneous sections, at an arbitrary open -/

/-- **The comparison carries the homogeneous section of `a` to the homogeneous section of
`ψ a`, over an arbitrary open.** This is
`Stacks.AlgebraicGeometry.ProjTwistTheta.twistPushforwardMap_degreeSection_val` with `⊤`
replaced by an arbitrary open `U`: the value of the comparison at a point is the fibre
comparison of the value at the image point, that value is `a / 1` at every point of `U` by
`Stacks.AlgebraicGeometry.TwistRigidity.degreeSectionOn_apply`, and the fibre comparison sends
`a / 1` to `ψ a / ψ 1 = ψ a / 1`. -/
public theorem twistPushforwardMap_degreeSectionOn (ψ : 𝒜 →+*ᵍ ℬ) (i : ℕ) (a : 𝒜 i)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) :
    ((twistPushforwardMap 𝒜 ℬ ψ (i : ℤ)).val.app (op U)).hom' (degreeSectionOn 𝒜 i a.2 U) =
      degreeSectionOn ℬ i (ψ.map_mem a.2)
        ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)) := by
  have hone : (ψ (1 : A)) = 1 := map_one ψ
  refine Subtype.ext (funext fun z => ?_)
  have hs : (1 : A) ∉ (basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).asHomogeneousIdeal.toIdeal :=
    (basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).isPrime.one_notMem
  have hψs : (ψ (1 : A)) ∉
      (ambientPoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).asHomogeneousIdeal.toIdeal := by
    rw [hone]
    exact (ambientPoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).isPrime.one_notMem
  refine Eq.trans
    (twistPushforwardMap_app_val 𝒜 ℬ ψ (i : ℤ) (op U) (degreeSectionOn 𝒜 i a.2 U) z) ?_
  refine Eq.trans (congrArg (twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z))
    (degreeSectionOn_apply 𝒜 i a.2 U
      ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩)) ?_
  refine Eq.trans (twistFibreMap_mk 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z) (a : A) 1 hs hψs) ?_
  refine Eq.trans (congrArg (fun s => LocalizedModule.mk (M := B) (ψ (a : A)) s)
    (Subtype.ext hone :
      (⟨ψ (1 : A), hψs⟩ :
          (ambientPoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).asHomogeneousIdeal.toIdeal.primeCompl) = 1)) ?_
  exact (degreeSectionOn_apply ℬ i (ψ.map_mem a.2)
    ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)) z).symm

/-! ### The multiplicativity square -/

/-- **Tag 01MY's comparison intertwines multiplication by a homogeneous scalar with
multiplication by its image:** `ρ_{i + n} (a · s) = (ψ a) · ρ_n s`, for an arbitrary section `s`
of `𝒪(n)` over an arbitrary open `U` of `Proj 𝒜`, in every integer degree `n`, with both scalar
multiplications written as
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap`.

Three existing facts in a row, and no transport: the scalar action is the canonical twist product
against the homogeneous section
(`Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap_app_eq_absoluteTwistProduct`),
the comparison carries that product to the product of the images
(`twistPushforwardMap_absoluteTwistProduct`), and it carries the homogeneous section of `a` to
the homogeneous section of `ψ a` (`twistPushforwardMap_degreeSectionOn`). -/
public theorem twistPushforwardMap_twistScalarSheafMap (ψ : 𝒜 →+*ᵍ ℬ) (i : ℕ) (n : ℤ) (a : 𝒜 i)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) (s : (twistingSheaf 𝒜 n).val.obj (op U)) :
    ((twistPushforwardMap 𝒜 ℬ ψ ((i : ℤ) + n)).val.app (op U)).hom'
        (((twistScalarSheafMap 𝒜 i n ((i : ℤ) + n) rfl a).val.app (op U)).hom s) =
      ((twistScalarSheafMap ℬ i n ((i : ℤ) + n) rfl ⟨ψ a, ψ.map_mem a.2⟩).val.app
          (op ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)))).hom
        (((twistPushforwardMap 𝒜 ℬ ψ n).val.app (op U)).hom' s) := by
  refine Eq.trans (congrArg
    (fun t => ((twistPushforwardMap 𝒜 ℬ ψ ((i : ℤ) + n)).val.app (op U)).hom' t)
    (twistScalarSheafMap_app_eq_absoluteTwistProduct 𝒜 i n a U s)) ?_
  refine Eq.trans (twistPushforwardMap_absoluteTwistProduct 𝒜 ℬ ψ (i : ℤ) n U
    (degreeSectionOn 𝒜 i a.2 U) s) ?_
  refine Eq.trans (congrArg
    (fun t => absoluteTwistProduct ℬ (i : ℤ) n
      ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)) t
      (((twistPushforwardMap 𝒜 ℬ ψ n).val.app (op U)).hom' s))
    (twistPushforwardMap_degreeSectionOn 𝒜 ℬ ψ i a U)) ?_
  exact absoluteTwistProduct_degreeSectionOn_eq ℬ i n ⟨ψ a, ψ.map_mem a.2⟩
    ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)) _

/-- The multiplicativity square written with
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistSection`, which is the adjoint comparison's
action on sections by definition. -/
public theorem twistSection_twistScalarSheafMap (ψ : 𝒜 →+*ᵍ ℬ) (i : ℕ) (n : ℤ) (a : 𝒜 i)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) (s : (twistingSheaf 𝒜 n).val.obj (op U)) :
    twistSection 𝒜 ℬ ψ ((i : ℤ) + n) U
        (((twistScalarSheafMap 𝒜 i n ((i : ℤ) + n) rfl a).val.app (op U)).hom s) =
      ((twistScalarSheafMap ℬ i n ((i : ℤ) + n) rfl ⟨ψ a, ψ.map_mem a.2⟩).val.app
          (op ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)))).hom
        (twistSection 𝒜 ℬ ψ n U s) :=
  twistPushforwardMap_twistScalarSheafMap 𝒜 ℬ ψ i n a U s

end Stacks.AlgebraicGeometry.ThetaMultiplicative

end
