module

public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.ModelComparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TopDegreeRow
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction

/-!
# The degree-`n` row of Tag 01XW over the affine opens of an arbitrary base

Let `S` be a scheme, let `n = m + 1 ≥ 1`, let `d` be an integer and let `f : ℙⁿ_S ⟶ S` be the
structure morphism of projective `n`-space over `S`. The degree-`n` row of the display of
[Stacks, Tag 01XW] reads

`Rⁿ f_* 𝒪(d) = Hom_{𝒪_S}((𝒪_S[T₀, …, Tₙ])_{-n-1-d}, 𝒪_S)`,

and over an affine base it is proved, for every twist, in
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage`
`.rightDerivedPlusTopIsoDualBaseDegreeSheaf_of_isAffine`. This file localises that identification
to the affine opens `V` of an arbitrary base: the restriction of `Rⁿ f_* 𝒪(d)` to `V` is the
`𝒪_V`-dual of `(𝒪_V[T₀, …, Tₙ])_{-n-1-d}`.

The names in the lists below are relative to the
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage` namespace.

## Main definitions

* `rightDerivedPlusPushforwardPullbackIso`: **a higher direct image is unchanged by an
  isomorphism of schemes over the base** — for `α : X₁ ≅ X₂` and `f₂ : X₂ ⟶ Y`,
  `Rⁿ (α ≫ f₂)_* (α^* ℳ) ≅ Rⁿ (f₂)_* ℳ`.
* `preimageProjectiveSpaceIso`: the comparison `f⁻¹V ≅ ℙⁿ_V` of the preimage of an open of the
  base with projective space over that open.
* `restrictTwistIsoPullback`: the restriction of `𝒪(d)` to `f⁻¹V` is the inverse image along
  that comparison of the twist of `ℙⁿ_V`.
* `restrictRightDerivedPlusTopIsoDualBaseDegreeSheaf`: **the degree-`n` row of
  [Stacks, Tag 01XW] on an affine open of an arbitrary base**, in its whole range of twists.

## Main results

* `preimageProjectiveSpaceIso_hom_comp_structureMorphism` and
  `preimageProjectiveSpaceIso_hom_comp_ι`: the comparison `f⁻¹V ≅ ℙⁿ_V` carries the structure
  morphism of `ℙⁿ_V` to the restriction `f ∣_ V` and the base-change morphism `ℙⁿ_V ⟶ ℙⁿ_S` to
  the inclusion of `f⁻¹V`.
* `rightDerivedPushforwardPullbackIso`: the transport of the previous item in Mathlib's
  `ℕ`-indexing of the right derived functors.

## Implementation notes

**The route** is the one
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing`
`.isZero_rightDerivedPlus_pushforward_twistOver_of_isZero` takes for the vanishing row, carrying
an isomorphism rather than a vanishing. Three steps: [Stacks, Tag 01E5] for schemes,
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso`, which
identifies the restriction to `V` of `Rⁿ f_* 𝒪(d)` with the `n`-th higher direct image along
`f ∣_ V` of the restriction of `𝒪(d)`; the comparison of `f⁻¹V` with `ℙⁿ_V`, both being
pullbacks of `ℙⁿ_S` along the inclusion of `V`, together with the matching of the restricted
twist with the twist of `ℙⁿ_V`; and the row over the affine base `V`.

**The transport of a higher direct image along an isomorphism over the base** is what this file
supplies beyond the vanishing argument, where it was not needed. Direct image along an
isomorphism of schemes is an equivalence of the categories of sheaves of modules
(`AlgebraicGeometry.Scheme.Modules.pushforwardEquivOfIso`), hence exact and injective-preserving,
so the right derived functor of a composite beginning with it collapses onto the right derived
functor of the second factor; that collapse is
`Stacks.RightDerivedTransport.rightDerivedPrecomposeEquivObjIso`, and `(α ≫ f₂)_*` is
`α_* ⋙ (f₂)_*` on the nose. The direct image of an inverse image along an isomorphism is the
module itself, by `Stacks.Cohomology.SchemeIso.pushforwardPullbackIso`. The passage from
Mathlib's `ℕ`-indexed right derived functors to the `ℤ`-indexed
`CategoryTheory.Functor.rightDerivedPlus` is `Stacks.DerivedIndexing.rightDerivedIso`.

**The derived category.** `HasDerivedCategory.standard` is installed at priority `2000`, as in
the modules whose statements are composed here, so that
`CategoryTheory.Functor.rightDerivedPlus` elaborates in the same model; at the default priority
the globally declared locally small model is preferred, whose morphisms live one universe lower,
and the composition fails on a universe constraint.

**What is not proved.** Nothing here glues the identifications over a cover of `S` into a
statement about `Rⁿ f_* 𝒪(d)` itself: the isomorphism produced on an affine open is obtained
through several choices and no compatibility with the restriction maps between two affine opens
is available. See the module documentation of
`StacksFrontier/AlgebraicGeometry/ProjectiveSpaceHigherDirectImage/MiddleVanishing.lean` for what
the gluing would need.

No `stacks` attribute is attached: what is proved here is one row of [Stacks, Tag 01XW], and
only locally on the base.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage (rightDerivedPlusRestrictObjIso)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 2000] HasDerivedCategory.standard

/-! ### Higher direct images along an isomorphism of schemes over the base -/

/-- **A higher direct image is unchanged by an isomorphism of schemes over the base**, in
Mathlib's `ℕ`-indexing: for an isomorphism `α : X₁ ≅ X₂`, a morphism `f₂ : X₂ ⟶ Y` and a module
`ℳ` on `X₂`,

`R ⁿ (α ≫ f₂)_* (α^* ℳ) ≅ R ⁿ (f₂)_* ℳ`.

The functors `(α ≫ f₂)_*` and `α_* ⋙ (f₂)_*` are equal, and `α_*` is an equivalence, so the
right derived functor of the composite collapses onto that of `(f₂)_*` evaluated at `α_* α^* ℳ`,
which is `ℳ`. -/
def rightDerivedPushforwardPullbackIso {X₁ X₂ Y : Scheme.{u}} (α : X₁ ≅ X₂) (f₂ : X₂ ⟶ Y)
    (n : ℕ) (M : X₂.Modules) :
    ((Scheme.Modules.pushforward (α.hom ≫ f₂)).rightDerived n).obj
        ((Scheme.Modules.pullback α.hom).obj M) ≅
      ((Scheme.Modules.pushforward f₂).rightDerived n).obj M :=
  Stacks.RightDerivedTransport.rightDerivedPrecomposeEquivObjIso
      (Scheme.Modules.pushforward α.hom) (Scheme.Modules.pushforward f₂)
      ((Scheme.Modules.pullback α.hom).obj M) n ≪≫
    ((Scheme.Modules.pushforward f₂).rightDerived n).mapIso
      (Stacks.Cohomology.SchemeIso.pushforwardPullbackIso α M)

/-- **A higher direct image is unchanged by an isomorphism of schemes over the base**, in the
`ℤ`-indexing `CategoryTheory.Functor.rightDerivedPlus` at a natural-number degree. This is
`rightDerivedPushforwardPullbackIso` read through `Stacks.DerivedIndexing.rightDerivedIso`, the
comparison of the two indexings. -/
def rightDerivedPlusPushforwardPullbackIso {X₁ X₂ Y : Scheme.{u}} (α : X₁ ≅ X₂) (f₂ : X₂ ⟶ Y)
    (n : ℕ) (M : X₂.Modules) :
    ((Scheme.Modules.pushforward (α.hom ≫ f₂)).rightDerivedPlus (n : ℤ)).obj
        ((Scheme.Modules.pullback α.hom).obj M) ≅
      ((Scheme.Modules.pushforward f₂).rightDerivedPlus (n : ℤ)).obj M :=
  ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward (α.hom ≫ f₂)) n).app
      ((Scheme.Modules.pullback α.hom).obj M)).symm ≪≫
    rightDerivedPushforwardPullbackIso α f₂ n M ≪≫
    (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f₂) n).app M

/-! ### The preimage of an open of the base -/

/-- **The preimage of an open `V` of the base in `ℙⁿ_S` is projective `n`-space over `V`.** Both
are pullbacks of `ℙⁿ_S` along the inclusion of `V`: the first by
`AlgebraicGeometry.isPullback_morphismRestrict`, the second by
`AlgebraicGeometry.isPullback_projectiveSpaceOverMap`. -/
def preimageProjectiveSpaceIso (n : ℕ) {S : Scheme.{u}} (V : S.Opens) :
    ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V).toScheme ≅ projectiveSpaceOver n V.toScheme :=
  (isPullback_morphismRestrict (projectiveSpaceOver n S ↘ S) V).isoIsPullback _ _
    (isPullback_projectiveSpaceOverMap n V.ι).flip

/-- The comparison `f⁻¹V ≅ ℙⁿ_V` carries the structure morphism of `ℙⁿ_V` to the restriction
`f ∣_ V` of the structure morphism of `ℙⁿ_S`. -/
theorem preimageProjectiveSpaceIso_hom_comp_structureMorphism (n : ℕ) {S : Scheme.{u}}
    (V : S.Opens) :
    (preimageProjectiveSpaceIso n V).hom ≫ (projectiveSpaceOver n V.toScheme ↘ V.toScheme) =
      (projectiveSpaceOver n S ↘ S) ∣_ V :=
  IsPullback.isoIsPullback_hom_fst _ _
    (isPullback_morphismRestrict (projectiveSpaceOver n S ↘ S) V)
    (isPullback_projectiveSpaceOverMap n V.ι).flip

/-- The comparison `f⁻¹V ≅ ℙⁿ_V` carries the base-change morphism `ℙⁿ_V ⟶ ℙⁿ_S` to the inclusion
of `f⁻¹V`. -/
theorem preimageProjectiveSpaceIso_hom_comp_ι (n : ℕ) {S : Scheme.{u}} (V : S.Opens) :
    (preimageProjectiveSpaceIso n V).hom ≫ projectiveSpaceOverMap n V.ι =
      ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V).ι :=
  IsPullback.isoIsPullback_hom_snd _ _
    (isPullback_morphismRestrict (projectiveSpaceOver n S ↘ S) V)
    (isPullback_projectiveSpaceOverMap n V.ι).flip

/-- **The restriction of `𝒪(d)` to `f⁻¹V` is the twist of `ℙⁿ_V`**, read through the comparison
`preimageProjectiveSpaceIso`: restriction along an open immersion is the inverse image, the two
successive inverse images along `preimageProjectiveSpaceIso` and `ℙⁿ_V ⟶ ℙⁿ_S` compose to the
inverse image along the inclusion of `f⁻¹V` by
`preimageProjectiveSpaceIso_hom_comp_ι`, and the inverse image of `𝒪(d)` along the base-change
morphism is the twist of `ℙⁿ_V` by
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.twistOverPullbackIso`. -/
def restrictTwistIsoPullback (n : ℕ) {S : Scheme.{u}} (V : S.Opens) (d : ℤ) :
    (Scheme.Modules.restrictFunctor ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V).ι).obj
        (twistOver n S d) ≅
      (Scheme.Modules.pullback (preimageProjectiveSpaceIso n V).hom).obj
        (twistOver n V.toScheme d) :=
  (Scheme.Modules.restrictFunctorIsoPullback _).app (twistOver n S d) ≪≫
    (Scheme.Modules.pullbackCongr
      (preimageProjectiveSpaceIso_hom_comp_ι n V).symm).app (twistOver n S d) ≪≫
    ((Scheme.Modules.pullbackComp (preimageProjectiveSpaceIso n V).hom
      (projectiveSpaceOverMap n V.ι)).app (twistOver n S d)).symm ≪≫
    (Scheme.Modules.pullback (preimageProjectiveSpaceIso n V).hom).mapIso
      (twistOverPullbackIso n V.ι d)

/-! ### The degree-`n` row on an affine open -/

/-- **The degree-`n` row of [Stacks, Tag 01XW] on an affine open of an arbitrary base**, in its
whole range of twists: for the structure morphism `f : ℙⁿ_S ⟶ S` over an arbitrary scheme `S`,
for `n = m + 1 ≥ 1`, for every integer `d` and for every affine open `V ⊆ S`,

`(Rⁿ f_* 𝒪(d))|_V ≅ Hom_{𝒪_V}((𝒪_V[T₀, …, Tₙ])_{-n-1-d}, 𝒪_V)`.

The restriction of `Rⁿ f_* 𝒪(d)` to `V` is the `n`-th higher direct image along `f ∣_ V` of the
restriction of `𝒪(d)` to `f⁻¹V`, by [Stacks, Tag 01E5]; that restriction is the inverse image of
the twist of `ℙⁿ_V` along the comparison `f⁻¹V ≅ ℙⁿ_V`, which carries `f ∣_ V` to the structure
morphism of `ℙⁿ_V`, so the higher direct image is the one over the base `V`; and `V` is
affine. -/
def restrictRightDerivedPlusTopIsoDualBaseDegreeSheaf (m : ℕ) (S : Scheme.{u}) (d : ℤ)
    {V : S.Opens} (hV : IsAffineOpen V) :
    (Scheme.Modules.restrictFunctor V.ι).obj
        (((Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)).rightDerivedPlus
          ((m + 1 : ℕ) : ℤ)).obj (twistOver (m + 1) S d)) ≅
      dualSheaf (baseDegreeSheaf (m + 1) V.toScheme (-((m + 1 : ℕ) : ℤ) - 1 - d)) := by
  have : IsAffine V.toScheme := hV
  refine (rightDerivedPlusRestrictObjIso (projectiveSpaceOver (m + 1) S ↘ S) V (m + 1)
      (twistOver (m + 1) S d)).symm ≪≫ ?_
  refine ((Scheme.Modules.pushforward
      ((projectiveSpaceOver (m + 1) S ↘ S) ∣_ V)).rightDerivedPlus
      ((m + 1 : ℕ) : ℤ)).mapIso (restrictTwistIsoPullback (m + 1) V d) ≪≫ ?_
  refine ?_ ≪≫ rightDerivedPlusTopIsoDualBaseDegreeSheaf_of_isAffine m V.toScheme d
  rw [← preimageProjectiveSpaceIso_hom_comp_structureMorphism (m + 1) V]
  exact rightDerivedPlusPushforwardPullbackIso (preimageProjectiveSpaceIso (m + 1) V)
    (projectiveSpaceOver (m + 1) V.toScheme ↘ V.toScheme) (m + 1) (twistOver (m + 1) V.toScheme d)

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
