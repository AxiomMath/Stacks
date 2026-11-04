module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.Regularity

/-!
# Twisting on projective space commutes with base change

`AlgebraicGeometry.projectiveTwist n F d` is `F ⊗_{𝒪} π^* 𝒪(d)`, where `π` is the projection of
`ℙⁿ_R` to the integral model and `𝒪(d)` is the integral twisting sheaf. Both factors are stable
under a base change `R ⟶ S` of the coefficient ring: the first tautologically, and the second
because the projection to the integral model is unchanged by
`AlgebraicGeometry.projectiveSpaceOverMap_snd`. So twisting commutes with pulling back along
`AlgebraicGeometry.projectiveSpaceOverRingMap`.

This is the non-cohomological half of [Stacks, Tag 08A4]. Combining it with the fact that
cohomology is a functor gives `AlgebraicGeometry.isMRegular_pullback_iff_forall_isZero`, which
rewrites `m`-regularity of the pulled-back sheaf on `ℙⁿ_{K}` as a vanishing statement about the
*pullbacks of the twists of the original sheaf*. That is the form flat base change for cohomology
consumes, so it isolates exactly what 08A4 still owes.

## Main definitions

* `AlgebraicGeometry.projectiveSpaceAtUniverseTwistingSheaf`: the integral twisting sheaf
  `𝒪(d)` on the integral model of projective space, with the total-degree grading supplied.

## Main results

* `AlgebraicGeometry.projectiveTwist_eq`: `projectiveTwist` written as the tensor-product
  bifunctor of the ambient ringed space applied to a pair, by `rfl`.
* `AlgebraicGeometry.twistingSheafPullbackIso`: the pullback of `π^* 𝒪(d)` along a base change
  of projective spaces is `π^* 𝒪(d)` on the smaller base.
* `AlgebraicGeometry.projectiveTwistPullbackIso`: `(f^* F)(d) ≅ f^* (F(d))` for the base-change
  morphism of projective spaces induced by a ring map.
* `AlgebraicGeometry.isMRegular_pullback_iff_forall_isZero`: `m`-regularity of the pullback of
  `F` to `ℙⁿ_{K}` is the vanishing of `Hⁱ(ℙⁿ_{K}, f^*(F(m - i)))` for `1 ≤ i ≤ n`.

## Implementation notes

**No `@[stacks 08A4]` attribute is attached anywhere in this file, and 08A4 is not proved here.**
What 08A4 asserts is that `F` is `m`-regular if and only if its pullback to `ℙⁿ_{K}` is, and the
source's proof is flat base change for cohomology, [Stacks, Tag 02KH] part (2), in the degrees
`1 ≤ i ≤ n`. The results here remove everything *else* from 08A4: after
`isMRegular_pullback_iff_forall_isZero` the two sides of the tag differ by exactly
`IsZero (Hⁱ(ℙⁿ_k, G)) ↔ IsZero (Hⁱ(ℙⁿ_{K}, f^* G))` at `G = F(m - i)` — which is supplied, in
every degree, by `AlgebraicGeometry.isZero_Hgroup_projectiveSpace_baseChange_iff`, and the tag
itself by `isMRegular_iff_fieldExtension`, both in `ProjectiveSpaceBaseChange/FieldExtension.lean`.

Three spelling facts make this cheap, and each is `rfl`:

* `Stacks.SheafOfModules.TensorSheafification.tensorSheaf X.presheaf X.ringCatSheaf.2 A B` is
  `(Stacks.RingedSpace.tensorSheaf X.toSheafedSpace).obj (A, B)`, so `projectiveTwist` — which is
  written in the first spelling — is a value of the bifunctor the [Stacks, Tag 01CD]
  comparison `Stacks.RingedSpace.comparisonBifunctorIso` is stated for. No bridge between tensor
  constructions is needed; `projectiveTwist_eq` records the identification.
* `Scheme.Modules.pullback f` is `Stacks.RingedSpace.pullbackFunctor f.toLRSHom.toShHom`, so that
  comparison applies to the scheme-level pullback directly.
* The underlying ringed space of a scheme `X` is `X.toSheafedSpace`, `RingedSpace` being
  `SheafedSpace CommRingCat`.

The one obstacle is the heartbeat budget, and no option is set for it: writing
`(Stacks.RingedSpace.comparisonBifunctorIso _).app _` and leaving the pair to unification exhausts
the default heartbeat budget at `whnf`, because the metavariable has to be solved against an
unfolding of `projectiveTwist`. Supplying the pair explicitly — the closed-pattern cure — makes
the same term elaborate at once, and the final isomorphism is then assembled after `rw` by
`projectiveTwist_eq` so that nothing has to unfold `projectiveTwist` at all.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 08A4](https://stacks.math.columbia.edu/tag/08A4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The integral twisting sheaf `𝒪(d)` on the integral model `ℙⁿ_ℤ` of projective space, for the
total-degree grading of the polynomial ring in `n + 1` variables over `ULift ℤ`. -/
public noncomputable abbrev projectiveSpaceAtUniverseTwistingSheaf (n : ℕ) (d : ℤ) :
    (projectiveSpaceAtUniverse.{u} n).Modules :=
  ProjectiveSpectrum.Proj.twistingSheaf
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) d

variable {R S : Type u} [CommRing R] [CommRing S]

/-- `AlgebraicGeometry.projectiveTwist` is the tensor-product bifunctor of the ambient ringed
space applied to the pair consisting of the module and the pulled-back integral twisting sheaf.
This is the identification that lets the [Stacks, Tag 01CD] comparison be applied to it. -/
public theorem projectiveTwist_eq (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of R)).Modules) (d : ℤ) :
    projectiveTwist n F d =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(((projectiveSpaceOverRing n (.of R)).toSheafedSpace)).presheaf,
            (((projectiveSpaceOverRing n (.of R)).toSheafedSpace)).IsSheaf⟩))).obj
        (F, (Scheme.Modules.pullback
          (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of R)))).obj
          (projectiveSpaceAtUniverseTwistingSheaf n d)) :=
  rfl

/-- Pulling back the twisting sheaf of `ℙⁿ_R` along the base-change morphism gives the twisting
sheaf of `ℙⁿ_S`: both are pulled back from the integral model, and the base-change morphism is the
identity on the integral model. -/
public noncomputable def twistingSheafPullbackIso
    (f : CommRingCat.of R ⟶ CommRingCat.of S) (n : ℕ) (d : ℤ) :
    (Scheme.Modules.pullback (projectiveSpaceOverRingMap n f)).obj
        ((Scheme.Modules.pullback
          (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of R)))).obj
          (projectiveSpaceAtUniverseTwistingSheaf n d)) ≅
      (Scheme.Modules.pullback
          (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of S)))).obj
        (projectiveSpaceAtUniverseTwistingSheaf n d) :=
  (Scheme.Modules.pullbackComp (projectiveSpaceOverRingMap n f)
      (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of R)))).app _ ≪≫
    (Scheme.Modules.pullbackCongr (projectiveSpaceOverMap_snd n (Spec.map f))).app _

/-- The tensor-product step of `AlgebraicGeometry.projectiveTwistPullbackIso`, stated in the
bifunctor spelling so that no unfolding of `projectiveTwist` is needed: the pair at which the
[Stacks, Tag 01CD] comparison is read is written out, which is what keeps the elaboration inside
the default budget. -/
public noncomputable def projectiveTwistPullbackCoreIso
    (f : CommRingCat.of R ⟶ CommRingCat.of S) (n : ℕ) (d : ℤ)
    (F : (projectiveSpaceOverRing n (.of R)).Modules) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((projectiveSpaceOverRing n (.of S)).toSheafedSpace)).presheaf,
          (((projectiveSpaceOverRing n (.of S)).toSheafedSpace)).IsSheaf⟩))).obj
      ((Scheme.Modules.pullback (projectiveSpaceOverRingMap n f)).obj F,
        (Scheme.Modules.pullback
          (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of S)))).obj
          (projectiveSpaceAtUniverseTwistingSheaf n d)) ≅
      (Scheme.Modules.pullback (projectiveSpaceOverRingMap n f)).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(((projectiveSpaceOverRing n (.of R)).toSheafedSpace)).presheaf,
              (((projectiveSpaceOverRing n (.of R)).toSheafedSpace)).IsSheaf⟩))).obj
          (F, (Scheme.Modules.pullback
            (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of R)))).obj
            (projectiveSpaceAtUniverseTwistingSheaf n d))) :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((projectiveSpaceOverRing n (.of S)).toSheafedSpace)).presheaf,
        (((projectiveSpaceOverRing n (.of S)).toSheafedSpace)).IsSheaf⟩))).mapIso
      (Iso.prod (Iso.refl ((Scheme.Modules.pullback (projectiveSpaceOverRingMap n f)).obj F))
        (twistingSheafPullbackIso f n d).symm) ≪≫
    ((Stacks.RingedSpace.comparisonBifunctorIso
        (projectiveSpaceOverRingMap n f).toLRSHom.toShHom).app
      (F, (Scheme.Modules.pullback
        (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of R)))).obj
        (projectiveSpaceAtUniverseTwistingSheaf n d))).symm

/-- **Twisting on projective space commutes with base change of the coefficient ring:**
`(f^* F)(d) ≅ f^* (F(d))`. -/
public noncomputable def projectiveTwistPullbackIso
    (f : CommRingCat.of R ⟶ CommRingCat.of S) (n : ℕ) (d : ℤ)
    (F : (projectiveSpaceOverRing n (.of R)).Modules) :
    projectiveTwist n
        ((Scheme.Modules.pullback (projectiveSpaceOverRingMap n f)).obj F) d ≅
      (Scheme.Modules.pullback (projectiveSpaceOverRingMap n f)).obj
        (projectiveTwist n F d) := by
  rw [projectiveTwist_eq n _ d, projectiveTwist_eq n F d]
  exact projectiveTwistPullbackCoreIso f n d F

/-- Cohomology does not distinguish the twist of a pullback from the pullback of a twist, being a
functor: this is `AlgebraicGeometry.projectiveTwistPullbackIso` read through `Hⁱ`. -/
public theorem isZero_Hgroup_projectiveTwist_pullback_iff
    (f : CommRingCat.of R ⟶ CommRingCat.of S) (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of R)).Modules) (d : ℤ) (i : ℕ) :
    IsZero (Hgroup (projectiveSpaceOverRing n (.of S)).ringCatSheaf ⊤ i
        (projectiveTwist n
          ((Scheme.Modules.pullback (projectiveSpaceOverRingMap n f)).obj F) d)) ↔
      IsZero (Hgroup (projectiveSpaceOverRing n (.of S)).ringCatSheaf ⊤ i
        ((Scheme.Modules.pullback (projectiveSpaceOverRingMap n f)).obj
          (projectiveTwist n F d))) :=
  ((Hfunctor (projectiveSpaceOverRing n (.of S)).ringCatSheaf ⊤ i).mapIso
    (projectiveTwistPullbackIso f n d F)).isZero_iff

/-- **The non-cohomological half of [Stacks, Tag 08A4].** `m`-regularity of the pullback of `F` to
`ℙⁿ_{K}` says exactly that the cohomology of the *pullbacks of the twists of `F`* vanishes in the
degrees `1 ≤ i ≤ n`. Tag 08A4 is therefore equivalent to flat base change for those cohomology
groups, and nothing else; the tag is not proved here. -/
public theorem isMRegular_pullback_iff_forall_isZero (k K : Type u) [Field k] [Field K]
    [Algebra k K] (n : ℕ) (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent]
    (m : ℤ) :
    letI : IsLocallyNoetherian (projectiveSpaceOverRing n (.of K)) :=
      projectiveSpaceOver_isLocallyNoetherian n (Spec (.of K))
    letI : ((Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k K n)).obj F).IsCoherent :=
      isCoherent_pullback (projectiveSpaceFieldExtensionMap k K n) F
    IsMRegular K n
        ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj F) m ↔
      ∀ i : ℕ, 1 ≤ i → i ≤ n →
        IsZero (Hgroup (projectiveSpaceOverRing n (.of K)).ringCatSheaf ⊤ i
          ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj
            (projectiveTwist n F (m - i)))) := by
  refine forall_congr' fun i => forall_congr' fun _ => forall_congr' fun _ => ?_
  exact isZero_Hgroup_projectiveTwist_pullback_iff
    (CommRingCat.ofHom (algebraMap k K)) n F (m - i) i

end AlgebraicGeometry

end
