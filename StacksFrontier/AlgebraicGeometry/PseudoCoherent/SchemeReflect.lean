module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardReflectPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SchemePushforwardPseudoCoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The converse half of Stacks 09VA for a closed immersion of schemes, and Stacks 09VC

`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_derivedPushforwardOXMod` is the converse
implication of Stacks 09VA for a morphism of ringed spaces whose underlying continuous map is a
closed embedding. This file restates it for a closed immersion of schemes, in the idiom
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward` that Stacks 09VC, 09VD and
09VE use, and feeds it to
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_reflect_fin`, whose
`reflect` hypothesis it is.

The restatement needs no comparison isomorphism, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/SchemePushforwardPseudoCoherent.lean`: the two
derived pushforwards are the same functor, and an application is elaborated at default
transparency, which sees through the two `def`s separating
`AlgebraicGeometry.Scheme.Modules` from `Stacks.StrictlyPerfect.OXMod`. This file is the mirror of
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_pushforward_mapDerivedCategory`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_of_pushforward_mapDerivedCategory`: the
  converse half of Stacks 09VA for a closed immersion of schemes.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_fin`: **Stacks 09VC
  with both halves of Stacks 09VA discharged.** Only the side condition of Stacks 09VA — that
  `p_*𝒪` is pseudo-coherent for a closed immersion `p` of finite-dimensional affine spaces over
  the base — is still asked for.

## Implementation notes

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`, made
a local instance as in the file this one mirrors. The converse half of Stacks 09VA carries, besides
the instances for the two spaces, instances for the modules on every open subspace of each; those
too come from `CategoryTheory.HasDerivedCategory.standard`, since instance search discharges a
universally quantified instance goal by introducing the open and applying it.

No `stacks` attribute is placed on
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_fin`: Stacks 09VC is
stated without the side condition, which is still a hypothesis here.

## References

* [The Stacks Project, Lemma 36.60.9 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **The converse half of Stacks 09VA for a closed immersion of schemes.** Let `k : Y ⟶ Z` be a
closed immersion of schemes such that `k_*𝒪_Y` is a pseudo-coherent sheaf of `𝒪_Z`-modules. If
`k_*A` is an `m`-pseudo-coherent object of `D(𝒪_Z)` then `A` is an `m`-pseudo-coherent object of
`D(𝒪_Y)`.

This is `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_derivedPushforwardOXMod` applied to
the morphism of ringed spaces underlying `k`, whose underlying continuous map is a closed
embedding by `Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom`. No comparison isomorphism
intervenes: `k_*` on derived categories is the same functor in both developments. -/
@[sga "6 III 1.1.1" "Sufficiency clause"]
public theorem isPseudoCoherentFrom_of_pushforward_mapDerivedCategory {Y Z : Scheme.{u}}
    (k : Y ⟶ Z) [IsClosedImmersion k]
    (hO : RingedSpace.IsPseudoCoherent (X := Z.toRingedSpace)
      ((DerivedCategory.singleFunctor Z.Modules 0).obj
        ((pushforward k).obj (SheafOfModules.unit Y.ringCatSheaf))))
    (m : ℤ) (A : DerivedCategory Y.Modules)
    (hA : RingedSpace.IsPseudoCoherentFrom (X := Z.toRingedSpace)
      ((pushforward k).mapDerivedCategory.obj A) m) :
    RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace) A m :=
  RingedSpace.isPseudoCoherentFrom_of_derivedPushforwardOXMod k.toLRSHom.toShHom
    (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom k) hO m A hA

/-- **Stacks 09VC, with both halves of Stacks 09VA discharged.** Let `f : X ⟶ S` be a morphism of
affine schemes locally of finite type, let `E` be an object of `D(𝒪_X)` and assume the side
condition of Stacks 09VA: for every closed immersion `p : 𝔸ᵃ_S ⟶ 𝔸ᵇ_S` of finite-dimensional
affine spaces over `S`, the sheaf `p_*𝒪` is pseudo-coherent. Then `m`-pseudo-coherence of the
derived pushforward of `E` along *some* closed immersion of `X` into an affine space over `S`
factoring `f` is equivalent to the same along *every* such closed immersion.

This is
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_reflect_fin` with its
`reflect` hypothesis supplied by
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_of_pushforward_mapDerivedCategory`. -/
public theorem isPseudoCoherentFrom_some_iff_forall_of_fin {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules) (m : ℤ)
    (hO : ∀ {a b : ℕ}
      (p : AffineSpace (ULift.{u} (Fin a)) S ⟶ AffineSpace (ULift.{u} (Fin b)) S)
      [IsClosedImmersion p],
      RingedSpace.IsPseudoCoherent (X := (AffineSpace (ULift.{u} (Fin b)) S).toRingedSpace)
        ((DerivedCategory.singleFunctor (AffineSpace (ULift.{u} (Fin b)) S).Modules 0).obj
          ((pushforward p).obj
            (SheafOfModules.unit (AffineSpace (ULift.{u} (Fin a)) S).ringCatSheaf)))) :
    (∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = f ∧
          IsPseudoCoherentFromAfterPushforward i E m) ↔
      (∀ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S),
        IsClosedImmersion i →
          i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = f →
            IsPseudoCoherentFromAfterPushforward i E m) :=
  isPseudoCoherentFrom_some_iff_forall_of_reflect_fin f E m hO
    fun p _ _ A hA => isPseudoCoherentFrom_of_pushforward_mapDerivedCategory p (hO p) m A hA

end AlgebraicGeometry.Scheme.Modules

end
