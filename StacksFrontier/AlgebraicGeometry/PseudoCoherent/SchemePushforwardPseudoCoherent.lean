module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.KoszulPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The forward half of Stacks 09VA for a closed immersion of schemes

`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedPushforwardOXMod` is the forward
implication of Stacks 09VA for a morphism of ringed spaces whose underlying continuous map is a
closed embedding: if `E` is `m`-pseudo-coherent and `i_*𝒪_Z` is a pseudo-coherent `𝒪_X`-module,
then `Ri_*E` is `m`-pseudo-coherent. Stacks 09VC, 09VD and 09VE all consume that implication for
a closed immersion of *schemes*, and in the idiom
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward`: the proof of Stacks 09VD
factors a closed immersion `X ⟶ 𝔸ⁿ⁺¹_S` as `X ⟶ 𝔸ⁿ_V ⟶ 𝔸ⁿ⁺¹_S` and pushes the hypothesis
forward along the second factor, and the proof of Stacks 09VE does the same along
`T ⟶ 𝔸³ⁿ_S` for `T` the closed subscheme cut out by `∑ yᵢzᵢ - 1`.

This file supplies the restatement. The categories `AlgebraicGeometry.Scheme.Modules` and
`Stacks.StrictlyPerfect.OXMod` of the underlying ringed space are the same type with the same
abelian structure, so no transport is needed; see the implementation notes.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_pushforward_mapDerivedCategory`: the
  forward implication of Stacks 09VA for a closed immersion of schemes.
* `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward.comp`: the step the
  proofs of Stacks 09VD and 09VE take — the local condition of Stacks 09UI at a closed immersion
  `i` implies it at `i ≫ k`, for any closed immersion `k` whose pushforward of the structure
  sheaf is pseudo-coherent.
* `AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_comp` and
  `AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_affineOpen`:
  **the first paragraph of the proof of Stacks 09VD** — the equivalent conditions of Stacks 09VC
  for `(X ⟶ V, E)` imply them for `(X ⟶ S, E)`, for `V` an affine open of an affine `S`.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_reflect_fin`:
  **Stacks 09VC with the forward half of Stacks 09VA discharged.** Only the reverse half of
  Stacks 09VA, and its side condition at a closed immersion of finite-dimensional affine spaces
  over `S`, are still asked for.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules X` is a `def` for
`AlgebraicGeometry.SheafOfModules X.ringCatSheaf` carrying its own `Category` instance, and
`Stacks.StrictlyPerfect.OXMod X.toRingedSpace` is the same type again
(`Stacks.DerivedQCoh.oxMod_eq_sheafOfModules` is `rfl`). Typeclass synthesis does not cross that
boundary, because it unfolds at reducible transparency only. Nothing here needs it to: the proofs
below are `exact`/`rw` applications of the ringed-space results, and an application is elaborated
at default transparency, which does see through the two `def`s. In particular
`AlgebraicGeometry.Scheme.Modules.pushforward k` and
`Stacks.StrictlyPerfect.OXMod`-level `AlgebraicGeometry.RingedSpace.pushforwardOXMod` of
`k.toLRSHom.toShHom` are both `CategoryTheory.SheafOfModules.pushforward` of the same morphism of
sheaves of rings, so `(pushforward k).mapDerivedCategory` *is* the `Ri_*` of the ringed-space
development and no comparison isomorphism is needed. The hypothesis on `k_*𝒪` is accordingly
stated at the scheme-level spelling `(pushforward k).obj (SheafOfModules.unit _)`, which is the
spelling `AlgebraicGeometry.Scheme.Modules.epi_unitToPushforwardObjUnit` uses, and is accepted
where the ringed-space `AlgebraicGeometry.RingedSpace.pushforwardStructureModule` is expected.

What Stacks 09VC still waits on is therefore exactly two things, and
`isPseudoCoherentFrom_some_iff_forall_of_reflect_fin` names both. The first is the reverse
implication of Stacks 09VA. The second is the side condition of Stacks 09VA at a closed immersion
`p : 𝔸ᵃ_S ⟶ 𝔸ᵇ_S`, namely that `p_*𝒪` is a pseudo-coherent sheaf of modules. The *module-level*
form of that side condition is
`PseudoCoherence.isModulePseudoCoherentFrom_mvPolynomial_of_surjective`; what is missing between
the two is the easy half of Stacks 08E7, that a pseudo-coherent complex of `A`-modules gives a
pseudo-coherent object of `D(𝒪_{Spec A})`. The degree-zero case of the sheaf-level statement holds
for *every* closed immersion of schemes and needs no algebra at all — it is
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_singleFunctor_unit_zero`,
whose argument is that `𝒪 ⟶ p_*𝒪` is an epimorphism — but the side condition of Stacks 09VA asks
for every degree, and in negative degrees it is a genuine finiteness condition on `p`.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 20.49.2 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Lemma 36.61.4 (09VD)](https://stacks.math.columbia.edu/tag/09VD)
* [The Stacks Project, Lemma 36.61.5 (09VE)](https://stacks.math.columbia.edu/tag/09VE)
* [The Stacks Project, Lemma 36.17.1 (08E7)](https://stacks.math.columbia.edu/tag/08E7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **The forward half of Stacks 09VA for a closed immersion of schemes.** Let `k : Y ⟶ Z` be a
closed immersion of schemes such that `k_*𝒪_Y` is a pseudo-coherent sheaf of `𝒪_Z`-modules. Then
`k_*` carries an `m`-pseudo-coherent object of `D(𝒪_Y)` to an `m`-pseudo-coherent object of
`D(𝒪_Z)`.

This is `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedPushforwardOXMod` applied to
the morphism of ringed spaces underlying `k`, whose underlying continuous map is a closed
embedding by `Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom`. No comparison isomorphism
intervenes: `k_*` on derived categories is the same functor in both developments. -/
@[sga "6 III 1.1.1" "Necessity clause", sga "6 III 2.5" "special case"]
public theorem isPseudoCoherentFrom_pushforward_mapDerivedCategory {Y Z : Scheme.{u}} (k : Y ⟶ Z)
    [IsClosedImmersion k]
    (hO : RingedSpace.IsPseudoCoherent (X := Z.toRingedSpace)
      ((DerivedCategory.singleFunctor Z.Modules 0).obj
        ((pushforward k).obj (SheafOfModules.unit Y.ringCatSheaf))))
    (m : ℤ) (A : DerivedCategory Y.Modules)
    (hA : RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace) A m) :
    RingedSpace.IsPseudoCoherentFrom (X := Z.toRingedSpace)
      ((pushforward k).mapDerivedCategory.obj A) m :=
  RingedSpace.isPseudoCoherentFrom_derivedPushforwardOXMod k.toLRSHom.toShHom
    (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom k) hO m A hA

/-- **Pushing the local condition of Stacks 09UI forward along a further closed immersion.** Let
`i : X ⟶ Y` and `k : Y ⟶ Z` be closed immersions of schemes with `k_*𝒪_Y` a pseudo-coherent sheaf
of `𝒪_Z`-modules. If `Ri_*E` is `m`-pseudo-coherent on `Y`, then `R(i ≫ k)_*E` is
`m`-pseudo-coherent on `Z`.

This is the step both Stacks 09VD and Stacks 09VE take: a closed immersion of `X` into an affine
space over a *standard open* of the base, resp. into the closed subscheme of an affine space cut
out by `∑ yᵢzᵢ - 1`, is composed with a closed immersion of that target into an affine space over
the base itself, and the hypothesis is carried along by Stacks 09VA.

The two pushforwards are related by
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_comp_iff`, which identifies
the local condition at `i ≫ k` with pseudo-coherence of the iterated pushforward. -/
public theorem IsPseudoCoherentFromAfterPushforward.comp {X Y Z : Scheme.{u}} (i : X ⟶ Y)
    (k : Y ⟶ Z) [IsClosedImmersion i] [IsClosedImmersion k]
    (hO : RingedSpace.IsPseudoCoherent (X := Z.toRingedSpace)
      ((DerivedCategory.singleFunctor Z.Modules 0).obj
        ((pushforward k).obj (SheafOfModules.unit Y.ringCatSheaf))))
    {E : DerivedCategory X.Modules} {m : ℤ}
    (h : IsPseudoCoherentFromAfterPushforward i E m) :
    IsPseudoCoherentFromAfterPushforward (i ≫ k) E m := by
  rw [isPseudoCoherentFromAfterPushforward_comp_iff]
  exact isPseudoCoherentFrom_pushforward_mapDerivedCategory k hO m _
    ((isPseudoCoherentFromAfterPushforward_iff i E m).mp h)

/-- **Enlarging the base of the local condition of Stacks 09UI along a morphism locally of finite
type.** Let `i : X ⟶ Y` be a closed immersion of affine schemes, let `g : Y ⟶ S` be locally of
finite type with `S` affine, and assume the side condition of Stacks 09VA for every closed
immersion of `Y` into an affine space over `S`. If `Ri_*E` is `m`-pseudo-coherent on `Y`, then
there is a closed immersion of `X` into an affine space over `S`, factoring `i ≫ g`, along which
the derived pushforward of `E` is `m`-pseudo-coherent.

`AlgebraicGeometry.exists_isClosedImmersion_affineSpace` produces a closed immersion
`p : Y ⟶ 𝔸ᴺ_S` factoring `g`, and `i ≫ p` is the required closed immersion by
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward.comp`.

**This is the first paragraph of the proof of Stacks 09VD**, read with `Y = 𝔸ⁿ_V` for `V ⊆ S` an
affine open and `g` the composite `𝔸ⁿ_V ⟶ V ⟶ S`; see
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_affineOpen`. The
source takes `V` to be a *standard* open there and writes the closed immersion
`𝔸ⁿ_V ⟶ 𝔸ⁿ⁺¹_S` down in coordinates, `x₀ ↦ 1/a`; it is not necessary to, because an open
immersion is locally of finite type whatever the open, so `𝔸ⁿ_V ⟶ S` is locally of finite type
and a closed immersion into some affine space over `S` exists for that reason alone. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_of_comp {X Y S : Scheme.{u}}
    [IsAffine Y] [IsAffine S] (i : X ⟶ Y) [IsClosedImmersion i] (g : Y ⟶ S)
    [LocallyOfFiniteType g]
    (hO : ∀ (N : ℕ) (p : Y ⟶ AffineSpace (ULift.{u} (Fin N)) S), IsClosedImmersion p →
      RingedSpace.IsPseudoCoherent (X := (AffineSpace (ULift.{u} (Fin N)) S).toRingedSpace)
        ((DerivedCategory.singleFunctor (AffineSpace (ULift.{u} (Fin N)) S).Modules 0).obj
          ((pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf))))
    (E : DerivedCategory X.Modules) (m : ℤ) (h : IsPseudoCoherentFromAfterPushforward i E m) :
    ∃ (N : ℕ) (j : X ⟶ AffineSpace (ULift.{u} (Fin N)) S),
      IsClosedImmersion j ∧
        j ≫ (AffineSpace.over (ULift.{u} (Fin N)) S).hom = i ≫ g ∧
          IsPseudoCoherentFromAfterPushforward j E m := by
  obtain ⟨N, p, hp, hpo⟩ := exists_isClosedImmersion_affineSpace g
  have := hp
  exact ⟨N, i ≫ p, inferInstance, by rw [Category.assoc, hpo],
    IsPseudoCoherentFromAfterPushforward.comp i p (hO N p hp) h⟩

/-- **The first step of the proof of Stacks 09VD.** Let `S` be affine, let `V ⊆ S` be an affine
open, let `f : X ⟶ V` be a morphism of affine schemes locally of finite type, and let `E` be an
object of `D(𝒪_X)`. Granted the side condition of Stacks 09VA for the closed immersions of
affine spaces over `V` into affine spaces over `S`, the equivalent conditions of Stacks 09VC for
the pair `(X ⟶ V, E)` imply them for the pair `(X ⟶ S, E)`.

This is
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_comp` with
`Y = 𝔸ⁿ_V` and `g` the composite `𝔸ⁿ_V ⟶ V ⟶ S`, which is locally of finite type because
`𝔸ⁿ_V ⟶ V` is locally of finite presentation and `V ⟶ S` is an open immersion. The source
assumes `V` is a standard open; this step does not need that. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_of_affineOpen {S X : Scheme.{u}}
    [IsAffine S] (V : S.affineOpens) (f : X ⟶ (V.1 : Scheme.{u}))
    (hO : ∀ (n N : ℕ) (p : AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u}) ⟶
        AffineSpace (ULift.{u} (Fin N)) S), IsClosedImmersion p →
      RingedSpace.IsPseudoCoherent (X := (AffineSpace (ULift.{u} (Fin N)) S).toRingedSpace)
        ((DerivedCategory.singleFunctor (AffineSpace (ULift.{u} (Fin N)) S).Modules 0).obj
          ((pushforward p).obj
            (SheafOfModules.unit
              (AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).ringCatSheaf))))
    (E : DerivedCategory X.Modules) (m : ℤ)
    (h : ∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u})),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom = f ∧
          IsPseudoCoherentFromAfterPushforward i E m) :
    ∃ (N : ℕ) (j : X ⟶ AffineSpace (ULift.{u} (Fin N)) S),
      IsClosedImmersion j ∧
        j ≫ (AffineSpace.over (ULift.{u} (Fin N)) S).hom = f ≫ V.1.ι ∧
          IsPseudoCoherentFromAfterPushforward j E m := by
  obtain ⟨n, i, hi, hio, hpc⟩ := h
  have := hi
  have hover : LocallyOfFiniteType
      ((AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom) := by
    rw [AffineSpace.over_hom_eq]
    infer_instance
  have hg : LocallyOfFiniteType
      ((AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom ≫ V.1.ι) :=
    MorphismProperty.comp_mem _ _ _ hover inferInstance
  obtain ⟨N, j, hj, hjo, hjpc⟩ :=
    exists_isPseudoCoherentFromAfterPushforward_of_comp i
      ((AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom ≫ V.1.ι) (hO n) E m hpc
  exact ⟨N, j, hj, by rw [hjo, ← Category.assoc, hio], hjpc⟩

/-- **Stacks 09VC, with the forward half of Stacks 09VA discharged.** Let `f : X ⟶ S` be a
morphism of affine schemes locally of finite type and let `E` be an object of `D(𝒪_X)`. Assume

* `hO`: for every closed immersion `p : 𝔸ᵃ_S ⟶ 𝔸ᵇ_S` of finite-dimensional affine spaces over
  `S`, the sheaf `p_*𝒪` is a pseudo-coherent sheaf of modules — this is the side condition of
  Stacks 09VA; and
* `reflect`: the *reverse* implication of Stacks 09VA for such a `p` over `S`, namely that
  `m`-pseudo-coherence of `p_*A` implies `m`-pseudo-coherence of `A`.

Then `m`-pseudo-coherence of the derived pushforward of `E` along *some* closed immersion of `X`
into an affine space over `S` factoring `f` is equivalent to the same along *every* such closed
immersion.

This is `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_of_transport_fin`
with the forward direction of its `transport` hypothesis supplied by
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_pushforward_mapDerivedCategory`, so it is
the stronger statement; the implementation notes of this file record what the two remaining
hypotheses still cost. The index types are the `ULift (Fin a)` of that lemma, at which the
hypotheses are satisfiable — asked for at an arbitrary index type they are not, because
Stacks 09VA fails for a closed immersion of affine spaces of infinite dimension. -/
public theorem isPseudoCoherentFrom_some_iff_forall_of_reflect_fin {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules) (m : ℤ)
    (hO : ∀ {a b : ℕ}
      (p : AffineSpace (ULift.{u} (Fin a)) S ⟶ AffineSpace (ULift.{u} (Fin b)) S)
      [IsClosedImmersion p],
      RingedSpace.IsPseudoCoherent (X := (AffineSpace (ULift.{u} (Fin b)) S).toRingedSpace)
        ((DerivedCategory.singleFunctor (AffineSpace (ULift.{u} (Fin b)) S).Modules 0).obj
          ((pushforward p).obj
            (SheafOfModules.unit (AffineSpace (ULift.{u} (Fin a)) S).ringCatSheaf))))
    (reflect : ∀ {a b : ℕ}
      (p : AffineSpace (ULift.{u} (Fin a)) S ⟶ AffineSpace (ULift.{u} (Fin b)) S)
      [IsClosedImmersion p],
      p ≫ (AffineSpace.over (ULift.{u} (Fin b)) S).hom =
        (AffineSpace.over (ULift.{u} (Fin a)) S).hom →
      ∀ A : DerivedCategory (AffineSpace (ULift.{u} (Fin a)) S).Modules,
        RingedSpace.IsPseudoCoherentFrom
            (X := (AffineSpace (ULift.{u} (Fin b)) S).toRingedSpace)
            ((pushforward p).mapDerivedCategory.obj A) m →
          RingedSpace.IsPseudoCoherentFrom
            (X := (AffineSpace (ULift.{u} (Fin a)) S).toRingedSpace) A m) :
    (∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = f ∧
          IsPseudoCoherentFromAfterPushforward i E m) ↔
      (∀ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S),
        IsClosedImmersion i →
          i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = f →
            IsPseudoCoherentFromAfterPushforward i E m) :=
  isPseudoCoherentFrom_some_iff_forall_of_transport_fin f E m
    fun p _ hp A => ⟨isPseudoCoherentFrom_pushforward_mapDerivedCategory p (hO p) m A,
      reflect p hp A⟩

end AlgebraicGeometry.Scheme.Modules

end
