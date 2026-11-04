module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedAbove
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrictPushforward
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardStrictlyPerfect
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `E` pseudo-coherent implies `Ri_*E` pseudo-coherent: the forward half of Stacks 09VA

Let `i : Z ⟶ X` be a morphism of ringed spaces whose underlying continuous map is a closed
embedding and such that `i_*𝒪_Z` is a pseudo-coherent `𝒪_X`-module. This file proves that
`Ri_*E` is `m`-pseudo-coherent whenever `E ∈ D(𝒪_Z)` is, which is one of the two implications of
Stacks 09VA.

The argument is local on `X` and splits in two, exactly as the source does.

At a point `x` outside the image of `i` the restriction of `Ri_*E` to the (open) complement of
that image is a zero object, hence pseudo-coherent; this is
`AlgebraicGeometry.RingedSpace.isZero_derivedRestrict_derivedPushforward_of_preimage_eq_bot`.

At a point `x = i(z)` the proof departs from the source. Rather than inducting on the top
nonvanishing cohomological degree of `E`, it uses the strictly perfect approximation that
`m`-pseudo-coherence of `E` already provides: there is an open `V` of `Z` containing `z`, a
strictly perfect complex `𝒫` on `Z|_V` and a map `α : 𝒫 ⟶ 𝒦|_V` which is an isomorphism on
cohomology above `m` and an epimorphism in degree `m`, for a complex `𝒦` representing `E`.
Because `i` is an embedding, `V` is the preimage of an open `U` of `X`
(`AlgebraicGeometry.RingedSpace.exists_opens_preimage_eq`), and `x ∈ U`. Applying `(i|_V)_*`
degreewise to `α` keeps both cohomological properties, `(i|_V)_*` being exact
(`CategoryTheory.isIso_homologyMap_mapHomologicalComplex` and its `Epi` companion), while
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_pushforward_isStrictlyPerfect` makes
`(i|_V)_*𝒫` an `m`-pseudo-coherent object of `D(𝒪_{X|U})`. The target of the pushed-forward map
is identified with `(Ri_*E)|_U` by the restriction square
`AlgebraicGeometry.RingedSpace.derivedRestrictPushforwardObjIso`, and
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_approximation` — Stacks 08CC part (1)
with a merely `m`-pseudo-coherent approximant — concludes.

## Main results

* `isPseudoCoherentFrom_singleFunctor_pushforwardStructureModule_restrictHom`, in the namespace
  `AlgebraicGeometry.RingedSpace`: the hypothesis of Stacks 09VA, localized to an open subspace
  of `X`.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedPushforwardOXMod`: the forward
  implication of Stacks 09VA.

## Implementation notes

The hypothesis on `i_*𝒪_Z` has to be carried to the open subspace `U`, where it becomes the
hypothesis of
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_pushforward_isStrictlyPerfect` for the
restricted morphism `i|_V`. Two steps do that: the module-level square
`AlgebraicGeometry.RingedSpace.restrictPushforwardStructureModuleIso` identifies
`(i_*𝒪_Z)|_U` with `(i|_V)_*𝒪_{Z|V}`, and
`AlgebraicGeometry.RingedSpace.derivedRestrictSingleFunctorIso` moves the restriction past
`DerivedCategory.singleFunctor`, which is needed because restriction of an object of `D(𝒪_X)`
and placing a module in degree zero are two different functors that have to be commuted.

`AlgebraicGeometry.RingedSpace.preservesFiniteColimits_pushforwardOXMod` is a theorem and not an
instance, so right exactness of `(i|_V)_*` has to be put into the local context before the two
exactness lemmas can be applied to it.

## References

* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [Stacks Project, Lemma 20.46.9 (Tag 08CC)](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Lemma 17.6.1 (Tag 01AX)](https://stacks.math.columbia.edu/tag/01AX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe d d' u

namespace AlgebraicGeometry.RingedSpace

/-! ### The forward implication -/

variable {Z X : RingedSpace.{u, u}} (i : Z ⟶ X) [HasDerivedCategory.{d} (OXMod.{u, u} X)]
  [∀ V : Opens X.carrier,
    HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict V.isOpenEmbedding))]

/-- The hypothesis of Stacks 09VA localizes: if `i_*𝒪_Z` is a pseudo-coherent `𝒪_X`-module then,
for every open `U` of `X`, the module `(i|_{i⁻¹U})_*𝒪_{Z|i⁻¹U}` placed in degree zero is
`k`-pseudo-coherent on `X|_U` for every `k`. -/
public theorem isPseudoCoherentFrom_singleFunctor_pushforwardStructureModule_restrictHom
    (hO : IsPseudoCoherent ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj
      (pushforwardStructureModule i)))
    (U : Opens X.carrier) (k : ℤ) :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor
      (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) 0).obj
        (pushforwardStructureModule (restrictHom i U))) k :=
  (((isPseudoCoherentFrom_derivedRestrictModules _ k (hO.isPseudoCoherentFrom k) U).ofIso
    (derivedRestrictSingleFunctorIso U 0 (pushforwardStructureModule i))).ofIso
    ((DerivedCategory.singleFunctor (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) 0).mapIso
      (restrictPushforwardStructureModuleIso i U)))

variable [HasDerivedCategory.{d} (OXMod.{u, u} Z)]
  [∀ V : Opens Z.carrier,
    HasDerivedCategory.{d'} (OXMod.{u, u} (Z.restrict V.isOpenEmbedding))]

/-- **The forward half of Stacks 09VA.** Let `i : Z ⟶ X` be a morphism of ringed spaces whose
underlying continuous map is a closed immersion and such that `i_*𝒪_Z` is pseudo-coherent as an
`𝒪_X`-module. If `E ∈ D(𝒪_Z)` is `m`-pseudo-coherent then so is `Ri_*E`.

Pseudo-coherence is local on `X`. Away from the image of `i` the restriction of `Ri_*E` vanishes.
Around a point `i(z)` of the image, a strictly perfect approximation `𝒫 ⟶ 𝒦|_{i⁻¹U}` of a
complex `𝒦` representing `E` is pushed forward degreewise along `i|_{i⁻¹U}`; exactness of
pushforward preserves the two cohomological conditions, `(i|_{i⁻¹U})_*𝒫` is `m`-pseudo-coherent
because its terms are direct summands of powers of `(i|_{i⁻¹U})_*𝒪` and it is bounded, and the
target is `(Ri_*E)|_U`. Stacks 08CC part (1) in the form
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_approximation` finishes. -/
@[stacks 09VA "E m-pseudo-coherent implies Ri_*E m-pseudo-coherent",
  sga "6 III 1.1.1" "necessity: E ⇒ Ri_*E"]
public theorem isPseudoCoherentFrom_derivedPushforwardOXMod
    (hi : Topology.IsClosedEmbedding i.hom.base)
    (hO : IsPseudoCoherent ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj
      (pushforwardStructureModule i)))
    (m : ℤ) (E : DerivedCategory (OXMod.{u, u} Z)) (hE : IsPseudoCoherentFrom E m) :
    IsPseudoCoherentFrom ((derivedPushforwardOXMod i hi).obj E) m := by
  refine isPseudoCoherentFrom_of_local_restrict _ m fun x => ?_
  by_cases hx : x ∈ Set.range i.hom.base
  case neg =>
    refine ⟨⟨(Set.range i.hom.base)ᶜ, hi.isClosed_range.isOpen_compl⟩, hx,
      IsPseudoCoherent.isPseudoCoherentFrom (isPseudoCoherent_of_isZero ?_) m⟩
    refine isZero_derivedRestrict_derivedPushforward_of_preimage_eq_bot i _ hi ?_ E
    ext z
    simp
  case pos =>
  obtain ⟨z, hxz⟩ := hx
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  obtain ⟨V, hzV, P, hP, α, hα, hαepi⟩ := hK z
  obtain ⟨U, hU⟩ := exists_opens_preimage_eq i hi.toIsInducing V
  subst hU
  refine ⟨U, hxz ▸ hzV, ?_⟩
  have := preservesFiniteColimits_pushforwardOXMod (restrictHom i U)
    (isClosedEmbedding_restrictHom i U hi)
  set ψ := ((pushforwardOXMod (restrictHom i U)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map α with hψ
  have eTarget : DerivedCategory.Q.obj
        (((pushforwardOXMod (restrictHom i U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (restrictComplex K ((Opens.map i.hom.base).obj U))) ≅
      (derivedRestrictModules X U).obj ((derivedPushforwardOXMod i hi).obj E) :=
    ((derivedPushforwardOXModFactors (restrictHom i U)
          (isClosedEmbedding_restrictHom i U hi)).app
        (restrictComplex K ((Opens.map i.hom.base).obj U))).symm ≪≫
      (derivedPushforwardOXMod (restrictHom i U)
          (isClosedEmbedding_restrictHom i U hi)).mapIso
        ((derivedRestrictModulesObjQIso Z ((Opens.map i.hom.base).obj U) K).symm ≪≫
          (derivedRestrictModules Z ((Opens.map i.hom.base).obj U)).mapIso e) ≪≫
      (derivedRestrictPushforwardObjIso i U hi E).symm
  refine isPseudoCoherentFrom_of_approximation m
    (isPseudoCoherentFrom_Q_pushforward_isStrictlyPerfect (restrictHom i U) m
      (isPseudoCoherentFrom_singleFunctor_pushforwardStructureModule_restrictHom i hO U) hP)
    (DerivedCategory.Q.map ψ ≫ eTarget.hom) (fun j hj => ?_) ?_
  · have : IsIso ((DerivedCategory.homologyFunctor _ j).map (DerivedCategory.Q.map ψ)) :=
      CategoryTheory.isIso_homologyFunctor_map_Q_map ψ j
        (CategoryTheory.isIso_homologyMap_mapHomologicalComplex _ α j (hα j hj))
    rw [CategoryTheory.Functor.map_comp]
    infer_instance
  · have : Epi ((DerivedCategory.homologyFunctor _ m).map (DerivedCategory.Q.map ψ)) :=
      CategoryTheory.epi_homologyFunctor_map_Q_map ψ m
        (CategoryTheory.epi_homologyMap_mapHomologicalComplex _ α m hαepi)
    rw [CategoryTheory.Functor.map_comp]
    exact epi_comp _ _

end AlgebraicGeometry.RingedSpace

end
