module

public import StacksFrontier.AlgebraicGeometry.Algebraization.BoundaryNoComponent
public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletionIsoOnIdealSupport
public import StacksFrontier.AlgebraicGeometry.Algebraization.StrictDepthFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesDepthThree
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthLocusGlue
public import StacksFrontier.CategoryTheory.Functor.IsoOfHomBijective

/-!
# The depth-two algebraization of a coherent adic system, and its uniqueness

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`. Let `A` be `I`-adically complete with a dualizing
complex and `cd(A, I) ≤ d` for some `d ≥ 1`, and let `(ℱ_n)` be a coherent `I𝒪_U`-adic system
satisfying the strict `(1, 1 + d)`-inequalities of [Stacks, Tag 0EJ3].

[Stacks, Tag 0EJ8] asserts that, if `(ℱ_n)` is the completion of *some* coherent
`𝒪_U`-module, then it has a *unique* algebraization of depth at least two: a unique coherent
`𝒪_U`-module `ℱ` with `ℱ^∧ ≅ (ℱ_n)` and `depth(ℱ_x) ≥ 2` at every `x ∈ U` whose closure meets
`Y` only inside `Z`. This file proves both halves. Existence improves a given algebraization
along the locus where the depth is to be raised; uniqueness says that any two such modules `𝒢`
and `ℋ`, with chosen isomorphisms `𝒢^∧ ≅ (ℱ_n)` and `ℋ^∧ ≅ (ℱ_n)`, are isomorphic by a *unique*
isomorphism `𝒢 ≅ ℋ` intertwining those two isomorphisms.

## Main results

* `Stacks.Algebraization.existsUnique_depthTwoAlgebraization` — **Stacks Tag 0EJ8**.
* `Stacks.Algebraization.exists_completionIso_depthTwoOffFormalLocus` — its existence half.
* `Stacks.Algebraization.existsUnique_completionCompatibleIso` — its uniqueness half.
* `Stacks.Algebraization.completedStalkDepth_eq_of_iso` and
  `Stacks.Algebraization.satisfiesStrictDepthInequalities_of_iso` — the inequalities of
  [Stacks, Tag 0EJ3] depend only on the isomorphism class of the adic system, which is what
  transports the hypothesis from `(ℱ_n)` to `𝒢^∧` and to `ℋ^∧`.
* `Stacks.Algebraization.notMem_depthTwoLocus_of_mem_support` — the depth-two locus misses the
  support of `I𝒪_U`, which is why improving a module along it does not change its completion.

## Implementation notes

### The shape of the existence proof

It is the source's. The depth-two locus `T = {x ∈ U : \overline{\{x\}} ∩ Y ⊆ Z}` of
`StacksFrontier/AlgebraicGeometry/Algebraization/DepthTwoLocus.lean` is stable under
specialization, and
`Stacks.Algebraization.one_le_depth_stalk_of_isImmediateSpecialization_notMem_depthTwoLocus` —
the source's second paragraph — bounds the depth of the given algebraization `𝒢` from below by
one at a point outside `T` admitting an immediate specialization inside `T`. Those are exactly
the two hypotheses of the existence half of [Stacks, Tag 0EI3], which therefore extends `𝒢` to
a coherent `ℋ` of depth at least two along `T`, by a morphism `𝒢 ⟶ ℋ` which is an isomorphism
on the stalks away from `T`.

Nothing is left to check but that the extension has not changed the completion, and the reason
is that `T` misses the support of `I𝒪_U`: completion only sees a morphism along that support,
which is
`Stacks.Algebraization.isIso_completionFunctor_map_of_isIso_stalkMap_on_support`.

### The shape of the uniqueness proof

The source says only "uniqueness will follow from the mapping property of Lemma 0EJ7". That
mapping property is
`Stacks.Algebraization.completionFunctor_map_bijective_of_satisfiesStrictDepthInequalities`,
and it is invoked four times — on `(𝒢, ℋ)`, `(ℋ, 𝒢)`, `(𝒢, 𝒢)` and `(ℋ, ℋ)` — after which the
conclusion is pure category theory:
`CategoryTheory.Functor.existsUnique_iso_of_map_bijective` lifts the isomorphism
`𝒢^∧ ≅ ℋ^∧` obtained from the two chosen isomorphisms, uniquely, through the completion
functor.

Each of those four invocations needs the strict inequalities and the depth-two condition *for
its target*, so the hypothesis on `(ℱ_n)` has to be moved to `𝒢^∧` and to `ℋ^∧` along the
chosen isomorphisms. That is `satisfiesStrictDepthInequalities_of_iso`: an isomorphism of adic
systems induces, at each point `y` of `U`, an isomorphism of the formal stalks `ℱ_y^∧`, hence a
linear equivalence of their localizations at every prime of `𝒪_{X,y}^∧`, and
`Module.depth_eq_depth_of_linearEquiv` leaves the depth unchanged.

### The depth-two condition

It is `Stacks.Algebraization.FormalSectionsII.DepthTwoOffFormalLocus`, the transcription of
condition (3) already used by [Stacks, Tag 0EJ7]: the depth of the stalk at `x` is at least `2`
whenever `closure {x} ∩ V(I) ⊆ V(𝔞)`. No separate predicate is introduced for it here.

### Hypotheses

Nothing is assumed beyond the source's conditions. For uniqueness these are conditions (1) and
(3), condition (2) — that `(ℱ_n)` be a completion — being the data of the two isomorphisms; for
existence, condition (2) is the hypothesis `halg` and the conclusion is condition (3). The input
[Stacks, Tag 0EIF] of [Stacks, Tag 0EJ5] is `Stacks.Algebraization.serreOneAlternativeComparison`.

## References

* [Stacks Project, Tag 0EJ8](https://stacks.math.columbia.edu/tag/0EJ8)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), the inequalities.
* [Stacks Project, Tag 0EJ7](https://stacks.math.columbia.edu/tag/0EJ7), the mapping property.
* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3), the depth-two extension.
* [Stacks Project, Tag 0EJ5](https://stacks.math.columbia.edu/tag/0EJ5), the depth bound.
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880), the completion functor.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-- **The depth of a localized formal stalk depends only on the isomorphism class of the adic
system.** An isomorphism of coherent adic systems is in particular an isomorphism of the
underlying inverse systems of sheaves of modules, so it induces an isomorphism of the limits of
their stalks at a point, an equivalence of the `I`-adic completions of those limits, and hence
a linear equivalence of their localizations at a prime of `𝒪_{X,x}^∧`. -/
public theorem completedStalkDepth_eq_of_iso {X : Scheme.{u}} (I : X.IdealSheafData)
    {F G : Stacks.Coherent.CoherentAdicSystems I} (e : F ≅ G) (x : X)
    (p : PrimeSpectrum (completedLocalRing I x)) :
    completedStalkDepth I F x p = completedStalkDepth I G x p := by
  let eStalk : formalStalk F x ≅ formalStalk G x :=
    lim.mapIso (Functor.isoWhiskerRight ((ObjectProperty.ι _).mapIso e) (stalkModuleFunctor x))
  let eFormal := AdicCompletion.congr (IdealSheafData.stalk I x) eStalk.toLinearEquiv
  exact Module.depth_eq_depth_of_linearEquiv _
    (LinearEquiv.ofBijective (LocalizedModule.map p.asIdeal.primeCompl eFormal.toLinearMap)
      ⟨LocalizedModule.map_injective _ _ eFormal.injective,
        LocalizedModule.map_surjective _ _ eFormal.surjective⟩)

/-- **The strict `(a, b)`-inequalities of [Stacks, Tag 0EJ3] depend only on the isomorphism
class of the adic system.** Both quantities they bound are built from the depth of the localized
formal stalk, which `Stacks.Algebraization.completedStalkDepth_eq_of_iso` leaves unchanged. -/
public theorem satisfiesStrictDepthInequalities_of_iso (S : AlgebraizationSituation.{u})
    {F G : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)} (e : F ≅ G) (a b : ℤ)
    (hF : SatisfiesStrictDepthInequalities S F a b) :
    SatisfiesStrictDepthInequalities S G a b := by
  intro y z hyz p hp
  have hdepth := completedStalkDepth_eq_of_iso (idealOnOpen S) e y p
  have hdist : depthAddDistance S F y z p = depthAddDistance S G y z p :=
    congrArg (fun t => enatToEInt t + enatToEInt (S.distanceToZ z)) hdepth
  have hdim : depthAddDimAddDistance S F y z p = depthAddDimAddDistance S G y z p :=
    congrArg (fun t => enatToEInt t +
      krullDimToEInt (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) +
      enatToEInt (S.distanceToZ z)) hdepth
  exact (hF y z hyz p hp).imp (fun h => lt_of_lt_of_eq h hdist) fun h => lt_of_lt_of_eq h hdim

/-- **The uniqueness half of [Stacks, Tag 0EJ8].** In an algebraization situation, let `(ℱ_n)` be a
coherent `I𝒪_U`-adic system and let `d ≥ 1`. Assume

1. `A` is `I`-adically complete, has a dualizing complex, and `cd(A, I) ≤ d`,
2. `(ℱ_n)` satisfies the strict `(1, 1 + d)`-inequalities of [Stacks, Tag 0EJ3].

Let `𝒢` and `ℋ` be coherent `𝒪_U`-modules with `depth(𝒢_x) ≥ 2` and `depth(ℋ_x) ≥ 2` for every
`x ∈ U` with `closure {x} ∩ Y ⊆ Z`, and let `φ : 𝒢^∧ ≅ (ℱ_n)` and `ψ : ℋ^∧ ≅ (ℱ_n)`. Then there
is a unique isomorphism `e : 𝒢 ≅ ℋ` with `e^∧ ≫ ψ = φ`.

Together with the existence half this is the uniqueness of the algebraization asserted by the
source: condition (2) of the source, that `(ℱ_n)` be the completion of a coherent module, is
witnessed by `φ` (or by `ψ`). -/
@[stacks 0EJ8 "the uniqueness half: two depth-two algebraizations are isomorphic by a unique \
isomorphism compatible with the identifications of completions"]
public theorem existsUnique_completionCompatibleIso
    (S : AlgebraizationSituation.{u}) [IsAdicComplete S.I S.A]
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (d : ℤ) (hd : 1 ≤ d)
    (K : DerivedCategory (ModuleCat.{u} S.A)) (hK : Dualizing.IsDualizingComplex K)
    (hcd : cohomologicalDimension S.A S.I S.I.fg_of_isNoetherianRing ≤ d)
    (hstrict : SatisfiesStrictDepthInequalities S F 1 (1 + d))
    (G H : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf)
    (hG : FormalSectionsII.DepthTwoOffFormalLocus S.A S.I S.a G.obj)
    (hH : FormalSectionsII.DepthTwoOffFormalLocus S.A S.I S.a H.obj)
    (φ : (completionFunctor S.U.toScheme (idealOnOpen S)).obj G ≅ F)
    (ψ : (completionFunctor S.U.toScheme (idealOnOpen S)).obj H ≅ F) :
    ∃! e : G ≅ H,
      (completionFunctor S.U.toScheme (idealOnOpen S)).map e.hom ≫ ψ.hom = φ.hom := by
  have hstrictG := satisfiesStrictDepthInequalities_of_iso S φ.symm 1 (1 + d) hstrict
  have hstrictH := satisfiesStrictDepthInequalities_of_iso S ψ.symm 1 (1 + d) hstrict
  obtain ⟨e, he, heUnique⟩ :=
    CategoryTheory.Functor.existsUnique_iso_of_map_bijective
      (completionFunctor S.U.toScheme (idealOnOpen S)) G H (φ ≪≫ ψ.symm)
      (completionFunctor_map_bijective_of_satisfiesStrictDepthInequalities
        S H d hd K hK hcd hstrictH hH G)
      (completionFunctor_map_bijective_of_satisfiesStrictDepthInequalities
        S G d hd K hK hcd hstrictG hG H)
      (completionFunctor_map_bijective_of_satisfiesStrictDepthInequalities
        S G d hd K hK hcd hstrictG hG G)
      (completionFunctor_map_bijective_of_satisfiesStrictDepthInequalities
        S H d hd K hK hcd hstrictH hH H)
  exact ⟨e, (Iso.eq_comp_inv ψ).1 he, fun e' he' => heUnique e' ((Iso.eq_comp_inv ψ).2 he')⟩

/-- The depth-two locus of the situation is the locus of condition (3): membership is the
inclusion `\overline{\{x\}} ∩ Y ⊆ Z`, with `Y` and `Z` read as the zero loci of `I` and `𝔞`. -/
public theorem mem_depthTwoLocus_of_closure_inter_subset (S : AlgebraizationSituation.{u})
    (x : S.U.toScheme)
    (hx : closure ({(x.1 : PrimeSpectrum S.A)} : Set (PrimeSpectrum S.A)) ∩
      PrimeSpectrum.zeroLocus (S.I : Set S.A) ⊆ PrimeSpectrum.zeroLocus (S.a : Set S.A)) :
    x ∈ depthTwoLocus S := by
  rw [mem_depthTwoLocus_iff, range_Yι_base, range_Zι_base]
  exact hx

/-- **A point of `U` on the adic locus is outside the depth-two locus.** The support of `I𝒪_U`
is the part of `U` lying over `V(I)`, and such a point is a point of its own closure meeting `Y`
and lying outside `Z`. -/
public theorem notMem_depthTwoLocus_of_mem_support (S : AlgebraizationSituation.{u})
    {x : S.U.toScheme} (hx : x ∈ ((idealOnOpen S).support : Set S.U.toScheme)) :
    x ∉ depthTwoLocus S := by
  have hI : S.I ≤ (S.U.ι.base x).asIdeal :=
    support_baseIdealSheaf_le S.I S.U.ι (idealOnOpen_eq_baseIdealSheaf S ▸ hx)
  have hY : S.U.ι.base x ∈ Set.range S.Yι.base := by
    rw [range_Yι_base]
    exact hI
  obtain ⟨z, hz⟩ := hY
  exact notMem_depthTwoLocus_of_mem_range_Yι S x z hz.symm

/-- **The existence half of [Stacks, Tag 0EJ8].** In an algebraization situation, let `(ℱ_n)` be a
coherent `I𝒪_U`-adic system and let `d ≥ 1`. Assume

1. `A` is `I`-adically complete, has a dualizing complex, and `cd(A, I) ≤ d`,
2. `(ℱ_n)` is the completion of some coherent `𝒪_U`-module,
3. `(ℱ_n)` satisfies the strict `(1, 1 + d)`-inequalities of [Stacks, Tag 0EJ3].

Then `(ℱ_n)` is the completion of a coherent `𝒪_U`-module `ℋ` with `depth(ℋ_x) ≥ 2` at every
`x ∈ U` whose closure meets `Y` only inside `Z`.

These are the source's three conditions: condition (2) is the hypothesis `halg`, which is the
source's "`(ℱ_n)` is the completion of a coherent module", and the depth-two conclusion is
`Stacks.Algebraization.FormalSectionsII.DepthTwoOffFormalLocus`, the transcription of the
source's condition (3) already used by [Stacks, Tag 0EJ7] and by the uniqueness half.

The proof is the source's: the depth-two locus `T = {x ∈ U : \overline{\{x\}} ∩ Y ⊆ Z}` is
stable under specialization, the depth bound
`Stacks.Algebraization.one_le_depth_stalk_of_isImmediateSpecialization_notMem_depthTwoLocus` is
the source's second paragraph, and the existence half of [Stacks, Tag 0EI3] then extends the
given algebraization `𝒢` to a coherent `ℋ` of depth at least two along `T`, by a morphism which
is an isomorphism on the stalks off `T`. Since `T` misses the support of `I𝒪_U`, that morphism
has an isomorphism for its completion
(`Stacks.Algebraization.isIso_completionFunctor_map_of_isIso_stalkMap_on_support`), so `ℋ` is
again an algebraization of `(ℱ_n)`. -/
@[stacks 0EJ8 "the existence half: a depth-two algebraization exists"]
public theorem exists_completionIso_depthTwoOffFormalLocus
    (S : AlgebraizationSituation.{u}) [IsAdicComplete S.I S.A]
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (d : ℤ) (hd : 1 ≤ d)
    (K : DerivedCategory (ModuleCat.{u} S.A)) (hK : Dualizing.IsDualizingComplex K)
    (hcd : cohomologicalDimension S.A S.I S.I.fg_of_isNoetherianRing ≤ d)
    (hstrict : SatisfiesStrictDepthInequalities S F 1 (1 + d))
    (halg : ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf,
      Nonempty ((completionFunctor S.U.toScheme (idealOnOpen S)).obj G ≅ F)) :
    ∃ H : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf,
      Nonempty ((completionFunctor S.U.toScheme (idealOnOpen S)).obj H ≅ F) ∧
        FormalSectionsII.DepthTwoOffFormalLocus S.A S.I S.a H.obj := by
  obtain ⟨G, ⟨e⟩⟩ := halg
  have _ : G.obj.IsCoherent := G.property
  have hGstrict := satisfiesStrictDepthInequalities_of_iso S e.symm 1 (1 + d) hstrict
  have hdual : LocallyHasDualizingComplex S.U.toScheme :=
    locallyHasDualizingComplex_of_locallyOfFiniteType S.U.ι K hK
  have hdepth : ∀ x z : S.U.toScheme, x ∉ depthTwoLocus S → z ∈ depthTwoLocus S →
      IsImmediateSpecialization x z →
      (1 : ℕ∞) ≤ Module.depth (S.U.toScheme.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (S.U.toScheme.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.obj.val.presheaf x) := by
    intro x z hx hz himm
    exact (depth_stalkModuleFunctor_eq_depth_valPresheafStalk G.obj x) ▸
      one_le_depth_stalk_of_isImmediateSpecialization_notMem_depthTwoLocus S G d hd K hK hcd
        hGstrict x z himm hz hx
  obtain ⟨H, φ, hH⟩ := AlgebraicGeometry.exists_isDepthTwoExtension_of_stableUnderSpecialization
    S.U.toScheme (depthTwoLocus S) (depthTwoLocus_stableUnderSpecialization S) G.obj hdual hdepth
  refine ⟨⟨H, hH.1⟩, ⟨?_⟩, fun x hx => hH.2.2 x (mem_depthTwoLocus_of_closure_inter_subset S x hx)⟩
  have hiso : IsIso ((completionFunctor S.U.toScheme (idealOnOpen S)).map
      (ObjectProperty.homMk φ :
        G ⟶ (⟨H, hH.1⟩ : AlgebraicGeometry.SheafOfModules.CoherentModules
          S.U.toScheme.ringCatSheaf))) :=
    isIso_completionFunctor_map_of_isIso_stalkMap_on_support (idealOnOpen S) _
      fun x hx => hH.2.1 x (notMem_depthTwoLocus_of_mem_support S hx)
  exact (asIso ((completionFunctor S.U.toScheme (idealOnOpen S)).map
    (ObjectProperty.homMk φ))).symm ≪≫ e

/-- **Stacks Project, Tag 0EJ8.** In an algebraization situation, let `(ℱ_n)` be a coherent
`I𝒪_U`-adic system, an object of `Coh(U, I𝒪_U)`, and let `d ≥ 1`. Assume

1. `A` is `I`-adically complete, has a dualizing complex, and `cd(A, I) ≤ d`,
2. `(ℱ_n)` is the completion of a coherent `𝒪_U`-module,
3. `(ℱ_n)` satisfies the strict `(1, 1 + d)`-inequalities of [Stacks, Tag 0EJ3].

Then there exists a unique coherent `𝒪_U`-module `ℋ` whose completion is `(ℱ_n)` such that
`depth(ℋ_x) ≥ 2` for every `x ∈ U` with `\overline{\{x\}} ∩ Y ⊆ Z`.

"Unique" is read in the only sense in which a module "whose completion is `(ℱ_n)`" can be
unique: the module comes with an isomorphism `ψ : ℋ^∧ ≅ (ℱ_n)`, and any other coherent `𝒢` of
depth at least two off the formal locus, with any `φ : 𝒢^∧ ≅ (ℱ_n)`, is isomorphic to `ℋ` by a
*unique* isomorphism `e : 𝒢 ≅ ℋ` with `e^∧ ≫ ψ = φ`.

The existence is `Stacks.Algebraization.exists_completionIso_depthTwoOffFormalLocus` (the
source's construction through [Stacks, Tag 0EI3]) and the uniqueness is
`Stacks.Algebraization.existsUnique_completionCompatibleIso` (the source's appeal to the mapping
property of [Stacks, Tag 0EJ7]). -/
@[stacks 0EJ8 "existence and uniqueness, up to unique isomorphism compatible with the \
identifications of completions, of the depth-two algebraization"]
public theorem existsUnique_depthTwoAlgebraization
    (S : AlgebraizationSituation.{u}) [IsAdicComplete S.I S.A]
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (d : ℤ) (hd : 1 ≤ d)
    (K : DerivedCategory (ModuleCat.{u} S.A)) (hK : Dualizing.IsDualizingComplex K)
    (hcd : cohomologicalDimension S.A S.I S.I.fg_of_isNoetherianRing ≤ d)
    (halg : ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf,
      Nonempty ((completionFunctor S.U.toScheme (idealOnOpen S)).obj G ≅ F))
    (hstrict : SatisfiesStrictDepthInequalities S F 1 (1 + d)) :
    ∃ (H : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf)
      (ψ : (completionFunctor S.U.toScheme (idealOnOpen S)).obj H ≅ F),
      FormalSectionsII.DepthTwoOffFormalLocus S.A S.I S.a H.obj ∧
      ∀ (G : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf),
        FormalSectionsII.DepthTwoOffFormalLocus S.A S.I S.a G.obj →
        ∀ φ : (completionFunctor S.U.toScheme (idealOnOpen S)).obj G ≅ F,
          ∃! e : G ≅ H,
            (completionFunctor S.U.toScheme (idealOnOpen S)).map e.hom ≫ ψ.hom = φ.hom := by
  obtain ⟨H, ⟨ψ⟩, hH⟩ :=
    exists_completionIso_depthTwoOffFormalLocus S F d hd K hK hcd hstrict halg
  exact ⟨H, ψ, hH, fun G hG φ =>
    existsUnique_completionCompatibleIso S F d hd K hK hcd hstrict G H hG hH φ ψ⟩

end Stacks.Algebraization

end
