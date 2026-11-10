module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DevissageChow
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DevissageComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DirectImageRestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.SubschemeDevissage
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackAnyUniverse

/-!
# The inductive step of the dévissage of Stacks 088C, after replacing `X` by `V(K)`

The Noetherian induction of [Stacks, Tag 088C] is carried in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/Devissage.lean`, and its single
inductive step enters there as the hypothesis `hDev` of
`Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage`: a coherent `𝓘`-adic system
killed by a quasi-coherent ideal sheaf `K ⊆ 𝒪_X` is in the essential image of the completion
functor as soon as every coherent `𝓘`-adic system killed by an ideal sheaf **strictly larger**
than `K` is.

This file proves `hDev`, with one hypothesis: Stacks 088B at a general base.

## The order of the ideal sheaves

Read naively on `X`, the step does not close. Stacks 088A consumes its hypothesis (1) at the
*powers* `𝒦 ᵉ⁺¹` of the ideal sheaf along which the comparison of Stacks 088B is annihilated, and
powers descend, so that family lies *below* `𝒦` while the antecedent of `hDev` lives strictly
above `K`. That is the side condition `hpow : ∀ e, K < 𝒦 ᵉ⁺¹` of
`Stacks.Algebraization.essImage_completionFunctor_of_devissageComparison`, and it is
unsatisfiable for `K ≠ ⊥`.

The source does not read it on `X`. Its step begins by replacing `X` by the closed subscheme
`V(K)` and only then applies Chow's lemma, so its `𝒦` is an ideal sheaf `𝒦₀` of `V(K)` and the
ideal sheaves at which hypothesis (1) is consumed are the **inverse images in `X`** of the powers
`𝒦₀ ᵉ⁺¹` — the joins `K ⊔ 𝒦₀ ᵉ⁺¹`, which lie above `K` by construction and strictly above it
exactly when `𝒦₀ ᵉ⁺¹ ≠ ⊥`. That replacement is carried by
`StacksFrontier/AlgebraicGeometry/Scheme/SubschemeIdealJoin.lean` and
`CompletionProper/SubschemeDevissage.lean`, whose
`Stacks.Algebraization.essImage_completionFunctor_of_devissageChowSubscheme` is the inductive step
with the comparison of Stacks 088B on `V(K)`, asked at the Chow data, as its only binder; this
file supplies that binder.

## Stacks 088B at a general base

`Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isProper`
(`CompletionProper/DevissageComparison.lean`) is Stacks 088B with the binder

`halg : (completionFunctor X (baseIdealSheaf A I f)).essImage G`,

standing for the source's reduction of 088B to an affine base (the uniqueness of `α`, which makes
its construction local on the base, and the flat base change along `B ⟶ B ^∧`). In the dévissage
that binder is asked at the system being algebraized, so it is the conclusion of Stacks 088C
itself. The hypothesis `Stacks.Algebraization.IsProperDirectImageComparison` is that theorem's
statement with `halg` deleted. Over an affine base it is
`Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isAffine`.

## The rest of the step

* **The condition `hc` of Stacks 088B, from `π` being an isomorphism over the open.** Stacks 088B
  uses that the modification is an isomorphism away from `V(𝒦₀)` in the form `hc`: the adjunction
  map `𝒜 ⟶ π_*π^*𝒜` restricts to an isomorphism on the complement of the support of `𝒦₀`. Chow's
  lemma delivers `IsIso (π ∣_ U)`, and the passage between the two is
  `Stacks.Algebraization.isIso_restrictFunctor_map_pullbackPushforwardAdjunction_unit` below.
* **The comparison data at the Chow modification.** The isomorphism `β` of Stacks 088B is produced
  by the projective case Stacks 0885
  (`Stacks.Algebraization.isEquivalenceCompletionFunctorOfIsProjectiveMorphism_holds`): the
  modification is H-projective over `Spec A`, so the completion functor upstairs is an
  equivalence, and essential surjectivity applied to the termwise pullback of the system
  (Stacks 0887, `Stacks.Coherent.coherentAdicPullback`) is `β`. The coherent module `H` is the
  proper direct image `π_*𝓕`, coherent by Stacks 02O5
  (`Stacks.Algebraization.properPushforwardCoherent`).
* **The assembly.** Those two feed the binder `hComp` of
  `Stacks.Algebraization.essImage_completionFunctor_of_devissageChowSubscheme`, which is the
  inductive step; the step at every `K` is `hDev`.

## Main definitions

* `Stacks.Algebraization.IsProperDirectImageComparison` — Stacks 088B at a general base, as a
  proposition: the statement of
  `Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isProper`
  with its binder `halg` deleted.

## Main results

* `Stacks.Algebraization.isIso_restrictFunctor_map_pullbackPushforwardAdjunction_unit` — the
  adjunction map `M ⟶ π_*π^*M` restricts to an isomorphism on an open `V` of the base over which
  `π` is an isomorphism; this is the condition `hc` of Stacks 088B.
* `Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_vanishingIdealCompl` —
  the comparison of Stacks 088A at the Chow data: for a proper `g : Y ⟶ Spec A`, a proper
  `π : X'' ⟶ Y` which is H-projective over `Spec A` and an isomorphism over an open `U ⊆ Y`, every
  coherent adic system on `Y` admits a coherent module and a map into its completion whose
  levelwise kernels and cokernels are annihilated by a power of the vanishing ideal of `Y ∖ U`,
  given `IsProperDirectImageComparison`.
* `Stacks.Algebraization.essImage_completionFunctor_of_devissageStep` — the inductive step of
  Stacks 088C at a single ideal sheaf `K`, from the antecedent of `hDev` and
  `IsProperDirectImageComparison`.
* `Stacks.Algebraization.devissageStep` — `hDev` itself, given `IsProperDirectImageComparison`.
* `Stacks.Algebraization.isEquivalence_completionFunctor_of_isProperDirectImageComparison` —
  Stacks 088C for a proper morphism, with Stacks 088B at a general base as the only hypothesis.

## Implementation notes

Neither reducedness of the complement nor density of the Chow open is a hypothesis anywhere
below; see the module docstring of
`StacksFrontier/AlgebraicGeometry/Scheme/SubschemeIdealJoin.lean`.

`hc` is stated at the open `𝒦₀.support.compl` while Chow's lemma produces the open `U`, and the
two agree because the support of the vanishing ideal of a closed set is that closed set,
`AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal`, so that
`(vanishingIdeal (Y ∖ U)).support.compl = U` by `compl_compl`.

`IsNoetherian` of each scheme in sight is produced from properness over the Noetherian base:
local Noetherianity from `LocallyOfFiniteType` and quasi-compactness from the universal closedness
of the morphism, as in `CompletionProper/SubschemeDevissage.lean`.

`AlgebraicGeometry.Scheme.Modules` is a `def` for a category of sheaves of modules agreeing with
it only at default transparency, so the submodule lattice used to state annihilation is introduced
as a local instance, as in `CompletionProper/Devissage.lean` and
`CompletionProper/DevissageChow.lean`.

## References

* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions Stacks.Coherent

/-! ### The condition `hc` of Stacks 088B, from `π` being an isomorphism over the open -/

/-- **The adjunction map `M ⟶ π_*π^*M` restricts to an isomorphism on an open of the base over
which `π` is an isomorphism.** Let `π : X' ⟶ Y` be a morphism of schemes, let `V ⊆ Y` be open and
suppose `π ∣_ V : π ⁻¹ V ⟶ V` is an isomorphism. Then for every sheaf of `𝒪_Y`-modules `M` the
unit of `π^* ⊣ π_*` at `M`, restricted to `V`, is an isomorphism.

This is the condition `hc` in which Stacks 088B uses that the modification is an isomorphism away
from the closed set cut out by `𝒦`, deduced from the form Chow's lemma delivers. The unit commutes
with restriction to an open of the base,
`Stacks.AlgebraicGeometry.AffinePushforward.pullbackPushforwardAdjunction_unit_restrict`: read
through the base-change isomorphisms for the direct and inverse image, its restriction to `V` *is*
the unit of `(π ∣_ V)^* ⊣ (π ∣_ V)_*`. That unit is invertible because the direct image along an
isomorphism of schemes is an equivalence
(`AlgebraicGeometry.Scheme.Hom.pushforward_isEquivalence_of_isIso`), hence so is its left adjoint
the inverse image (`CategoryTheory.Adjunction.isEquivalence_left_of_isEquivalence_right`), and the
unit of an adjunction with fully faithful left adjoint is invertible. -/
public theorem isIso_restrictFunctor_map_pullbackPushforwardAdjunction_unit
    {X' Y : Scheme.{u}} (π : X' ⟶ Y) (V : Y.Opens) (hπV : IsIso (π ∣_ V)) (M : Y.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι V)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app M)) := by
  have := hπV
  have hpf : (Scheme.Modules.pushforward (π ∣_ V)).IsEquivalence :=
    AlgebraicGeometry.Scheme.Hom.pushforward_isEquivalence_of_isIso.{u, u} (π ∣_ V)
  have hpb := (Scheme.Modules.pullbackPushforwardAdjunction
    (π ∣_ V)).isEquivalence_left_of_isEquivalence_right
  have key :=
    Stacks.AlgebraicGeometry.AffinePushforward.pullbackPushforwardAdjunction_unit_restrict π V M
  refine @IsIso.of_isIso_comp_right _ _ _ _ _ _
    ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso π V).hom.app
      ((Scheme.Modules.pullback π).obj M)) inferInstance ?_
  rw [key]; infer_instance

/-! ### Stacks 088B at a general base, as a hypothesis -/

/-- **Stacks 088B at a general base, as a hypothesis.** Let `A` be a Noetherian ring complete with
respect to `I`. The statement asserts: for every proper `f : X ⟶ Spec A` with `X` Noetherian,
every proper `π : X' ⟶ X` with `X'` Noetherian, every quasi-coherent sheaf of ideals `𝒦 ⊆ 𝒪_X`,
every coherent `𝒪_{X'}`-module `𝓕` and every object `G` of `Coh(X, 𝓘)`, `𝓘 = I · 𝒪_X`, the
source's isomorphism

`β : π^*G ≅ 𝓕 ^∧`   in `Coh(X', 𝓘 𝒪_{X'})`

together with the condition `hc` in which the source uses that `π` is an isomorphism away from
`V(𝒦)` produce a morphism

`α : G ⟶ (π_*𝓕) ^∧`

whose levelwise kernels and cokernels are annihilated by a power of `𝒦` — the pair of hypotheses
`α` and `hα` that Stacks 088A consumes.

This is the statement of
`Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isProper`
with its binder `halg : (completionFunctor X (baseIdealSheaf A I f)).essImage G` deleted,
universally quantified over everything that theorem takes. Over an affine base it is
`Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isAffine`. -/
public def IsProperDirectImageComparison
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A] : Prop :=
  ∀ {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X]
    (f : X ⟶ Spec (.of A)) (π : X' ⟶ X) [IsProper π] [IsProper f]
    (𝒦 : X.IdealSheafData)
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
    (G : CoherentAdicSystems (baseIdealSheaf A I f)),
    ((coherentAdicPullback π (baseIdealSheaf A I f)).obj G ≅
        (completionFunctor X' ((baseIdealSheaf A I f).comap π)).obj 𝓕) →
      (∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
        (G ≅ (completionFunctor X (baseIdealSheaf A I f)).obj 𝒜) →
          IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι 𝒦.support.compl)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app 𝒜.obj))) →
        ∃ α : G.obj ⟶ ((completionFunctor X (baseIdealSheaf A I f)).obj
            (properPushforwardCoherent π 𝓕)).obj,
          IsKernelCokernelAnnihilatedByPower 𝒦 α

/-! ### The comparison of Stacks 088A at the Chow data -/

/-- **The comparison data of Stacks 088A, at a Chow modification.** Let `A` be a Noetherian ring
complete with respect to `I`, let `g : Y ⟶ Spec A` be proper, let `π : X' ⟶ Y` be proper and
H-projective over `Spec A`, and let `U ⊆ Y` be an open over which `π` is an isomorphism. Granted
Stacks 088B at a general base and nothing else, every object `(𝓖_n)` of `Coh(Y, 𝓘 𝒪_Y)` admits a
coherent `𝒪_Y`-module `H` and a morphism

`α : (𝓖_n) ⟶ H ^∧`

whose levelwise kernels and cokernels are annihilated by a power of the vanishing ideal of
`Y ∖ U` — which is the pair of hypotheses Stacks 088A consumes, at the ideal sheaf the source's
Chow step produces.

The projective case Stacks 0885
(`Stacks.Algebraization.isEquivalenceCompletionFunctorOfIsProjectiveMorphism_holds`) makes the
completion functor of `X'` along the inverse image of `𝓘` an equivalence — the ideal sheaf
being the base ideal sheaf of `π ≫ g` by
`Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap` — and essential surjectivity applied to the
termwise pullback `π^*(𝓖_n)` of Stacks 0887 (`Stacks.Coherent.coherentAdicPullback`) is the
source's `β`. The module `H` is the proper direct image `π_*𝓕`, coherent by Stacks 02O5
(`Stacks.Algebraization.properPushforwardCoherent`). The condition `hc` is
`Stacks.Algebraization.isIso_restrictFunctor_map_pullbackPushforwardAdjunction_unit`, read at the
open `U` through the identification of `U` with the complement of the support of the vanishing
ideal of `Y ∖ U`.

Neither surjectivity of `π` nor density of `U` is assumed, nor Noetherianity of `Y` and of `X'`,
which follows from properness over the Noetherian base. -/
public theorem exists_isKernelCokernelAnnihilatedByPower_vanishingIdealCompl
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (h088B : IsProperDirectImageComparison A I)
    {Y X' : Scheme.{u}} (g : Y ⟶ Spec (.of A)) [IsProper g] (π : X' ⟶ Y) [IsProper π]
    (U : Y.Opens) (hproj : AlgebraicGeometry.IsProjectiveMorphism (π ≫ g))
    (hiso : IsIso (π ∣_ U)) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
    ∀ 𝓖 : CoherentAdicSystems (baseIdealSheaf A I g),
      ∃ (H : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
        (α : 𝓖.obj ⟶ ((completionFunctor Y (baseIdealSheaf A I g)).obj H).obj),
        IsKernelCokernelAnnihilatedByPower
          (Scheme.IdealSheafData.vanishingIdeal
            (⟨(U : Set Y)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds Y)) α := by
  -- properness over the Noetherian base makes the source Noetherian
  have hNoeth : ∀ {Z : Scheme.{u}} (h : Z ⟶ Spec (.of A)) [IsProper h], IsNoetherian Z := by
    intro Z h _
    let _ := LocallyOfFiniteType.isLocallyNoetherian h
    let _ := QuasiCompact.compactSpace_of_compactSpace h
    exact { }
  have _ : IsProper (π ≫ g) := isProper_of_isProjectiveMorphism (π ≫ g) hproj
  have _ := hNoeth g
  have _ := hNoeth (π ≫ g)
  -- the complement of the support of the vanishing ideal of `Y ∖ U` is `U`
  have hsupp : (Scheme.IdealSheafData.vanishingIdeal
      (⟨(U : Set Y)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds Y)).support.compl = U := by
    have h1 : (Scheme.IdealSheafData.vanishingIdeal
          (⟨(U : Set Y)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds Y)).support =
        (⟨(U : Set Y)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds Y) :=
      TopologicalSpace.Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
    rw [h1]
    exact TopologicalSpace.Opens.ext (compl_compl _)
  have hiso' : IsIso (π ∣_ (Scheme.IdealSheafData.vanishingIdeal
      (⟨(U : Set Y)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds Y)).support.compl) := by
    rw [hsupp]; exact hiso
  -- the projective case of Grothendieck existence on the modification
  have hEq : (completionFunctor X' ((baseIdealSheaf A I g).comap π)).IsEquivalence := by
    rw [Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap A I g π]
    exact isEquivalenceCompletionFunctorOfIsProjectiveMorphism_holds A I (π ≫ g) hproj
  intro 𝓖
  -- the source's `β`: the algebraization upstairs of the termwise pullback of the system
  obtain ⟨𝓕, ⟨e⟩⟩ : (completionFunctor X' ((baseIdealSheaf A I g).comap π)).essImage
      ((coherentAdicPullback π (baseIdealSheaf A I g)).obj 𝓖) :=
    Functor.EssSurj.mem_essImage _ _
  refine ⟨properPushforwardCoherent π 𝓕, ?_⟩
  -- Stacks 088B, with `hc` supplied by the restriction of the adjunction map
  exact h088B g π _ 𝓕 𝓖 e.symm fun 𝒜 _ =>
    isIso_restrictFunctor_map_pullbackPushforwardAdjunction_unit π _ hiso' 𝒜.obj

/-! ### The inductive step of Stacks 088C -/

/-- **The inductive step of the Noetherian induction of [Stacks, Tag 088C], at a single ideal
sheaf.** Let `A` be a Noetherian ring complete with respect to `I`, let `f : X ⟶ Spec A` be proper,
set `𝓘 = I · 𝒪_X` and let `K ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals. Granted Stacks 088B at a
general base and `hInd`, the antecedent of `hDev` — every coherent `𝓘`-adic system killed by an
ideal sheaf **strictly larger** than `K` is in the essential image of the completion functor —
every coherent `𝓘`-adic system killed by `K` is in the essential image.

This is the source's step verbatim, carried out after its replacement of `X` by `V(K)`. The
replacement, Chow's lemma on `V(K)`, the transport of `hInd` through [Stacks, Tag 087T],
hypothesis (1) of [Stacks, Tag 088A] on the subschemes `V(𝒦₀ ᵉ⁺¹)` of `V(K)`, Stacks 088A itself,
the way back along the direct image and the base case `K = ⊤` are all carried by
`Stacks.Algebraization.essImage_completionFunctor_of_devissageChowSubscheme`, whose single binder
`hComp` — the comparison of Stacks 088B on `V(K)` asked at the Chow data — is supplied here by
`Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_vanishingIdealCompl`, applied to
the proper morphism `V(K) ⟶ X ⟶ Spec A` and read through
`Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap`. -/
public theorem essImage_completionFunctor_of_devissageStep
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (h088B : IsProperDirectImageComparison A I)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (K : X.IdealSheafData)
    (hInd : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ K' : X.IdealSheafData, K < K' →
        ∀ 𝓖 : CoherentAdicSystems (baseIdealSheaf A I f),
          IsSystemAnnihilatedBy K' 𝓖.obj →
            (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓖) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ 𝓕 : CoherentAdicSystems (baseIdealSheaf A I f),
      IsSystemAnnihilatedBy K 𝓕.obj →
        (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓕 := by
  refine essImage_completionFunctor_of_devissageChowSubscheme A I f K hInd ?_
  intro X' π U hπ _ hproj _ hisoU
  have _ := hπ
  rw [Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap A I f K.subschemeι]
  exact exists_isKernelCokernelAnnihilatedByPower_vanishingIdealCompl A I h088B
    (K.subschemeι ≫ f) π U hproj hisoU

/-- **`hDev`, the hypothesis of the Noetherian induction of [Stacks, Tag 088C].** Let `A` be a
Noetherian ring complete with respect to `I`, let `f : X ⟶ Spec A` be proper and set
`𝓘 = I · 𝒪_X`. Granted Stacks 088B at a general base, the inductive step holds at *every*
quasi-coherent ideal sheaf of `X`: a coherent `𝓘`-adic system killed by `K` is in the essential
image of the completion functor as soon as every coherent `𝓘`-adic system killed by an ideal sheaf
strictly larger than `K` is.

This is the binder `hDev` of
`Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage`, and it is
`Stacks.Algebraization.essImage_completionFunctor_of_devissageStep` quantified over `K`. -/
public theorem devissageStep
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (h088B : IsProperDirectImageComparison A I)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ K : X.IdealSheafData,
      (∀ K' : X.IdealSheafData, K < K' →
          ∀ 𝓖 : CoherentAdicSystems (baseIdealSheaf A I f),
            IsSystemAnnihilatedBy K' 𝓖.obj →
              (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓖) →
        ∀ 𝓕 : CoherentAdicSystems (baseIdealSheaf A I f),
          IsSystemAnnihilatedBy K 𝓕.obj →
            (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓕 :=
  fun K hInd => essImage_completionFunctor_of_devissageStep A I h088B f K hInd

/-! ### Stacks 088C with Stacks 088B at a general base as the only hypothesis -/

/-- **[Stacks, Tag 088C] for a proper morphism, with Stacks 088B at a general base as the only
hypothesis.** Let `A` be a Noetherian ring complete with respect to an ideal `I`, let
`f : X ⟶ Spec A` be proper and set `𝓘 = I · 𝒪_X`. Granted
`Stacks.Algebraization.IsProperDirectImageComparison` — Stacks 088B with its binder `halg`
removed, and nothing else — the completion functor

`Coh(𝒪_X) ⥤ Coh(X, 𝓘)`,  `F ↦ (F / 𝓘ⁿ F)`

of Stacks 0880 is an equivalence.

This is `Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage` with its binder
`hDev` discharged by `Stacks.Algebraization.devissageStep`. -/
public theorem isEquivalence_completionFunctor_of_isProperDirectImageComparison
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (h088B : IsProperDirectImageComparison A I)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (completionFunctor X (baseIdealSheaf A I f)).IsEquivalence :=
  isEquivalence_completionFunctor_of_devissage A I f
    (fun H => isIso_globalSectionsToLimit_of_isProper A I f H) (devissageStep A I h088B f)

end Stacks.Algebraization

end
