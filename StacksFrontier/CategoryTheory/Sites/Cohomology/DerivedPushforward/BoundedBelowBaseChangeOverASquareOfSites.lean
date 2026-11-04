module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOverASquareOfSites
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.AcyclicityForAContinuousPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.TotalAcyclicityOfTheInverseImage
import StacksCore.Tactic.StacksAttribute

/-!
# Bounded below base change for the total direct image over a square of sites

Let
```
  (Sh(C'), O_{C'}) --g'--> (Sh(C), O_C)
        |                      |
        f'                     f
        v                      v
  (Sh(D'), O_{D'}) --g-->  (Sh(D), O_D)
```
be a commutative square of ringed topoi in which the horizontal morphisms `g`, `g'` come from
functors of sites `v : D' ⥤ D`, `v' : C' ⥤ C` that are continuous as well as cocontinuous, in
which the vertical morphisms `f`, `f'` come from continuous functors `u : D ⥤ C`, `u' : D' ⥤ C'`
with `v ⋙ u = u' ⋙ v'`, and in which the structure sheaves pull back correctly:
`O_{D'} = g^{-1} O_D` and `O_{C'} = (g')^{-1} O_C`. This is the situation of Stacks 0FN7, with
its conditions (1)–(5).

The *first* conclusion of that tag is base change on the **bounded below** derived categories,

`Rf'_* ∘ (g')^* ≅ g^* ∘ Rf_*` as functors `D⁺(O_C) ⥤ D⁺(O_{D'})`,

and it holds **without** the tag's condition (6), the exactness of `g'_!`. That condition is
what the second conclusion — the same identity on the unbounded derived categories — needs, and
that conclusion, under the source's own condition (6), is
`inverseImageCompTotalDerivedPushforwardIsoOfExactLowerShriek`.

## Main definitions

* `Stacks.Cohomology.DerivedBaseChange.inverseImageCompDerivedPushforwardPlusIsoOfRingedSite`:
  **Stacks 0FN7, first conclusion.**
* `Stacks.Cohomology.DerivedBaseChange.inverseImageCompDerivedPushforwardPlusIso`: the same
  isomorphism with the four sites at independent universes, taking the acyclicity step of the
  source's proof as a hypothesis instead of proving it.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.rightAcyclic_pushforward_inverseImage_of_injective`: the
  inverse image `(g')^* I` of an injective `O_C`-module is right acyclic for `f'_*`, which is
  the acyclicity step of the source's proof.

## The shape of the argument

The source's proof of the first conclusion is: condition (5) makes `g^* = g^{-1}` and
`(g')^* = (g')^{-1}` exact; for a bounded below complex take an injective resolution
`I^\bullet`; by Stacks 0D6X the cohomology `H^p(U', (g')^{-1}I^q)` vanishes for `p > 0` and
every object `U'` of `C'`, and by Stacks 072W `R^p f'_*` is the sheafification of the presheaf
`V' ↦ H^p(u'(V'), -)`, so each `(g')^{-1}I^q` is right acyclic for `f'_*`; Leray's acyclicity
lemma, Stacks 015E, then identifies `f'_*(g')^{-1}I^\bullet` with `Rf'_*(g')^{-1}K`, and the
underived identity `f'_* ∘ (g')^* = g^* ∘ f_*` — which is Stacks 0FN4 — concludes.

That is exactly how the proof is assembled here. The acyclicity step, Stacks 0D6X together with
Stacks 072W, is `rightAcyclic_pushforward_inverseImage_of_injective`; Leray's acyclicity lemma
is consumed through `Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso`, which
produces base change on `D⁺` from the underived identity and from exactly that acyclicity, by
way of the composition isomorphism of Stacks 015M.

No K-injective complex and no lower shriek occurs: the difference between the two conclusions of
Stacks 0FN7 is precisely that on `D⁺` injective resolutions and Leray acyclicity are available,
whereas on `D(O_C)` one needs a K-injective resolution to survive `(g')^{-1}`, which is what
condition (6) buys through Stacks 08BJ.

## Implementation notes

*An isomorphism, not an equality.* As in the unbounded file, a right derived functor is
determined only up to a canonical isomorphism, so the conclusion is an isomorphism of functors.
Here the derived functors are not carried as data but are the canonical
`Functor.rightDerivedFunctorPlus`, which exists because the source categories have enough
injectives; and `g^*`, `(g')^*` enter as the functors `Functor.mapDerivedCategoryPlus` that
their exactness induces on bounded below derived categories.

*Where the universes collapse.* The acyclicity step is the one place with a universe
restriction. Stacks 0D6X is available in this library for a small site mapping to a ringed site
whose structure sheaf, module sections and `Ext`-groups all lie in the universe of its objects,
and the comparison of the `Ext`-style sheaf cohomology with derived sections (Stacks 03FD) is
available at the same universes. So in
`rightAcyclic_pushforward_inverseImage_of_injective` — and hence in the hypothesis-free form of
the base change — the site `C'` is small and `C` is the site of a ringed site `Y` at a single
universe `w`, while `D` and `D'` keep arbitrary universes. The base change isomorphism itself,
`inverseImageCompDerivedPushforwardPlusIso`, is universe polymorphic in all four sites and takes
the acyclicity as a hypothesis.

*Condition (2) of the Stacks definition of a continuous functor.* Mathlib's
`CategoryTheory.Functor.IsContinuous` is the conclusion of Sites, Lemma 00WW — restriction along
the functor preserves sheaves — and is weaker than Sites, Definition 00WV, whose clause (2)
demands in addition that the comparison `u(T ×_V V_i) ⟶ u(T) ×_{u(V)} u(V_i)` be invertible for
every covering `{V_i ⟶ V}` and every `T ⟶ V`. Stacks 0D6X genuinely uses that clause, and
carries it as `Stacks.Sites.PreservesCoveringPullbacks`; the hypothesis is therefore inherited
here for `v'`. It is not an extra assumption relative to the source, where `v'` is continuous in
the sense of Definition 00WV: the project's own formalization of that definition supplies it, by
`Stacks.Sites.preservesCoveringPullbacks_of_isContinuous`. What it is *not* derivable from is
Mathlib's weaker `IsContinuous`, which records no fibre products at all.

## References

* [Stacks Project, Tag 0FN7](https://stacks.math.columbia.edu/tag/0FN7)
* [Stacks Project, Tag 0FN4](https://stacks.math.columbia.edu/tag/0FN4)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.DerivedBaseChange

open Stacks.SheafOfModules Stacks.Cohomology.BoundedBelowComplexes

universe m r w dC dC' dD dD' w₁ t₁ w₂ t₂ w₃ t₃ w₄ t₄

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section ContinuousRowsPlus

variable {C' : Type t₁} [Category.{w₁} C'] {C : Type t₂} [Category.{w₂} C] {D' : Type t₃}
  [Category.{w₃} D'] {D : Type t₄} [Category.{w₄} D] (J' : GrothendieckTopology C')
  (J : GrothendieckTopology C) (K' : GrothendieckTopology D') (K : GrothendieckTopology D)
  (u : D ⥤ C) (u' : D' ⥤ C') (v : D' ⥤ D) (v' : C' ⥤ C) [u.IsContinuous K J]
  [u'.IsContinuous K' J'] [v.IsContinuous K' K] [v.IsCocontinuous K' K] [v'.IsContinuous J' J]
  [v'.IsCocontinuous J' J] (OC : Sheaf J RingCat.{r}) (OD : Sheaf K RingCat.{r})
  (fSharp : OD ⟶ (u.sheafPushforwardContinuous RingCat.{r} K J).obj OC)
  (f'Sharp : inverseImageRing K' K v OD ⟶
    (u'.sheafPushforwardContinuous RingCat.{r} K' J').obj (inverseImageRing J' J v' OC))
  [HasSheafify J AddCommGrpCat.{m}] [HasSheafify J' AddCommGrpCat.{m}]
  [HasSheafify K AddCommGrpCat.{m}] [HasSheafify K' AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{m}] [K'.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory.{dC} (_root_.SheafOfModules.{m} OC)]
  [HasDerivedCategory.{dC'} (_root_.SheafOfModules.{m} (inverseImageRing J' J v' OC))]
  [HasDerivedCategory.{dD} (_root_.SheafOfModules.{m} OD)]
  [HasDerivedCategory.{dD'} (_root_.SheafOfModules.{m} (inverseImageRing K' K v OD))]
  [EnoughInjectives (_root_.SheafOfModules.{m} OC)]
  [EnoughInjectives (_root_.SheafOfModules.{m} (inverseImageRing J' J v' OC))]
  [EnoughInjectives (_root_.SheafOfModules.{m} OD)]

/-- **Base change on `D⁺` over a square of sites**, the content of the first conclusion of
Stacks 0FN7 with the four sites at independent universes and the acyclicity step of the source's
proof taken as a hypothesis; for the tag itself, with that step proved, see
`inverseImageCompDerivedPushforwardPlusIsoOfRingedSite`.

For a commutative square of ringed topoi whose horizontal
functors `u : D ⥤ C`, `u' : D' ⥤ C'` are continuous — giving `f`, `f'` with `f_* = u^s`,
`f'_* = (u')^s` — whose vertical functors `v : D' ⥤ D`, `v' : C' ⥤ C` are continuous as well as
cocontinuous — giving `g`, `g'` with `g^{-1}`, `(g')^{-1}` restriction — with `v ⋙ u = u' ⋙ v'`
and with `g^{-1} O_D = O_{D'}`, `(g')^{-1} O_C = O_{C'}`, we have
`Rf'_* ∘ (g')^* ≅ g^* ∘ Rf_*` as functors `D⁺(O_C) ⥤ D⁺(O_{D'})`.

Condition (5) is built into the statement by taking the restrictions along `v` and `v'` as *the*
sheaves of rings on `D'` and `C'`, so that `g^* = g^{-1}` and `(g')^* = (g')^{-1}` are
`Stacks.SheafOfModules.inverseImage` and are exact; the commutativity of the square of ringed
topoi is `hcomm`, as in Stacks 0FN4, whose conclusion is the underived identity
`f'_* ∘ (g')^* = g^* ∘ f_*` that this proof derives from.

The source's condition (6) is *not* a hypothesis: it is what the second conclusion needs. What
is used instead is the acyclicity step of the source's own proof of this conclusion, that
`(g')^* I` be right acyclic for `f'_*` for every injective `O_C`-module `I`; it is Stacks 0D6X
together with Stacks 072W, and it is discharged — at the universes those tags are available at —
by `rightAcyclic_pushforward_inverseImage_of_injective`. -/
def inverseImageCompDerivedPushforwardPlusIso (hsq : v ⋙ u = u' ⋙ v')
    (hcomm : f'Sharp = restrictStructureMap J' J K' K u u' v v' OC OD fSharp hsq)
    (hacyclic : ∀ I : _root_.SheafOfModules.{m} OC, Injective I →
      (_root_.SheafOfModules.pushforward.{m} f'Sharp).rightAcyclic
        ((inverseImage.{m} J' J v' OC).obj I)) :
    (inverseImage.{m} J' J v' OC).mapDerivedCategoryPlus ⋙
        (_root_.SheafOfModules.pushforward.{m} f'Sharp).rightDerivedFunctorPlus ≅
      (_root_.SheafOfModules.pushforward.{m} fSharp).rightDerivedFunctorPlus ⋙
        (inverseImage.{m} K' K v OD).mapDerivedCategoryPlus :=
  derivedBaseChangePlusIso (inverseImage.{m} J' J v' OC) (inverseImage.{m} K' K v OD)
    (_root_.SheafOfModules.pushforward.{m} fSharp)
    (_root_.SheafOfModules.pushforward.{m} f'Sharp)
    (eqToIso (inverseImage_comp_pushforward_eq.{m} J' J K' K u u' v v' OC OD fSharp f'Sharp hsq
      hcomm))
    hacyclic

end ContinuousRowsPlus

section InverseImageAcyclicity

variable {C' : Type w} [SmallCategory C'] (J' : GrothendieckTopology C')
  (Y : AlgebraicGeometry.RingedSite.{w, w, w}) (v' : C' ⥤ Y.C)
  [v'.IsContinuous J' Y.J] [v'.IsCocontinuous J' Y.J]
  [Stacks.Sites.PreservesCoveringPullbacks J' v']
  [HasExt.{w} (Sheaf J' AddCommGrpCat.{w})]

omit [v'.IsCocontinuous J' Y.J] in
/-- **Stacks 0D6X for the inverse image of an injective module**, in the form of the vanishing
of the `Ext`-style sheaf cohomology of the underlying abelian sheaf: `H^p(U', (g')^{-1}I) = 0`
for `p > 0` and every object `U'` of `C'`.

The covering system of `Stacks.CechSite.injective_module_sheafCohomology_isZero_of_functor` is
the cofinal one furnished by `Stacks.Sites.PreservesCoveringPullbacks`; the iterated fibre
products of the image coverings exist and the comparison maps to them are invertible because
`Over.post v'` preserves the iterated fibre products of those coverings. -/
theorem isZero_H'_inverseImage_of_injective
    (I : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) [Injective I]
    (U : C') (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H'.{w, w, w}
      ((v'.sheafPushforwardContinuous AddCommGrpCat.{w} J' Y.J).obj
        ((_root_.SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj I))
      p U) := by
  let P (V : C') : Set { E : PreZeroHypercover.{w} V // E.sieve₀ ∈ J' V } :=
    { E | (∀ (j : E.1.I₀) ⦃W : C'⦄ (g : W ⟶ V), HasPullback (E.1.f j) g) ∧
      (∀ (j : E.1.I₀) ⦃W : C'⦄ (g : W ⟶ V), PreservesLimit (cospan (E.1.f j) g) v') }
  have hProducts : ∀ {V : C'} (E : { E : PreZeroHypercover.{w} V // E.sieve₀ ∈ J' V }),
      E ∈ P V → ∀ (q : ℕ) (i : Fin (q + 1) → E.1.I₀),
        HasProduct (fun a ↦ Over.mk (E.1.f (i a))) :=
    fun E hE q i ↦ Stacks.Sites.hasProduct_fibreProducts E.1 hE.1 q i
  have hPres : ∀ {V : C'} (E : { E : PreZeroHypercover.{w} V // E.sieve₀ ∈ J' V }),
      E ∈ P V → ∀ (q : ℕ) (i : Fin (q + 1) → E.1.I₀),
        PreservesLimit (Discrete.functor (fun a ↦ Over.mk (E.1.f (i a)))) (Over.post v') :=
    fun E hE q i ↦ Stacks.Sites.preservesLimit_fibreProducts_overPost v' E.1 hE.1 hE.2 q i
  have hImage : ∀ {V : C'} (E : { E : PreZeroHypercover.{w} V // E.sieve₀ ∈ J' V }),
      E ∈ P V → ∀ (q : ℕ) (i : Fin (q + 1) → (E.1.map v').I₀),
        HasProduct (fun a ↦ Over.mk ((E.1.map v').f (i a))) := by
    intro V E hE q i
    have := hProducts E hE q i
    have := hPres E hE q i
    exact HasLimit.mk ⟨_, isLimitOfHasProductOfPreservesLimit (Over.post (X := V) v')
      (fun a ↦ Over.mk (E.1.f (i a)))⟩
  refine Stacks.CechSite.injective_module_sheafCohomology_isZero_of_functor.{w, w, w, w, w, w}
    Y J' v' Set.univ P hProducts hImage (fun E hE ↦ ⟨Set.mem_univ _, fun i ↦ Set.mem_univ _,
      fun q i ↦ Set.mem_univ _⟩) ?_ ?_ I U (Set.mem_univ U) p hp
  · intro V _ S hS
    obtain ⟨E, hJ, hle, hpb, hpr⟩ := Stacks.Sites.exists_preZeroHypercover_le J' v' S hS
    exact ⟨⟨E, hJ⟩, ⟨hpb, hpr⟩, hle⟩
  · intro V E hE q i
    have := hProducts E hE
    have := hImage E hE
    have := hPres E hE q i
    exact Stacks.CechSite.isIso_cechProductMapOfFunctor v' E.1 q i

variable {D' : Type t₃} [Category.{w₃} D'] (K' : GrothendieckTopology D')
  (u' : D' ⥤ C') [u'.IsContinuous K' J'] (OD' : Sheaf K' RingCat.{w})
  (f'Sharp : OD' ⟶ (u'.sheafPushforwardContinuous RingCat.{w} K' J').obj
    (inverseImageRing J' Y.J v' (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  [HasSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify K' AddCommGrpCat.{w}] [K'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasInjectiveResolutions (Sheaf J' AddCommGrpCat.{w})]
  [EnoughInjectives (_root_.SheafOfModules.{w}
    (inverseImageRing J' Y.J v' (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))]
  [HasDerivedCategory.{dC'}
    (_root_.SheafOfModules.{w}
      (inverseImageRing J' Y.J v' (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))]
  [HasDerivedCategory.{dD'} (_root_.SheafOfModules.{w} OD')]

/-- **The acyclicity step of the source's proof of the first conclusion of Stacks 0FN7.** The
inverse image `(g')^* I` of an injective `O_C`-module `I` is right acyclic for `f'_* = (u')^s`.

By Stacks 0D6X the cohomology `H^p(U', (g')^{-1}I)` vanishes for `p > 0` and every object `U'`
of `C'`, in particular over the objects `u'(V')`; and by Stacks 072W the higher direct image
`R^p f'_*` is the sheafification of the presheaf `V' ↦ H^p(u'(V'), -)`, so it vanishes too. -/
theorem rightAcyclic_pushforward_inverseImage_of_injective
    (I : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) [Injective I] :
    (_root_.SheafOfModules.pushforward.{w} f'Sharp).rightAcyclic
      ((inverseImage.{w} J' Y.J v' (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj I) :=
  ContinuousPushforward.rightAcyclic_pushforward_of_isZero u'
    (inverseImageRing J' Y.J v' (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) OD' f'Sharp _
    fun V n hn ↦
      ContinuousPushforward.isZero_rightDerived_evaluation_of_isZero_H' J'
        (inverseImageRing J' Y.J v' (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (u'.obj V) n _
        (isZero_H'_inverseImage_of_injective J' Y v' I (u'.obj V) n hn)

end InverseImageAcyclicity

section SmallSiteRowsPlus

variable {C' : Type w} [SmallCategory C'] {D' : Type t₃} [Category.{w₃} D'] {D : Type t₄}
  [Category.{w₄} D] (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
  (K : GrothendieckTopology D) (Y : AlgebraicGeometry.RingedSite.{w, w, w})
  (u : D ⥤ Y.C) (u' : D' ⥤ C') (v : D' ⥤ D) (v' : C' ⥤ Y.C) [u.IsContinuous K Y.J]
  [u'.IsContinuous K' J'] [v.IsContinuous K' K] [v.IsCocontinuous K' K]
  [v'.IsContinuous J' Y.J] [v'.IsCocontinuous J' Y.J]
  [Stacks.Sites.PreservesCoveringPullbacks J' v'] (OD : Sheaf K RingCat.{w})
  (fSharp : OD ⟶ (u.sheafPushforwardContinuous RingCat.{w} K Y.J).obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (f'Sharp : inverseImageRing K' K v OD ⟶
    (u'.sheafPushforwardContinuous RingCat.{w} K' J').obj
      (inverseImageRing J' Y.J v' (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  [HasSheafify Y.J AddCommGrpCat.{w}] [HasSheafify J' AddCommGrpCat.{w}]
  [HasSheafify K AddCommGrpCat.{w}] [HasSheafify K' AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [K'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasExt.{w} (Sheaf J' AddCommGrpCat.{w})]
  [HasInjectiveResolutions (Sheaf J' AddCommGrpCat.{w})]
  [HasDerivedCategory.{dC} (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{dC'}
    (_root_.SheafOfModules.{w}
      (inverseImageRing J' Y.J v' (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))]
  [HasDerivedCategory.{dD} (_root_.SheafOfModules.{w} OD)]
  [HasDerivedCategory.{dD'} (_root_.SheafOfModules.{w} (inverseImageRing K' K v OD))]
  [EnoughInjectives (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [EnoughInjectives (_root_.SheafOfModules.{w}
    (inverseImageRing J' Y.J v' (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))]
  [EnoughInjectives (_root_.SheafOfModules.{w} OD)]

/-- **Stacks 0FN7, first conclusion, with the acyclicity step discharged.** The same statement
as `inverseImageCompDerivedPushforwardPlusIso`, in the universes at which Stacks 0D6X and
Stacks 072W are available: `C'` is a small site and `C` is the site of a ringed site `Y` whose
structure sheaf, module sections and `Ext`-groups lie in the universe of its objects, while `D`
and `D'` keep arbitrary universes.

The source's condition (6) is not a hypothesis, and neither is the acyclicity it would be used
for: it is proved here from Stacks 0D6X and Stacks 072W by
`rightAcyclic_pushforward_inverseImage_of_injective`. -/
@[stacks 0FN7 "first conclusion: `Rf'_* ∘ (g')^* ≅ g^* ∘ Rf_*` on the *bounded below* derived
  categories `D⁺(O_C) → D⁺(O_{D'})`, for a commutative square of ringed topoi whose horizontal
  functors `u`, `u'` are continuous and whose vertical functors `v`, `v'` are continuous as well
  as cocontinuous, with `v ⋙ u = u' ⋙ v'`, `g^{-1} O_D = O_{D'}` and `(g')^{-1} O_C = O_{C'}`,
  and WITHOUT the tag's condition (6), exactness of `g'_!` — which is what the second
  conclusion, on the unbounded derived categories, needs; that conclusion, under the source's
  own condition (6), is
`Stacks.Cohomology.DerivedBaseChange.inverseImageCompTotalDerivedPushforwardIsoOfExactLowerShriek`.
  Proved as in the source, through the vanishing of Stacks 0D6X, the sheafified cohomology
  presheaf of Stacks 072W, and Leray's acyclicity lemma Stacks 015E. An isomorphism rather than an
  equality, a right derived functor being determined only up to a canonical isomorphism. The sites
  `C` and `C'` are at the single universe at which Stacks 0D6X and the Ext-to-derived-sections
  comparison of Stacks 03FD are available in this library — `C'` small and `C` the site of a ringed
  site — and `v'` is continuous in the sense of Sites, Definition 00WV, which is the hypothesis
  Stacks 0D6X uses and which Mathlib's `IsContinuous` does not supply; that is not an extra
  assumption relative to the source, where `v'` is continuous in exactly that sense, and
  `Stacks.Sites.preservesCoveringPullbacks_of_isContinuous` derives it from the project's
  formalization of Definition 00WV."]
def inverseImageCompDerivedPushforwardPlusIsoOfRingedSite (hsq : v ⋙ u = u' ⋙ v')
    (hcomm : f'Sharp =
      restrictStructureMap J' Y.J K' K u u' v v' (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) OD
        fSharp hsq) :
    (inverseImage.{w} J' Y.J v'
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).mapDerivedCategoryPlus ⋙
        (_root_.SheafOfModules.pushforward.{w} f'Sharp).rightDerivedFunctorPlus ≅
      (_root_.SheafOfModules.pushforward.{w} fSharp).rightDerivedFunctorPlus ⋙
        (inverseImage.{w} K' K v OD).mapDerivedCategoryPlus :=
  inverseImageCompDerivedPushforwardPlusIso J' Y.J K' K u u' v v'
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) OD fSharp f'Sharp
    hsq hcomm fun I hI ↦
      haveI := hI
      rightAcyclic_pushforward_inverseImage_of_injective J' Y v' K' u'
        (inverseImageRing K' K v OD) f'Sharp I

end SmallSiteRowsPlus

end Stacks.Cohomology.DerivedBaseChange

end
