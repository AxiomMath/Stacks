module

public import Mathlib.Logic.Equiv.Fin.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Basic
public import StacksFrontier.AlgebraicGeometry.TensorSectionNonvanishing.Basic

/-!
# Steps 6 and 7 of Stacks Tag 01VS on the source's own route: the product family

[Stacks, Tag 01VS] passes from one degree to all sufficiently high degrees by multiplying two
families of global sections. The source's own words: *"denote `s_0, …, s_k` the collection of
sections `s'_α s''_β` … These generate `L ^⊗ d` over `X` and therefore define a morphism
`i : X ⟶ ℙ^{k-1}_S` such that `i ^* 𝒪(1) ≅ L ^⊗ d`. To see that `i` is an immersion, observe that
`i` is the composition `X ⟶ ℙᵐ_S ×_S ℙ^{t-1}_S ⟶ ℙ^{k-1}_S` where the first morphism is `(j, j')`
… and the second morphism is the Segre embedding."*

So the source **never identifies `𝒪(1)` along the Segre embedding.** The twist comes from
[Stacks, Tag 01NE] applied to the product family, and the Segre embedding is invoked only for the
immersion property. This file takes that route.

## What this changes, compared with the route through the Segre twist

`StacksFrontier/AlgebraicGeometry/ChartImmersionAssembly/SegrePassage.lean` and
`StacksFrontier/AlgebraicGeometry/ExternalTensorPullback/Basic.lean` build the other route: carry
the twist *along* the Segre embedding, which needs the added clause
`Stacks.ChartImmersionAssembly.SegreTwist` and then the pullback of an external tensor product
(proved there from [Stacks, Tag 01CD]). Two points are recorded there as the residue of
`Stacks.AmpleImmersionReduction.TwistPassage`, and on this route **both disappear**:

1. **The two tensor products of sheaves of modules on a scheme are not identified.**
   `Stacks.Ample.tensorPowModule` and `Stacks.AmpleEventualGeneration.tensorPowAdd` live over
   `Stacks.SheafInternalHom.schemeMonoidalCategory` while
   `AlgebraicGeometry.externalTensorProduct` lives over
     `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`. Here the
   twist never leaves the monoidal vocabulary: it is produced by
   `Stacks.AmpleImmersionReduction.TwistPullback` at the product family, whose target is
   `Stacks.Ample.tensorPowModule X L c`. Neither
     `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` nor
   `AlgebraicGeometry.externalTensorProduct` occurs in this file, and [Stacks, Tag 01CD] is not
   used.
2. **No bridge between the two generation predicates is needed.**
   `TwistPassage` hypothesises `Stacks.AmpleEventualGeneration.IsFinGen`, while every morphism to
   projective space in this repository is built from
   `Stacks.ProjectiveFromSections.GeneratesStalks`. On this route the second family enters as a
   `GeneratesStalks` family throughout — `EventuallyGeneratesStalksPowers` below. The comparison
   of the two predicates is `Stacks.StalkwiseGeneration.exists_generatesStalks_of_isFinGen`.
   One positive degree of it is proved outright
   (`exists_pos_generatesStalks_tensorPowModule`, from
   `Stacks.AmpleImmersionReduction.exists_generating_family_of_isAmple`), which is the stalkwise
   twin of `Stacks.FinGenFromCover.exists_pos_isFinGen_tensorPowModule`.

**What it costs, and the cost is one statement.** The source's `i` has to be identified with
`(j, j') ≫ σ` for the immersion property. [Stacks, Tag 01WD] is stated in this repository as an
existential over `σ` with no clause about its coordinates
(`Stacks.AlgebraicGeometry.SegreProdIso.exists_segreEmbedding`), so the identification cannot be
made against that statement as it stands. **The coordinate data is nevertheless present one level
down**, and this is worth saying precisely rather than recording an absence: the Segre morphism is
built from `Stacks.RingTheory.SegreProduct.presentationAlgHom`
(`StacksFrontier/AlgebraicGeometry/SegreEmbedding/SegrePresentation.lean:219`), whose generator is
`Stacks.RingTheory.SegreProduct.gen R X Y p = X_{inl p.1} * X_{inr p.2}` (`:93`) — exactly
`T_{αβ} ↦ T_α S_β`. So what is owed is the passage from that construction to a *named* Segre
morphism over `S` with its chart ring maps in hand, together with the comparison of the
product-family chart morphisms with `(j, j')`. That single obligation is isolated as
`Stacks.ProductFamilyTwist.ProductFamilyImmersion` and nothing else on this route is open.

**And it costs a change of bookkeeping.** `Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver`
is existential in the morphism and remembers no family, while the source's induction multiplies
*families*; so the induction is carried here on `FamilyImmersionTwist`, which keeps the family.
That is not an extra hypothesis: it is exactly the conclusion
`Stacks.AmpleImmersionReduction.ChartImmersion` already produces, as
`exists_familyImmersionTwist_of_chartImmersion` records in three lines.

## Main definitions

* `Stacks.ProductFamilyTwist.prodSection`, `prodFamily`, `prodPowFamily`: the products
  `s'_α s''_β` of the source's step 6, indexed by the homogeneous coordinates of
  `ℙ^{nm + n + m}` — which is the target of the Segre embedding of `ℙⁿ × ℙᵐ`, so the index count
  `(n + 1)(m + 1)` is the source's `k`.
* `Stacks.ProductFamilyTwist.FamilyImmersionTwist`: the conclusion of Tag 01VS at one degree,
  carrying its generating family.
* `Stacks.ProductFamilyTwist.ProductFamilyImmersion`: **the one statement this route still owes**,
  the source's Segre factorization, as a statement about morphisms only.
* `Stacks.ProductFamilyTwist.EventuallyGeneratesStalksPowers`: step 5 of the source, in the
  generation predicate Tag 01NE's morphism consumes.

## Main results

* `Stacks.ProductFamilyTwist.generatesStalks_prodFamily` and `generatesStalks_prodPowFamily`:
  **the generation claim of step 6**, from the Tag 01CY remark `X_{e ⊗ f} = X_e ∩ X_f`
  (`Stacks.TensorSectionNonvanishing.nonvanishingOpen_unitMul`) and the equivalence of
  stalkwise generation with the nonvanishing cover
  (`Stacks.AmpleImmersionReduction.generatesStalks_iff_forall_exists_mem`). Unconditional.
* `Stacks.ProductFamilyTwist.exists_hom_twist_prodPowFamily`: **the twist half of steps 6 and 7,
  from `Stacks.AmpleImmersionReduction.TwistPullback` alone** — no Segre embedding, no external
  tensor product, no [Stacks, Tag 01CD].
* `Stacks.ProductFamilyTwist.familyImmersionTwist_add`: the step of the source's induction, from
  `ProductFamilyImmersion`.
* `Stacks.ProductFamilyTwist.hasImmersionTwistOver_multiples_of_isAmple`: **Tag 01VS in every
  degree `N + d k` from three inputs**, the eventual generation not being used.
* `Stacks.ProductFamilyTwist.immersionTwistGap_of_productFamilyImmersion` and
  `exists_immersion_projectiveSpaceOver_of_isAmple`: **Tag 01VS from four named inputs**, with
  `Stacks.AmpleImmersionReduction.TwistPassage` replaced by `ProductFamilyImmersion` and
  `Stacks.AmpleEventualGeneration.IsEventuallyFinGenPowers` by
  `EventuallyGeneratesStalksPowers`.

## Implementation notes

**Why the index type is `Fin (n * m + n + m + 1)`.** The morphism builder
`Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks` consumes a
family indexed by `Fin (n + 1)` and returns a morphism to `ℙⁿ_S`, so the product family has to be
reindexed off `Fin (n + 1) × Fin (m + 1)`. `Mathlib.Logic.Equiv.Fin.Basic`'s `finProdFinEquiv`
does it after one `finCongr` on `(n + 1) * (m + 1) = n * m + n + m + 1`, and the resulting
dimension agrees with the Segre target of [Stacks, Tag 01WD] as the repository states it.

**`prodPowFamily` is written as a `Function.comp`, not as a lambda.** Stated as
`fun k => e.hom.app ⊤ (prodFamily s t (segreIndexEquiv n m k))` the generation proof is a
`isDefEq` timeout: the reindexing lemma concludes about `s ∘ e` and matching that against the
lambda forces the whole chain of monoidal localization instances through unification. Writing the
definition in the shape the lemma concludes in makes the proof three lines of `exact`.

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)

## What is not done

**No Stacks attribute is attached, and in particular not Tag 01VS.** The tag has a single,
unlabelled assertion, and
`exists_immersion_projectiveSpaceOver_of_isAmple` below carries four hypotheses the tag does not.
The faithfulness `example` at the end of the file makes the comparison explicit: the binders of the
tagged statement in its own order, the four named inputs last.

**`ProductFamilyImmersion` is not proved.** It is the source's Segre sentence, and against Tag
01WD as this repository states it — an existential with no coordinate clause — it cannot be
discharged. What is needed is a Segre embedding over `S` whose coordinates are named, together
with the identification of the product-family morphism with `(j, j') ≫ σ`; the coordinate half of
that is constructed in `F3/SegreEmbedding/`, as the module docstring records, and the
identification is not stated anywhere.
**`Stacks.ChartImmersionAssembly.SegreTwist` is not what it needs** — that is the twist along
Segre, which this route does not use.

**`EventuallyGeneratesStalksPowers` and
`Stacks.AmpleEventualGeneration.IsEventuallyFinGenPowers` are the same mathematics** — a finite
family of global sections generating every stalk, versus an epimorphism out of a finite free
module. Neither is derived from the other *in this file*: what is claimed here is only that this
route consumes the predicate the library's morphism builder produces, while
`Stacks.AmpleImmersionReduction.TwistPassage` consumes the other. The comparison is
`Stacks.StalkwiseGeneration.exists_generatesStalks_of_isFinGen`, and with it
`Stacks.StalkwiseGeneration.eventuallyGeneratesStalksPowers_of_isAmple` makes
`EventuallyGeneratesStalksPowers` a theorem for an ample `L`.
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections Stacks.AmpleProjectiveImmersion
open Stacks.SectionProduct Stacks.TensorSectionNonvanishing Stacks.SectionsToProjectiveSpace

universe u

namespace Stacks.ProductFamilyTwist

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X : Scheme.{u}}

/-- A global section read as a morphism out of the monoidal unit. -/
def unitOfSection (F : X.Modules) (s : Γ(F, ⊤)) : 𝟙_ X.Modules ⟶ F :=
  (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X F).symm s

/-- The global section determined by the morphism `unitOfSection F s` is `s`. -/
@[simp] theorem globalSection_unitOfSection (F : X.Modules) (s : Γ(F, ⊤)) :
    globalSection X F (unitOfSection F s) = s :=
  (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X F).apply_symm_apply s

/-- The product of two global sections. -/
def prodSection {F G : X.Modules} (s : Γ(F, ⊤)) (t : Γ(G, ⊤)) : Γ(F ⊗ G, ⊤) :=
  globalSection X (F ⊗ G) (unitMul (unitOfSection F s) (unitOfSection G t))

/-- For invertible `F` and `G`, the nonvanishing open of the product section `prodSection s t`
is the intersection of the nonvanishing opens of `s` and `t`. -/
theorem nvOpen_prodSection {F G : X.Modules} [IsInvertibleModule X F] [IsInvertibleModule X G]
    (s : Γ(F, ⊤)) (t : Γ(G, ⊤)) :
    nvOpen (F ⊗ G) (prodSection s t) = nvOpen F s ⊓ nvOpen G t := by
  have h := nonvanishingOpen_unitMul (unitOfSection F s) (unitOfSection G t)
  simpa [prodSection, nvOpen] using h


/-! ### The product family -/

/-- **The product family.** From families of global sections of `F` and of `G`, the family of
pairwise products, a family of global sections of `F ⊗ G`. -/
def prodFamily {F G : X.Modules} {ι κ : Type*} (s : ι → Γ(F, ⊤)) (t : κ → Γ(G, ⊤)) :
    ι × κ → Γ(F ⊗ G, ⊤) := fun p => prodSection (s p.1) (t p.2)

/-- For invertible `F` and `G`, if the families `s` and `t` generate the stalks, then so does
their product family `prodFamily s t`. -/
theorem generatesStalks_prodFamily {F G : X.Modules} [IsInvertibleModule X F]
    [IsInvertibleModule X G] {ι κ : Type*} {s : ι → Γ(F, ⊤)} {t : κ → Γ(G, ⊤)}
    (hs : GeneratesStalks s) (ht : GeneratesStalks t) : GeneratesStalks (prodFamily s t) := by
  refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
  obtain ⟨i, hi⟩ := exists_mem_nvCover_of_generatesStalks s hs x
  obtain ⟨j, hj⟩ := exists_mem_nvCover_of_generatesStalks t ht x
  refine ⟨(i, j), ?_⟩
  have : nvCover (prodFamily s t) (i, j) = nvCover s i ⊓ nvCover t j :=
    nvOpen_prodSection (s i) (t j)
  rw [this]
  exact ⟨hi, hj⟩

/-- The image of a stalk-generating family of global sections of `M` under an isomorphism
`e : M ≅ N` is a stalk-generating family of global sections of `N`. -/
theorem generatesStalks_congr {M N : X.Modules} [IsInvertibleModule X M] [IsInvertibleModule X N]
    {ι : Type*} (e : M ≅ N) {s : ι → Γ(M, ⊤)} (hs : GeneratesStalks s) :
    GeneratesStalks (fun i => e.hom.app ⊤ (s i)) := by
  refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
  obtain ⟨i, hi⟩ := exists_mem_nvCover_of_generatesStalks s hs x
  refine ⟨i, ?_⟩
  change x ∈ nonvanishingLocus N (e.hom.app ⊤ (s i))
  rw [nonvanishingLocus_congr e (s i)]
  exact hi

/-- Reindexing a stalk-generating family along a bijection `e : κ ≃ ι` gives a
stalk-generating family. -/
theorem generatesStalks_comp_equiv {M : X.Modules} [IsInvertibleModule X M] {ι κ : Type*}
    (e : κ ≃ ι) {s : ι → Γ(M, ⊤)} (hs : GeneratesStalks s) : GeneratesStalks (s ∘ e) := by
  refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
  obtain ⟨i, hi⟩ := exists_mem_nvCover_of_generatesStalks s hs x
  exact ⟨e.symm i, by simpa [nvCover, Function.comp_apply] using hi⟩

/-! ### The product family at two tensor powers -/

/-- The index bijection of the source's step 6: the pairs `(α, β)` with
`α : Fin (n + 1)`, `β : Fin (m + 1)` are the homogeneous coordinates of
`ℙ^{nm + n + m}`, which is the target of the Segre embedding of `ℙⁿ × ℙᵐ`. -/
def segreIndexEquiv (n m : ℕ) : Fin (n * m + n + m + 1) ≃ Fin (n + 1) × Fin (m + 1) :=
  (finCongr (by ring)).trans (finProdFinEquiv (m := n + 1) (n := m + 1)).symm

/-- **The family of products `s'_α s''_β` of the source's step 6**, as a family of global
sections of `L ^⊗ c` indexed by the homogeneous coordinates of `ℙ^{nm + n + m}`. -/
def prodPowFamily (L : X.Modules) [IsInvertibleModule X L] {a b c : ℤ} (hc : a + b = c)
    {n m : ℕ} (s : Fin (n + 1) → Γ(tensorPowModule X L a, ⊤))
    (t : Fin (m + 1) → Γ(tensorPowModule X L b, ⊤)) :
    Fin (n * m + n + m + 1) → Γ(tensorPowModule X L c, ⊤) :=
  (fun p => (Stacks.AmpleEventualGeneration.tensorPowAdd hc).hom.app ⊤ (prodFamily s t p)) ∘
    segreIndexEquiv n m

/-- **The products of two generating families generate the product power.** This is the
generation claim of step 6 of the proof of [Stacks, Tag 01VS]. -/
theorem generatesStalks_prodPowFamily (L : X.Modules) [IsInvertibleModule X L] {a b c : ℤ}
    (hc : a + b = c) {n m : ℕ} {s : Fin (n + 1) → Γ(tensorPowModule X L a, ⊤)}
    {t : Fin (m + 1) → Γ(tensorPowModule X L b, ⊤)} (hs : GeneratesStalks s)
    (ht : GeneratesStalks t) : GeneratesStalks (prodPowFamily L hc s t) :=
  generatesStalks_comp_equiv (segreIndexEquiv n m)
    (generatesStalks_congr (Stacks.AmpleEventualGeneration.tensorPowAdd hc)
      (generatesStalks_prodFamily hs ht))

/-! ### The twist of the product-family morphism, from Tag 01NE alone -/

section Twist

variable {S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L]

/-- **The twist half of steps 6 and 7 of the proof of [Stacks, Tag 01VS], on the source's own
route.** The product family generates `L ^⊗ c`, so Tag 01NE's morphism is defined on it, and the
twist identification is then the twist half of Tag 01NE at that family. -/
theorem exists_hom_twist_prodPowFamily
    (htw : Stacks.AmpleImmersionReduction.TwistPullback f) {a b c : ℤ} (hc : a + b = c) {n m : ℕ}
    {s : Fin (n + 1) → Γ(tensorPowModule X L a, ⊤)}
    {t : Fin (m + 1) → Γ(tensorPowModule X L b, ⊤)} (hs : GeneratesStalks s)
    (ht : GeneratesStalks t) :
    ∃ p : X ⟶ projectiveSpaceOver (n * m + n + m) S,
      p ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} (n * m + n + m))) = f ∧
      (∀ i, (nvCover (prodPowFamily L hc s t) i).ι ≫ p ≫
          projectiveSpaceOver.toIntegralAtUniverse (n * m + n + m) S =
        toProjectiveSpaceAtUniverse (chartRatio (prodPowFamily L hc s t) i)
          (span_range_chartRatio (prodPowFamily L hc s t) i)) ∧
      Nonempty (tensorPowModule X L c ≅ (Scheme.Modules.pullback p).obj
        (projectiveSpaceTwistingSheaf (n * m + n + m) S)) := by
  have hgen := generatesStalks_prodPowFamily L hc hs ht
  obtain ⟨p, hpf, hchart⟩ :=
    Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks
      (prodPowFamily L hc s t) hgen f
  exact ⟨p, hpf, hchart, htw _ _ _ hgen p hpf hchart⟩

end Twist

/-! ### The family-carrying form of the conclusion, and the one input the route still owes -/

section Passage

variable {S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L]

/-- **The conclusion of Tag 01VS at one degree, carrying its generating family.** There is a
family of global sections of `L ^⊗ d` generating every stalk whose pinned morphism to projective
space over `S` is an immersion.

This is exactly the conclusion of `Stacks.AmpleImmersionReduction.ChartImmersion` at the degree it
produces, and it differs from `Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver` in keeping
the family: the source's induction multiplies families, so the family is what has to be carried. -/
def FamilyImmersionTwist (d : ℤ) : Prop :=
  ∃ (n : ℕ) (s : Fin (n + 1) → Γ(tensorPowModule X L d, ⊤)), GeneratesStalks s ∧
    ∀ p : X ⟶ projectiveSpaceOver n S,
      p ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f →
        (∀ i, (nvCover s i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
          toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i)) →
        IsImmersion p

/-- **The one statement steps 6 and 7 of [Stacks, Tag 01VS] still owe on the source's route: the
Segre factorization.** If the morphism pinned by a generating family `s` of `L ^⊗ a` is an
immersion, then so is the morphism pinned by the product family of `s` with any generating family
of `L ^⊗ b`.

This is the sentence the source proves with the Segre embedding — *"observe that `i` is the
composition `X ⟶ ℙᵐ_S ×_S ℙᵗ_S ⟶ ℙ^{k-1}_S` where the first morphism is `(j, j')` and the second
morphism is the Segre embedding"* — together with Tags 07RK and 02V0, which are the two steps
`Stacks.ChartImmersionAssembly.exists_isImmersion_over_of_isImmersion_pair` already performs
unconditionally. What it is *not* is a statement about `𝒪(1)`: on this route the twist never
travels along the Segre embedding, so `Stacks.ChartImmersionAssembly.SegreTwist` is not needed.

**It is not Stacks Tag 01VS**: no ampleness, no finite type hypothesis and no degree bound occurs
in it. -/
def ProductFamilyImmersion : Prop :=
  ∀ (a b : ℤ) (n m : ℕ) (s : Fin (n + 1) → Γ(tensorPowModule X L a, ⊤))
      (t : Fin (m + 1) → Γ(tensorPowModule X L b, ⊤)), GeneratesStalks s → GeneratesStalks t →
    (∀ p : X ⟶ projectiveSpaceOver n S,
      p ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f →
        (∀ i, (nvCover s i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
          toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i)) →
        IsImmersion p) →
    ∀ q : X ⟶ projectiveSpaceOver (n * m + n + m) S,
      q ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} (n * m + n + m))) = f →
        (∀ i, (nvCover (prodPowFamily L (rfl : a + b = a + b) s t) i).ι ≫ q ≫
            projectiveSpaceOver.toIntegralAtUniverse (n * m + n + m) S =
          toProjectiveSpaceAtUniverse (chartRatio (prodPowFamily L rfl s t) i)
            (span_range_chartRatio (prodPowFamily L rfl s t) i)) →
          IsImmersion q

/-- **Eventual generation of the powers, in the stalkwise form the source's route consumes.**
Every sufficiently high tensor power of `L` carries a finite family of global sections generating
every stalk.

This is clause (7) of [Stacks, Tag 01Q3] at `F = 𝒪_X`, in the generation predicate Tag 01NE's
morphism is built from. `Stacks.AmpleEventualGeneration.IsEventuallyFinGenPowers` is the same
mathematics stated as an epimorphism out of a finite free module; this is the side that
`Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem` produces from a nonvanishing
cover, and `Stacks.StalkwiseGeneration.exists_generatesStalks_of_isFinGen` passes from the other
one to this one. For an ample `L` the predicate holds, by
`Stacks.StalkwiseGeneration.eventuallyGeneratesStalksPowers_of_isAmple`. -/
def EventuallyGeneratesStalksPowers : Prop :=
  ∃ d₁ : ℤ, ∀ d : ℤ, d₁ ≤ d →
    ∃ (m : ℕ) (t : Fin (m + 1) → Γ(tensorPowModule X L d, ⊤)), GeneratesStalks t

/-- **The step of the source's induction**, from `ProductFamilyImmersion`: the family-carrying
conclusion at `a` and a generating family of `L ^⊗ b` give the family-carrying conclusion at
`a + b`, the family being the product family. -/
theorem familyImmersionTwist_add (hpfi : ProductFamilyImmersion f L) {a b : ℤ}
    (ha : FamilyImmersionTwist f L a) {m : ℕ}
    {t : Fin (m + 1) → Γ(tensorPowModule X L b, ⊤)} (ht : GeneratesStalks t) :
    FamilyImmersionTwist f L (a + b) := by
  obtain ⟨n, s, hs, himm⟩ := ha
  exact ⟨n * m + n + m, prodPowFamily L rfl s t, generatesStalks_prodPowFamily L rfl hs ht,
    hpfi a b n m s t hs ht himm⟩

/-- **The family-carrying conclusion gives Tag 01VS's conclusion at that degree**, as soon as the
twist half of Tag 01NE is available: the morphism is the one of step 3, the immersion
property is the predicate's, and the twist is `Stacks.AmpleImmersionReduction.TwistPullback`. -/
theorem hasImmersionTwistOver_of_familyImmersionTwist
    (htw : Stacks.AmpleImmersionReduction.TwistPullback f) {d : ℤ}
    (h : FamilyImmersionTwist f L d) :
    HasImmersionTwistOver f (tensorPowModule X L d) := by
  obtain ⟨n, s, hs, himm⟩ := h
  obtain ⟨p, hpf, hchart⟩ :=
    Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks s hs f
  exact ⟨n, p, himm p hpf hchart, hpf, htw _ n s hs p hpf hchart⟩

/-- **The base of the source's induction is `Stacks.AmpleImmersionReduction.ChartImmersion`
verbatim**: steps 1 to 4 already produce the family-carrying conclusion, in one degree. -/
theorem exists_familyImmersionTwist_of_chartImmersion
    (hch : Stacks.AmpleImmersionReduction.ChartImmersion f L) (hL : IsAmple X L)
    (hft : LocallyOfFiniteType f) : ∃ N : ℤ, 1 ≤ N ∧ FamilyImmersionTwist f L N := by
  obtain ⟨N, n, s, hN, hs, himm⟩ := hch hL hft
  exact ⟨N, hN, n, s, hs, himm⟩

end Passage

/-! ### Stacks Tag 01VS on the source's route -/

section Reduction

variable {S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L]

/-- **One positive degree of `EventuallyGeneratesStalksPowers` holds**, from ampleness alone:
`Stacks.AmpleImmersionReduction.exists_generating_family_of_isAmple`. This is the stalkwise twin of
`Stacks.FinGenFromCover.exists_pos_isFinGen_tensorPowModule`, and it needs no bridge between the
two generation predicates because that declaration already concludes in this one. -/
theorem exists_pos_generatesStalks_tensorPowModule (hL : IsAmple X L) :
    ∃ (N : ℕ) (n : ℕ) (s : Fin (n + 1) → Γ(tensorPowModule X L (N : ℤ), ⊤)),
      1 ≤ N ∧ GeneratesStalks s := by
  obtain ⟨N, n, s, hN, hs, -⟩ := Stacks.AmpleImmersionReduction.exists_generating_family_of_isAmple
    L hL
  exact ⟨N, n, s, hN, hs⟩

/-- **Tag 01VS in every degree `N + d k`, from three of the four inputs** — the eventual generation
of the powers is not used, because one positive degree of it is proved as
`exists_pos_generatesStalks_tensorPowModule`. The parallel of
`Stacks.AmpleImmersionReduction.hasImmersionTwistOver_multiples_of_isAmple`, with `TwistPassage`
replaced by `ProductFamilyImmersion`. -/
theorem hasImmersionTwistOver_multiples_of_isAmple
    (htw : Stacks.AmpleImmersionReduction.TwistPullback f)
    (hch : Stacks.AmpleImmersionReduction.ChartImmersion f L)
    (hpfi : ProductFamilyImmersion f L) (hL : IsAmple X L) (hft : LocallyOfFiniteType f) :
    ∃ N d : ℤ, 1 ≤ N ∧ 1 ≤ d ∧
      ∀ k : ℕ, HasImmersionTwistOver f (tensorPowModule X L (N + d * (k : ℤ))) := by
  obtain ⟨N, hN, hfam⟩ := exists_familyImmersionTwist_of_chartImmersion f L hch hL hft
  obtain ⟨d, _, t, hd, ht⟩ := exists_pos_generatesStalks_tensorPowModule L hL
  refine ⟨N, (d : ℤ), hN, by exact_mod_cast hd, fun k => ?_⟩
  have key : ∀ k : ℕ, FamilyImmersionTwist f L (N + (d : ℤ) * (k : ℤ)) := by
    intro k
    induction k with
    | zero => simpa using hfam
    | succ k ih =>
      have step := familyImmersionTwist_add f L hpfi ih ht
      rw [show N + (d : ℤ) * (k : ℤ) + (d : ℤ) = N + (d : ℤ) * ((k + 1 : ℕ) : ℤ) from by
        push_cast; ring] at step
      exact step
  exact hasImmersionTwistOver_of_familyImmersionTwist f L htw (key k)

/-- **The whole of `Stacks.AmpleProjectiveImmersion.ImmersionTwistGap` on the source's route**,
from four named inputs. The bound is the source's `d₀ = d₁ + d₂`, with `d₂` the single degree of
`Stacks.AmpleImmersionReduction.ChartImmersion` and `d₁` the bound of
`EventuallyGeneratesStalksPowers`. -/
theorem immersionTwistGap_of_productFamilyImmersion
    (htw : Stacks.AmpleImmersionReduction.TwistPullback f)
    (hch : Stacks.AmpleImmersionReduction.ChartImmersion f L)
    (hgen : EventuallyGeneratesStalksPowers L) (hpfi : ProductFamilyImmersion f L) :
    ImmersionTwistGap f L (tensorPowModule X L) := by
  intro hL hft
  obtain ⟨N, hN, hfam⟩ := exists_familyImmersionTwist_of_chartImmersion f L hch hL hft
  obtain ⟨d₁, hd₁⟩ := hgen
  refine ⟨N.toNat + d₁.toNat, by omega, fun d hd => ?_⟩
  have hdz : ((N.toNat : ℤ)) + ((d₁.toNat : ℤ)) ≤ (d : ℤ) := by exact_mod_cast hd
  have hb : d₁ ≤ (d : ℤ) - N := by omega
  obtain ⟨m, t, ht⟩ := hd₁ _ hb
  have key := familyImmersionTwist_add f L hpfi hfam ht
  rw [show N + ((d : ℤ) - N) = (d : ℤ) from by ring] at key
  exact (hasImmersionTwist_iff f _).mpr
    (hasImmersionTwistOver_of_familyImmersionTwist f L htw key)

/-- **Stacks Tag 01VS on the source's own route**, from four named inputs:
`Stacks.AmpleImmersionReduction.TwistPullback`,
`Stacks.AmpleImmersionReduction.ChartImmersion`,
`Stacks.ProductFamilyTwist.EventuallyGeneratesStalksPowers` and
`Stacks.ProductFamilyTwist.ProductFamilyImmersion`.

The conclusion is that of the tagged statement with its auxiliary definitions replaced by
their library names and nothing else changed.

**No Tag 01VS attribute is attached**: this carries four hypotheses the tag does not. -/
theorem exists_immersion_projectiveSpaceOver_of_isAmple (hL : IsAmple X L)
    [hf : LocallyOfFiniteType f] (htw : Stacks.AmpleImmersionReduction.TwistPullback f)
    (hch : Stacks.AmpleImmersionReduction.ChartImmersion f L)
    (hgen : EventuallyGeneratesStalksPowers L) (hpfi : ProductFamilyImmersion f L) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ∃ (n : ℕ) (i : X ⟶ projectiveSpaceOver n S),
        IsImmersion i ∧
        i ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
        Nonempty (tensorPowModule X L (d : ℤ) ≅
          (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S)) :=
  exists_immersion_projectiveSpaceOver_of_isAmple' f L hL
    (immersionTwistGap_of_productFamilyImmersion f L htw hch hgen hpfi)

end Reduction

/-! ### Faithfulness: the tagged statement's binders, in its order -/

section Faithfulness

/-- **The hypotheses of Tag 01VS, in its own binder order, and the four named inputs last.**
Stated as checked code rather than asserted in prose, so that the excess over the tagged statement
is checkable: the only hypotheses beyond those of Tag 01VS are the four `Prop`s named above, and
when they are proved the assertion of the tag follows with nothing added. -/
example {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple X L) [LocallyOfFiniteType f]
    (htw : Stacks.AmpleImmersionReduction.TwistPullback f)
    (hch : Stacks.AmpleImmersionReduction.ChartImmersion f L)
    (hgen : EventuallyGeneratesStalksPowers L) (hpfi : ProductFamilyImmersion f L) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ∃ (n : ℕ) (i : X ⟶ projectiveSpaceOver n S),
        IsImmersion i ∧
        i ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
        Nonempty (tensorPowModule X L (d : ℤ) ≅
          (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S)) :=
  exists_immersion_projectiveSpaceOver_of_isAmple f L hL htw hch hgen hpfi

end Faithfulness

end Stacks.ProductFamilyTwist

end
