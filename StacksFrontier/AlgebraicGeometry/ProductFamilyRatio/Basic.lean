module

public import StacksFrontier.AlgebraicGeometry.ChartDictionary.Basic
public import StacksFrontier.AlgebraicGeometry.ChartImmersionFinish.Basic
public import StacksFrontier.AlgebraicGeometry.ProductFamilyTwist.Basic
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers

/-!
# The product family on a chart: the coordinate ratios, and the Segre factorization

Steps 6 and 7 of the proof of [Stacks, Tag 01VS] multiply a family `s` of global sections of
`L ^⊗ a` with a family `t` of global sections of `L ^⊗ b` and consider the morphism `q` to
projective space that the product family `s_α t_β` defines. `Stacks.ProductFamilyTwist` proves the
generation claim of that step and, from `Stacks.AmpleImmersionReduction.TwistPullback`, the twist;
what it leaves open is `Stacks.ProductFamilyTwist.ProductFamilyImmersion`, the claim that `q` is an
immersion as soon as the morphism `j` pinned by `s` alone is one.

**This file proves it**, as `Stacks.ProductFamilyRatio.productFamilyImmersion`, by a chart
computation and with no Segre embedding.

## The arithmetic

The claim rests on **the coordinate ratios of the product family along a fixed second index being
the coordinate ratios of the first family**,

`(s_{α'} t_β) / (s_α t_β) = s_{α'} / s_α`,

which is `Stacks.ProductFamilyRatio.ratio_prodFamily` on the product family itself and
`Stacks.ProductFamilyRatio.ratio_prodPowFamily` on the re-indexed and transported family
`Stacks.ProductFamilyTwist.prodPowFamily` that pins `q`. Together with
`Stacks.ChartDictionary.appLE_chartCoordOver` — which says the chart ring map of a pinned morphism
sends the chart coordinate `T_k/T_i` to the coordinate ratio `s_k/s_i` — this identifies the
product-family chart morphism with the first family's chart morphism in the coordinates
`T_{α'β}`, which is what the immersion property is read off from.

## The chart route, in place of the Segre embedding

`StacksFrontier/AlgebraicGeometry/ChartImmersionAssembly/SegrePassage.lean` and
`StacksFrontier/AlgebraicGeometry/ProductFamilyTwist/Basic.lean` both record a route to
`ProductFamilyImmersion` through a *named* Segre embedding over `S` with its coordinates in hand,
so that `q` can be identified with `(j, j') ≫ σ`. **That is not the only route, and the one taken
here needs no Segre embedding at all.**

`AlgebraicGeometry.IsImmersion.of_comp` says that if `q ≫ h` is an immersion then so is `q`, for
an arbitrary `h`. So to see that `q` is an immersion it is enough, by
`Stacks.ChartImmersionFinish.isImmersion_of_isImmersion_standardChart_subcover`, to produce on
each chart of the product family *some* morphism out of the standard chart of `ℙ^{nm+n+m}_S`
along which the chart restriction of `q` becomes the chart restriction of `j`. On the standard
chart at `(α, β)` that morphism is the linear projection `T_{α'} ↦ T_{α'β}`, which exists there
although it does not exist on the whole of `ℙ^{nm+n+m}_S`; it is
`Stacks.ProductFamilyRatio.chartProj`, assembled from
`Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse` applied to the chart coordinates
`T_{α'β}/T_{αβ}` — a family spanning the unit ideal because its `α`-th member is `1`, which is
`Stacks.ProductFamilyRatio.chartCoord_self` — followed by
`Stacks.AmpleProjectiveImmersion.liftOver`. The identification of the composite is
`Stacks.ProductFamilyRatio.resLE_comp_chartProj`, from
`Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality` together with the arithmetic above.

So nothing about `𝒪(1)` travels along a Segre embedding on this route, and in particular neither
`Stacks.ChartImmersionAssembly.SegreTwist` nor [Stacks, Tag 01CD] nor
`AlgebraicGeometry.externalTensorProduct` occurs in it.

## Main definitions

* `Stacks.ProductFamilyRatio.segreIdx`: the coordinate `T_{αβ}` of `ℙ^{nm+n+m}` indexed by a pair.
* `Stacks.ProductFamilyRatio.chartCoordScheme`: the chart coordinate `T_k/T_i` as a global section
  of the `i`-th standard chart of `ℙⁿ_S` read as a scheme.
* `Stacks.ProductFamilyRatio.chartProjFamily`, `chartProj`: **the linear projection
  `T_{α'} ↦ T_{α'β}` out of a standard chart of `ℙ^{nm+n+m}_S`.**

## Main results

* `Stacks.ProductFamilyRatio.resT_prodSection`, `mulSec_smul`: the restriction of a product of
  global sections is the product of the restriction, and multiplication by a global section is
  `𝒪_X`-linear on sections — the two facts that make the ratio computation go through.
* `Stacks.ProductFamilyRatio.ratio_prodFamily`: **`(s_{α'} t_β)/(s_α t_β) = s_{α'}/s_α`.**
* `Stacks.ProductFamilyRatio.ratio_congr`: the coordinate ratios of a family transported along an
  isomorphism of invertible modules are the original ones. Needed because
  `Stacks.ProductFamilyTwist.prodPowFamily` carries the product family across
  `Stacks.AmpleEventualGeneration.tensorPowAdd`.
* `Stacks.ProductFamilyRatio.awayCoord_self`, `chartCoord_self`, `chartCoordScheme_self`:
  **`T_i/T_i = 1`.**
* `Stacks.ProductFamilyRatio.ratio_prodPowFamily`: the arithmetic above for the family that pins
  the product-family morphism, after both transports.
* `Stacks.ProductFamilyRatio.appTop_resLE_chartCoordScheme`: the chart dictionary in the
  `AlgebraicGeometry.Scheme.Hom.appTop` spelling the naturality statement consumes.
* `Stacks.ProductFamilyRatio.resLE_comp_chartProj`: **the transport identification** — on each
  chart, the restriction of `q` followed by the linear projection is the restriction of `j`.
* `Stacks.ProductFamilyRatio.productFamilyImmersion`:
  **`Stacks.ProductFamilyTwist.ProductFamilyImmersion`.**
What that discharges is spent in the sibling file
`StacksFrontier/AlgebraicGeometry/ProductFamilyRatio/Consequences.lean`, which keeps the heavier
imports out of this one.

## What is not done

**No Stacks attribute is attached.** Nothing here is a statement of the Stacks Project:
`productFamilyImmersion` mentions no ampleness, no finite type hypothesis and no degree bound, and
the rest is substrate about coordinate ratios and charts.

`Stacks.AmpleImmersionReduction.TwistPassage` is **not** proved. It is the Segre-twist form of
steps 6 and 7, and nothing here is about it: it consumes
`Stacks.AmpleEventualGeneration.IsFinGen` where this route consumes
`Stacks.ProjectiveFromSections.GeneratesStalks`, and
`StacksFrontier/AlgebraicGeometry/AmpleImmersionReduction/Generation.lean` records those two
predicates as unbridged; and its conclusion needs a generating family recovered from
`Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver`, which forgets the family.

The one condition that remains between this route and [Stacks, Tag 01VS] is
`Stacks.ProductFamilyTwist.EventuallyGeneratesStalksPowers L`, clause (7) of [Stacks, Tag 01Q3] at
`F = 𝒪_X` in the stalkwise generation predicate; see the sibling file. It is not a statement about
charts, coordinate ratios or the Segre embedding.

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections Stacks.AmpleProjectiveImmersion
open Stacks.SectionProduct Stacks.TensorSectionNonvanishing Stacks.SectionsToProjectiveSpace

universe u

namespace Stacks.ProductFamilyRatio

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
attribute [local instance] Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}}

/-! ### Products of sections under restriction and under scalars -/

/-- **The restriction of a product of two global sections** is the product of the restriction of
the first with the second: `Stacks.ProductFamilyTwist.prodSection` is
`Stacks.TensorSectionNonvanishing.mulSec`, which is the evaluation of a morphism of modules and so
commutes with restriction. -/
theorem resT_prodSection {F G : X.Modules} (s : Γ(F, ⊤)) (t : Γ(G, ⊤)) (W : X.Opens) :
    resT W (Stacks.ProductFamilyTwist.prodSection s t) =
      mulSec F (Stacks.ProductFamilyTwist.unitOfSection G t) (resT W s) := by
  rw [Stacks.ProductFamilyTwist.prodSection, globalSection_unitMul,
    Stacks.ProductFamilyTwist.globalSection_unitOfSection]
  exact map_mulSec F (Stacks.ProductFamilyTwist.unitOfSection G t)
    (homOfLE (le_top : W ≤ ⊤)) s

/-- **Multiplication by a global section is `𝒪_X`-linear on sections.**
`Stacks.TensorSectionNonvanishing.mulSec` is the evaluation of the module morphism
`Stacks.TensorSectionNonvanishing.mulRight`, so this is that morphism's semilinearity. -/
theorem mulSec_smul {F G : X.Modules} (f : 𝟙_ X.Modules ⟶ G) {W : X.Opens}
    (a : Γ(X, W)) (m : Γ(F, W)) :
    mulSec F f (a • m) = a • mulSec F f m :=
  Scheme.Modules.Hom.app_smul (mulRight F f) a m

/-! ### The coordinate ratios of a product family -/

/-- The chart of a product family lies in the chart of the first family, by the Tag 01CY remark
`X_{e ⊗ f} = X_e ⊓ X_f`
(`Stacks.TensorSectionNonvanishing.nonvanishingOpen_unitMul`, in the form
`Stacks.ProductFamilyTwist.nvOpen_prodSection`). -/
theorem nvCover_prodFamily_le_left {F G : X.Modules} [IsInvertibleModule X F]
    [IsInvertibleModule X G] {ι κ : Type*} (s : ι → Γ(F, ⊤)) (t : κ → Γ(G, ⊤)) (p : ι × κ) :
    nvCover (Stacks.ProductFamilyTwist.prodFamily s t) p ≤ nvCover s p.1 := by
  rw [show nvCover (Stacks.ProductFamilyTwist.prodFamily s t) p =
      nvOpen (F ⊗ G) (Stacks.ProductFamilyTwist.prodSection (s p.1) (t p.2)) from rfl,
    Stacks.ProductFamilyTwist.nvOpen_prodSection]
  exact inf_le_left

/-- **The coordinate ratios of a product family along a fixed second index are the coordinate
ratios of the first family**: `(s_{α'} t_β) / (s_α t_β) = s_{α'} / s_α` on
`X_{s_α} ⊓ X_{t_β}`.

This is the arithmetic of step 6 of the proof of [Stacks, Tag 01VS]. The proof is the uniqueness
clause `Stacks.ProjectiveFromSections.eq_div` of the ratio: multiplying `s_α t_β` by the
restriction of `s_{α'}/s_α` gives `s_{α'} t_β`, because multiplication by `t_β` is linear. -/
theorem ratio_prodFamily {F G : X.Modules} [IsInvertibleModule X F] [IsInvertibleModule X G]
    {ι κ : Type*} (s : ι → Γ(F, ⊤)) (t : κ → Γ(G, ⊤)) (a a' : ι) (b : κ) :
    ratio (Stacks.ProductFamilyTwist.prodFamily s t) (a, b) (a', b) =
      resO (nvCover_prodFamily_le_left s t (a, b)) (ratio s a a') := by
  refine (eq_div (Stacks.ProductFamilyTwist.prodFamily s t (a, b)) le_rfl ?_).symm
  show resO (nvCover_prodFamily_le_left s t (a, b)) (ratio s a a') •
      resT (nvCover (Stacks.ProductFamilyTwist.prodFamily s t) (a, b))
        (Stacks.ProductFamilyTwist.prodSection (s a) (t b)) =
    resT (nvCover (Stacks.ProductFamilyTwist.prodFamily s t) (a, b))
      (Stacks.ProductFamilyTwist.prodSection (s a') (t b))
  rw [resT_prodSection, resT_prodSection, ← mulSec_smul,
    resO_ratio_smul s (nvCover_prodFamily_le_left s t (a, b)) a']

/-! ### Coordinate ratios under an isomorphism of invertible modules -/

/-- The chart of a family transported along an isomorphism is the chart of the original family. -/
theorem nvCover_congr_le {M N : X.Modules} [IsInvertibleModule X M] [IsInvertibleModule X N]
    {ι : Type*} (e : M ≅ N) (s : ι → Γ(M, ⊤)) (i : ι) :
    nvCover (fun j => e.hom.app ⊤ (s j)) i ≤ nvCover s i :=
  le_of_eq (TopologicalSpace.Opens.ext (nonvanishingLocus_congr e (s i)))

/-- **The coordinate ratios are unchanged by an isomorphism of invertible modules.** -/
theorem ratio_congr {M N : X.Modules} [IsInvertibleModule X M] [IsInvertibleModule X N]
    {ι : Type*} (e : M ≅ N) (s : ι → Γ(M, ⊤)) (i k : ι) :
    ratio (fun j => e.hom.app ⊤ (s j)) i k = resO (nvCover_congr_le e s i) (ratio s i k) := by
  refine (eq_div _ le_rfl ?_).symm
  have h := resO_ratio_smul s (nvCover_congr_le e s i) k
  have hn : ∀ (W : X.Opens) (x : Γ(M, ⊤)),
      resT W (e.hom.app ⊤ x) = e.hom.app W (resT W x) := fun W x =>
    (PresheafOfModules.naturality_apply e.hom.val (homOfLE (le_top : W ≤ ⊤)).op x).symm
  rw [hn, hn, ← h, Scheme.Modules.Hom.app_smul]

/-! ### The chart coordinate at its own index -/

/-- `T_i/T_i = 1` as a degree-zero fraction. -/
theorem awayCoord_self (n : ℕ) (i : Fin (n + 1)) :
    Stacks.ChartDictionary.awayCoord.{u} n i i = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [Stacks.ChartDictionary.awayCoord]
  simp [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one]

/-- **`T_i/T_i = 1`** as a section of `𝒪` over the `i`-th standard open of `ℙⁿ_ℤ`. -/
theorem chartCoord_self (n : ℕ) (i : Fin (n + 1)) :
    Stacks.ChartDictionary.chartCoord.{u} n i i = 1 := by
  rw [Stacks.ChartDictionary.chartCoord, awayCoord_self]
  exact map_one _

/-! ### The linear projection out of a standard chart of `ℙ^{nm+n+m}_S` -/

/-- The homogeneous coordinate of `ℙ^{nm+n+m}` indexed by the pair `(α, β)` of a coordinate of
`ℙⁿ` and a coordinate of `ℙᵐ`, under the index bijection of step 6 of the proof of
[Stacks, Tag 01VS]. -/
def segreIdx (n m : ℕ) (α : Fin (n + 1)) (β : Fin (m + 1)) : Fin (n * m + n + m + 1) :=
  (Stacks.ProductFamilyTwist.segreIndexEquiv n m).symm (α, β)

/-- The coordinate `segreIdx n m α β` of `ℙ^{nm+n+m}` corresponds to the pair `(α, β)`. -/
@[simp] theorem segreIndexEquiv_segreIdx (n m : ℕ) (α : Fin (n + 1)) (β : Fin (m + 1)) :
    Stacks.ProductFamilyTwist.segreIndexEquiv n m (segreIdx n m α β) = (α, β) :=
  (Stacks.ProductFamilyTwist.segreIndexEquiv n m).apply_symm_apply _

/-- Every coordinate of `ℙ^{nm+n+m}` is a product coordinate. -/
@[simp] theorem segreIdx_segreIndexEquiv (n m : ℕ) (k : Fin (n * m + n + m + 1)) :
    segreIdx n m (Stacks.ProductFamilyTwist.segreIndexEquiv n m k).1
        (Stacks.ProductFamilyTwist.segreIndexEquiv n m k).2 = k :=
  (Stacks.ProductFamilyTwist.segreIndexEquiv n m).symm_apply_apply k

/-- **The chart coordinate `Tₖ/Tᵢ` as a global section of the `i`-th standard chart of `ℙⁿ_S`,
read as a scheme**, transported from `Stacks.ChartDictionary.chartCoordOver` along
`AlgebraicGeometry.Scheme.Opens.topIso`. -/
def chartCoordScheme (n : ℕ) (S : Scheme.{u}) (i k : Fin (n + 1)) :
    Γ((projectiveSpaceOver.standardChart n S i).toScheme, ⊤) :=
  (projectiveSpaceOver.standardChart n S i).topIso.inv
    (Stacks.ChartDictionary.chartCoordOver.{u} n S i k)

/-- **`Tᵢ/Tᵢ = 1`** on the `i`-th standard chart of `ℙⁿ_S`. -/
@[simp] theorem chartCoordScheme_self (n : ℕ) (S : Scheme.{u}) (i : Fin (n + 1)) :
    chartCoordScheme.{u} n S i i = 1 := by
  rw [chartCoordScheme, Stacks.ChartDictionary.chartCoordOver, chartCoord_self, map_one, map_one]

/-- **The coordinates of the linear projection `T_{α'} ↦ T_{α'β}`**: on the standard chart of
`ℙ^{nm+n+m}_S` at the coordinate `T_{αβ}`, the chart coordinates `T_{α'β}/T_{αβ}` indexed by the
coordinates `α'` of `ℙⁿ`. -/
def chartProjFamily (n m : ℕ) (S : Scheme.{u}) (α : Fin (n + 1)) (β : Fin (m + 1))
    (α' : Fin (n + 1)) :
    Γ((projectiveSpaceOver.standardChart (n * m + n + m) S (segreIdx n m α β)).toScheme, ⊤) :=
  chartCoordScheme.{u} (n * m + n + m) S (segreIdx n m α β) (segreIdx n m α' β)

/-- **The coordinates of the linear projection span the unit ideal**, the one at `α' = α` being
`T_{αβ}/T_{αβ} = 1`. This is what lets
`Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse` be applied to them, and it is the
reason the projection exists on the chart although it does not exist on the whole of
`ℙ^{nm+n+m}_S`. -/
theorem span_range_chartProjFamily (n m : ℕ) (S : Scheme.{u}) (α : Fin (n + 1))
    (β : Fin (m + 1)) : Ideal.span (Set.range (chartProjFamily.{u} n m S α β)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span ⟨α, by rw [chartProjFamily, chartCoordScheme_self]⟩

/-- **The linear projection `T_{α'} ↦ T_{α'β}` out of a standard chart of `ℙ^{nm+n+m}_S`.** On the
standard chart at the coordinate `T_{αβ}` the ratios `T_{α'β}/T_{αβ}` are regular functions
spanning the unit ideal, so they define a morphism to `ℙⁿ_ℤ`; over `S` it is the
`Stacks.AmpleProjectiveImmersion.liftOver` of that morphism along the structure morphism of the
chart.

It is **not** a morphism `ℙ^{nm+n+m}_S ⟶ ℙⁿ_S`, which does not exist, and it is **not** a Segre
embedding: it is a linear projection, defined only where `T_{αβ}` is invertible. It serves only to
recognise the chart restriction of the product-family morphism as an immersion, by
`AlgebraicGeometry.IsImmersion.of_comp`. -/
def chartProj (n m : ℕ) (S : Scheme.{u}) (α : Fin (n + 1)) (β : Fin (m + 1)) :
    (projectiveSpaceOver.standardChart (n * m + n + m) S (segreIdx n m α β)).toScheme ⟶
      projectiveSpaceOver n S :=
  liftOver ((projectiveSpaceOver.standardChart (n * m + n + m) S (segreIdx n m α β)).ι ≫
      pullback.fst (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} (n * m + n + m))))
    (toProjectiveSpaceAtUniverse (chartProjFamily.{u} n m S α β)
      (span_range_chartProjFamily.{u} n m S α β))

/-! ### The chart and the ratios of the product power family at a product coordinate -/

section ProductPower

variable {L : X.Modules} [IsInvertibleModule X L]

/-- The member of `Stacks.ProductFamilyTwist.prodPowFamily` at the product coordinate `T_{αβ}` is
the transported product `s_α t_β`: the re-indexing is undone by
`Stacks.ProductFamilyRatio.segreIndexEquiv_segreIdx`. -/
theorem prodPowFamily_segreIdx {a b c : ℤ} (hc : a + b = c) {n m : ℕ}
    (s : Fin (n + 1) → Γ(tensorPowModule X L a, ⊤))
    (t : Fin (m + 1) → Γ(tensorPowModule X L b, ⊤)) (α : Fin (n + 1)) (β : Fin (m + 1)) :
    Stacks.ProductFamilyTwist.prodPowFamily L hc s t (segreIdx n m α β) =
      (Stacks.AmpleEventualGeneration.tensorPowAdd hc).hom.app ⊤
        (Stacks.ProductFamilyTwist.prodFamily s t (α, β)) :=
  congrArg (fun p => (Stacks.AmpleEventualGeneration.tensorPowAdd hc).hom.app ⊤
    (Stacks.ProductFamilyTwist.prodFamily s t p)) (segreIndexEquiv_segreIdx n m α β)

/-- The chart of the product power family at the product coordinate `T_{αβ}` is the chart of the
transported product family at `(α, β)`. -/
theorem nvCover_prodPowFamily_segreIdx {a b c : ℤ} (hc : a + b = c) {n m : ℕ}
    (s : Fin (n + 1) → Γ(tensorPowModule X L a, ⊤))
    (t : Fin (m + 1) → Γ(tensorPowModule X L b, ⊤)) (α : Fin (n + 1)) (β : Fin (m + 1)) :
    nvCover (Stacks.ProductFamilyTwist.prodPowFamily L hc s t) (segreIdx n m α β) =
      nvCover (fun p => (Stacks.AmpleEventualGeneration.tensorPowAdd hc).hom.app ⊤
        (Stacks.ProductFamilyTwist.prodFamily s t p)) (α, β) :=
  congrArg (nvOpen (tensorPowModule X L c)) (prodPowFamily_segreIdx hc s t α β)

/-- **The chart of the product power family at `T_{αβ}` lies in the chart of the first family at
`α`.** This is the Tag 01CY remark `X_{e ⊗ f} = X_e ⊓ X_f` after the two transports the family
carries: the re-indexing and `Stacks.AmpleEventualGeneration.tensorPowAdd`. -/
theorem nvCover_prodPowFamily_le_left {a b c : ℤ} (hc : a + b = c) {n m : ℕ}
    (s : Fin (n + 1) → Γ(tensorPowModule X L a, ⊤))
    (t : Fin (m + 1) → Γ(tensorPowModule X L b, ⊤)) (α : Fin (n + 1)) (β : Fin (m + 1)) :
    nvCover (Stacks.ProductFamilyTwist.prodPowFamily L hc s t) (segreIdx n m α β) ≤
      nvCover s α :=
  (nvCover_prodPowFamily_segreIdx hc s t α β).le.trans
    ((nvCover_congr_le (Stacks.AmpleEventualGeneration.tensorPowAdd hc)
        (Stacks.ProductFamilyTwist.prodFamily s t) (α, β)).trans
      (nvCover_prodFamily_le_left s t (α, β)))

/-- **The coordinate ratios of the product power family along a fixed second index are the
coordinate ratios of the first family**:
`(s_{α'} t_β)/(s_α t_β) = s_{α'}/s_α` on the chart at `T_{αβ}`.

This is `Stacks.ProductFamilyRatio.ratio_prodFamily` carried across
`Stacks.AmpleEventualGeneration.tensorPowAdd` by `Stacks.ProductFamilyRatio.ratio_congr` and
across the re-indexing of step 6. It is the arithmetic input to the identification of the
product-family chart morphism with the first family's. -/
theorem ratio_prodPowFamily {a b c : ℤ} (hc : a + b = c) {n m : ℕ}
    (s : Fin (n + 1) → Γ(tensorPowModule X L a, ⊤))
    (t : Fin (m + 1) → Γ(tensorPowModule X L b, ⊤)) (α : Fin (n + 1)) (β : Fin (m + 1))
    (α' : Fin (n + 1)) :
    ratio (Stacks.ProductFamilyTwist.prodPowFamily L hc s t) (segreIdx n m α β)
        (segreIdx n m α' β) =
      resO (nvCover_prodPowFamily_le_left hc s t α β) (ratio s α α') := by
  have hQ := resO_ratio_smul (fun p => (Stacks.AmpleEventualGeneration.tensorPowAdd hc).hom.app ⊤
    (Stacks.ProductFamilyTwist.prodFamily s t p)) (nvCover_prodPowFamily_segreIdx hc s t α β).le
    (α', β)
  rw [ratio_congr, ratio_prodFamily, Stacks.ChartImmersionFinish.resO_resO,
    Stacks.ChartImmersionFinish.resO_resO] at hQ
  refine (eq_div (Stacks.ProductFamilyTwist.prodPowFamily L hc s t (segreIdx n m α β))
    le_rfl ?_).symm
  have hr (γ : Fin (n + 1)) :
      resT (nvCover (Stacks.ProductFamilyTwist.prodPowFamily L hc s t) (segreIdx n m α β))
        (Stacks.ProductFamilyTwist.prodPowFamily L hc s t (segreIdx n m γ β)) = _ :=
    congrArg (resT _) (prodPowFamily_segreIdx hc s t γ β)
  rw [hr, hr]
  exact hQ

end ProductPower

/-! ### The chart ring map of a pinned morphism, in the `appTop` spelling -/

/-- **The chart restriction of a pinned morphism sends the chart coordinate `Tₖ/Tᵢ` to the
coordinate ratio `sₖ/sᵢ`.** This is `Stacks.ChartDictionary.appLE_chartCoordOver` transported from
`AlgebraicGeometry.Scheme.Hom.appLE` to the `AlgebraicGeometry.Scheme.Hom.appTop` of the
restricted morphism `X_{sᵢ} ⟶ D₊(Tᵢ) ⊆ ℙⁿ_S`, by
`Stacks.ProjGlobalSectionsAppTop.topIso_inv_resLE_appTop`. That is the spelling in which
`Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality` compares the two families of sections. -/
theorem appTop_resLE_chartCoordScheme {M : X.Modules} [IsInvertibleModule X M] {N : ℕ}
    (P : Fin (N + 1) → Γ(M, ⊤)) {S : Scheme.{u}} (q : X ⟶ projectiveSpaceOver N S)
    (i : Fin (N + 1))
    (hchart : (nvCover P i).ι ≫ q ≫ projectiveSpaceOver.toIntegralAtUniverse N S =
      toProjectiveSpaceAtUniverse (chartRatio P i) (span_range_chartRatio P i))
    (e : nvCover P i ≤ q ⁻¹ᵁ projectiveSpaceOver.standardChart N S i) (k : Fin (N + 1)) :
    (q.resLE (projectiveSpaceOver.standardChart N S i) (nvCover P i) e).appTop
        (chartCoordScheme.{u} N S i k) = chartRatio P i k := by
  have h := CategoryTheory.ConcreteCategory.congr_hom
    (Stacks.ProjGlobalSectionsAppTop.topIso_inv_resLE_appTop q e)
    (Stacks.ChartDictionary.chartCoordOver.{u} N S i k)
  exact h.trans (congrArg (fun z => (nvCover P i).topIso.inv z)
    (Stacks.ChartDictionary.appLE_chartCoordOver P q i hchart e k))

/-! ### The transport identification -/

/-- **THE TRANSPORT IDENTIFICATION.** Let `q : X ⟶ ℙ^{nm+n+m}_S` be pinned over `f` by a family `P`
whose coordinate ratios along a fixed second index `β` are the coordinate ratios of a family `s`,
and let `j : X ⟶ ℙⁿ_S` be pinned over `f` by `s`. Then on the chart of `P` at the product
coordinate `T_{αβ}` the restriction of `q` followed by the linear projection
`Stacks.ProductFamilyRatio.chartProj` is the restriction of `j`.

Both sides are morphisms into `ℙⁿ_S = S ×_{Spec ℤ} ℙⁿ_ℤ`, so the identity splits by
`CategoryTheory.Limits.pullback.hom_ext` into two components.

* Over `S` both sides are the structure morphism of the chart, because `q` and `j` both lie over
  `f`: that component is formal.
* Into `ℙⁿ_ℤ` both sides are morphisms attached to a family of sections of the structure sheaf by
  `Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse`, and the naturality of that
  construction in the source scheme is
  `Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality`, which holds unconditionally. The two
  families then agree section by section: the chart ring map of `q` sends `T_{α'β}/T_{αβ}` to the
  ratio `P_{α'β}/P_{αβ}` by `Stacks.ProductFamilyRatio.appTop_resLE_chartCoordScheme`, and that
  ratio is `s_{α'}/s_α` by hypothesis.

Nothing about `𝒪(1)` and no Segre embedding occurs. -/
theorem resLE_comp_chartProj {M : X.Modules} [IsInvertibleModule X M] {n m : ℕ}
    (P : Fin (n * m + n + m + 1) → Γ(M, ⊤)) {M' : X.Modules} [IsInvertibleModule X M']
    (s : Fin (n + 1) → Γ(M', ⊤)) {S : Scheme.{u}} {f : X ⟶ S}
    (q : X ⟶ projectiveSpaceOver (n * m + n + m) S)
    (hqf : q ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} (n * m + n + m))) = f)
    (j : X ⟶ projectiveSpaceOver n S)
    (hjf : j ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f)
    (α : Fin (n + 1)) (β : Fin (m + 1))
    (hqchart : (nvCover P (segreIdx n m α β)).ι ≫ q ≫
        projectiveSpaceOver.toIntegralAtUniverse (n * m + n + m) S =
      toProjectiveSpaceAtUniverse (chartRatio P (segreIdx n m α β))
        (span_range_chartRatio P (segreIdx n m α β)))
    (hjchart : (nvCover s α).ι ≫ j ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
      toProjectiveSpaceAtUniverse (chartRatio s α) (span_range_chartRatio s α))
    (hle : nvCover P (segreIdx n m α β) ≤ nvCover s α)
    (hratio : ∀ α' : Fin (n + 1),
      ratio P (segreIdx n m α β) (segreIdx n m α' β) = resO hle (ratio s α α'))
    (e : nvCover P (segreIdx n m α β) ≤
      q ⁻¹ᵁ projectiveSpaceOver.standardChart (n * m + n + m) S (segreIdx n m α β)) :
    q.resLE (projectiveSpaceOver.standardChart (n * m + n + m) S (segreIdx n m α β))
        (nvCover P (segreIdx n m α β)) e ≫ chartProj.{u} n m S α β =
      (nvCover P (segreIdx n m α β)).ι ≫ j := by
  have hgfam : ∀ α' : Fin (n + 1),
      (q.resLE (projectiveSpaceOver.standardChart (n * m + n + m) S (segreIdx n m α β))
          (nvCover P (segreIdx n m α β)) e).appTop (chartProjFamily.{u} n m S α β α') =
        (X.homOfLE hle).appTop (chartRatio s α α') := by
    intro α'
    have h3 : (X.homOfLE hle).appTop (chartRatio s α α') =
        (nvCover P (segreIdx n m α β)).topIso.inv (resO hle (ratio s α α')) :=
      Stacks.ProjectiveFromSections.homOfLE_appTop_topIso_inv hle (ratio s α α')
    have h4 := appTop_resLE_chartCoordScheme P q (segreIdx n m α β) hqchart e
      (segreIdx n m α' β)
    rw [chartProjFamily, h4, h3, chartRatio, hratio α']
  have hspan1 : Ideal.span (Set.range fun α' =>
      (q.resLE (projectiveSpaceOver.standardChart (n * m + n + m) S (segreIdx n m α β))
        (nvCover P (segreIdx n m α β)) e).appTop (chartProjFamily.{u} n m S α β α')) = ⊤ :=
    Stacks.SectionsToProjectiveSpace.span_range_comp _ _ (span_range_chartProjFamily n m S α β)
  have hspan2 : Ideal.span
      (Set.range fun α' => (X.homOfLE hle).appTop (chartRatio s α α')) = ⊤ :=
    Stacks.SectionsToProjectiveSpace.span_range_comp _ _ (span_range_chartRatio s α)
  refine pullback.hom_ext ?_ ?_ <;> simp only [Category.assoc]
  · rw [show chartProj.{u} n m S α β ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
        (projectiveSpaceOver.standardChart (n * m + n + m) S (segreIdx n m α β)).ι ≫
          pullback.fst (terminal.from S)
            (terminal.from (projectiveSpaceAtUniverse.{u} (n * m + n + m))) from
      liftOver_fst _ _, hjf, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hqf]
  · rw [show chartProj.{u} n m S α β ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
        toProjectiveSpaceAtUniverse (chartProjFamily.{u} n m S α β)
          (span_range_chartProjFamily.{u} n m S α β) from liftOver_snd _ _,
      Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality _ _ _ hspan1,
      toProjectiveSpaceAtUniverse_congr (funext hgfam) hspan1 hspan2,
      ← Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality _ _ (span_range_chartRatio s α)
        hspan2, ← hjchart, ← Category.assoc, Scheme.homOfLE_ι]

/-! ### The Segre factorization statement of steps 6 and 7, on the chart route -/

/-- **`Stacks.ProductFamilyTwist.ProductFamilyImmersion`, proved.** If the morphism pinned by a
generating family `s` of `L ^⊗ a` is an immersion, so is the morphism pinned by the product family
of `s` with any generating family `t` of `L ^⊗ b`.

This is the sentence the source of [Stacks, Tag 01VS] proves with the Segre embedding — *"observe
that `i` is the composition `X ⟶ ℙᵐ_S ×_S ℙᵗ_S ⟶ ℙ^{k-1}_S` where the first morphism is `(j, j')`
and the second morphism is the Segre embedding"* — and the proof here uses no Segre embedding and
no statement about `𝒪(1)`.

Being an immersion is Zariski local on the target, and the charts of the product family cover `X`
(`Stacks.ChartImmersionFinish.isImmersion_of_isImmersion_standardChart_subcover`), so it suffices
that on each chart the restriction `X_{P_{αβ}} ⟶ D₊(T_{αβ})` is an immersion. Composed with the
linear projection `Stacks.ProductFamilyRatio.chartProj` that restriction becomes the restriction of
the first family's morphism `j` — this is
`Stacks.ProductFamilyRatio.resLE_comp_chartProj`, whose arithmetic input is
`Stacks.ProductFamilyRatio.ratio_prodPowFamily` — and `j` is an immersion by hypothesis, so the
composite is one and hence so is the restriction, by
`AlgebraicGeometry.IsImmersion.of_comp`.

**It is not [Stacks, Tag 01VS]**: no ampleness, no finite type hypothesis and no degree bound
occurs in it. -/
theorem productFamilyImmersion {S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] : Stacks.ProductFamilyTwist.ProductFamilyImmersion f L := by
  intro a b n m s t hs ht himm q hqf hqchart
  have hgen : GeneratesStalks (Stacks.ProductFamilyTwist.prodPowFamily L rfl s t) :=
    Stacks.ProductFamilyTwist.generatesStalks_prodPowFamily L rfl hs ht
  obtain ⟨j, hjf, hjchart⟩ :=
    Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks s hs f
  have hjimm : IsImmersion j := himm j hjf hjchart
  refine Stacks.ChartImmersionFinish.isImmersion_of_isImmersion_standardChart_subcover
    (Stacks.ProductFamilyTwist.prodPowFamily L rfl s t) hgen q hqchart
    (fun p : Fin (n + 1) × Fin (m + 1) => segreIdx n m p.1 p.2) ?_ ?_
  · intro x
    obtain ⟨k, hk⟩ := exists_mem_nvCover_of_generatesStalks _ hgen x
    exact ⟨Stacks.ProductFamilyTwist.segreIndexEquiv n m k, by
      simpa only [segreIdx_segreIndexEquiv] using hk⟩
  · rintro ⟨α, β⟩
    have hpre := Stacks.AmpleImmersionReduction.preimage_standardChart
      (Stacks.ProductFamilyTwist.prodPowFamily L rfl s t) hgen q hqchart (segreIdx n m α β)
    refine ⟨q.resLE (projectiveSpaceOver.standardChart (n * m + n + m) S (segreIdx n m α β))
      (nvCover (Stacks.ProductFamilyTwist.prodPowFamily L rfl s t) (segreIdx n m α β)) hpre.ge,
      ?_, Scheme.Hom.resLE_comp_ι _ _⟩
    have hcomp := resLE_comp_chartProj (Stacks.ProductFamilyTwist.prodPowFamily L rfl s t) s q
      hqf j hjf α β (hqchart (segreIdx n m α β)) (hjchart α)
      (nvCover_prodPowFamily_le_left (rfl : a + b = a + b) s t α β)
      (ratio_prodPowFamily (rfl : a + b = a + b) s t α β) hpre.ge
    have himm' : IsImmersion
        ((nvCover (Stacks.ProductFamilyTwist.prodPowFamily L rfl s t)
          (segreIdx n m α β)).ι ≫ j) := inferInstance
    have hcomp' : IsImmersion
        (q.resLE (projectiveSpaceOver.standardChart (n * m + n + m) S (segreIdx n m α β))
          (nvCover (Stacks.ProductFamilyTwist.prodPowFamily L rfl s t) (segreIdx n m α β))
          hpre.ge ≫ chartProj.{u} n m S α β) := by
      rw [hcomp]; exact himm'
    exact IsImmersion.of_comp _ (chartProj.{u} n m S α β)

end Stacks.ProductFamilyRatio

end
