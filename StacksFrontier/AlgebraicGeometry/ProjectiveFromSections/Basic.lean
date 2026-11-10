module

public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Ratio
public import StacksFrontier.AlgebraicGeometry.SectionsToProjectiveSpace.Basic

/-!
# Stacks Tag 01NE for a nontrivial invertible sheaf

Stacks Tag 01NE says that `ℙⁿ_ℤ = Proj ℤ[T₀, …, Tₙ]` represents the functor sending a scheme `Y`
to the pairs `(L, (s₀, …, sₙ))` with `L` an invertible `𝒪_Y`-module and the `sᵢ` global sections
generating it, two pairs identified by an isomorphism matching the sections. The half with
geometric content is the passage from such a pair to a morphism `Y ⟶ ℙⁿ_ℤ`, and the source's own
proof (through Tag 01NA and Tag 01N9) builds it by glueing, over the nonvanishing opens `Y_{sᵢ}`,
the morphism attached to the *ratios* `sₖ / sᵢ`, which are sections of `𝒪_Y` because `sᵢ`
trivializes `L` there.

This file performs that glueing. It supplies, from
`StacksFrontier/AlgebraicGeometry/ProjectiveFromSections/Ratio.lean`, exactly the three inputs
the glueing step `Stacks.SectionsToProjectiveSpace.exists_hom_of_cover` asks for — a cover,
a spanning family on each chart, and agreement up to a unit on each overlap — and so reduces Tag
01NE's morphism, **for a nontrivial `L`**, to the two statements about *Mathlib's* construction
that that step is conditional on. See "What is not done".

## Why the trivial case does not suffice

`AlgebraicGeometry.Proj.fromOfGlobalSections`
(`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean`) takes a ring homomorphism
`A →+* Γ(X, ⊤)`, i.e. sections of `𝒪_X` itself, so it gives the morphism only where `L` is
trivial, and it lands in the absolute `Proj`. This is why this file exists: the whole content here
is the reduction of the nontrivial case to the
trivial one over a cover, which is precisely the ratio package of the sibling file.

## Main definitions

* `Stacks.ProjectiveFromSections.chartRatio`: the ratio family `k ↦ sₖ / sᵢ`, read as global
  sections of the open subscheme `X_{sᵢ}` rather than as sections of `𝒪_X` over the open
  `X_{sᵢ}` — the spelling the morphism to projective space is stated at.
* `Stacks.ProjectiveFromSections.chartTransUnit`: the transition unit `sⱼ/sᵢ` at that spelling.

## Main results

* `Stacks.ProjectiveFromSections.topIso_inv_homOfLE_appTop` and
  `homOfLE_appTop_topIso_inv`: restriction of global sections of an open subscheme along an
  inclusion of opens is restriction of sections of `𝒪_X`. This is the bridge between the two
  spellings, and it is Mathlib's own `AlgebraicGeometry.Scheme.restrictFunctorΓ` read as a
  naturality square; see the implementation notes.
* `Stacks.ProjectiveFromSections.span_range_chartRatio`: the ratios out of `sᵢ` span the unit
  ideal of `Γ(X_{sᵢ}, ⊤)`, because `sᵢ/sᵢ = 1`.
* `Stacks.ProjectiveFromSections.chartRatio_agree`: **the two chart families agree up to the
  transition unit on each overlap**, by the cocycle identity.
* `Stacks.ProjectiveFromSections.exists_hom_projectiveSpaceAtUniverse` and
  `exists_hom_projectiveSpaceAtUniverse_of_generatesStalks`: **the morphism of Tag 01NE for a
  nontrivial invertible sheaf**, from the nonvanishing-cover hypothesis and from the generation
  hypothesis respectively, each conditional on the two statements named below.
* `Stacks.ProjectiveFromSections.exists_hom_projectiveSpaceOver_of_generatesStalks`: the same
  over a base scheme `S`, which is the shape Tag 01VS consumes.

## Implementation notes

**The two spellings of a section over an open, bridged by Mathlib's own natural
isomorphism.** `Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse` takes sections of
the *structure sheaf of the open subscheme*, `Γ(U.toScheme, ⊤)`, while the ratios are sections of
`𝒪_X` over `U`, and `AlgebraicGeometry.Scheme.Opens.topIso` is the identification. The
compatibility of that identification with restriction cannot be proved by rewriting:
`← CategoryTheory.Functor.map_comp` is refused on the composite, the goal failing to be
type-correct at `implicit` transparency because `(↑V).Opens` and
`Opens ↑((Opens.toTopCat ↑X.toPresheafedSpace).obj V)` are not the same expression, and
Mathlib's own `Scheme.homOfLE_app` relaxes `backward.isDefEq.respectTransparency` for the same
reason. No compiler option is set here: the square *is* a naturality square of
`AlgebraicGeometry.Scheme.restrictFunctorΓ`, whose components are that very identification, so
`topIso_inv_homOfLE_appTop` is one application of `NatTrans.naturality` and nothing is rewritten.

**The units are built, not transported.** `chartTransUnit` is given by its value and inverse
directly rather than as `Units.map` of `transUnit`, so that both sides of
`chartRatio_agree` are spelled through the same coercion of `topIso.inv`; with `Units.map` one
side arrives as `CommRingCat.Hom.hom` and the other as `ConcreteCategory.hom`, and the final
`map_mul` does not apply.

## What is not done

`hasPullbackNaturality` and `hasUnitInvariance` are proved at
`StacksFrontier/AlgebraicGeometry/ProjGlobalSectionsAppTop/Consumers.lean`, and the `appTop`
computation below is `toBasicOpenOfGlobalSections_appTop` in
`StacksFrontier/AlgebraicGeometry/ProjGlobalSectionsAppTop/Basic.lean`. Mathlib may still have no
naturality lemma for `basicOpenIsoSpecAway` along a ring map, but that does not block anything
here.

The superseded text follows.

**The two statements about Mathlib's construction are not proved**, and they are the only thing
between this file and an unconditional Tag 01NE morphism:
`Stacks.SectionsToProjectiveSpace.HasPullbackNaturality` and
`Stacks.SectionsToProjectiveSpace.HasUnitInvariance`. Both mention no object of this repository.
Both follow from one missing Mathlib lemma — the computation of
`AlgebraicGeometry.Scheme.Hom.appTop` of `AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections`,
which identifies the chart morphism with the ring map `p / tᵏ ↦ f(p) / f(t)ᵏ` into
`Γ(X, X.basicOpen (f t))` — since that ring map manifestly does not change when the whole family
is scaled by a unit and is manifestly natural in the scheme. Mathlib exposes
`Proj.fromOfGlobalSections_resLE`, `fromOfGlobalSections_morphismRestrict`,
`fromOfGlobalSections_preimage_basicOpen` and `fromOfGlobalSections_toSpecZero`, but no
computation of that `appTop`; `toBasicOpenOfGlobalSections` is a composite of `Scheme.toSpecΓ`
restricted to a basic open, `AlgebraicGeometry.basicOpenIsoSpecAway`, `Spec.map` of
`IsLocalization.map`, and `Proj.basicOpenIsoSpec`, and only the last of those has its `appTop`
recorded (`Proj.basicOpenToSpec_app_top`). `AlgebraicGeometry.basicOpenIsoSpecAway` in particular
has no naturality lemma along a ring map in Mathlib at this pin, which is what
`HasPullbackNaturality` needs; that was checked.

**Nothing is proved about the pullback of `𝒪(1)`.** Tag 01NE is a representability statement, and
even its geometric half is incomplete without the identification `L ≅ φ^* 𝒪(1)` carrying `sᵢ` to
`φ^* Tᵢ`, and without the inverse construction. The comparison maps on twists are constructed
nowhere in this development — the same gap that
`StacksFrontier/AlgebraicGeometry/AmpleProjectiveImmersion/Basic.lean` records for Tag 01VS.
**No attribute for Tag 01NE is claimed anywhere below**, under the
covering-set rule: the tag's assertions include the representability bijection and the twist
identification, and neither is proved.

**`Stacks.ProjectiveFromSections.GeneratesStalks` is not compared with Mathlib's
`SheafOfModules.GeneratingSections`**; see the sibling file's docstring for what that comparison
needs.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.ProjectiveFromSections

variable {X : Scheme.{u}}

/-- **Restriction of global sections of an open subscheme is restriction of sections of `𝒪_X`**,
through `AlgebraicGeometry.Scheme.Opens.topIso`. One naturality square of Mathlib's
`AlgebraicGeometry.Scheme.restrictFunctorΓ`; see the implementation notes for why it is not a
rewrite. -/
theorem topIso_inv_homOfLE_appTop {U V : X.Opens} (h : U ≤ V) :
    V.topIso.inv ≫ (X.homOfLE h).appTop =
      X.presheaf.map (homOfLE h).op ≫ U.topIso.inv :=
  (X.restrictFunctorΓ.inv.naturality (homOfLE h).op).symm

/-- `topIso_inv_homOfLE_appTop` applied to a section. -/
theorem homOfLE_appTop_topIso_inv {U V : X.Opens} (h : U ≤ V) (a : Γ(X, V)) :
    (X.homOfLE h).appTop (V.topIso.inv a) = U.topIso.inv (resO h a) :=
  CategoryTheory.ConcreteCategory.congr_hom (topIso_inv_homOfLE_appTop h) a

/-! ### The chart families -/

variable {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] {n : ℕ}

/-- The family of ratios `sₖ / sᵢ` on the `i`-th chart, read as global sections of the open
subscheme `X_{sᵢ}`. -/
def chartRatio (s : Fin (n + 1) → Γ(L, ⊤)) (i k : Fin (n + 1)) :
    Γ((nvCover s i).toScheme, ⊤) :=
  (nvCover s i).topIso.inv (ratio s i k)

/-- `sᵢ / sᵢ = 1` on the `i`-th chart. -/
@[simp] theorem chartRatio_self (s : Fin (n + 1) → Γ(L, ⊤)) (i : Fin (n + 1)) :
    chartRatio s i i = 1 := by
  rw [chartRatio, ratio_self]; exact map_one _

/-- **The ratios out of `sᵢ` span the unit ideal** of `Γ(X_{sᵢ}, ⊤)`. This is the hypothesis
Mathlib's construction takes, and it holds here precisely because one of the sections is `1`. -/
theorem span_range_chartRatio (s : Fin (n + 1) → Γ(L, ⊤)) (i : Fin (n + 1)) :
    Ideal.span (Set.range (chartRatio s i)) = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← chartRatio_self s i]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- The transition unit `sⱼ/sᵢ` on the overlap of the `i`-th and `j`-th charts, in the
open-subscheme spelling. -/
def chartTransUnit (s : Fin (n + 1) → Γ(L, ⊤)) (i j : Fin (n + 1)) :
    Γ((nvCover s i ⊓ nvCover s j : X.Opens).toScheme, ⊤)ˣ where
  val := (nvCover s i ⊓ nvCover s j : X.Opens).topIso.inv
    (resO (inf_le_left : nvCover s i ⊓ nvCover s j ≤ nvCover s i) (ratio s i j))
  inv := (nvCover s i ⊓ nvCover s j : X.Opens).topIso.inv
    (resO (inf_le_right : nvCover s i ⊓ nvCover s j ≤ nvCover s j) (ratio s j i))
  val_inv := by
    rw [← map_mul, resO_ratio_mul_resO_ratio]; exact map_one _
  inv_val := by
    rw [← map_mul, mul_comm, resO_ratio_mul_resO_ratio]; exact map_one _

/-- The value of the transition unit, by `rfl`. -/
@[simp] theorem chartTransUnit_val (s : Fin (n + 1) → Γ(L, ⊤)) (i j : Fin (n + 1)) :
    (chartTransUnit s i j : Γ((nvCover s i ⊓ nvCover s j : X.Opens).toScheme, ⊤)) =
      (nvCover s i ⊓ nvCover s j : X.Opens).topIso.inv
        (resO (inf_le_left : nvCover s i ⊓ nvCover s j ≤ nvCover s i) (ratio s i j)) := rfl

/-- **The two chart families differ by the transition unit on the overlap.** This is the glueing
hypothesis of `Stacks.SectionsToProjectiveSpace.exists_hom_of_cover`, and it is the cocycle
identity of the ratios transported to the open-subscheme spelling. -/
theorem chartRatio_agree (s : Fin (n + 1) → Γ(L, ⊤)) (i j : Fin (n + 1)) (k : Fin (n + 1)) :
    Stacks.SectionsToProjectiveSpace.resOfLE
        (inf_le_left : nvCover s i ⊓ nvCover s j ≤ nvCover s i) (chartRatio s i k) =
      (chartTransUnit s i j : Γ((nvCover s i ⊓ nvCover s j : X.Opens).toScheme, ⊤)) *
        Stacks.SectionsToProjectiveSpace.resOfLE
          (inf_le_right : nvCover s i ⊓ nvCover s j ≤ nvCover s j) (chartRatio s j k) := by
  simp only [Stacks.SectionsToProjectiveSpace.resOfLE, chartRatio, chartTransUnit_val,
    homOfLE_appTop_topIso_inv]
  rw [← map_mul, ← ratio_cocycle s inf_le_left inf_le_right k]

/-! ### The morphism of Tag 01NE -/

/-- **Stacks Tag 01NE, the morphism**: a family `s₀, …, sₙ` of global sections of an invertible
`𝒪_X`-module whose nonvanishing opens cover `X` determines a morphism `X ⟶ ℙⁿ_ℤ` restricting on
the `i`-th chart to the morphism of the ratio family `sₖ / sᵢ`. -/
theorem exists_hom_projectiveSpaceAtUniverse
    (hA : Stacks.SectionsToProjectiveSpace.HasPullbackNaturality.{u})
    (hB : Stacks.SectionsToProjectiveSpace.HasUnitInvariance.{u})
    (s : Fin (n + 1) → Γ(L, ⊤)) (hs : IsOpenCover (nvCover s)) :
    ∃ g : X ⟶ projectiveSpaceAtUniverse.{u} n, ∀ i,
      (nvCover s i).ι ≫ g =
        Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (chartRatio s i)
          (span_range_chartRatio s i) :=
  Stacks.SectionsToProjectiveSpace.exists_hom_of_cover hA hB (nvCover s) hs (chartRatio s)
    (span_range_chartRatio s) fun i j => ⟨chartTransUnit s i j, chartRatio_agree s i j⟩

/-- **Stacks Tag 01NE, the morphism, from a generating family of global sections of a nontrivial
invertible sheaf.** The hypothesis is that the germs of the `sᵢ` generate every stalk of `L`,
which is what "the `sᵢ` generate `L`" says. -/
theorem exists_hom_projectiveSpaceAtUniverse_of_generatesStalks
    (hA : Stacks.SectionsToProjectiveSpace.HasPullbackNaturality.{u})
    (hB : Stacks.SectionsToProjectiveSpace.HasUnitInvariance.{u})
    (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s) :
    ∃ g : X ⟶ projectiveSpaceAtUniverse.{u} n, ∀ i,
      (nvCover s i).ι ≫ g =
        Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (chartRatio s i)
          (span_range_chartRatio s i) :=
  exists_hom_projectiveSpaceAtUniverse hA hB s (isOpenCover_nvCover_of_generatesStalks s hs)

/-- **Stacks Tag 01NE over a base scheme.** The morphism of the previous theorem, read as a
morphism to `ℙⁿ_S` lying over `S`. No compatibility has to be checked: `ℙⁿ_S` is a fibre product
over the terminal scheme, which is `Stacks.AmpleProjectiveImmersion.liftOver`. This is the shape
Tag 01VS consumes. -/
theorem exists_hom_projectiveSpaceOver_of_generatesStalks
    (hA : Stacks.SectionsToProjectiveSpace.HasPullbackNaturality.{u})
    (hB : Stacks.SectionsToProjectiveSpace.HasUnitInvariance.{u})
    (s : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s) {S : Scheme.{u}} (f : X ⟶ S) :
    ∃ p : X ⟶ projectiveSpaceOver n S,
      p ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
      ∀ i, (nvCover s i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
        Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (chartRatio s i)
          (span_range_chartRatio s i) := by
  obtain ⟨g, hg⟩ := exists_hom_projectiveSpaceAtUniverse_of_generatesStalks hA hB s hs
  refine ⟨Stacks.AmpleProjectiveImmersion.liftOver f g,
    Stacks.AmpleProjectiveImmersion.liftOver_fst f g, fun i => ?_⟩
  rw [Stacks.AmpleProjectiveImmersion.liftOver_snd f g]
  exact hg i

end Stacks.ProjectiveFromSections

end
