module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartFullGradedGluing
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled

/-!
# The morphism `r_{L, ψ} : U(ψ) ⟶ Proj_S(𝒜)` into a relative Proj

Let `S` be a scheme and `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN), let
`f : X ⟶ S` be a morphism of schemes, `L` an invertible module on `X` and `ψ` a graded map from
`f^*𝒜` to the powers of `L`. **Tag 01O9** produces, on the open `U(ψ) ⊆ X` where `ψ` generates,
a morphism

`r_{L, ψ} : U(ψ) ⟶ Proj_S(𝒜)`

over `S`, together with a homomorphism `θ` of graded `𝒪_{U(ψ)}`-algebras from the pullback of
`⨁_{d ≥ 0} 𝒪(d)` to `⨁_{d ≥ 0} L^{⊗ d}|_{U(ψ)}`, and asserts that the pair is characterized by
three properties:

1. for every open `V ⊆ S` and every `d ≥ 0` the square relating the two readings of `ψ` on
   `𝒜_d(V)` — one into `Γ(f^{-1}(V), L^{⊗ d})`, one into `Γ(π^{-1}(V), 𝒪(d))` followed by `θ`
   and restriction to `f^{-1}(V) ∩ U(ψ)` — commutes;
2. on an open `W ⊆ X` where `ψ|_W` is surjective onto `L^{⊗ d}|_W`, the restriction of
   `r_{L, ψ}` is the morphism `W ⟶ Proj_S(𝒜)` of Definition 27.16.7 (Tag 01O0);
3. for an affine open `V ⊆ S` the restriction of the triple `(U(ψ), r_{L, ψ}, θ)` to
   `U(ψ) ∩ f^{-1}(V)` matches, through the chart `i_V` of Tag 01NQ, the triple
   `(U(ψ'), r_{L, ψ'}, θ')` of Lemma 27.14.1 (**Tag 01NK**) for the induced map
   `ψ' : A = 𝒜(V) → Γ_*(f^{-1}(V), L)`.

The source's proof is: build `(r, θ)` locally on `S` by property (3), and glue, the local pieces
agreeing by the uniqueness in Lemma 27.14.1. "Details omitted."

This file carries out the **affine-local** half of that for the **morphism**. The absolute Lemma
27.14.1 is available as `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued`;
composing it with the chart of Tag 01NQ gives `r_{L, ψ}` over an affine open of the base, and
that composite — with its restriction property, its preimage computation and its uniqueness — is
what the four tagged declarations below state, unconditionally. The glueing of those local
morphisms into a global `r_{L, ψ}` is also carried out, but only from local data that is *given*
rather than derived from a global `(L, ψ)`, and only under a *hypothesis* that the local
morphisms agree on the overlaps; those four declarations therefore carry **no** project tag. See
"The glued morphism of this file" below for what that glueing does and does not say, and for
where the global `r_{L, ψ}` of a global datum is delivered instead.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjFromSections.relativeChart`: **the morphism `r_{L, ψ}`
  over an affine open `V` of the base**, the morphism of Tag 01NK for the graded ring
  `A = 𝒜(V)` read into `Proj_S(𝒜)` through the chart of Tag 01NQ.
* `Stacks.AlgebraicGeometry.RelativeProjFromSections.localOpen` and `localChart`: the member
  `U(ψ) ∩ f^{-1}(V_i)` of the cover of `U(ψ)`, as an open of `X`, and `relativeChart` read on
  it.
* `Stacks.AlgebraicGeometry.RelativeProjFromSections.totalCover`: the cover of
  `U(ψ) = ⨆_i (U(ψ) ∩ f^{-1}(V_i))` by its members.
* `Stacks.AlgebraicGeometry.RelativeProjFromSections.glued`: the morphism
  `⨆_i (U(ψ_i) ∩ f^{-1}(V_i)) ⟶ Proj_S(𝒜)` glued from the local ones. **Conditional, and
  untagged**; see below.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjFromSections.chartIsOpenImmersion`: a chart of the
  relative Proj is an open immersion, being the base change of the inclusion of its affine open.
* `Stacks.AlgebraicGeometry.RelativeProjFromSections.homOfLE_relativeChart_of_pos`: over an
  affine open of the base, `r_{L, ψ}` restricts on each `T_{ψ(g)}` to the dehomogenisation chart
  of `g` followed by the chart of Tag 01NQ.
* `Stacks.AlgebraicGeometry.RelativeProjFromSections.preimage_image_basicOpen_relativeChart`:
  the preimage under `r_{L, ψ}` of the standard open `D₊(g)`, read inside `Proj_S(𝒜)` through
  the chart, is `T_{ψ(g)}` (Tag 01NK's preimage computation, through the chart).
* `Stacks.AlgebraicGeometry.RelativeProjFromSections.eq_relativeChart_of_homOfLE_eq`: over an
  affine open of the base, `r_{L, ψ}` is the unique morphism restricting that way.
* `Stacks.AlgebraicGeometry.RelativeProjFromSections.relativeChart_comp_toBase`: **`r_{L, ψ}` is
  a morphism over the base**, over an affine open `V` of it: composed with the structure
  morphism of `Proj_S(𝒜)` it is Tag 01NK's morphism followed by the structure morphism of the
  chart and the inclusion of `V`. Its set-theoretic reading is
  `Stacks.AlgebraicGeometry.RelativeProjFromSections.toBase_base_relativeChart_mem`, and
  `localChart_comp_toBase` and `homOfLE_glued_comp_toBase` are the same statement for the local
  pieces and for the glued morphism.
* `Stacks.AlgebraicGeometry.RelativeProjFromSections.homOfLE_glued` and
  `eq_glued_of_homOfLE_eq`, `existsUnique_glued`: the glued morphism exists and is the unique one
  restricting over each member of the cover to the local morphism. **Conditional, and untagged**;
  see below.

## The glued morphism of this file

`glued`, `homOfLE_glued`, `eq_glued_of_homOfLE_eq` and `existsUnique_glued` glue local triples
indexed by a family of affine opens of the base, and take the agreement of the local morphisms on
the overlaps, `hagree`, as an argument; for unrelated local triples that agreement is false, so
they are a glueing step at that shape, not the tag. The morphism `r_{ℒ,ψ}` of a global datum is
`…RelativeProjInvertibleMorphism.GradedPowerMap.globalMorphism`, glued over the preimages of the
affine opens of the base with no overlap condition, and the whole statement of
[Stacks, Tag 01O9] is `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.tag01O9`.

## Implementation notes

The cover and the glued morphism are introduced as named definitions, and the cover's structure
maps are identified with the inclusions of opens by `totalCover_f`, which holds by `rfl`. Doing
the glueing inline instead — applying `AlgebraicGeometry.Scheme.Cover.glueMorphisms` to
`AlgebraicGeometry.Scheme.Opens.iSupOpenCover` at the point of use — makes the unifier unfold
the image opens `(f^{-1}(V_i)).ι ''ᵁ U(ψ_i)` while matching the cover's `X` and `f` fields, and
does not terminate within the default heartbeat budget. The same discipline is what the library's
Tag 01NK uses for its own cover.

A local piece is `(f^{-1}(V_i)).ι ''ᵁ U(ψ_i)`, the image in `X` of the open `U(ψ_i)` of
`f^{-1}(V_i)`, and `localChart` is `relativeChart` precomposed with
`AlgebraicGeometry.Scheme.Hom.isoImage`, the canonical isomorphism of an open of an open with
its image. That is what puts the local morphisms, which are defined on opens of different
schemes, on opens of the one scheme `X` so that they can be glued.

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O0](https://stacks.math.columbia.edu/tag/01O0)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 0D2Y](https://stacks.math.columbia.edu/tag/0D2Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.ProjChartFullGraded
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u v

namespace Stacks.AlgebraicGeometry.RelativeProjFromSections

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### The morphism over one affine open of the base -/

section Affine

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S} (rp : RelativeProjData A)
  (V : S.Opens) (hV : IsAffineOpen V) {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections (A.grading V) L)

/-- A chart of the relative homogeneous spectrum is an open immersion: by Tag 01NQ it is the
base change of the inclusion `V ⊆ S` of its affine open along the structure morphism, and open
immersions are stable under base change. -/
instance chartIsOpenImmersion : IsOpenImmersion (rp.chart V hV) :=
  MorphismProperty.of_isPullback (rp.chart_isPullback V hV).flip (P := @IsOpenImmersion)
    (by infer_instance)

/-- **Stacks Project, Tag 01O9, over an affine open `V` of the base.** The morphism
`r_{L, ψ'} : U(ψ') ⟶ Proj_S(𝒜)` attached to a Tag 01NK datum `ψ'` for the graded ring
`A = 𝒜(V)` of homogeneous sections over `V`: the morphism `U(ψ') ⟶ Proj A` of Tag 01NK followed
by the chart of `Proj_S(𝒜)` over `V` of Tag 01NQ.

This is the "via `i_V`" of clause (3): the local morphism of the tag is the one of Tag 01NK read
inside the relative homogeneous spectrum. -/
def relativeChart : ψ.coveringOpen.toScheme ⟶ rp.scheme := ψ.glued ≫ rp.chart V hV

/-- **`r_{L, ψ'}` restricts on each `T_{ψ'(g)}` to the dehomogenisation chart of `g` followed by
the chart of the relative Proj**, for every homogeneous `g` of positive degree. This is the Tag
01NK restriction property, `GradedSections.homOfLE_glued_of_pos`, whiskered by the chart. -/
theorem homOfLE_relativeChart_of_pos {e : ℕ} {g : A.sectionRing V} (hg : g ∈ A.grading V e)
    (he : 0 < e) :
    T.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen_of_pos hg he) ≫ relativeChart rp V hV ψ
      = ψ.chartToProj hg
          (le_refl (nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨g, hg⟩))) he
        ≫ rp.chart V hV := by
  rw [relativeChart, ← Category.assoc, ψ.homOfLE_glued_of_pos hg he]

/-- **Tag 01NK's preimage computation, read through the chart of Tag 01NQ.** The preimage
under `r_{L, ψ'}` of the standard open `D₊(g)` of `Proj A`, read inside `Proj_S(𝒜)` as its image
under the chart over `V`, is the nonvanishing open `T_{ψ'(g)}`.

This is the Tag 01NK preimage computation `GradedSections.preimage_basicOpen_glued` together
with the fact that the chart is an open immersion, so that taking the preimage of its image of
an open gives that open back. -/
theorem preimage_image_basicOpen_relativeChart {e : ℕ} {g : A.sectionRing V}
    (hg : g ∈ A.grading V e) (he : 0 < e) :
    relativeChart rp V hV ψ ⁻¹ᵁ
        (rp.chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g)
      = ψ.coveringOpen.ι ⁻¹ᵁ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨g, hg⟩) := by
  rw [relativeChart, Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq,
    ψ.preimage_basicOpen_glued hg he]

/-- **Over an affine open of the base, `r_{L, ψ'}` is the unique morphism to `Proj_S(𝒜)` whose
restriction to each `T_{ψ'(g)}` is the dehomogenisation chart of `g` followed by the chart of
the relative Proj.** With `homOfLE_relativeChart_of_pos` this characterizes it, and it is the
uniqueness the source uses to glue the local pieces. -/
theorem eq_relativeChart_of_homOfLE_eq {Φ : ψ.coveringOpen.toScheme ⟶ rp.scheme}
    (h : ∀ (e : ℕ) (g : A.sectionRing V) (hg : g ∈ A.grading V e) (he : 0 < e),
      T.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen_of_pos hg he) ≫ Φ
        = ψ.chartToProj hg
            (le_refl (nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨g, hg⟩))) he
          ≫ rp.chart V hV) :
    Φ = relativeChart rp V hV ψ :=
  ψ.hom_ext_of_homOfLE_eq fun e g =>
    (h (e + 1) (g : A.sectionRing V) g.2 (Nat.succ_pos e)).trans
      (homOfLE_relativeChart_of_pos rp V hV ψ g.2 (Nat.succ_pos e)).symm

/-- **Stacks Project, Tag 01O9: `r_{L, ψ'}` is a morphism over the base.** The tag calls
`r_{ℒ, ψ}` a morphism of schemes *over* `S`; over an affine open `V` of the base that says the
triangle below commutes, the structure morphism of the source being the one Tag 01NK's morphism
carries, namely `U(ψ') ⟶ Proj A ⟶ V ⊆ S`.

The chart of Tag 01NQ is cartesian over its affine open — that is
`Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData.chart_isPullback` — so the square it
sits in already says that the chart composed with the structure morphism of `Proj_S(𝒜)` is the
structure morphism of the absolute `Proj` followed by the inclusion of `V`. Composing with Tag
01NK's morphism gives the statement, and that is the whole proof.

Here `T` is an arbitrary scheme carrying an invertible module, with no morphism `T ⟶ S` in the
data; for the datum of a global `(ℒ, ψ)` on `f : X ⟶ S` the composite is `f` restricted to
`U(ψ)`, which is `…RelativeProjInvertibleMorphism.GradedPowerMap.globalMorphism_comp_toBase`. -/
theorem relativeChart_comp_toBase :
    relativeChart rp V hV ψ ≫ rp.toBase
      = ψ.glued ≫ projInclusionToOpen A V hV ≫ V.ι := by
  rw [relativeChart, Category.assoc, (rp.chart_isPullback V hV).w]

/-- **The image of `r_{L, ψ'}` lies over `V`.** The set-theoretic reading of
`relativeChart_comp_toBase`: every point of `U(ψ')` is sent by `r_{L, ψ'}` to a point of
`Proj_S(𝒜)` lying over the affine open `V` of the base. -/
theorem toBase_base_relativeChart_mem (t : ψ.coveringOpen.toScheme) :
    rp.toBase.base ((relativeChart rp V hV ψ).base t) ∈ V := by
  have h : rp.toBase.base ((relativeChart rp V hV ψ).base t)
      = (ψ.glued ≫ projInclusionToOpen A V hV ≫ V.ι).base t := by
    rw [← relativeChart_comp_toBase rp V hV ψ]; rfl
  rw [h]
  exact ((projInclusionToOpen A V hV).base (ψ.glued.base t)).2

end Affine

/-! ### The global morphism, glued over the base -/

section Glue

variable {S X : Scheme.{u}} {A : SheafGradedAlgebra S} (rp : RelativeProjData A) (f : X ⟶ S)
  {ι : Type v} (V : ι → S.Opens) (hV : ∀ i, IsAffineOpen (V i))
  (L : ∀ i, (f ⁻¹ᵁ V i).toScheme.Modules)
  [∀ i, Stacks.Ample.IsInvertibleModule (f ⁻¹ᵁ V i).toScheme (L i)]
  (ψ : ∀ i, GradedSections (A.grading (V i)) (L i))

/-- The member `U(ψ) ∩ f^{-1}(V_i)` of the cover of `U(ψ)`, as an open of `X`: the image in `X`
of the open `U(ψ_i)` of `f^{-1}(V_i)` on which the local datum `ψ_i` generates. -/
def localOpen (i : ι) : X.Opens := (f ⁻¹ᵁ V i).ι ''ᵁ (ψ i).coveringOpen

/-- The local morphism `U(ψ) ∩ f^{-1}(V_i) ⟶ Proj_S(𝒜)`: the morphism `relativeChart` of the
datum `ψ_i`, read on the image open through the canonical isomorphism of an open of an open with
its image. -/
def localChart (i : ι) : (localOpen f V L ψ i).toScheme ⟶ rp.scheme :=
  ((f ⁻¹ᵁ V i).ι.isoImage (ψ i).coveringOpen).inv ≫ relativeChart rp (V i) (hV i) (ψ i)

/-- **Each local piece of `r_{L, ψ}` lies over its affine open of the base.** This is
`relativeChart_comp_toBase` read on the image open; unlike `glued` it needs no agreement
hypothesis. It carries no project tag for the same reason `localChart` does not: the local
triples are given rather than obtained by restricting one global pair. -/
theorem localChart_comp_toBase (i : ι) :
    localChart rp f V hV L ψ i ≫ rp.toBase
      = ((f ⁻¹ᵁ V i).ι.isoImage (ψ i).coveringOpen).inv ≫ (ψ i).glued
          ≫ projInclusionToOpen A (V i) (hV i) ≫ (V i).ι :=
  (Category.assoc _ _ _).trans
    (congrArg (fun k => ((f ⁻¹ᵁ V i).ι.isoImage (ψ i).coveringOpen).inv ≫ k)
      (relativeChart_comp_toBase rp (V i) (hV i) (ψ i)))

/-- The cover of `U(ψ) = ⨆_i (U(ψ) ∩ f^{-1}(V_i))` by its members. -/
def totalCover : (⨆ i, localOpen f V L ψ i).toScheme.OpenCover :=
  Scheme.Opens.iSupOpenCover (localOpen f V L ψ)

/-- The `i`-th member map of `totalCover` is the inclusion of `U(ψ) ∩ f^{-1}(V_i)` into
`⨆_i (U(ψ) ∩ f^{-1}(V_i))`. -/
@[simp] theorem totalCover_f (i : ι) :
    (totalCover f V L ψ).f i = X.homOfLE (le_iSup (localOpen f V L ψ) i) := rfl

/-- The morphism `⨆_i (U(ψ_i) ∩ f^{-1}(V_i)) ⟶ Proj_S(𝒜)` glued from the local morphisms of the
members of the cover.

The local morphisms are the ones of Tag 01NK read into the relative homogeneous spectrum, which
is clause (3) of Tag 01O9. **This is not a delivery of Tag 01O9 and carries no project tag**:
the local triples `(V i, hV i, L i, ψ i)` are given rather than obtained by restricting one
global pair `(L, ψ)`, so they are unrelated to one another, and their agreement on the overlaps
is the hypothesis `hagree` rather than a consequence. The source obtains that agreement from the
uniqueness in Lemma 27.14.1 together with the compatibility of the local triples under
restriction of the base; for the local triples a global `(ℒ, ψ)` induces it is obtained in
`Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap.globalMorphism`, which
needs no agreement hypothesis. -/
def glued
    (hagree : ∀ i j, pullback.fst ((totalCover f V L ψ).f i) ((totalCover f V L ψ).f j)
          ≫ localChart rp f V hV L ψ i
        = pullback.snd _ _ ≫ localChart rp f V hV L ψ j) :
    (⨆ i, localOpen f V L ψ i).toScheme ⟶ rp.scheme :=
  (totalCover f V L ψ).glueMorphisms (localChart rp f V hV L ψ) hagree

/-- **`glued` restricts over each member of the cover to the local morphism there.** Conditional
on the same carried data and the same hypothesis `hagree` as `glued`, and so carrying no project
tag for the same reason. -/
theorem homOfLE_glued
    (hagree : ∀ i j, pullback.fst ((totalCover f V L ψ).f i) ((totalCover f V L ψ).f j)
          ≫ localChart rp f V hV L ψ i
        = pullback.snd _ _ ≫ localChart rp f V hV L ψ j) (i : ι) :
    X.homOfLE (le_iSup (localOpen f V L ψ) i) ≫ glued rp f V hV L ψ hagree
      = localChart rp f V hV L ψ i :=
  Scheme.Cover.ι_glueMorphisms (totalCover f V L ψ) _ _ i

/-- **The glued morphism lies over the base, member by member.** Over each member of the cover
the composite of `glued` with the structure morphism of `Proj_S(𝒜)` is the local structure
morphism of `localChart_comp_toBase`. Conditional on the same carried data and the same
hypothesis `hagree` as `glued`, and so carrying no project tag. -/
theorem homOfLE_glued_comp_toBase
    (hagree : ∀ i j, pullback.fst ((totalCover f V L ψ).f i) ((totalCover f V L ψ).f j)
          ≫ localChart rp f V hV L ψ i
        = pullback.snd _ _ ≫ localChart rp f V hV L ψ j) (i : ι) :
    X.homOfLE (le_iSup (localOpen f V L ψ) i) ≫ glued rp f V hV L ψ hagree ≫ rp.toBase
      = ((f ⁻¹ᵁ V i).ι.isoImage (ψ i).coveringOpen).inv ≫ (ψ i).glued
          ≫ projInclusionToOpen A (V i) (hV i) ≫ (V i).ι :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ rp.toBase) (homOfLE_glued rp f V hV L ψ hagree i)).trans
      (localChart_comp_toBase rp f V hV L ψ i))

/-- **`glued` is the unique morphism restricting over each member of the cover to the local
morphism there.** With `homOfLE_glued` this characterizes it. Conditional on the same carried
data and the same hypothesis `hagree` as `glued`, and so carrying no project tag. -/
theorem eq_glued_of_homOfLE_eq
    (hagree : ∀ i j, pullback.fst ((totalCover f V L ψ).f i) ((totalCover f V L ψ).f j)
          ≫ localChart rp f V hV L ψ i
        = pullback.snd _ _ ≫ localChart rp f V hV L ψ j)
    {R : (⨆ i, localOpen f V L ψ i).toScheme ⟶ rp.scheme}
    (hR : ∀ i, X.homOfLE (le_iSup (localOpen f V L ψ) i) ≫ R = localChart rp f V hV L ψ i) :
    R = glued rp f V hV L ψ hagree :=
  (totalCover f V L ψ).hom_ext _ _ fun i =>
    (hR i).trans (homOfLE_glued rp f V hV L ψ hagree i).symm

/-- **Existence and uniqueness, in one statement.** There is exactly one morphism
`⨆_i (U(ψ_i) ∩ f^{-1}(V_i)) ⟶ Proj_S(𝒜)` whose restriction over each member of the cover is the
local morphism of Tag 01NK read through the chart of Tag 01NQ. Conditional on the same carried
data and the same hypothesis `hagree` as `glued`, and so carrying no project tag. -/
theorem existsUnique_glued
    (hagree : ∀ i j, pullback.fst ((totalCover f V L ψ).f i) ((totalCover f V L ψ).f j)
          ≫ localChart rp f V hV L ψ i
        = pullback.snd _ _ ≫ localChart rp f V hV L ψ j) :
    ∃! R : (⨆ i, localOpen f V L ψ i).toScheme ⟶ rp.scheme,
      ∀ i, X.homOfLE (le_iSup (localOpen f V L ψ) i) ≫ R = localChart rp f V hV L ψ i :=
  ⟨glued rp f V hV L ψ hagree, homOfLE_glued rp f V hV L ψ hagree,
    fun _ hR => eq_glued_of_homOfLE_eq rp f V hV L ψ hagree hR⟩

end Glue

end Stacks.AlgebraicGeometry.RelativeProjFromSections

end
