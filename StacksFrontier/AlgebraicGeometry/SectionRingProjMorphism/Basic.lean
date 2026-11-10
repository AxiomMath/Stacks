module

public import StacksFrontier.AlgebraicGeometry.SectionRingChartOpen.Overlap

/-!
# The canonical morphism to `Proj` of the section ring: Stacks Tag 01PZ

Let `X` be a scheme and `L` an invertible `𝒪_X`-module, and let
`S = Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L ^⊗ n)` be the graded section ring of Stacks Tag 01CV. Stacks
Tag 01PZ constructs the canonical morphism of schemes to `Proj S`, characterised by: for every
homogeneous `a ∈ S` of positive degree, the preimage of the chart `D₊(a)` is the nonvanishing
open `X_a`, and on that open the morphism is the chart determined by the degree-zero part of the
localization of `S` at `a`.

**The morphism is defined on the open `⋃_a X_a`, not on `X`.** That is where the construction
lives: the charts cover `⋃_a X_a` and nothing more, and no hypothesis on `L` is needed to glue
them. Ampleness of `L` is exactly the statement that this open is all of `X`
(`Stacks.SectionRingProjMorphism.nvUnion_eq_top_of_isAmple`), and
`Stacks.SectionRingProjMorphism.projHomOfIsAmple` is the resulting morphism `X ⟶ Proj S`.

## Main definitions

* `Stacks.SectionRingProjMorphism.PosSection`: a homogeneous element of `Γ_*(X, L)` of positive
  degree, bundled with its degree. This is the index of the cover.
* `Stacks.SectionRingProjMorphism.nvUnion`: the open `⋃_a X_a` the morphism is defined on.
* `Stacks.SectionRingProjMorphism.projHom`: **the canonical morphism
  `⋃_a X_a ⟶ Proj Γ_*(X, L)` of Stacks Tag 01PZ.**
* `Stacks.SectionRingProjMorphism.projHomOfCovers`: the same morphism with source `X`, under
  clause (a) of Stacks Tag 01PZ — that the `X_a` cover `X`.
* `Stacks.SectionRingProjMorphism.projHomOfIsAmple`: that morphism for `L` ample, ampleness being
  one way of knowing clause (a).

## Main results

* `Stacks.SectionRingProjMorphism.homOfLE_projHom`: **on `X_a` the morphism is the chart at
  `a`**, which is the second half of the characterisation of Stacks Tag 01PZ; it is
  `AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms` for this cover.
* `Stacks.SectionRingProjMorphism.projHom_preimage_projBasicOpen` and
  `image_projHom_preimage_projBasicOpen`: **clause (1) of Stacks Tag 01PZ**, that the preimage of
  `D₊(a)` is `X_a`, in the two shapes available on an open subscheme — as an open of `⋃_a X_a`
  and as its image in `X`.
* `Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen`: clause (1) read on
  all of `X`, for `L` ample.

## Implementation notes

**The cover is indexed by *every* homogeneous element of positive degree**, so clause (1) comes
out at every such element directly, with no propagation step: the identity is checked on the
pieces of the cover, and every piece is an `X_b`. The multiplicative propagation of
`StacksFrontier/AlgebraicGeometry/SectionRingProjOverlap/Basic.lean`
(`preimage_projBasicOpen_eq_nvOpen_mul`, `preimage_projBasicOpen_eq_nvOpen_powSec`) is therefore
not needed here; what *is* spent from that file is the `D₊` dictionary itself, through the
sibling `StacksFrontier/AlgebraicGeometry/SectionRingChartOpen/Overlap.lean`.

**No existence statement is ever used to choose data.** The cover is the family of *all*
positive-degree homogeneous elements, a genuine index type, and ampleness enters only as the
proposition `⋃_a X_a = ⊤`, proved from
`Stacks.SectionExtension.exists_pos_affine_nvOpen` pointwise.

**The gluing is Mathlib's.** `AlgebraicGeometry.Scheme.Opens.iSupOpenCover` is the cover of
`⋃ Uᵢ` by the `Uᵢ`, `AlgebraicGeometry.isPullback_opens_inf_le` identifies the pullback of two of
its legs with the intersection, and `AlgebraicGeometry.Scheme.Cover.glueMorphisms` does the
gluing — the same route `AlgebraicGeometry.Proj.fromOfGlobalSections` takes.

## References

* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)

## What is not done

**Clauses (2), (3) and (4) of Stacks Tag 01PZ are not here.** Clauses (2) and (3) — the maps
`f^*𝒪_Y(n) ⟶ L^{⊗ n}` and the fact that `S_n ⟶ Γ(Y, 𝒪_Y(n)) ⟶ Γ(X, L^{⊗ n})` is the identity —
are in the sibling `StacksFrontier/AlgebraicGeometry/SectionRingProjMorphism/Theta.lean`, where they
are read off the triple of Stacks Tag 01NK at the identity map of `Γ_*(X, L)`; that file's
`Stacks.SectionRingProjMorphism.Theta.homOfLE_projHom_eq_glued` identifies the morphism below with
the Tag 01NK morphism they are stated at. Clause (4), the local invertibility of
`f^*𝒪_Y(dn) ⟶ L^{⊗ dn}` for all `n ∈ ℤ`, is in
`StacksFrontier/AlgebraicGeometry/SectionRingProjMorphism/ThetaIso.lean`
(`Stacks.SectionRingProjMorphism.Theta.exists_isIso_pullback_projTheta_app_intMul`).

**Nothing is claimed about the morphism being an open immersion, or an isomorphism onto its
image.** That is Stacks Tag 01Q1, which additionally needs `L` ample and the surjectivity half of
Stacks Tag 01PW; no attribute for it is written here. Neither is the morphism compared with the
relative construction of `AlgebraicGeometry.Proj.fromOfGlobalSections`, and nothing is said about
its behaviour over `Spec Γ(X, 𝒪_X)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.GradedSections (powSections)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)

universe u

namespace Stacks.SectionRingProjMorphism

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-! ### The index of the cover -/

/-- A homogeneous element of the section ring `Γ_*(X, L)` of **positive** degree, bundled with its
degree. These index the charts of Stacks Tag 01PZ: each one contributes the open `X_a` and the
morphism `X_a ⟶ Proj Γ_*(X, L)` of `Stacks.SectionRingChartMap.chartHom`. -/
public structure PosSection (L : X.Modules) where
  /-- The degree. -/
  deg : ℕ
  /-- The degree is positive, which is what makes the chart `D₊(a)` affine. -/
  deg_pos : 0 < deg
  /-- The homogeneous element itself, as a global section of `L ^⊗ deg`. -/
  val : powSections L deg

/-- **The open on which the canonical morphism of Stacks Tag 01PZ is defined**: the union of the
nonvanishing opens `X_a` of the homogeneous elements of positive degree. It is all of `X` exactly
when the `X_a` cover `X`, which is the case for `L` ample
(`Stacks.SectionRingProjMorphism.nvUnion_eq_top_of_isAmple`). -/
public noncomputable abbrev nvUnion : X.Opens := ⨆ c : PosSection L, nvOpen L c.val

/-- Each `X_a` sits inside the union. -/
public theorem nvOpen_le_nvUnion {d : ℕ} (a : powSections L d) (hd : 0 < d) :
    nvOpen L a ≤ nvUnion L :=
  le_iSup (fun c : PosSection L ↦ nvOpen L c.val) ⟨d, hd, a⟩

/-- The cover of the union by the `X_a`. -/
public noncomputable abbrev nvCover : (nvUnion L).toScheme.OpenCover :=
  Scheme.Opens.iSupOpenCover (fun c : PosSection L ↦ nvOpen L c.val)

/-! ### Opens of a union are determined on the pieces -/

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- Membership in an open of `⋃ Uᵢ` is membership in its preimage on a piece containing the
point. -/
private theorem mem_iff_mem_preimage_homOfLE {J : Type*} {U : J → X.Opens}
    (W : TopologicalSpace.Opens ↥(⨆ i, U i)) (i : J) {x : ↥(⨆ i, U i)} (hi : x.1 ∈ U i) :
    x ∈ W ↔ (⟨x.1, hi⟩ : ↥(U i)) ∈ X.homOfLE (le_iSup U i) ⁻¹ᵁ W := by
  have hx : X.homOfLE (le_iSup U i) (⟨x.1, hi⟩ : ↥(U i)) = x := Subtype.ext (by simp)
  exact iff_of_eq (congrArg (· ∈ W) hx).symm

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- **Two opens of `⋃ Uᵢ` with the same preimage on every piece are equal.** -/
private theorem opens_ext_of_preimage_homOfLE {J : Type*} {U : J → X.Opens}
    {W₁ W₂ : TopologicalSpace.Opens ↥(⨆ i, U i)}
    (h : ∀ i, X.homOfLE (le_iSup U i) ⁻¹ᵁ W₁ = X.homOfLE (le_iSup U i) ⁻¹ᵁ W₂) :
    W₁ = W₂ := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x ↦ ?_)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp x.2
  refine (mem_iff_mem_preimage_homOfLE W₁ i hi).trans ?_
  rw [h i]
  exact (mem_iff_mem_preimage_homOfLE W₂ i hi).symm

/-! ### The canonical morphism -/

/-- **The canonical morphism `⋃ X_a ⟶ Proj Γ_*(X, L)` of Stacks Tag 01PZ.** It is glued from the
charts `Stacks.SectionRingChartMap.chartHom` over the cover of `⋃ X_a` by the nonvanishing opens
of the homogeneous elements of positive degree; the overlap condition is
`Stacks.SectionRingChartOpen.chartHomOn_eq`, which says that the chart at `a` and the chart at `b`
agree on `X_a ∩ X_b`.

For `L` ample the source is all of `X` (`Stacks.SectionRingProjMorphism.projHomOfIsAmple`); in
general `⋃ X_a` is the largest open on which the construction makes sense, and that is where the
Stacks project's statement puts it as well. -/
@[stacks 01PZ]
public noncomputable def projHom : (nvUnion L).toScheme ⟶ Proj (grading L) :=
  (nvCover L).glueMorphisms
    (fun c ↦ (Stacks.SectionRingChartOpen.chartHomOn L c.val c.deg_pos
      (le_refl (nvOpen L c.val))).1)
    fun c c' ↦ by
      have hc : nvOpen L c.val ≤ nvUnion L := le_iSup (fun i : PosSection L ↦ nvOpen L i.val) c
      have hc' : nvOpen L c'.val ≤ nvUnion L := le_iSup (fun i : PosSection L ↦ nvOpen L i.val) c'
      have hpb := isPullback_opens_inf_le hc hc'
      refine (cancel_epi hpb.isoPullback.hom).mp ?_
      change hpb.isoPullback.hom ≫
            Limits.pullback.fst (X.homOfLE hc) (X.homOfLE hc') ≫ _
          = hpb.isoPullback.hom ≫ Limits.pullback.snd (X.homOfLE hc) (X.homOfLE hc') ≫ _
      rw [← Category.assoc, ← Category.assoc, hpb.isoPullback_hom_fst, hpb.isoPullback_hom_snd,
        Stacks.SectionRingChartOpen.homOfLE_chartHomOn L c.val c.deg_pos
          (le_refl (nvOpen L c.val)) inf_le_left inf_le_left,
        Stacks.SectionRingChartOpen.homOfLE_chartHomOn L c'.val c'.deg_pos
          (le_refl (nvOpen L c'.val)) inf_le_right inf_le_right]
      exact Stacks.SectionRingChartOpen.chartHomOn_eq L c.val c'.val c.deg_pos c'.deg_pos
        inf_le_left inf_le_right

/-- **On `X_a` the canonical morphism is the chart at `a`.** This is the second half of the
characterisation of the morphism of Stacks Tag 01PZ, not one of the tag's numbered clauses. For
`a` homogeneous of positive degree, the restriction of the canonical morphism to `X_a` is the
morphism `X_a ⟶ Proj Γ_*(X, L)` determined by the degree-zero part of the localization of
`Γ_*(X, L)` at `a`, namely `Stacks.SectionRingChartMap.chartHom`. -/
@[stacks 01PZ "the restriction to a nonvanishing open is the chart"]
public theorem homOfLE_projHom {d : ℕ} (a : powSections L d) (hd : 0 < d) :
    X.homOfLE (nvOpen_le_nvUnion L a hd) ≫ projHom L
      = Stacks.SectionRingChartMap.chartHom L a hd :=
  (nvCover L).ι_glueMorphisms _ _ ⟨d, hd, a⟩

/-- **Clause (1) of Stacks Tag 01PZ: the preimage of a basic open.** For every homogeneous element
`a` of `Γ_*(X, L)` of positive degree, the canonical morphism pulls the chart `D₊(a)` of
`Proj Γ_*(X, L)` back to the nonvanishing open `X_a`.

The identity is checked on the cover: on the piece `X_b` the composite is the chart at `b`, and
`Stacks.SectionRingChartOpen.chartHomOn_preimage_projBasicOpen` computes its preimage of `D₊(a)`
as `X_b ∩ X_a`, which is also what the right-hand side restricts to. -/
@[stacks 01PZ "the preimage of a basic open"]
public theorem projHom_preimage_projBasicOpen {d : ℕ} (a : powSections L d) (hd : 0 < d) :
    projHom L ⁻¹ᵁ Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a)
      = (nvUnion L).ι ⁻¹ᵁ nvOpen L a := by
  refine opens_ext_of_preimage_homOfLE fun c ↦ ?_
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι]
  change (X.homOfLE (nvOpen_le_nvUnion L c.val c.deg_pos) ≫ projHom L) ⁻¹ᵁ _ = _
  rw [homOfLE_projHom L c.val c.deg_pos,
    ← Stacks.SectionRingChartOpen.chartHomOn_self L c.val c.deg_pos,
    Stacks.SectionRingChartOpen.chartHomOn_preimage_projBasicOpen L c.val c.deg_pos
      (le_refl (nvOpen L c.val)) a hd]

/-- **Clause (1) of Stacks Tag 01PZ, read as an open of `X`.** The image in `X` of the preimage of
`D₊(a)` is the nonvanishing open `X_a` itself, which is the shape the Stacks project's statement
takes. -/
@[stacks 01PZ "the preimage of a basic open, as an open of X"]
public theorem image_projHom_preimage_projBasicOpen {d : ℕ} (a : powSections L d) (hd : 0 < d) :
    (nvUnion L).ι ''ᵁ
        (projHom L ⁻¹ᵁ Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a))
      = nvOpen L a := by
  rw [projHom_preimage_projBasicOpen L a hd, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr (nvOpen_le_nvUnion L a hd)

/-! ### Under ampleness the morphism is defined on all of `X` -/

/-- **For `L` ample the nonvanishing opens of the homogeneous elements of positive degree cover
`X`.** This is `Stacks.SectionExtension.exists_pos_affine_nvOpen`, which is ampleness read in the
section ring's vocabulary. -/
public theorem nvUnion_eq_top_of_isAmple (hL : Stacks.Ample.IsAmple X L) : nvUnion L = ⊤ :=
  le_antisymm le_top fun x _ ↦ by
    obtain ⟨d, b, hd, hx, -⟩ := Stacks.SectionExtension.exists_pos_affine_nvOpen L hL x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨d, hd, b⟩, hx⟩

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- The inclusion of an open equal to `⊤`, read from `X`, is the identity. -/
private theorem topIso_inv_isoOfEq_inv_ι {U : X.Opens} (h : U = ⊤) :
    (Scheme.topIso X).inv ≫ (X.isoOfEq h).inv ≫ U.ι = 𝟙 X := by
  have hι : (X.isoOfEq h).inv ≫ U.ι = (⊤ : X.Opens).ι := by
    rw [Iso.inv_comp_eq, Scheme.isoOfEq_hom_ι]
  rw [hι, ← Scheme.topIso_hom, Iso.inv_hom_id]

/-- **The canonical morphism `X ⟶ Proj Γ_*(X, L)` of Stacks Tag 01PZ.** The hypothesis is exactly
clause (a) of Stacks Tag 01PZ — every point of `X` lies in `X_s` for some homogeneous `s ∈ S_+`,
that is, the open `⋃ X_a` of `Stacks.SectionRingProjMorphism.projHom` is the whole of `X` — and
nothing more. Ampleness is not needed:
`Stacks.SectionRingProjMorphism.projHomOfIsAmple` is this morphism at the proof
`Stacks.SectionRingProjMorphism.nvUnion_eq_top_of_isAmple` of that hypothesis. -/
public noncomputable def projHomOfCovers (h : nvUnion L = ⊤) : X ⟶ Proj (grading L) :=
  (Scheme.topIso X).inv ≫ (X.isoOfEq h).inv ≫ projHom L

/-- **Clause (1) of Stacks Tag 01PZ on all of `X`, under clause (a) of that tag alone.** -/
public theorem projHomOfCovers_preimage_projBasicOpen (h : nvUnion L = ⊤) {d : ℕ}
    (a : powSections L d) (hd : 0 < d) :
    projHomOfCovers L h ⁻¹ᵁ Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a)
      = nvOpen L a := by
  rw [projHomOfCovers, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    projHom_preimage_projBasicOpen L a hd, ← Scheme.Hom.comp_preimage,
    ← Scheme.Hom.comp_preimage, Category.assoc, topIso_inv_isoOfEq_inv_ι,
    Scheme.Hom.id_preimage]

/-- **The canonical morphism `X ⟶ Proj Γ_*(X, L)` for `L` ample.** Ampleness is exactly what makes
the open `⋃ X_a` of `Stacks.SectionRingProjMorphism.projHom` the whole of `X`. -/
public noncomputable def projHomOfIsAmple (hL : Stacks.Ample.IsAmple X L) :
    X ⟶ Proj (grading L) :=
  projHomOfCovers L (nvUnion_eq_top_of_isAmple L hL)

/-- **Clause (1) of Stacks Tag 01PZ on all of `X`, for `L` ample.** -/
public theorem projHomOfIsAmple_preimage_projBasicOpen (hL : Stacks.Ample.IsAmple X L) {d : ℕ}
    (a : powSections L d) (hd : 0 < d) :
    projHomOfIsAmple L hL ⁻¹ᵁ Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a)
      = nvOpen L a :=
  projHomOfCovers_preimage_projBasicOpen L (nvUnion_eq_top_of_isAmple L hL) a hd

end Monoidal

end Stacks.SectionRingProjMorphism

end
