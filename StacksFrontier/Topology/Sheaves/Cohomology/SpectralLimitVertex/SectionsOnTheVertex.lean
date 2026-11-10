module

public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralLimitVertex.CechAcyclicityOfTheVertex

/-!
# Abelian Stacks 0A33 on the vertex of an abstract limiting cone

`StacksDraft.Ch20.Sec16.Tag0A37StageSystem` reduces the quasi-compact-open clause of Stacks 0A37
in positive degree, for a system of injective abelian sheaves, to one degree-zero statement:
`SpectralAbelianSheafSystem.IsStageSectionsColimit`, that the sections of the sheaf on the vertex
of a limiting cone over `pⱼ⁻¹Z` are the filtered colimit of the stage sections `𝒜ₘ(f_b⁻¹Z)` for
`b : m ⟶ j`, over quasi-compact `Z`.  **This file proves that statement**, and with it the clause
for an injective system, unconditionally.

Abelian Stacks 0A33 is proved, but over the *concrete* limit `S.invLim`:
`isColimitAbelianStageSectionsCocone` says that the cocone from the stage diagram
`abelianStageFunctor Z` into `colimⱼ pⱼ⁻¹𝒜ⱼ(pⱼ⁻¹Z)` is a colimit cocone, the inverse images
being the germ models along the *concrete* projections.  The two statements have the **same
diagram** — that is why `stageSystem` was built out of `abelianStageFunctor` — so all that
separates them is the identification of the two vertices, compatibly with the legs.  That
identification is what this file supplies, and it comes down to a single germ-model computation.

The space underlying the vertex is homeomorphic to `S.invLim` (`conePointIso`), and
`GermPullback.comap` along a map is *precomposition* on germ-model sections, so the homeomorphism
carries the concrete germ model `pₖ⁻¹𝒜ₖ` isomorphically onto the abstract one `pullSheaf c k`
(`pullCompare`, `pullCompareInv`).  **The content is that this comparison is natural in the
stage**: that it intertwines the transition maps `pullbackMap` of the concrete system with the
transition maps `SheafedSpaceLimit.trans` of the abstract one.  Both are determined by their
values on germwise pullbacks — `pullback_hom_ext` for the concrete one, which is the germ-model
mapping-out property `GermPullback.mapOut_unique` — and on a germwise pullback both send
`ofSection hV s` to `ofSection hV' (φ_a s)`.  For `trans` that is `trans_ofSection`;
for `pullbackMap` it is `pullbackMap_ofSection`, proved here, which is the general form of
`pullbackMap_stageToPullback`.

From the natural isomorphism the vertices are identified in three steps: the two diagrams of
section groups over `Jᵒᵖ` are isomorphic (`sectionsCompareIso`), so their colimits are; the
colimit on the vertex side is the sections of the sheaf on the vertex, which is abelian Stacks
009F (4) applied to `SheafedSpaceLimit.pullSystem` on the spectral space underlying the vertex
(`isIso_colimit_post_vertexSections`); and `pⱼ⁻¹Z` read on the vertex through the homeomorphism
is `pⱼ⁻¹Z` read directly (`legOpen_eq`).  The legs then agree because `coleg`, evaluated on a
germwise pullback, is the sheaf component of the cone projection followed by a restriction
(`coleg_ofSection`), which is exactly how `stageLeg` was defined.

## Main definitions

* `SpectralAbelianSheafSystem.pullCompare` and `SpectralAbelianSheafSystem.pullCompareInv`: the
  mutually inverse comparisons between the concrete germ model `pₖ⁻¹𝒜ₖ` on `S.invLim` and the
  pushforward along `conePointIso` of the germ model `pₖ⁻¹𝒜ₖ` on the vertex of the cone.
* `SpectralAbelianSheafSystem.sectionsCompareIso`: the induced isomorphism of the two diagrams of
  section groups over `Jᵒᵖ`.
* `SpectralAbelianSheafSystem.stageSectionsVertexIso`: the identification of the vertex of abelian
  Stacks 0A33 with the sections of the sheaf on the vertex of the cone over `pⱼ⁻¹Z`.

## Main results

* `SpectralAbelianSheafSystem.pullbackMap_ofSection`: **the transition map of the concrete pullback
  system, on a germwise pullback**: it sends the germwise pullback of `s` to the germwise pullback
  of the `f_a`-image of `s`.  This is the general form of `pullbackMap_stageToPullback`, and it is
  the lemma the naturality argument turns on.
* `SpectralAbelianSheafSystem.pullback_hom_ext`: a morphism out of the concrete germ model into a
  sheaf is determined by its values on germwise pullbacks.
* `SpectralAbelianSheafSystem.pullCompare_comp_trans`: **the comparison is natural in the stage.**
* `SpectralAbelianSheafSystem.isStageSectionsColimit`: **abelian Stacks 0A33 on the vertex of an
  abstract limiting cone.**
* `SpectralAbelianSheafSystem.isZero_cechComplex_homology_conePoint_of_injective'`,
  `isZero_H'_succ_conePoint_of_injective'`, `isColimit_cohomologyCocone_of_injective'` and
  `isIso_comparison_of_injective'`: **the Čech acyclicity on the vertex, the vanishing
  `Hⁿ⁺¹(pᵢ⁻¹U, c.pt.sheaf) = 0`, and the quasi-compact-open clause of Stacks 0A37 in positive
  degree for a system of injective sheaves — all unconditionally.**

## Implementation notes

### Why the comparison is written with `comap` and the extensionality with `mapOut`

`GermPullback.comap` is literally precomposition (`comap_val` holds by definition), so the two
comparisons are mutually inverse for a reason that needs no germ-model theory: a section of a germ
model is a function on the open, and composing with a homeomorphism and with its inverse returns
it.  Both round trips are therefore `congrArg σ.1` applied to `Subtype.ext` of the
homeomorphism's own identity.  Naturality in the open is likewise definitional.

The naturality in the stage is the one place where germ-model theory is used, and it is used
exactly once: `SheafedSpaceLimit.trans` has no pointwise formula — it is defined by the
mapping-out property of the germ model — so the identity has to be checked on germwise pullbacks.
`pullback_hom_ext` is the extensionality principle for that, and it is the argument of
`SheafedSpaceLimit.pull_hom_ext` run at the concrete projections instead of the cone legs:
`GermPullback.mapOut_unique` together with `GermPullback.toPushforwardPresheaf_comp_eq_iff`.

### Spellings and transparency

`Stacks.Cohomology.AbelianSpectral.isIso_colimit_post_sheafSections_of_isCompact` is applied with
the system passed **explicitly**.  Its instance-search form cannot be used here: the system
`SheafedSpaceLimit.pullSystem c` is valued in `(c.pt : TopCat).Sheaf AddCommGrpCat`, which is a
semireducible `def` over `Sheaf (Opens.grothendieckTopology _) AddCommGrpCat`, and instance search
does not cross that boundary — `PreservesColimit (pullSystem c) _` is not found even with the
`PreservesColimitsOfShape` hypothesis in scope.  Supplying the functor as an argument makes the
elaborator check the definitional equality instead, which succeeds.

For the same reason — keyed matching happens at `instances` transparency — several steps that look
like rewrites are applications: `GermPullback.coleg_ofSection` and
`IsColimit.comp_coconePointUniqueUpToIso_hom` are fed to `congrArg`, and
`vertexColimitIso` is unfolded by `exact` rather than by `rw`, because it is a `def` over
`IsColimit.coconePointUniqueUpToIso` and `rw` does not see through it.  The two spellings of the
open `pⱼ⁻¹Z` on the vertex are mediated by `legOpenIso`, a pair of restriction maps along the
equality rather than an `eqToHom`, so that the leg computation contracts by
`presheaf_res_eq₂` — two restriction maps between opens that are equal but differently presented
are identified for free, `Opens` being a partial order.

### What remains after this file

The clause of Stacks 0A37 is about an *arbitrary* system of abelian sheaves; what is closed here
is the case of a system of injective sheaves.  Passing to the general case is the degree induction
of the source: embed the system in a system of injectives, compare the two long exact sequences
levelwise and on the limit, and conclude by the four lemma.  Carrying that out needs a category
of systems of abelian sheaves over the varying diagram of spaces, which
`StacksFrontier.Topology.Sheaves.Limits.AbelianSystem` does not provide —
  `SpectralDiagram.AbelianSystem`
is pure data, with no `Hom` and no abelian structure.

## References

* [Stacks Project, Tag 0A32](https://stacks.math.columbia.edu/tag/0A32)
* [Stacks Project, Tag 0A33](https://stacks.math.columbia.edu/tag/0A33)
* [Stacks Project, Tag 009F](https://stacks.math.columbia.edu/tag/009F)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.Basis (OpenCover)
open Stacks.Cohomology.Vanishing (compactCovers)

universe u

namespace Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem

variable {J : Type u} [SmallCategory J] [IsCofiltered J]
  (S : SpectralAbelianSheafSystem.{u, u, u} J)

/-! ### The transition maps of the concrete pullback system on germwise pullbacks -/

/-- **The transition map of the concrete pullback system, on a germwise pullback.**  The germwise
pullback along `pᵢ` of `s ∈ 𝒜ᵢ(V)` is carried to the germwise pullback along `pⱼ` of the
`f_a`-image of `s`, over any open of the limit carried into `V` by `pᵢ`.

This is the general form of `SpectralSheafSystem.pullbackMap_stageToPullback`, which
states it only for the open `pᵢ⁻¹U` and with the `f_a`-map followed by a restriction.  It is the
one description the naturality of the comparison needs, so that it can be read beside
`SheafedSpaceLimit.trans_ofSection` and `GermPullback.comap_ofSection`. -/
lemma pullbackMap_ofSection {j i : J} (a : j ⟶ i) {W : Opens (S.invLim)}
    {V : Opens (S.E.obj i)} (hV : ∀ z : W, S.proj i z.1 ∈ V)
    (hV' : ∀ z : W, S.proj j z.1 ∈ (Opens.map (S.E.map a).hom.base).obj V)
    (s : (S.stagePresheaf i).obj (op V)) :
    S.pullbackMap a (GermPullback.ofSection (g := S.proj i)
        (𝒢 := GermPullback.typePresheaf (S.stagePresheaf i)) hV s) =
      GermPullback.ofSection (g := S.proj j)
        (𝒢 := GermPullback.typePresheaf (S.stagePresheaf j)) hV' (S.pushSection a s) := by
  refine GermPullback.ext fun z ↦ ?_
  exact S.typeSystem.pullbackMap_val_of_germ a _ z (hV z) s rfl (hV' z)

/-- **A morphism out of the concrete germ model `pᵢ⁻¹𝒜ᵢ` into a sheaf is determined by its values
on the germwise pullbacks of the sections of `𝒜ᵢ`.**  Both morphisms solve the same mapping-out
problem for the germ model, so `GermPullback.mapOut_unique` identifies them.

This is `SheafedSpaceLimit.pull_hom_ext` run at the projections of the concrete limit instead of
at the legs of an abstract cone. -/
lemma pullback_hom_ext {i : J} {H : (S.invLim : TopCat.{u}).Presheaf AddCommGrpCat.{u}}
    (hH : TopCat.Presheaf.IsSheaf H) {ψ₁ ψ₂ : (S.abelianPullback i).presheaf ⟶ H}
    (h : ∀ (V : Opens (S.E.obj i)) (s : (S.stagePresheaf i).obj (op V)),
      ψ₁.app (op ((Opens.map (S.typeSystem.diagram.proj i)).obj V))
          (GermPullback.ofSection (g := S.proj i)
            (𝒢 := GermPullback.typePresheaf (S.stagePresheaf i)) (fun z ↦ z.2) s) =
        ψ₂.app (op ((Opens.map (S.typeSystem.diagram.proj i)).obj V))
          (GermPullback.ofSection (g := S.proj i)
            (𝒢 := GermPullback.typePresheaf (S.stagePresheaf i)) (fun z ↦ z.2) s)) :
    ψ₁ = ψ₂ := by
  set φ := GermPullback.toPushforwardPresheaf (S.typeSystem.diagram.proj i) (S.stagePresheaf i) ≫
    (TopCat.Presheaf.pushforward AddCommGrpCat.{u}
      (S.typeSystem.diagram.proj i)).map ψ₁ with hφ
  have k1 : ψ₁ = GermPullback.mapOut (S.typeSystem.diagram.proj i) φ hH :=
    GermPullback.mapOut_unique (S.typeSystem.diagram.proj i) φ hH hφ.symm
  have hv := (GermPullback.toPushforwardPresheaf_comp_eq_iff
    (S.typeSystem.diagram.proj i) φ ψ₁).1 hφ.symm
  have k2 : ψ₂ = GermPullback.mapOut (S.typeSystem.diagram.proj i) φ hH :=
    GermPullback.mapOut_unique (S.typeSystem.diagram.proj i) φ hH
      ((GermPullback.toPushforwardPresheaf_comp_eq_iff (S.typeSystem.diagram.proj i) φ ψ₂).2
        fun V s ↦ (h V s).symm.trans (hv V s))
  exact k1.trans k2.symm

/-- For a presheaf `P` of abelian groups on `X` and opens `V₃ ≤ V₂ ≤ V₁`, the composite of the
restrictions `P(V₁) → P(V₂) → P(V₃)` is the restriction `P(V₁) → P(V₃)`. -/
lemma presheaf_res_eq₂ {X : TopCat.{u}} (P : X.Presheaf AddCommGrpCat.{u})
    {V₁ V₂ V₃ : (Opens ↥X)ᵒᵖ} (a : V₁ ⟶ V₂) (b : V₂ ⟶ V₃) (ab : V₁ ⟶ V₃) :
    P.map a ≫ P.map b = P.map ab := by
  rw [← P.map_comp]
  exact congrArg P.map (Subsingleton.elim _ _)

/-- For a presheaf `P` of abelian groups on `X`, restricting along `a : V₁ ⟶ V₂` and back along
`b : V₂ ⟶ V₁` is the identity of `P(V₁)`. -/
lemma presheaf_res_eq_id {X : TopCat.{u}} (P : X.Presheaf AddCommGrpCat.{u})
    {V₁ V₂ : (Opens ↥X)ᵒᵖ} (a : V₁ ⟶ V₂) (b : V₂ ⟶ V₁) : P.map a ≫ P.map b = 𝟙 _ := by
  rw [← P.map_comp, Subsingleton.elim (a ≫ b) (𝟙 _), P.map_id]

section Bridge

variable (c : Cone S.E) (hc : IsLimit c)

/-! ### The comparison of the two germ models -/

/-- The comparison homeomorphism is continuous. -/
lemma conePointIso_continuous :
    Continuous (ConcreteCategory.hom (conePointIso S c hc).hom) :=
  ((conePointIso S c hc).hom).hom.continuous

/-- Its inverse is continuous. -/
lemma conePointIso_inv_continuous :
    Continuous (ConcreteCategory.hom (conePointIso S c hc).inv) :=
  ((conePointIso S c hc).inv).hom.continuous

/-- The cone legs factor through the comparison homeomorphism, read on points. -/
lemma projFun_eq_proj (k : J) (z : ((c.pt : TopCat.{u}) : Type u)) :
    SheafedSpaceLimit.projFun c k z =
      S.proj k (ConcreteCategory.hom (conePointIso S c hc).hom z) :=
  (ConcreteCategory.congr_hom (conePointIso_hom_comp_proj S c hc k) z).symm

/-- The projections of the concrete limit factor through the inverse of the comparison
homeomorphism, read on points. -/
lemma proj_eq_projFun (k : J) (y : (S.invLim : Type u)) :
    S.proj k y =
      SheafedSpaceLimit.projFun c k (ConcreteCategory.hom (conePointIso S c hc).inv y) := by
  rw [projFun_eq_proj S c hc k]
  exact congrArg (S.proj k)
    (ConcreteCategory.congr_hom (conePointIso S c hc).inv_hom_id y).symm

/-- A point of the vertex lies over `V` through the cone leg if its image in `S.invLim` lies over
`V` through the projection. -/
private lemma projFun_mem_of_proj_mem (k : J) {V : Opens (S.E.obj k)}
    {z : ((c.pt : TopCat.{u}) : Type u)}
    (h : S.proj k (ConcreteCategory.hom (conePointIso S c hc).hom z) ∈ V) :
    SheafedSpaceLimit.projFun c k z ∈ V :=
  Eq.mpr (congrArg (· ∈ V) (projFun_eq_proj S c hc k z)) h

/-- **The comparison from the concrete germ model `pₖ⁻¹𝒜ₖ` on `S.invLim` to the pushforward along
the comparison homeomorphism of the germ model `pₖ⁻¹𝒜ₖ` on the vertex of the cone.**  Pullback of
germ-model sections along a map is precomposition, `GermPullback.comap`, so this is precomposition
with the homeomorphism; naturality in the open is therefore definitional. -/
def pullCompare (k : J) :
    (S.abelianPullback k).presheaf ⟶
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (conePointIso S c hc).hom).obj
        (SheafedSpaceLimit.pullSheaf c k).presheaf where
  app W := AddCommGrpCat.ofHom (GermPullback.comapAddHom (S.stagePresheaf k)
    (conePointIso_continuous S c hc) (projFun_eq_proj S c hc k) (fun z ↦ z.2))
  naturality := by
    intro W₁ W₂ m
    refine ConcreteCategory.hom_ext _ _ fun σ ↦ GermPullback.ext fun z ↦ ?_
    rfl

/-- The comparison in the other direction, precomposition with the inverse homeomorphism. -/
def pullCompareInv (k : J) :
    (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (conePointIso S c hc).hom).obj
        (SheafedSpaceLimit.pullSheaf c k).presheaf ⟶ (S.abelianPullback k).presheaf where
  app W := AddCommGrpCat.ofHom (GermPullback.comapAddHom (S.stagePresheaf k)
    (conePointIso_inv_continuous S c hc) (proj_eq_projFun S c hc k)
    (fun z ↦ Eq.mpr (congrArg (fun y ↦ y ∈ W.unop)
      (ConcreteCategory.congr_hom (conePointIso S c hc).inv_hom_id z.1)) z.2))
  naturality := by
    intro W₁ W₂ m
    refine ConcreteCategory.hom_ext _ _ fun σ ↦ GermPullback.ext fun z ↦ ?_
    rfl

/-- The two comparisons are mutually inverse: composing a section with the homeomorphism and then
with its inverse returns it. -/
lemma pullCompare_comp_pullCompareInv (k : J) :
    S.pullCompare c hc k ≫ S.pullCompareInv c hc k = 𝟙 _ := by
  refine NatTrans.ext (funext fun W ↦ ConcreteCategory.hom_ext _ _ fun σ ↦ ?_)
  refine GermPullback.ext (g := S.proj k)
    (𝒢 := GermPullback.typePresheaf (S.stagePresheaf k)) fun y ↦ ?_
  exact congrArg σ.1
    (Subtype.ext (ConcreteCategory.congr_hom (conePointIso S c hc).inv_hom_id y.1))

/-- The two comparisons are mutually inverse, the other composite. -/
lemma pullCompareInv_comp_pullCompare (k : J) :
    S.pullCompareInv c hc k ≫ S.pullCompare c hc k = 𝟙 _ := by
  refine NatTrans.ext (funext fun W ↦ ConcreteCategory.hom_ext _ _ fun τ ↦ ?_)
  refine GermPullback.ext (g := SheafedSpaceLimit.projFun c k)
    (𝒢 := GermPullback.typePresheaf (S.stagePresheaf k)) fun z ↦ ?_
  exact congrArg τ.1
    (Subtype.ext (ConcreteCategory.congr_hom (conePointIso S c hc).hom_inv_id z.1))

/-- **The comparison on a germwise pullback.**  It carries the germwise pullback along `pₖ` of a
section of `𝒜ₖ` to the germwise pullback of the same section along the `k`-th cone leg; the two
base points agree by `projFun_eq_proj`, which is all `GermPullback.Germs.mk_eq_mk` needs. -/
lemma pullCompare_ofSection (k : J) {W : Opens (S.invLim)} {V : Opens (S.E.obj k)}
    (hV : ∀ z : W, S.proj k z.1 ∈ V) (s : (S.stagePresheaf k).obj (op V))
    (hV' : ∀ z : (Opens.map (conePointIso S c hc).hom).obj W,
      SheafedSpaceLimit.projFun c k z.1 ∈ V) :
    ConcreteCategory.hom ((S.pullCompare c hc k).app (op W))
        (GermPullback.ofSection (g := S.proj k)
          (𝒢 := GermPullback.typePresheaf (S.stagePresheaf k)) hV s) =
      GermPullback.ofSection (g := SheafedSpaceLimit.projFun c k)
        (𝒢 := GermPullback.typePresheaf (S.stagePresheaf k)) hV' s := by
  refine GermPullback.ext (g := SheafedSpaceLimit.projFun c k)
    (𝒢 := GermPullback.typePresheaf (S.stagePresheaf k)) fun z ↦ ?_
  exact GermPullback.Germs.mk_eq_mk
    (𝒢 := GermPullback.typePresheaf (S.stagePresheaf k)) (V := V) s
    (projFun_eq_proj S c hc k z.1).symm _ _

/-- **The naturality of the comparison in the stage.** -/
lemma pullCompare_comp_trans {j i : J} (a : j ⟶ i) :
    S.pullCompare c hc i ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{u}
          (conePointIso S c hc).hom).map (SheafedSpaceLimit.trans c a) =
      (S.abelianPullbackSystem.map a.op).hom ≫ S.pullCompare c hc j := by
  refine S.pullback_hom_ext
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (conePointIso S c hc).hom).obj
      (SheafedSpaceLimit.pullSheaf c j)).2 ?_
  intro V s
  have hV' : ∀ z : (Opens.map (conePointIso S c hc).hom).obj
      ((Opens.map (S.typeSystem.diagram.proj i)).obj V),
      SheafedSpaceLimit.projFun c i z.1 ∈ V := fun z ↦ projFun_mem_of_proj_mem S c hc i z.2
  have hV'' : ∀ z : (Opens.map (conePointIso S c hc).hom).obj
      ((Opens.map (S.typeSystem.diagram.proj i)).obj V),
      SheafedSpaceLimit.projFun c j z.1 ∈ (Opens.map (S.E.map a).hom.base).obj V :=
    fun z ↦ SheafedSpaceLimit.mem_stageOpen c a V ⟨z.1, hV' z⟩
  have hX : ∀ z : (Opens.map (S.typeSystem.diagram.proj i)).obj V,
      S.proj j z.1 ∈ (Opens.map (S.E.map a).hom.base).obj V := fun z ↦
    Eq.mpr (congrArg (fun y ↦ y ∈ V) (S.typeSystem.diagram.projFun_eq_mapFun a z.1).symm) z.2
  refine Eq.trans (congrArg (fun t ↦ ConcreteCategory.hom
      ((SheafedSpaceLimit.trans c a).app (op ((Opens.map (conePointIso S c hc).hom).obj
        ((Opens.map (S.typeSystem.diagram.proj i)).obj V)))) t)
    (S.pullCompare_ofSection c hc i (fun z ↦ z.2) s hV')) ?_
  refine Eq.trans (SheafedSpaceLimit.trans_ofSection c a hV' hV'' s) ?_
  refine Eq.trans (S.pullCompare_ofSection c hc j hX (S.pushSection a s) hV'').symm ?_
  exact congrArg (fun t ↦ ConcreteCategory.hom ((S.pullCompare c hc j).app
      (op ((Opens.map (S.typeSystem.diagram.proj i)).obj V))) t)
    (S.pullbackMap_ofSection a (fun z ↦ z.2) hX s).symm

/-! ### Identifying the two vertices -/

/-- **The open `pⱼ⁻¹Z` of the concrete limit, pulled back along the comparison homeomorphism, is
the open `pⱼ⁻¹Z` of the vertex**, because the homeomorphism commutes with the projections. -/
lemma legOpen_eq (j : J) (Z : Opens (S.E.obj j)) :
    (Opens.map (conePointIso S c hc).hom).obj (S.limOpen Z) =
      (Opens.map (c.π.app j).hom.base).obj Z :=
  congrArg (fun m ↦ (Opens.map m).obj Z) (conePointIso_hom_comp_proj S c hc j)

/-- Sections over an open of the vertex, as a functor on abelian sheaves there. -/
abbrev vertexSections (W : Opens ((c.pt : TopCat.{u}) : Type u)) :
    (c.pt : TopCat.{u}).Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (sheafSections (Opens.grothendieckTopology ((c.pt : TopCat.{u}) : Type u))
    AddCommGrpCat.{u}).obj (op W)

include hc in
/-- **Abelian Stacks 009F (4) on the vertex**: over a quasi-compact open of the vertex, sections
commute with the filtered colimit of the germ-model inverse images.  The vertex is a spectral
space (`spectralSpace_conePoint`), so both hypotheses of Stacks 009F are discharged. -/
theorem isIso_colimit_post_vertexSections (W : Opens ((c.pt : TopCat.{u}) : Type u))
    (hW : IsCompact (W : Set ((c.pt : TopCat.{u}) : Type u))) :
    IsIso (colimit.post (SheafedSpaceLimit.pullSystem c) (S.vertexSections c W)) :=
  have : SpectralSpace ((c.pt : TopCat.{u}) : Type u) := spectralSpace_conePoint S c hc
  Stacks.Cohomology.AbelianSpectral.isIso_colimit_post_sheafSections_of_isCompact
    W hW (SheafedSpaceLimit.pullSystem c)

/-- **The two diagrams of section groups over `Jᵒᵖ` agree**: the concrete `k ↦ (pₖ⁻¹𝒜ₖ)(pⱼ⁻¹Z)`
and the abstract one on the vertex.  The components are `pullCompare`, and the naturality is
`pullCompare_comp_trans`. -/
def sectionsCompareIso (j : J) (Z : Opens (S.E.obj j)) :
    S.abelianPullbackSystem ⋙ S.sectionsFunctor Z ≅
      SheafedSpaceLimit.pullSystem c ⋙
        S.vertexSections c ((Opens.map (conePointIso S c hc).hom).obj (S.limOpen Z)) :=
  NatIso.ofComponents
    (fun k ↦
      { hom := (S.pullCompare c hc k.unop).app (op (S.limOpen Z))
        inv := (S.pullCompareInv c hc k.unop).app (op (S.limOpen Z))
        hom_inv_id := NatTrans.congr_app
          (S.pullCompare_comp_pullCompareInv c hc k.unop) (op (S.limOpen Z))
        inv_hom_id := NatTrans.congr_app
          (S.pullCompareInv_comp_pullCompare c hc k.unop) (op (S.limOpen Z)) })
    (fun α ↦ (NatTrans.congr_app (S.pullCompare_comp_trans c hc α.unop)
      (op (S.limOpen Z))).symm)

/-- The open `pⱼ⁻¹Z` of the vertex is quasi-compact, in the spelling obtained by pulling back
along the comparison homeomorphism. -/
lemma isCompact_legOpen (j : J) (Z : Opens (S.E.obj j))
    (hZ : IsCompact (Z : Set (S.E.obj j))) :
    IsCompact ((((Opens.map (conePointIso S c hc).hom).obj (S.limOpen Z)) :
      Opens ((c.pt : TopCat.{u}) : Type u)) : Set ((c.pt : TopCat.{u}) : Type u)) :=
  Eq.mpr (congrArg (fun U : Opens ((c.pt : TopCat.{u}) : Type u) ↦
      IsCompact (U : Set ((c.pt : TopCat.{u}) : Type u))) (legOpen_eq S c hc j Z))
    (isCompact_legPreimage S c hc j Z hZ)

/-- The two spellings of the open on the vertex, as an isomorphism of section groups. -/
def legOpenIso (j : J) (Z : Opens (S.E.obj j)) :
    c.pt.presheaf.obj (op ((Opens.map (conePointIso S c hc).hom).obj (S.limOpen Z))) ≅
      c.pt.presheaf.obj (op ((Opens.map (c.π.app j).hom.base).obj Z)) where
  hom := c.pt.presheaf.map (homOfLE (le_of_eq (legOpen_eq S c hc j Z).symm)).op
  inv := c.pt.presheaf.map (homOfLE (le_of_eq (legOpen_eq S c hc j Z))).op
  hom_inv_id := presheaf_res_eq_id c.pt.presheaf _ _
  inv_hom_id := presheaf_res_eq_id c.pt.presheaf _ _

/-- The vertex of abelian Stacks 0A33 is the sections on the vertex of the cone. -/
def stageSectionsVertexIso (j : J) (Z : Opens (S.E.obj j))
    (hZ : IsCompact (Z : Set (S.E.obj j))) :
    (S.abelianStageSectionsCocone Z).pt ≅
      c.pt.presheaf.obj (op ((Opens.map (c.π.app j).hom.base).obj Z)) :=
  have hiso := S.isIso_colimit_post_vertexSections c hc
    ((Opens.map (conePointIso S c hc).hom).obj (S.limOpen Z)) (S.isCompact_legOpen c hc j Z hZ)
  (HasColimit.isoOfNatIso (S.sectionsCompareIso c hc j Z)).trans
    ((@asIso _ _ _ _ _ hiso).trans
      (((S.vertexSections c ((Opens.map (conePointIso S c hc).hom).obj
        (S.limOpen Z))).mapIso (vertexColimitIso S c hc)).trans (S.legOpenIso c hc j Z)))

/-- The components of `stageSectionsVertexIso`, written out. -/
lemma stageSectionsVertexIso_hom (j : J) (Z : Opens (S.E.obj j))
    (hZ : IsCompact (Z : Set (S.E.obj j))) :
    (S.stageSectionsVertexIso c hc j Z hZ).hom =
      (HasColimit.isoOfNatIso (S.sectionsCompareIso c hc j Z)).hom ≫
        colimit.post (SheafedSpaceLimit.pullSystem c)
            (S.vertexSections c ((Opens.map (conePointIso S c hc).hom).obj (S.limOpen Z))) ≫
          (S.vertexSections c ((Opens.map (conePointIso S c hc).hom).obj
              (S.limOpen Z))).map (vertexColimitIso S c hc).hom ≫
            (S.legOpenIso c hc j Z).hom :=
  rfl

/-- The `k`-th colimit injection of the pullback system on the vertex, followed by the
identification of that colimit with the sheaf on the vertex, is the `k`-th leg `coleg`. -/
lemma vertexSections_map_colimit_ι (W : Opens ((c.pt : TopCat.{u}) : Type u)) (k : J) :
    (S.vertexSections c W).map (colimit.ι (SheafedSpaceLimit.pullSystem c) (op k)) ≫
        (S.vertexSections c W).map (vertexColimitIso S c hc).hom =
      (SheafedSpaceLimit.coleg c k).app (op W) := by
  rw [← Functor.map_comp]
  exact congrArg (S.vertexSections c W).map
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (SheafedSpaceLimit.pullSystem c))
      (SheafedSpaceLimit.isColimitPullCocone c hc) (op k))

/-- The `k`-th colimit injection followed by the identification of the vertices is the comparison
of the germ models, the `k`-th leg `coleg`, and a restriction. -/
lemma colimit_ι_comp_stageSectionsVertexIso (j : J) (Z : Opens (S.E.obj j))
    (hZ : IsCompact (Z : Set (S.E.obj j))) (k : J) :
    colimit.ι (S.abelianPullbackSystem ⋙ S.sectionsFunctor Z) (op k) ≫
        (S.stageSectionsVertexIso c hc j Z hZ).hom =
      (S.pullCompare c hc k).app (op (S.limOpen Z)) ≫
        (SheafedSpaceLimit.coleg c k).app
            (op ((Opens.map (conePointIso S c hc).hom).obj (S.limOpen Z))) ≫
          (S.legOpenIso c hc j Z).hom := by
  rw [stageSectionsVertexIso_hom, HasColimit.ι_isoOfNatIso_hom_assoc, colimit.ι_post_assoc]
  refine congrArg (fun z ↦ (S.sectionsCompareIso c hc j Z).hom.app (op k) ≫ z) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun z ↦ z ≫ (S.legOpenIso c hc j Z).hom)
    (S.vertexSections_map_colimit_ι c hc _ k)

/-- **The identification of the vertices carries the comparison cocone of abelian Stacks 0A33 to
the comparison cocone on the vertex of the cone.**  On the germwise pullback of a stage section
`t`, the left-hand side is `coleg` of the germwise pullback of `t`, which by `coleg_ofSection` is
the sheaf component of the cone projection applied to `t`, restricted; and that is how `stageLeg`
was defined.  The two restrictions that remain contract to one. -/
theorem abelianStageSectionsCocone_ι_comp (j : J) (Z : Opens (S.E.obj j))
    (hZ : IsCompact (Z : Set (S.E.obj j))) (A : (Over j)ᵒᵖ) :
    (S.abelianStageSectionsCocone Z).ι.app A ≫ (S.stageSectionsVertexIso c hc j Z hZ).hom =
      (S.stageLeg c A.unop).app (op Z) := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z ↦ S.abelianStageToPullback Z A.unop ≫ z)
    (S.colimit_ι_comp_stageSectionsVertexIso c hc j Z hZ A.unop.left)) ?_
  refine ConcreteCategory.hom_ext _ _ fun t ↦ ?_
  have hVa : ∀ z : (Opens.map (conePointIso S c hc).hom).obj (S.limOpen Z),
      SheafedSpaceLimit.projFun c A.unop.left z.1 ∈
        (Opens.map (S.E.map A.unop.hom).hom.base).obj Z :=
    fun z ↦ projFun_mem_of_proj_mem S c hc A.unop.left
      (S.typeSystem.projFun_mem_stageOpen Z A.unop
        ⟨ConcreteCategory.hom (conePointIso S c hc).hom z.1, z.2⟩)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    show ConcreteCategory.hom (S.abelianStageToPullback Z A.unop) t =
      GermPullback.ofSection (g := S.proj A.unop.left)
        (𝒢 := GermPullback.typePresheaf (S.stagePresheaf A.unop.left))
        (S.typeSystem.projFun_mem_stageOpen Z A.unop) t from rfl,
    S.pullCompare_ofSection c hc A.unop.left _ t hVa]
  refine Eq.trans (congrArg (fun y ↦ ConcreteCategory.hom (S.legOpenIso c hc j Z).hom y)
    (SheafedSpaceLimit.coleg_ofSection c A.unop.left hVa t)) ?_
  exact ConcreteCategory.congr_hom
    (presheaf_res_eq₂ c.pt.presheaf _ _ (homOfLE (S.legOpen_le c A.unop Z)).op)
    (ConcreteCategory.hom ((c.π.app A.unop.left).hom.c.app
      (op ((Opens.map (S.E.map A.unop.hom).hom.base).obj Z))) t)

include hc in
/-- **Abelian Stacks 0A33 on the vertex of an abstract limiting cone.**  For every quasi-compact
open `Z` of a stage, the sections of the sheaf on the vertex over `pⱼ⁻¹Z` are the filtered colimit
of the stage sections `𝒜ₘ(f_b⁻¹Z)` over `b : m ⟶ j`.

This is abelian Stacks 0A33 over the concrete limit,
`isColimitAbelianStageSectionsCocone`, transported along `stageSectionsVertexIso`; the two cocones
have one and the same diagram, and `abelianStageSectionsCocone_ι_comp` matches their legs. -/
theorem isStageSectionsColimit : S.IsStageSectionsColimit c := fun j Z hZ ↦
  ⟨IsColimit.ofIsoColimit (S.isColimitAbelianStageSectionsCocone Z hZ)
    (Cocone.ext (S.stageSectionsVertexIso c hc j Z hZ)
      fun A ↦ S.abelianStageSectionsCocone_ι_comp c hc j Z hZ A)⟩

/-! ### The quasi-compact-open clause of Stacks 0A37 for an injective system, unconditionally -/

include hc in
/-- **The positive-degree Čech cohomology of the sheaf on the vertex of a limiting cone vanishes
for every finite cover of a quasi-compact open of the vertex by quasi-compact opens**, when every
stage sheaf is injective.  This is
`isZero_cechComplex_homology_conePoint_of_injective` with its degree-zero hypothesis discharged by
`isStageSectionsColimit`. -/
theorem isZero_cechComplex_homology_conePoint_of_injective'
    (hinj : ∀ k, Injective (S.E.obj k).sheaf)
    (W : OpenCover ((c.pt : TopCat.{u}) : Type u))
    (hW : W ∈ compactCovers ((c.pt : TopCat.{u}) : Type u)) (n : ℕ) :
    IsZero (((cechComplexFunctor W.obj).obj c.pt.sheaf.obj).homology (n + 1)) :=
  S.isZero_cechComplex_homology_conePoint_of_injective c hc
    (S.isStageSectionsColimit c hc) hinj W hW n

include hc in
/-- **The vanishing needed on the limit side of Stacks 0A37, unconditionally**:
`Hⁿ⁺¹(pᵢ⁻¹U, c.pt.sheaf) = 0` for a system of injective sheaves. -/
theorem isZero_H'_succ_conePoint_of_injective'
    (hinj : ∀ k, Injective (S.E.obj k).sheaf)
    (i : J) (U : Opens (S.E.obj i)) (hU : IsCompact (U : Set (S.E.obj i))) (n : ℕ) :
    IsZero (Sheaf.H'.{u, u, u} c.pt.sheaf (n + 1) (S.stageOpenCone c i U).pt) :=
  S.isZero_H'_succ_conePoint_of_injective c hc (S.isStageSectionsColimit c hc) hinj i U hU n

include hc in
/-- **The quasi-compact-open clause of Stacks 0A37 in positive degree for a system of injective
sheaves, unconditionally**: every presentation of the cohomology cocone over a quasi-compact open
`U` of a stage is a colimit cocone in degree `n + 1`. -/
def isColimit_cohomologyCocone_of_injective'
    (hinj : ∀ k, Injective (S.E.obj k).sheaf)
    (i : J) (U : Opens (S.E.obj i)) (hU : IsCompact (U : Set (S.E.obj i))) (n : ℕ)
    (D : CohomologyCocone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i))
      (S.stageOpenCone c i U) (n + 1)) :
    IsColimit D.cocone :=
  S.isColimit_cohomologyCocone_of_injective c hc (S.isStageSectionsColimit c hc) hinj i U hU n D

include hc in
/-- **The quasi-compact-open clause of Stacks 0A37 for a system of injective sheaves, in the form
the clause states it, unconditionally**: the comparison out of the colimit of the stage cohomology
groups is an isomorphism. -/
theorem isIso_comparison_of_injective'
    (hinj : ∀ k, Injective (S.E.obj k).sheaf)
    (i : J) (U : Opens (S.E.obj i)) (hU : IsCompact (U : Set (S.E.obj i))) (n : ℕ)
    (D : CohomologyCocone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i))
      (S.stageOpenCone c i U) (n + 1)) :
    IsIso D.comparison :=
  S.isIso_comparison_of_injective c hc (S.isStageSectionsColimit c hc) hinj i U hU n D

end Bridge

end Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem

end
