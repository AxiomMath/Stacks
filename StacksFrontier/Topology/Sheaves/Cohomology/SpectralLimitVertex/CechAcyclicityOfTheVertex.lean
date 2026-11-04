module

public import StacksFrontier.Topology.Sheaves.Cohomology.SheafedSpaceLimits.QuasiCompactCoverDescent
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralLimitDegreeInduction.InjectiveSystems
public import StacksFrontier.Topology.Sheaves.Cohomology.AbelianFilteredColimits.CechAcyclicityOfInjectives
public import StacksFrontier.CategoryTheory.Sites.CechCoverPullback

/-!
# Čech acyclicity on the vertex of a limiting cone, for a system of injective sheaves

The quasi-compact-open clause of Stacks 0A37 for a system of **injective** abelian sheaves is
reduced by `StacksDraft.Ch20.Sec16.Tag0A37InjectiveCase` and
`StacksDraft.Ch20.Sec16.Tag0A37CechVanishing` to one statement: the positive-degree Čech
cohomology of the sheaf `c.pt.sheaf` on the vertex of a limiting cone vanishes for every finite
cover of a quasi-compact open of the vertex by quasi-compact opens.  **This file proves that
statement**, and with it the clause, from a single degree-zero input: that the sections of
`c.pt.sheaf` over `pⱼ⁻¹Z` are the filtered colimit of the stage sections `𝒜ₘ(f_b⁻¹Z)` for
`b : m ⟶ j`, over quasi-compact `Z`.  That input is abelian Stacks 0A33 read on the vertex of an
abstract cone; it is isolated here as `SpectralAbelianSheafSystem.IsStageSectionsColimit`.

The argument is the one in the source.  A quasi-compact open of the vertex is the inverse image
of a quasi-compact open of a stage (Stacks 0A30), and by cofilteredness the finitely many members
of the cover descend to **one** stage `j`: the cover is `pⱼ⁻¹W` for a finite family `W` of
quasi-compact opens of `Xⱼ`.  Pulling a cover back does not change its Čech complex, only which
space it is read on —

  `Č(pⱼ⁻¹W, c.pt.sheaf) ≅ Č(W, (pⱼ)_* c.pt.sheaf)`,

by `Stacks.CategoryTheory.CechComplex.cechComplexPullbackIso` — so the computation moves to the
stage `Xⱼ`.  There the presheaf `(pⱼ)_* c.pt.sheaf` is, on quasi-compact opens, the filtered
colimit over `b : m ⟶ j` of the presheaves `(f_b)_* 𝒜ₘ`; all the opens occurring in the Čech
complex of a cover by quasi-compact opens are quasi-compact, so the two Čech complexes agree
(`Stacks.CategoryTheory.CechComplex.cechComplexIsoOfIsoOnInter`).  A finite Čech complex commutes
with filtered colimits, and the Čech complex of `(f_b)_* 𝒜ₘ` is — again by the pullback
identification, now in the other direction — the Čech complex of `𝒜ₘ` for the cover `f_b⁻¹W`,
which is acyclic in positive degrees because an injective abelian sheaf is flasque.  A filtered
colimit of complexes acyclic in a positive degree is acyclic there, which finishes it.

## Main definitions

* `SpectralAbelianSheafSystem.stageSystem`: **the system of stage presheaves pushed to a fixed
  stage**, `A ↦ (f_{A.hom})_* 𝒜_{A.left}`, as a functor `(Over j)ᵒᵖ ⥤ Xⱼ.Presheaf AddCommGrpCat`.
  Its value at an open `Z` is the stage diagram `abelianStageFunctor Z` of abelian Stacks 0A33,
  on the nose.
* `SpectralAbelianSheafSystem.stageLeg` and `SpectralAbelianSheafSystem.stageCocone`: the
  comparison cocone from that system to `(pⱼ)_* c.pt.sheaf`, whose leg at `A` is the sheaf
  component of the cone projection `p_{A.left}` followed by a restriction.
* `SpectralAbelianSheafSystem.IsStageSectionsColimit`: **the degree-zero input** — that cocone,
  evaluated at a quasi-compact open of a stage, is a colimit cocone of abelian groups.  This is
  abelian Stacks 0A33 on the vertex of an abstract limiting cone; see the implementation notes for
  what is proved and what the remaining step is.
* `SpectralAbelianSheafSystem.stageColimitDesc`: the induced map
  `colim_{b : m → j} (f_b)_* 𝒜ₘ ⟶ (pⱼ)_* c.pt.sheaf` of presheaves on `Xⱼ`.

## Main results

* `SpectralAbelianSheafSystem.isZero_cechComplex_homology_pushforward`: **the positive-degree
  Čech cohomology of `(f_a)_* 𝒜ₖ` vanishes** for every family of opens of the target, when `𝒜ₖ`
  is injective.
* `SpectralAbelianSheafSystem.isIso_stageColimitDesc_app`: `stageColimitDesc` is invertible on
  every quasi-compact open.
* `SpectralAbelianSheafSystem.isZero_cechComplex_homology_pullbackFamily`: **Čech acyclicity of
  `c.pt.sheaf` in positive degrees for a cover pulled back from a stage.**
* `SpectralAbelianSheafSystem.exists_stageFamily`: **a finite family of quasi-compact opens of the
  vertex is the family of inverse images of quasi-compact opens of a single stage.**  Only part (1)
  of Stacks 0A30 is used, together with cofilteredness; no covering condition is involved, because
  Čech acyclicity of a flasque sheaf holds for an arbitrary family.
* `SpectralAbelianSheafSystem.isZero_cechComplex_homology_conePoint_of_injective`: **the
  positive-degree Čech cohomology of the sheaf on the vertex vanishes for every finite cover of a
  quasi-compact open of the vertex by quasi-compact opens.**  This is the statement the Čech
  reduction of the clause asks for.
* `SpectralAbelianSheafSystem.isZero_H'_succ_conePoint_of_injective`: the vanishing of
  `Hⁿ⁺¹(pᵢ⁻¹U, c.pt.sheaf)`, obtained by feeding the previous result to
  `isZero_H'_succ_conePoint_of_cechAcyclic`.
* `SpectralAbelianSheafSystem.isColimit_cohomologyCocone_of_injective` and
  `SpectralAbelianSheafSystem.isIso_comparison_of_injective`: **the quasi-compact-open clause of
  Stacks 0A37 in positive degree for a system of injective sheaves**, with the vertex vanishing
  discharged.

## Implementation notes

### The stage system and its naturality

`Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem.abelianStageFunctor Z` — the stage
diagram `A ↦ 𝒜_{A.left}(f_{A.hom}⁻¹Z)` of abelian Stacks 0A33 — is available for *every* open `Z`
of a stage, and its functoriality in `A` is proved.  What the Čech computation needs is the same
data assembled into a functor valued in **presheaves** on `Xⱼ`, so that a Čech complex can be
formed from it and the colimit over the slice can be taken in presheaves, where it is pointwise.

`stageSystem` is exactly that assembly, and it is built so that the two things already proved are
reused rather than redone: its value at `A` is the pushforward `(f_{A.hom})_* 𝒜_{A.left}`, whose
value at `Z` is definitionally `(abelianStageFunctor Z).obj A`, and its morphism at `g` has
component `(abelianStageFunctor Z).map g` at `Z`.  The identity and composition laws of the
functor are then the identity and composition laws of `abelianStageFunctor Z`, one `Z` at a time,
through `CategoryTheory.NatTrans.ext`.

**The naturality in `Z` is the only new content**, and it is this.  Write `φ_g` for the sheaf
component of `S.E.map g.left`.  By `abelianStageFunctor_map_eq` the morphism at `Z` is `φ_g` at
`f_{A.hom}⁻¹Z` followed by the restriction from `f_{g.left}⁻¹f_{A.hom}⁻¹Z` to `f_{B.hom}⁻¹Z`, two
opens which are **equal** — the base maps compose, `f_{g.left} ≫ f_{A.hom} = f_{B.hom}` — but
which are not presented by the same expression.  The square for `Z' ≤ Z` therefore splits into
the naturality square of `φ_g`, which moves the restriction in `Z` across `φ_g` and is
`CategoryTheory.NatTrans.naturality`, and an identity between two composites of restriction maps
of `𝒜_{B.left}`.  The latter is free: those composites are restriction maps along two morphisms of
`Opens X_{B.left}` with the same source and the same target, and `Opens` is a partial order, so
`Subsingleton.elim` identifies them once `Functor.map_comp` has contracted each composite.  That
is what `presheaf_res_eq` and `presheaf_res_eq₃` package.

The same three steps — naturality of a sheaf component, then a subsingleton identity between
restriction maps — prove the naturality of `stageLeg` in `Z` and the cocone identity of
`stageCocone` in `A`; in the latter the composition law of morphisms of presheafed spaces
identifies `φ_{g.left}` followed by the sheaf component of `p_{B.left}` with the sheaf component
of `p_{B.left} ≫ f_{g.left}`, and `AlgebraicGeometry.PresheafedSpace.congr_app` applied to the
cone identity `p_{B.left} ≫ f_{g.left} = p_{A.left}` turns that into the sheaf component of
`p_{A.left}` followed by one more restriction.

### Why the proofs are in term mode

Expanding `abelianStageFunctor_map_eq` leaves a goal that is not type-correct at the `implicit`
transparency level, because the restriction map it produces is stated with the inequality
`mapOpen_le` while `abelianStageFunctor` states it with the corresponding inequality
for the underlying diagram of spaces, and the two spellings of that diagram differ by unfolding
`Functor.comp` and `SheafedSpace.forget`.  `simp` and `rw` refuse such a goal; `Eq.trans`,
`congrArg` and `exact` check their arguments up to full definitional equality and go through.  So
every step after that expansion is written as an explicit `Eq.trans` of a `Category.assoc` or a
`congrArg`, and the naturality of a natural transformation is applied through `naturality_comp`
rather than by rewriting with the generated `naturality_assoc`: `rw` matches at `instances`
transparency, which does not unfold the pushforward functor, so the right-hand factor of the
pattern is never recognised.  `pushforward_obj_map`, `stageSystem_obj_map` and
`stageSystem_map_app` exist for the same reason — to present a term that is already definitionally
a restriction map of a presheaf in the shape in which `rw` can see it.

### The remaining degree-zero input

`IsStageSectionsColimit` is abelian Stacks 0A33 read on the vertex of an abstract limiting cone.
Its two halves are both proved, but over the *concrete* limit `S.invLim`:
`Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem.isColimitAbelianStageSectionsCocone`
and `isColimitAbelianStageCocone` state it for the system `abelianPullbackSystem` of germ models
along the concrete projections, with vertex the sections of `colimⱼ pⱼ⁻¹𝒜ⱼ` over `pᵢ⁻¹U`.  The
diagram of that cocone is `abelianStageFunctor Z`, which is also the diagram here — that is why
`stageSystem` was built from it — so what is missing is only the identification of the two
*vertices*, compatibly with the legs:

  `c.pt.sheaf(pⱼ⁻¹Z) ≅ (colimⱼ pⱼ⁻¹𝒜ⱼ)(pⱼ⁻¹Z)`.

The space underlying the vertex is homeomorphic to `S.invLim` (`conePointIso`) and the sheaf on
the vertex is the colimit of the germ models along the cone legs
(`SheafedSpaceLimit.isColimitPullCocone`), so the identification is the statement that
`GermPullback.comap` along that homeomorphism carries the transition maps `pullbackMap` of
`abelianPullbackSystem` to the transition maps `SheafedSpaceLimit.trans` of
`SheafedSpaceLimit.pullSystem`.  Both are determined by their values on germwise pullbacks
(`SheafedSpaceLimit.pull_hom_ext`), so that is a single identity between germ-model sections; what
it needs is a description of `pullbackMap` on `GermPullback.ofSection` to match
`SheafedSpaceLimit.trans_ofSection` and `GermPullback.comap_ofSection`.  That identity is not
proved here.

Note that `isColimitPullCocone` alone does not give `IsStageSectionsColimit`: it presents
`c.pt.sheaf` as `colimₖ pₖ⁻¹𝒜ₖ`, and abelian Stacks 009F (4) on the vertex turns that into
`c.pt.sheaf(pⱼ⁻¹Z) = colimₖ (pₖ⁻¹𝒜ₖ)(pⱼ⁻¹Z)`, but the passage from there to the stage sections
`𝒜ₘ(f_b⁻¹Z)` is Stacks 0A32, which is available only over the concrete limit.  It is also what
makes the stagewise acyclicity used here unavoidable rather than a convenience: the Čech complex
of `pₖ⁻¹𝒜ₖ` for a cover of the vertex is *not* acyclic — inverse image does not preserve
injectives — so the colimit over `Jᵒᵖ` of the Čech complexes of the `pₖ⁻¹𝒜ₖ` cannot be shown
acyclic term by term, and the stage presentation is the only one in which injectivity can be used.

### Spelling

Everything is at `SpectralAbelianSheafSystem.{u, u, u}` with `J : Type u` a small category, the
collapse forced by the only available form of abelian Stacks 01FF.  `Injective` of a stage sheaf
is taken as an explicit argument and passed explicitly, because `TopCat.Sheaf` is a semireducible
`def` over `Sheaf (Opens.grothendieckTopology X)` and an `Injective` hypothesis stated at one of
the two spellings is not found by instance search at the other.

## References

* [Stacks Project, Tag 0A30](https://stacks.math.columbia.edu/tag/0A30)
* [Stacks Project, Tag 0A32](https://stacks.math.columbia.edu/tag/0A32)
* [Stacks Project, Tag 0A33](https://stacks.math.columbia.edu/tag/0A33)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.Basis (OpenCover)
open Stacks.Cohomology.Vanishing (compactCovers)

universe u

namespace Stacks.Cohomology.SpectralLimit

/-! ### Identities that `rw` cannot see

The three lemmas of this section exist to present terms which are already definitionally of the
required shape in a form that keyed matching recognises, and to apply naturality without
rewriting; see the implementation notes. -/

/-- **Two composites of restriction maps with the same source and target agree.**  The morphisms
of `Opens X` between a fixed pair of opens form a subsingleton, so the two composites are
restriction maps along one and the same morphism. -/
theorem presheaf_res_eq {X : TopCat.{u}} (P : X.Presheaf AddCommGrpCat.{u})
    {V₁ V₂ V₃ V₂' : (Opens ↥X)ᵒᵖ} (a : V₁ ⟶ V₂) (b : V₂ ⟶ V₃) (a' : V₁ ⟶ V₂')
    (b' : V₂' ⟶ V₃) : P.map a ≫ P.map b = P.map a' ≫ P.map b' := by
  rw [← P.map_comp, ← P.map_comp]
  exact congrArg P.map (Subsingleton.elim _ _)

/-- **A threefold composite of restriction maps is a single restriction map**, for the same
reason as `presheaf_res_eq`. -/
theorem presheaf_res_eq₃ {X : TopCat.{u}} (P : X.Presheaf AddCommGrpCat.{u})
    {V₁ V₂ V₃ V₄ : (Opens ↥X)ᵒᵖ} (a : V₁ ⟶ V₂) (b : V₂ ⟶ V₃) (d : V₃ ⟶ V₄) (ad : V₁ ⟶ V₄) :
    P.map a ≫ P.map b ≫ P.map d = P.map ad := by
  rw [← P.map_comp, ← P.map_comp]
  exact congrArg P.map (Subsingleton.elim _ _)

/-- **Naturality with a morphism appended**, stated so that it can be *applied* rather than
rewritten with.  The automatically generated `CategoryTheory.NatTrans.naturality_assoc` is this
statement, but `rw` matches at `instances` transparency and therefore does not recognise the
appended morphism when its source is the value of a pushforward functor. -/
theorem naturality_comp {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (α : F ⟶ G)
    {X Y : C} (f : X ⟶ Y) {T : D} (h : G.obj Y ⟶ T) :
    F.map f ≫ α.app Y ≫ h = α.app X ≫ G.map f ≫ h := by
  rw [← Category.assoc, α.naturality, Category.assoc]

/-- A restriction map of a pushforward presheaf is a restriction map of the presheaf along the
inverse image of the inclusion. -/
theorem pushforward_obj_map {X Y : TopCat.{u}} (f : X ⟶ Y) (P : X.Presheaf AddCommGrpCat.{u})
    {Z₁ Z₂ : (Opens ↥Y)ᵒᵖ} (m : Z₁ ⟶ Z₂) :
    ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj P).map m =
      P.map ((Opens.map f).map m.unop).op := rfl

namespace SpectralAbelianSheafSystem

variable {J : Type u} [SmallCategory J] [IsCofiltered J]
  (S : SpectralAbelianSheafSystem.{u, u, u} J)

/-! ### The system of stage presheaves pushed to a fixed stage -/

/-- **The opens of the slice diagram are nested**: for `h : B ⟶ A` in `Over i` the open
`f_{B.hom}⁻¹Z` is contained in — indeed equal to — `f_{h.left}⁻¹f_{A.hom}⁻¹Z`, because the base
maps compose, `f_{h.left} ≫ f_{A.hom} = f_{B.hom}`. -/
theorem mapOpen_le {i : J} {A B : Over i} (h : B ⟶ A) (Z : Opens (S.E.obj i)) :
    (Opens.map (S.E.map B.hom).hom.base).obj Z ≤
      (Opens.map (S.E.map h.left).hom.base).obj
        ((Opens.map (S.E.map A.hom).hom.base).obj Z) := by
  intro x hx
  have he : (S.E.map h.left).hom.base ≫ (S.E.map A.hom).hom.base =
      (S.E.map B.hom).hom.base := by
    change S.baseDiagram.map h.left ≫ S.baseDiagram.map A.hom = S.baseDiagram.map B.hom
    rw [← Functor.map_comp, Over.w h]
  change ((S.E.map h.left).hom.base ≫ (S.E.map A.hom).hom.base) x ∈ Z
  rw [he]
  exact hx

/-- **The stage diagram of abelian Stacks 0A33 is the `f`-map followed by a restriction**, as a
morphism of abelian groups.  This is `pushResSection_eq` read in the category rather than on
elements, with the restriction stated along `mapOpen_le`. -/
theorem abelianStageFunctor_map_eq {i : J} (Z : Opens (S.E.obj i)) {A B : (Over i)ᵒᵖ}
    (g : A ⟶ B) :
    (S.abelianStageFunctor Z).map g =
      (S.E.map g.unop.left).hom.c.app
          (op ((Opens.map (S.E.map A.unop.hom).hom.base).obj Z)) ≫
        (S.E.obj B.unop.left).presheaf.map (homOfLE (S.mapOpen_le g.unop Z)).op :=
  ConcreteCategory.hom_ext _ _ fun t ↦
    ((S.pushResSection_eq g.unop.left (S.typeSystem.stageOpen_le Z g.unop) t).trans
      (congrArg (fun mm ↦ ConcreteCategory.hom ((S.E.obj B.unop.left).presheaf.map mm)
        (S.pushSection g.unop.left t)) (Subsingleton.elim _ _))).trans
      (ConcreteCategory.comp_apply _ _ t).symm

/-- **The system of stage presheaves pushed to the stage `j`**: the functor
`(Over j)ᵒᵖ ⥤ Xⱼ.Presheaf AddCommGrpCat` sending `A` to `(f_{A.hom})_* 𝒜_{A.left}`.  Its value at
an open `Z` is the stage diagram `abelianStageFunctor Z` of abelian Stacks 0A33 on the nose, and
its functoriality is that of `abelianStageFunctor Z`, one `Z` at a time; the naturality in `Z` is
the content, and is the naturality of the `f`-map together with a subsingleton identity between
restriction maps. -/
def stageSystem (j : J) : (Over j)ᵒᵖ ⥤ ((S.E.obj j : TopCat.{u}).Presheaf AddCommGrpCat.{u}) where
  obj A := (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (S.E.map A.unop.hom).hom.base).obj
    (S.E.obj A.unop.left).presheaf
  map {A B} g :=
    { app := fun Z ↦ (S.abelianStageFunctor Z.unop).map g
      naturality := by
        intro Z₁ Z₂ m
        rw [S.abelianStageFunctor_map_eq, S.abelianStageFunctor_map_eq]
        refine Eq.trans (congrArg
          (fun z ↦ z ≫ (S.E.obj B.unop.left).presheaf.map
            (homOfLE (S.mapOpen_le g.unop Z₂.unop)).op)
          ((S.E.map g.unop.left).hom.c.naturality
            ((Opens.map (S.E.map A.unop.hom).hom.base).map m.unop).op)) ?_
        refine Eq.trans (Category.assoc _ _ _) ?_
        exact congrArg (fun z ↦ (S.E.map g.unop.left).hom.c.app
            (op ((Opens.map (S.E.map A.unop.hom).hom.base).obj Z₁.unop)) ≫ z)
          (presheaf_res_eq (S.E.obj B.unop.left).presheaf _ _ _ _) }
  map_id A := NatTrans.ext (funext fun Z ↦ (S.abelianStageFunctor Z.unop).map_id A)
  map_comp g g' := NatTrans.ext (funext fun Z ↦ (S.abelianStageFunctor Z.unop).map_comp g g')

/-- A restriction map of `stageSystem` is a restriction map of the stage presheaf along the
inverse image of the inclusion. -/
theorem stageSystem_obj_map (j : J) (A : (Over j)ᵒᵖ)
    {Z₁ Z₂ : (Opens ↥(S.E.obj j : TopCat.{u}))ᵒᵖ} (m : Z₁ ⟶ Z₂) :
    ((S.stageSystem j).obj A).map m =
      (S.E.obj A.unop.left).presheaf.map
        ((Opens.map (S.E.map A.unop.hom).hom.base).map m.unop).op := rfl

/-- The component at `Z` of a morphism of `stageSystem` is the corresponding morphism of the stage
diagram of abelian Stacks 0A33. -/
theorem stageSystem_map_app (j : J) {A B : (Over j)ᵒᵖ} (g : A ⟶ B)
    (Z : (Opens ↥(S.E.obj j : TopCat.{u}))ᵒᵖ) :
    ((S.stageSystem j).map g).app Z = (S.abelianStageFunctor Z.unop).map g := rfl

/-! ### The comparison cocone to the sections on the vertex -/

/-- **The open `pⱼ⁻¹Z` of the vertex is contained in — indeed equal to —
  `p_{A.left}⁻¹f_{A.hom}⁻¹Z`**,
because the cone projections compose with the transition maps. -/
theorem legOpen_le (c : Cone S.E) {j : J} (A : Over j) (Z : Opens (S.E.obj j)) :
    (Opens.map (c.π.app j).hom.base).obj Z ≤
      (Opens.map (c.π.app A.left).hom.base).obj
        ((Opens.map (S.E.map A.hom).hom.base).obj Z) := by
  intro x hx
  have he : (c.π.app A.left).hom.base ≫ (S.E.map A.hom).hom.base = (c.π.app j).hom.base :=
    ((SheafedSpace.forget _).mapCone c).w A.hom
  change ((c.π.app A.left).hom.base ≫ (S.E.map A.hom).hom.base) x ∈ Z
  rw [he]
  exact hx

/-- **The leg at `A` of the comparison cocone**, `(f_{A.hom})_* 𝒜_{A.left} ⟶ (pⱼ)_* c.pt.sheaf`:
over an open `Z` of the stage it is the sheaf component of the cone projection `p_{A.left}` at
`f_{A.hom}⁻¹Z`, followed by the restriction to `pⱼ⁻¹Z`. -/
def stageLeg (c : Cone S.E) {j : J} (A : Over j) :
    (S.stageSystem j).obj (op A) ⟶
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (c.π.app j).hom.base).obj c.pt.presheaf where
  app Z := (c.π.app A.left).hom.c.app (op ((Opens.map (S.E.map A.hom).hom.base).obj Z.unop)) ≫
    c.pt.presheaf.map (homOfLE (S.legOpen_le c A Z.unop)).op
  naturality := by
    intro Z₁ Z₂ m
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg
      (fun z ↦ z ≫ c.pt.presheaf.map (homOfLE (S.legOpen_le c A Z₂.unop)).op)
      ((c.π.app A.left).hom.c.naturality
        ((Opens.map (S.E.map A.hom).hom.base).map m.unop).op)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun z ↦ (c.π.app A.left).hom.c.app
        (op ((Opens.map (S.E.map A.hom).hom.base).obj Z₁.unop)) ≫ z)
      (presheaf_res_eq c.pt.presheaf
        ((Opens.map (c.π.app A.left).hom.base).map
          ((Opens.map (S.E.map A.hom).hom.base).map m.unop)).op
        (homOfLE (S.legOpen_le c A Z₂.unop)).op
        (homOfLE (S.legOpen_le c A Z₁.unop)).op
        ((Opens.map (c.π.app j).hom.base).map m.unop).op)) ?_
    exact (Category.assoc _ _ _).symm

/-- The component at `Z` of the leg at `A`. -/
theorem stageLeg_app (c : Cone S.E) {j : J} (A : Over j)
    (Z : (Opens ↥(S.E.obj j : TopCat.{u}))ᵒᵖ) :
    (S.stageLeg c A).app Z =
      (c.π.app A.left).hom.c.app (op ((Opens.map (S.E.map A.hom).hom.base).obj Z.unop)) ≫
        c.pt.presheaf.map (homOfLE (S.legOpen_le c A Z.unop)).op := rfl

/-- **The legs are compatible with the transition maps of the stage system.**  Over an open `Z`
the composition law of morphisms of presheafed spaces identifies the `f`-map of `g` followed by
the sheaf component of `p_{B.left}` with the sheaf component of `p_{B.left} ≫ f_{g.left}`, and
`AlgebraicGeometry.PresheafedSpace.congr_app` applied to the cone identity
`p_{B.left} ≫ f_{g.left} = p_{A.left}` turns that into the sheaf component of `p_{A.left}`
followed by one more restriction; the three restriction maps that remain collapse to the one on
the right-hand side. -/
theorem stageSystem_map_comp_stageLeg (c : Cone S.E) {j : J} {A B : (Over j)ᵒᵖ} (g : A ⟶ B) :
    (S.stageSystem j).map g ≫ S.stageLeg c B.unop = S.stageLeg c A.unop := by
  refine NatTrans.ext (funext fun Z ↦ ?_)
  rw [NatTrans.comp_app, stageSystem_map_app, stageLeg_app, stageLeg_app,
    S.abelianStageFunctor_map_eq]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg
    (fun z ↦ (S.E.map g.unop.left).hom.c.app
      (op ((Opens.map (S.E.map A.unop.hom).hom.base).obj Z.unop)) ≫ z)
    (naturality_comp (c.π.app B.unop.left).hom.c
      (homOfLE (S.mapOpen_le g.unop Z.unop)).op
      (c.pt.presheaf.map (homOfLE (S.legOpen_le c B.unop Z.unop)).op))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z ↦ z ≫
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u}
          (c.π.app B.unop.left).hom.base).obj c.pt.presheaf).map
        (homOfLE (S.mapOpen_le g.unop Z.unop)).op ≫
      c.pt.presheaf.map (homOfLE (S.legOpen_le c B.unop Z.unop)).op)
    (AlgebraicGeometry.PresheafedSpace.congr_app
      (congrArg (fun n ↦ n.hom) (c.w g.unop.left))
      (op ((Opens.map (S.E.map A.unop.hom).hom.base).obj Z.unop)))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (fun z ↦ (c.π.app A.unop.left).hom.c.app
      (op ((Opens.map (S.E.map A.unop.hom).hom.base).obj Z.unop)) ≫ z)
    (presheaf_res_eq₃ c.pt.presheaf _ _ _
      (homOfLE (S.legOpen_le c A.unop Z.unop)).op)

/-- **The comparison cocone of abelian Stacks 0A33 on the vertex of a cone, in presheaf form**:
from the system `A ↦ (f_{A.hom})_* 𝒜_{A.left}` of presheaves on the stage `Xⱼ` to
`(pⱼ)_* c.pt.sheaf`. -/
def stageCocone (c : Cone S.E) (j : J) : Cocone (S.stageSystem j) where
  pt := (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (c.π.app j).hom.base).obj c.pt.presheaf
  ι :=
    { app := fun A ↦ S.stageLeg c A.unop
      naturality := fun _ _ g ↦
        (S.stageSystem_map_comp_stageLeg c g).trans (Category.comp_id _).symm }

/-- **Abelian Stacks 0A33 on the vertex of a cone**: for every quasi-compact open `Z` of a stage
the comparison cocone of `stageCocone`, evaluated at `Z`, is a colimit cocone of abelian groups —
the sections of the sheaf on the vertex over `pⱼ⁻¹Z` are the filtered colimit of the stage
sections `𝒜ₘ(f_b⁻¹Z)` over `b : m ⟶ j`.

This is the one degree-zero input of the Čech computation below.  Over the concrete limit
`S.invLim` it is proved as `isColimitAbelianStageSectionsCocone`, with the same diagram; what
separates the two is the identification of the vertices, for which see the implementation
notes. -/
def IsStageSectionsColimit (c : Cone S.E) : Prop :=
  ∀ (j : J) (Z : Opens (S.E.obj j)), IsCompact (Z : Set (S.E.obj j)) →
    Nonempty (IsColimit (((evaluation (Opens ↥(S.E.obj j : TopCat.{u}))ᵒᵖ
      AddCommGrpCat.{u}).obj (op Z)).mapCocone (S.stageCocone c j)))

/-! ### Čech acyclicity at the stages -/

/-- **The positive-degree Čech cohomology of `(f_a)_* 𝒜ₖ` vanishes**, for every family of opens of
the target, whenever the stage sheaf `𝒜ₖ` is injective.

Pulling the family back along `f_a` does not change the Čech complex, only the space it is read
on (`Stacks.CategoryTheory.CechComplex.cechComplexPullbackIso`), and the Čech complex of an
injective abelian sheaf is acyclic in positive degrees because such a sheaf is flasque. -/
theorem isZero_cechComplex_homology_pushforward {k j : J} (a : k ⟶ j)
    (hI : Injective (S.E.obj k).sheaf) {T : Type u} (W : T → Opens (S.E.obj j))
    (p : ℕ) (hp : 0 < p) :
    IsZero (((cechComplexFunctor W).obj
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (S.E.map a).hom.base).obj
        (S.E.obj k).presheaf)).homology p) :=
  IsZero.of_iso
    (@Stacks.Cohomology.AbelianVanishing.isZero_cechComplex_homology_of_injective
      _ _ _ (S.E.obj k).sheaf hI
      (fun t ↦ (Opens.map (S.E.map a).hom.base).obj (W t)) p hp)
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).mapIso
      (Stacks.CategoryTheory.CechComplex.cechComplexPullbackIso
        (S.E.map a).hom.base W (S.E.obj k).presheaf)).symm

/-- **Every member of the stage system is Čech-acyclic in positive degrees** when every stage
sheaf is injective. -/
theorem isZero_cechComplex_homology_stageSystem (j : J)
    (hinj : ∀ k, Injective (S.E.obj k).sheaf)
    {T : Type u} (W : T → Opens (S.E.obj j)) (A : (Over j)ᵒᵖ) (p : ℕ) (hp : 0 < p) :
    IsZero (((cechComplexFunctor W).obj
      ((S.stageSystem j).obj A)).homology p) :=
  S.isZero_cechComplex_homology_pushforward A.unop.hom (hinj A.unop.left) W p hp

/-! ### The Čech complex on the vertex -/

/-- **The comparison out of the colimit of the stage system**,
`colim_{b : m → j} (f_b)_* 𝒜ₘ ⟶ (pⱼ)_* c.pt.sheaf`, as a morphism of presheaves on the stage. -/
def stageColimitDesc (c : Cone S.E) (j : J) :
    colimit (S.stageSystem j) ⟶
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (c.π.app j).hom.base).obj c.pt.presheaf :=
  colimit.desc (S.stageSystem j) (S.stageCocone c j)

/-- **The comparison is invertible over every quasi-compact open of the stage.**  Colimits of
presheaves are pointwise, so evaluation at an open carries the colimit cocone of the stage system
to a colimit cocone; over a quasi-compact open the evaluated comparison cocone is a colimit cocone
too, by hypothesis; and a morphism between two colimit cocones of one diagram is an
isomorphism. -/
theorem isIso_stageColimitDesc_app (c : Cone S.E) (hcol : S.IsStageSectionsColimit c)
    (j : J) (Z : Opens (S.E.obj j)) (hZ : IsCompact (Z : Set (S.E.obj j))) :
    IsIso ((S.stageColimitDesc c j).app (op Z)) := by
  obtain ⟨⟨g, hg₁, hg₂⟩⟩ := IsColimit.hom_isIso
    (isColimitOfPreserves
      ((evaluation (Opens ↥(S.E.obj j : TopCat.{u}))ᵒᵖ AddCommGrpCat.{u}).obj (op Z))
      (colimit.isColimit (S.stageSystem j)))
    (hcol j Z hZ).some
    (show ((evaluation (Opens ↥(S.E.obj j : TopCat.{u}))ᵒᵖ AddCommGrpCat.{u}).obj
          (op Z)).mapCocone (colimit.cocone (S.stageSystem j)) ⟶
        ((evaluation (Opens ↥(S.E.obj j : TopCat.{u}))ᵒᵖ AddCommGrpCat.{u}).obj
          (op Z)).mapCocone (S.stageCocone c j) from
      { hom := (S.stageColimitDesc c j).app (op Z)
        w := fun A ↦ congrArg (fun α ↦ NatTrans.app α (op Z))
          (colimit.ι_desc (S.stageCocone c j) A) })
  exact ⟨g.hom, congrArg (fun m ↦ m.hom) hg₁, congrArg (fun m ↦ m.hom) hg₂⟩

/-- **Čech acyclicity of the sheaf on the vertex, in positive degrees, for a finite family of
quasi-compact opens pulled back from a stage.**

The Čech complex of `pⱼ⁻¹W` with coefficients in `c.pt.sheaf` is the Čech complex of `W` with
coefficients in `(pⱼ)_* c.pt.sheaf`.  Every open occurring in the latter is a finite intersection
of the quasi-compact opens `W t`, hence quasi-compact — the stage is a spectral space, so quasi-
separated — so the comparison out of the colimit of the stage system is invertible on all of them
and the two Čech complexes agree.  The Čech complex of a finite family commutes with filtered
colimits, each stage complex is acyclic in positive degrees by injectivity, and a filtered colimit
of complexes acyclic in a positive degree is acyclic there. -/
theorem isZero_cechComplex_homology_pullbackFamily (c : Cone S.E)
    (hcol : S.IsStageSectionsColimit c) (hinj : ∀ k, Injective (S.E.obj k).sheaf)
    (j : J) {T : Type u} [Finite T] (W : T → Opens (S.E.obj j))
    (hW : ∀ t, IsCompact (W t : Set (S.E.obj j))) (n : ℕ) :
    IsZero (((cechComplexFunctor
        (fun t ↦ (Opens.map (c.π.app j).hom.base).obj (W t))).obj
      c.pt.presheaf).homology (n + 1)) := by
  have hsp : SpectralSpace ((S.E.obj j : TopCat.{u}) : Type u) := S.spectralSpace j
  have hInter : QuasiSeparatedSpace ((S.E.obj j : TopCat.{u}) : Type u) := inferInstance
  have hcpt : ∀ (m : ℕ) (x : Fin (m + 1) → T),
      IsCompact ((Stacks.CategoryTheory.CechComplex.inter W x : Opens (S.E.obj j)) :
        Set (S.E.obj j)) := by
    intro m x
    rw [Stacks.CategoryTheory.CechComplex.inter_eq_iInf]
    exact Stacks.Cohomology.Vanishing.isCompact_coe_iInf hInter (fun l ↦ W (x l)) fun l ↦ hW _
  have hzero : IsZero
      (((cechComplexFunctor W).obj
        (colimit (S.stageSystem j))).homology (n + 1)) :=
    Stacks.Cohomology.CechColimit.isZero_homology_cechComplex_of_isColimit W
      (colimit.isColimit (S.stageSystem j)) (n + 1) (Nat.succ_pos n)
      (fun A ↦ S.isZero_cechComplex_homology_stageSystem j hinj W A (n + 1) (Nat.succ_pos n))
  refine IsZero.of_iso hzero
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) (n + 1)).mapIso
      ((Stacks.CategoryTheory.CechComplex.cechComplexPullbackIso
        (c.π.app j).hom.base W c.pt.presheaf) ≪≫
      (Stacks.CategoryTheory.CechComplex.cechComplexIsoOfIsoOnInter W (S.stageColimitDesc c j)
        (fun m x ↦ S.isIso_stageColimitDesc_app c hcol j _ (hcpt m x))).symm))

/-- **A finite family of quasi-compact opens of the vertex is the family of inverse images of
quasi-compact opens of a single stage.**

Each member descends to its own stage by part (1) of Stacks 0A30 for an abstract limiting cone,
`SpectralLimits.descent_of_quasiCompact_opens_of_isLimit`, and
`CategoryTheory.IsCofiltered.inf_objs_exists` supplies one stage mapping to all of those; pulling
back there keeps the opens quasi-compact because the transition maps are spectral.  No covering
condition occurs, and part (3) of Stacks 0A30 is not needed: Čech acyclicity of a flasque sheaf
holds for an arbitrary family of opens, so the Čech computation does not use that the family
covers anything. -/
theorem exists_stageFamily (c : Cone S.E) (hc : IsLimit c) {T : Type u} [Finite T]
    (V : T → Opens ((c.pt : TopCat.{u}) : Type u))
    (hV : ∀ t, IsCompact ((V t : Set ((c.pt : TopCat.{u}) : Type u)))) :
    ∃ (j : J) (W : T → Opens (S.E.obj j)),
      (∀ t, IsCompact ((W t : Set (S.E.obj j)))) ∧
        ∀ t, (Opens.map (c.π.app j).hom.base).obj (W t) = V t := by
  classical
  have : Fintype T := Fintype.ofFinite T
  have hsp : ∀ k, SpectralSpace (S.baseDiagram.obj k) := S.spectralSpace
  choose k Vk hVko hVkc hVkeq using fun t ↦
    SpectralLimits.descent_of_quasiCompact_opens_of_isLimit S.baseDiagram
      (fun _ _ a ↦ S.spectralMap a) ((SheafedSpace.forget AddCommGrpCat.{u}).mapCone c)
      (SheafedSpaceLimit.isLimit_mapCone_forget hc)
      ((V t : Set ((c.pt : TopCat.{u}) : Type u))) (V t).isOpen (hV t)
  obtain ⟨m, hm⟩ := IsCofiltered.inf_objs_exists (Finset.image k Finset.univ)
  let bk : ∀ t, m ⟶ k t := fun t ↦
    (hm (Finset.mem_image.2 ⟨t, Finset.mem_univ t, rfl⟩)).some
  have hWo : ∀ t, IsOpen ((S.baseDiagram.map (bk t)) ⁻¹' (Vk t)) := fun t ↦
    (S.spectralMap (bk t)).toContinuous.isOpen_preimage _ (hVko t)
  have hWc : ∀ t, IsCompact ((S.baseDiagram.map (bk t)) ⁻¹' (Vk t)) := fun t ↦
    (S.spectralMap (bk t)).isCompact_preimage_of_isOpen (hVko t) (hVkc t)
  have hWpre : ∀ t, ((SheafedSpace.forget AddCommGrpCat.{u}).mapCone c).π.app m ⁻¹'
      ((S.baseDiagram.map (bk t)) ⁻¹' (Vk t)) =
      (V t : Set ((c.pt : TopCat.{u}) : Type u)) := fun t ↦ by
    rw [← Set.preimage_comp,
      show (ConcreteCategory.hom (S.baseDiagram.map (bk t))) ∘
            (ConcreteCategory.hom
              (((SheafedSpace.forget AddCommGrpCat.{u}).mapCone c).π.app m)) =
          ConcreteCategory.hom
            (((SheafedSpace.forget AddCommGrpCat.{u}).mapCone c).π.app (k t)) from
        funext fun x ↦ ConcreteCategory.congr_hom
          (((SheafedSpace.forget AddCommGrpCat.{u}).mapCone c).w (bk t)) x]
    exact hVkeq t
  exact ⟨m, fun t ↦ ⟨(S.baseDiagram.map (bk t)) ⁻¹' (Vk t), hWo t⟩, hWc,
    fun t ↦ Opens.ext (hWpre t)⟩

/-- **The positive-degree Čech cohomology of the sheaf on the vertex of a limiting cone vanishes
for every finite cover of a quasi-compact open of the vertex by quasi-compact opens**, when every
stage sheaf is injective.

This is the statement that the Čech reduction of the quasi-compact-open clause of Stacks 0A37
asks for.  The cover descends to a single stage by `exists_stageFamily`, and
`isZero_cechComplex_homology_pullbackFamily` computes its Čech complex there. -/
theorem isZero_cechComplex_homology_conePoint_of_injective (c : Cone S.E) (hc : IsLimit c)
    (hcol : S.IsStageSectionsColimit c) (hinj : ∀ k, Injective (S.E.obj k).sheaf)
    (W : OpenCover ((c.pt : TopCat.{u}) : Type u))
    (hW : W ∈ compactCovers ((c.pt : TopCat.{u}) : Type u)) (n : ℕ) :
    IsZero (((cechComplexFunctor W.obj).obj
      c.pt.sheaf.obj).homology (n + 1)) := by
  have : Finite W.ι := hW.1
  obtain ⟨j, W', hW'c, hW'eq⟩ := S.exists_stageFamily c hc W.obj hW.2.2
  refine Eq.mp (congrArg (fun F ↦ IsZero
    (((cechComplexFunctor F).obj
      c.pt.sheaf.obj).homology (n + 1))) (funext hW'eq)) ?_
  exact S.isZero_cechComplex_homology_pullbackFamily c hcol hinj j W' hW'c n

/-! ### The quasi-compact-open clause of Stacks 0A37 for a system of injective sheaves -/

/-- **The vanishing needed on the limit side of Stacks 0A37**:
`Hⁿ⁺¹(pᵢ⁻¹U, c.pt.sheaf) = 0` for a system of injective sheaves.  This is
`isZero_H'_succ_conePoint_of_cechAcyclic` — abelian Stacks 01EW on the vertex, which is a spectral
space — with its Čech hypothesis supplied by
`isZero_cechComplex_homology_conePoint_of_injective`. -/
theorem isZero_H'_succ_conePoint_of_injective (c : Cone S.E) (hc : IsLimit c)
    (hcol : S.IsStageSectionsColimit c) (hinj : ∀ k, Injective (S.E.obj k).sheaf)
    (i : J) (U : Opens (S.E.obj i)) (hU : IsCompact (U : Set (S.E.obj i))) (n : ℕ) :
    IsZero (Sheaf.H'.{u, u, u} c.pt.sheaf (n + 1) (S.stageOpenCone c i U).pt) :=
  S.isZero_H'_succ_conePoint_of_cechAcyclic c hc i U hU
    (fun W hW p hp ↦ by
      obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp).symm⟩
      exact S.isZero_cechComplex_homology_conePoint_of_injective c hc hcol hinj W hW m) n

/-- **The quasi-compact-open clause of Stacks 0A37 in positive degree for a system of injective
sheaves**: every presentation of the cohomology cocone over a quasi-compact open `U` of a stage is
a colimit cocone in degree `n + 1`.

This is `isColimit_cohomologyCocone_of_injective_system` with its single hypothesis — the
vanishing on the vertex — discharged by `isZero_H'_succ_conePoint_of_injective`. -/
def isColimit_cohomologyCocone_of_injective (c : Cone S.E) (hc : IsLimit c)
    (hcol : S.IsStageSectionsColimit c) (hinj : ∀ k, Injective (S.E.obj k).sheaf)
    (i : J) (U : Opens (S.E.obj i)) (hU : IsCompact (U : Set (S.E.obj i))) (n : ℕ)
    (D : CohomologyCocone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i))
      (S.stageOpenCone c i U) (n + 1)) :
    IsColimit D.cocone :=
  S.isColimit_cohomologyCocone_of_injective_system c hc i U hU n hinj
    (S.isZero_H'_succ_conePoint_of_injective c hc hcol hinj i U hU n) D

/-- **The quasi-compact-open clause of Stacks 0A37 for a system of injective sheaves, in the form
the clause states it**: the comparison out of the colimit of the stage cohomology groups is an
isomorphism. -/
theorem isIso_comparison_of_injective (c : Cone S.E) (hc : IsLimit c)
    (hcol : S.IsStageSectionsColimit c) (hinj : ∀ k, Injective (S.E.obj k).sheaf)
    (i : J) (U : Opens (S.E.obj i)) (hU : IsCompact (U : Set (S.E.obj i))) (n : ℕ)
    (D : CohomologyCocone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i))
      (S.stageOpenCone c i U) (n + 1)) :
    IsIso D.comparison :=
  CohomologyCocone.isIso_comparison_of_isColimit D
    (S.isColimit_cohomologyCocone_of_injective c hc hcol hinj i U hU n D)

end SpectralAbelianSheafSystem

end Stacks.Cohomology.SpectralLimit

end
