module

public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralLimitVertex.VanishingFromCechAcyclicity
public import StacksFrontier.Topology.Spectral.LimitOpenDescent

/-!
# Descent of a finite quasi-compact cover from the vertex of a limiting cone to a stage

Stacks 0A30 is proved in `StacksFrontier.Topology.Spectral.LimitOpenDescent` for the *chosen* limit
`Limits.limit F` of a cofiltered diagram `F : J ⥤ TopCat` of spectral spaces: part (1) descends a
quasi-compact open of the limit to a stage, and part (3) descends an equality of a quasi-compact
open with a finite union of quasi-compact opens at one stage to a stage below it.

The colimit-comparison clauses of Stacks 0A37 are about the vertex of an *abstract* limiting cone
of abelian sheafed spaces, and the Čech reduction of the vanishing on the limit side
(`StacksDraft.Ch20.Sec16.Tag0A37CechVanishing`) asks for Čech complexes of covers of `pᵢ⁻¹U` by
quasi-compact opens of that vertex.  This file bridges the two: it transports parts (1) and (3)
of Stacks 0A30 to an arbitrary limiting cone, and then assembles them into the statement the Čech
argument needs — **a finite cover of `pᵢ⁻¹U` by quasi-compact opens of the vertex is the inverse
image of a finite cover of `f_a⁻¹U` by quasi-compact opens of a stage.**

The transport is a change of model, not new mathematics: two limiting cones over one diagram have
canonically isomorphic vertices (`CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso`), the
isomorphism is a homeomorphism commuting with the projections, and every hypothesis and
conclusion of Stacks 0A30 is a statement about preimages along the projections, so it transfers
along a bijection of the vertices.

The assembly is where cofilteredness is used twice.  Each member of the cover descends to its own
stage by part (1), and `CategoryTheory.IsCofiltered.inf_objs_exists` produces one stage mapping to
all of them *and* to the stage `i` carrying `U`; pulling the descended opens back to that common
stage keeps them quasi-compact because the transition maps are spectral.  At that stage the cover
equation holds only after taking preimages in the vertex, and part (3) moves it down one more
stage, which is the stage the conclusion names.

## Main results

* `SpectralLimits.descent_of_quasiCompact_opens_of_isLimit`: **Stacks 0A30 (1) for an abstract
  limiting cone** — every quasi-compact open of the vertex is the inverse image of a quasi-compact
  open of a stage.
* `SpectralLimits.descent_of_finite_unions_of_isLimit`: **Stacks 0A30 (3) for an abstract limiting
  cone.**
* `SpectralLimits.exists_stage_cover_of_isLimit`: the two combined, for a diagram of spaces: a
  finite family of quasi-compact opens of the vertex whose union is the inverse image of a
  quasi-compact open `U` of the stage `i` is, after passing to a stage `j ⟶ i`, the family of
  inverse images of a finite family of quasi-compact opens of `F.obj j` whose union is the inverse
  image of `U`.
* `Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem.exists_stageOpenCover`: the same in
  the `Opens` language of Stacks 0A37, over the open `pᵢ⁻¹U` carried by the open cone of the
  quasi-compact-open clause.  **This is the geometric input of the Čech computation of
  `Hⁿ⁺¹(pᵢ⁻¹U, c.pt.sheaf)`.**

## Implementation notes

Stacks 0A30 is stated with sets and `Set.preimage`, Stacks 0A37 with `TopologicalSpace.Opens` and
`TopologicalSpace.Opens.map`.  The translation is done once, in `exists_stageOpenCover`: an
`Opens` is determined by its carrier, `(Opens.map f).obj V` has carrier `f ⁻¹' V` by `rfl`, and a
supremum of opens has carrier the union of the carriers (`TopologicalSpace.Opens.coe_iSup`).  No
`Opens`-level form of Stacks 0A30 is introduced, because the set-level form is what the two
cofilteredness steps are naturally phrased in.

That translation is carried out **in term mode**, and it has to be.  The two spellings of the
space underlying the stage `i` — `S.E.obj i` read through the `SheafedSpace` coercion and
`(S.E ⋙ SheafedSpace.forget _).obj i` — are equal only by unfolding `Functor.comp` and
`SheafedSpace.forget`, so a `rw` whose motive spans them is refused as not type-correct at the
`implicit` transparency level, and so is the `ext`/`simp` route into membership, which produces
the same motive.  `Eq.trans` and `congrArg` check their arguments up to full definitional
equality, so the carrier equality is assembled from `congrArg` of the coercion applied to the
hypothesis, composed with `TopologicalSpace.Opens.coe_iSup`, and handed to
`TopologicalSpace.Opens.ext`.  The general set-level statements in the `SpectralLimits` namespace
are free of this, because they never leave one spelling of the diagram.

The spectrality hypotheses of Stacks 0A30 are supplied for the diagram of underlying spaces
`S.baseDiagram = S.E ⋙ SheafedSpace.forget _` from the fields of
`Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem`, and the limiting cone of spaces is
`(SheafedSpace.forget _).mapCone c`, a limiting cone by
`Stacks.Cohomology.SpectralLimit.SheafedSpaceLimit.isLimit_mapCone_forget` — the forgetful functor
to spaces is a right adjoint, so it preserves limits.  That is also why the statement here is
about an abstract cone rather than about the concrete inverse limit: the sheaf on the vertex is
exhibited as a colimit of inverse images only over an abstract cone.

## References

* [Stacks Project, Tag 0A30](https://stacks.math.columbia.edu/tag/0A30)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u v

namespace SpectralLimits

variable {J : Type v} [SmallCategory J] [IsCofiltered J]
variable (F : J ⥤ TopCat.{max v u})

omit [IsCofiltered J] in
/-- The comparison homeomorphism commutes with the projections. -/
private theorem homeo_proj (c : Cone F) (hc : IsLimit c) (i : J) (x : ↥c.pt) :
    limit.π F i (TopCat.homeoOfIso (hc.conePointUniqueUpToIso (limit.isLimit F)) x) =
      c.π.app i x :=
  ConcreteCategory.congr_hom (hc.conePointUniqueUpToIso_hom_comp (limit.isLimit F) i) x

omit [IsCofiltered J] in
/-- A preimage along a projection of an abstract limiting cone is the preimage, along the
comparison homeomorphism with the chosen limit, of the corresponding preimage there. -/
private theorem preimage_proj_eq (c : Cone F) (hc : IsLimit c) (i : J) (V : Set (F.obj i)) :
    c.π.app i ⁻¹' V =
      TopCat.homeoOfIso (hc.conePointUniqueUpToIso (limit.isLimit F)) ⁻¹' (limit.π F i ⁻¹' V) := by
  ext x
  simp only [Set.mem_preimage, homeo_proj F c hc i x]

omit [IsCofiltered J] in
/-- Pulling back along a transition map and then a projection is pulling back along the
other projection. -/
theorem preimage_proj_preimage_map (c : Cone F) {m k : J} (f : m ⟶ k) (X : Set (F.obj k)) :
    c.π.app m ⁻¹' ((F.map f) ⁻¹' X) = c.π.app k ⁻¹' X := by
  rw [← Set.preimage_comp,
    show (ConcreteCategory.hom (F.map f)) ∘ (ConcreteCategory.hom (c.π.app m)) =
        ConcreteCategory.hom (c.π.app k) from
      funext fun x => ConcreteCategory.congr_hom (c.w f) x]

/-- The preimage of a quasi-compact open under a spectral map is a quasi-compact open. -/
private theorem isOpen_and_isCompact_preimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsSpectralMap f) {V : Set Y} (ho : IsOpen V)
    (hc : IsCompact V) : IsOpen (f ⁻¹' V) ∧ IsCompact (f ⁻¹' V) :=
  ⟨hf.toContinuous.isOpen_preimage _ ho, hf.isCompact_preimage_of_isOpen ho hc⟩

/-- **Stacks 0A30 (1) for an abstract limiting cone.**  Every quasi-compact open of the vertex of
a limiting cone of a cofiltered diagram of spectral spaces with spectral transition maps is the
inverse image of a quasi-compact open of some stage.

This is `SpectralLimits.descent_of_quasiCompact_opens` read through the comparison homeomorphism
with the chosen limit: the open transported to the chosen limit stays open and quasi-compact, and
pulling the resulting equality of preimages back along the homeomorphism gives the equality
asserted here. -/
theorem descent_of_quasiCompact_opens_of_isLimit [∀ i, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃i j : J⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (c : Cone F) (hc : IsLimit c)
    (V : Set ↥c.pt) (hVopen : IsOpen V) (hVcpt : IsCompact V) :
    ∃ (i : J) (Vi : Set (F.obj i)), IsOpen Vi ∧ IsCompact Vi ∧ c.π.app i ⁻¹' Vi = V := by
  set e := TopCat.homeoOfIso (hc.conePointUniqueUpToIso (limit.isLimit F))
  obtain ⟨i, Vi, hVio, hVic, hVieq⟩ :=
    descent_of_quasiCompact_opens F hF (e.symm ⁻¹' V)
      (e.symm.continuous.isOpen_preimage _ hVopen) (e.symm.isCompact_preimage.2 hVcpt)
  refine ⟨i, Vi, hVio, hVic, ?_⟩
  rw [preimage_proj_eq F c hc i Vi, hVieq]
  ext x
  simp only [Set.mem_preimage, e, Homeomorph.symm_apply_apply]

/-- **Stacks 0A30 (3) for an abstract limiting cone.**  If, in the vertex of a limiting cone, the
inverse image of a quasi-compact open `Ui` of a stage `i` is the union of the inverse images of
finitely many quasi-compact opens of that same stage, then the equality already holds after
pulling back along some `a : j ⟶ i`.

Both the hypothesis and the conclusion only involve preimages along the projections, so this is
`SpectralLimits.descent_of_finite_unions` with every preimage along `c.π.app i` rewritten as a
preimage along `limit.π F i` followed by the comparison homeomorphism; taking preimages along a
surjection is injective on subsets, which is what lets the hypothesis be transported. -/
theorem descent_of_finite_unions_of_isLimit [∀ i, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃i j : J⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (c : Cone F) (hc : IsLimit c)
    (i : J) (n : ℕ) (Ui : Set (F.obj i)) (U : Fin n → Set (F.obj i))
    (hUi_open : IsOpen Ui) (hUi_cpt : IsCompact Ui)
    (hU : ∀ s, IsOpen (U s) ∧ IsCompact (U s))
    (h : c.π.app i ⁻¹' Ui = ⋃ s, c.π.app i ⁻¹' (U s)) :
    ∃ (j : J) (a : j ⟶ i), (F.map a) ⁻¹' Ui = ⋃ s, (F.map a) ⁻¹' (U s) := by
  refine descent_of_finite_unions F hF i n Ui U hUi_open hUi_cpt hU ?_
  apply Set.preimage_injective.2
    (TopCat.homeoOfIso (hc.conePointUniqueUpToIso (limit.isLimit F))).surjective
  rw [Set.preimage_iUnion]
  simpa only [preimage_proj_eq F c hc i] using h

/-- **A finite quasi-compact cover of the inverse image of a quasi-compact open descends to a
stage.**  Let `c` be a limiting cone of a cofiltered diagram of spectral spaces with spectral
transition maps, let `U` be a quasi-compact open of the stage `i`, and let `V : Fin n → Set c.pt`
be quasi-compact opens whose union is `pᵢ⁻¹U`.  Then there are a stage `j`, a map `a : j ⟶ i` and
quasi-compact opens `W : Fin n → Set (F.obj j)` with `pⱼ⁻¹(W t) = V t` for every `t` and
`f_a⁻¹U = ⋃ t, W t`.

Each `V t` descends to some stage by `descent_of_quasiCompact_opens_of_isLimit`;
`CategoryTheory.IsCofiltered.inf_objs_exists` supplies a single stage mapping to all of those and
to `i`, and pulling back there keeps the opens quasi-compact because the transition maps are
spectral.  The union equation then holds at that stage only after taking preimages in the vertex,
and `descent_of_finite_unions_of_isLimit` descends it one further stage. -/
theorem exists_stage_cover_of_isLimit [∀ i, SpectralSpace (F.obj i)]
    (hF : ∀ ⦃i j : J⦄ (a : i ⟶ j), IsSpectralMap (F.map a))
    (c : Cone F) (hc : IsLimit c) (i : J) (U : Set (F.obj i))
    (hUopen : IsOpen U) (hUcpt : IsCompact U) (n : ℕ)
    (V : Fin n → Set ↥c.pt) (hVopen : ∀ t, IsOpen (V t))
    (hVcpt : ∀ t, IsCompact (V t)) (hcov : c.π.app i ⁻¹' U = ⋃ t, V t) :
    ∃ (j : J) (a : j ⟶ i) (W : Fin n → Set (F.obj j)),
      (∀ t, IsOpen (W t)) ∧ (∀ t, IsCompact (W t)) ∧
        (∀ t, c.π.app j ⁻¹' (W t) = V t) ∧
        (F.map a) ⁻¹' U = ⋃ t, W t := by
  classical
  choose k Vk hVko hVkc hVkeq using fun t =>
    descent_of_quasiCompact_opens_of_isLimit F hF c hc (V t) (hVopen t) (hVcpt t)
  obtain ⟨m, hm⟩ := IsCofiltered.inf_objs_exists (Finset.image k Finset.univ ∪ {i})
  obtain ⟨b⟩ := hm (Finset.mem_union_right _ (Finset.mem_singleton_self i))
  let bk : ∀ t, m ⟶ k t := fun t =>
    (hm (Finset.mem_union_left ({i} : Finset J)
      (Finset.mem_image.2 ⟨t, Finset.mem_univ t, rfl⟩))).some
  have hW : ∀ t, IsOpen ((F.map (bk t)) ⁻¹' (Vk t)) ∧ IsCompact ((F.map (bk t)) ⁻¹' (Vk t)) :=
    fun t => isOpen_and_isCompact_preimage (hF (bk t)) (hVko t) (hVkc t)
  have hWpre : ∀ t, c.π.app m ⁻¹' ((F.map (bk t)) ⁻¹' (Vk t)) = V t := fun t =>
    (preimage_proj_preimage_map F c (bk t) (Vk t)).trans (hVkeq t)
  have hcovm : c.π.app m ⁻¹' ((F.map b) ⁻¹' U) =
      ⋃ t, c.π.app m ⁻¹' ((F.map (bk t)) ⁻¹' (Vk t)) := by
    rw [preimage_proj_preimage_map F c b U, hcov]
    exact (Set.iUnion_congr hWpre).symm
  obtain ⟨j, a, haeq⟩ := descent_of_finite_unions_of_isLimit F hF c hc m n
    ((F.map b) ⁻¹' U) (fun t => (F.map (bk t)) ⁻¹' (Vk t))
    (isOpen_and_isCompact_preimage (hF b) hUopen hUcpt).1
    (isOpen_and_isCompact_preimage (hF b) hUopen hUcpt).2 hW hcovm
  refine ⟨j, a ≫ b, fun t => (F.map a) ⁻¹' ((F.map (bk t)) ⁻¹' (Vk t)),
    fun t => (isOpen_and_isCompact_preimage (hF a) (hW t).1 (hW t).2).1,
    fun t => (isOpen_and_isCompact_preimage (hF a) (hW t).1 (hW t).2).2,
    fun t => (preimage_proj_preimage_map F c a _).trans (hWpre t), ?_⟩
  rw [F.map_comp]
  simpa only [TopCat.coe_comp, Set.preimage_comp, Set.preimage_iUnion] using haeq

end SpectralLimits

namespace Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem

open Stacks.Cohomology Stacks.Cohomology.SpectralLimit
open Stacks.Cohomology.SpectralLimit.SheafedSpaceLimit

variable {J : Type u} [SmallCategory J] [IsCofiltered J]
  (S : SpectralAbelianSheafSystem.{u, u, u} J)

/-- **A finite cover of `pᵢ⁻¹U` by quasi-compact opens of the vertex is the inverse image of a
finite cover of `f_a⁻¹U` by quasi-compact opens of a stage.**  Here `U` is a quasi-compact open of
the stage `i` and `pᵢ⁻¹U` is `(S.stageOpenCone c i U).pt`, the open on the vertex carried by the
open cone of the quasi-compact-open clause of Stacks 0A37.

This is `SpectralLimits.exists_stage_cover_of_isLimit` applied to the diagram of underlying spaces
`S.baseDiagram`, whose stages are spectral and whose transition maps are spectral by the fields of
`SpectralAbelianSheafSystem`, and to the limiting cone `(SheafedSpace.forget _).mapCone c` of
spaces obtained from `c` by `SheafedSpaceLimit.isLimit_mapCone_forget`.  Opens are translated to
their carriers: `(Opens.map f).obj V` has carrier `f ⁻¹' V`, and a supremum of opens has carrier
the union of the carriers.

Together with the Čech reduction `isZero_H'_succ_conePoint_of_cechAcyclic`, this is what reduces
the vanishing of `Hⁿ⁺¹(pᵢ⁻¹U, c.pt.sheaf)` to a statement about Čech complexes of covers living
on a single stage. -/
theorem exists_stageOpenCover (c : Cone S.E) (hc : IsLimit c) (i : J)
    (U : Opens (S.E.obj i)) (hU : IsCompact (U : Set (S.E.obj i))) (n : ℕ)
    (V : Fin n → Opens ((c.pt : TopCat.{u}) : Type u))
    (hV : ∀ t, IsCompact ((V t : Set ((c.pt : TopCat.{u}) : Type u))))
    (hcov : (S.stageOpenCone c i U).pt = ⨆ t, V t) :
    ∃ (j : J) (a : j ⟶ i) (W : Fin n → Opens (S.E.obj j)),
      (∀ t, IsCompact ((W t : Set (S.E.obj j)))) ∧
        (∀ t, (Opens.map (c.π.app j).hom.base).obj (W t) = V t) ∧
        (Opens.map (S.E.map a).hom.base).obj U = ⨆ t, W t := by
  have hsp : ∀ k, SpectralSpace (S.baseDiagram.obj k) := S.spectralSpace
  obtain ⟨j, a, W, hWo, hWc, hWpre, hWcov⟩ :=
    SpectralLimits.exists_stage_cover_of_isLimit S.baseDiagram (fun _ _ a => S.spectralMap a)
      ((SheafedSpace.forget AddCommGrpCat.{u}).mapCone c)
      (SheafedSpaceLimit.isLimit_mapCone_forget hc) i
      (U : Set (S.E.obj i)) U.isOpen hU n
      (fun t => (V t : Set ((c.pt : TopCat.{u}) : Type u)))
      (fun t => (V t).isOpen) hV
      ((congrArg (fun Z : Opens ((c.pt : TopCat.{u}) : Type u) =>
        (Z : Set ((c.pt : TopCat.{u}) : Type u))) hcov).trans (Opens.coe_iSup V))
  exact ⟨j, a, fun t => ⟨W t, hWo t⟩, hWc,
    fun t => Opens.ext (hWpre t),
    Opens.ext (hWcov.trans
      (Opens.coe_iSup (fun t => (⟨W t, hWo t⟩ : Opens (S.E.obj j)))).symm)⟩

end Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem

end
