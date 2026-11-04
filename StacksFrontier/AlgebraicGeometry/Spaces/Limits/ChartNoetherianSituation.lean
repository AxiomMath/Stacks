module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.NoetherianSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent

/-!
# The limit-Noetherian situation carried by an affine chart of a stage

Let `B = lim_i B_i` be the limit of a directed inverse system of Noetherian algebraic spaces
over a scheme `S` with affine transition morphisms — an
`AlgebraicGeometry.Space.NoetherianLimitSystem`, Stacks 0CP6 — and let `U_i ⟶ B_i` be an affine
scheme-valued point of one of its stages. Base changing the later stages along it produces the
system of affine charts `U_{i'} = B_{i'} ×_{B_i} U_i` of
`AlgebraicGeometry.Space.AffineChartSystem`, whose limit is the chart `B ×_{B_i} U_i` of the
limit space. This file exhibits that system of charts as an
`AlgebraicGeometry.LimitNoetherianSituation` on the stages above `i`, which is the shape in
which the scheme-theoretic results about limits of Noetherian schemes are stated.

Two indexings have to be reconciled for this. A chart system is indexed by the slice
`Over (op i)` of `Iᵒᵖ`, because that is how a later stage together with its transition morphism
to the stage `i` is presented; a limit-Noetherian situation is indexed by the opposite of a
directed preorder. The stages above `i` form the directed preorder `Set.Ici i`, and
`CategoryTheory.iciOpEquivalenceOverOp` identifies `(Set.Ici i)ᵒᵖ` with `Over (op i)`: a
morphism `op i' ⟶ op i` of `Iᵒᵖ` is exactly an inequality `i ≤ i'`.

## Main definitions

* `CategoryTheory.iciOpToOverOp`, `CategoryTheory.overOpToIciOp` and
  `CategoryTheory.iciOpEquivalenceOverOp`: the two functors between `(Set.Ici i)ᵒᵖ` and the
  slice of `Iᵒᵖ` over `op i`, and the equivalence of categories they form.
* `AlgebraicGeometry.LimitNoetherianSituation.ofOverOp`: a diagram of Noetherian schemes with
  affine transition morphisms indexed by `Over (op i)`, together with a limit cone, read as a
  limit-Noetherian situation indexed by `Set.Ici i`.
* `AlgebraicGeometry.Space.NoetherianLimitSystem.limitIso`: the comparison isomorphism between
  the limit of the system of presheaves of a Noetherian limit system and the chosen limit
  space.
* `AlgebraicGeometry.Space.NoetherianLimitSystem.chartSystem`: the system of affine charts at a
  stage of a Noetherian limit system.
* `AlgebraicGeometry.Space.NoetherianLimitSystem.chartSituation`: the limit-Noetherian
  situation carried by that chart system, with
  `AlgebraicGeometry.Space.NoetherianLimitSystem.chartToLimit` the morphism from the chart of
  the limit space to the limit space.
* `AlgebraicGeometry.Space.NoetherianLimitSystem.chartLimitBridge` and
  `AlgebraicGeometry.Space.NoetherianLimitSystem.etaleChartSituation`: the limit of the chart
  system, and the chart situation, for an affine étale chart of the stage over an index type
  small enough for the site.

## Main results

* `AlgebraicGeometry.Space.NoetherianLimitSystem.isPullback_chartToLimit`: the limit of the
  chart situation is the chart `B ×_{B_i} U_i` of the limit space, that is, the fibre product
  of the limit space with `U_i` over the stage `B_i`.
* `AlgebraicGeometry.Space.NoetherianLimitSystem.isAffine_chartSituation_limitScheme`: that
  limit is an affine scheme.
* `AlgebraicGeometry.Space.NoetherianLimitSystem.isNoetherian_chart`: a chart of a stage is a
  Noetherian scheme when the chosen point of the stage is étale, so that
  `AlgebraicGeometry.Space.NoetherianLimitSystem.chartSituation` applies to an étale chart.

## Implementation notes

The stages above `i` are presented as the subtype `Set.Ici i`; its `Preorder` instance is the
one induced on a subtype, nonemptiness is `Set.nonempty_Ici_subtype`, and
`Set.Ici.instIsDirectedOrder` records that directedness is inherited from the ambient preorder.

Both `(Set.Ici i)ᵒᵖ` and `Over (op i)` are thin, so every coherence condition in the
equivalence between them is an instance of `Subsingleton.elim`; the unit and counit are
identities because an object of `Over (op i)` is reconstructed from its source and the
inequality underlying its structure morphism up to definitional equality only.

A limit-Noetherian situation is produced from the chart system rather than transported from a
preexisting one, because the chart system is a bare diagram with a limit cone and not itself a
situation: what is transported is its limiting cone, by
`CategoryTheory.Limits.IsLimit.whiskerEquivalence`.

Noetherianity of the individual charts is a hypothesis of
`AlgebraicGeometry.Space.NoetherianLimitSystem.chartSituation` rather than being derived
inside it, so that the construction does not depend on the chosen point of the stage being
étale; `AlgebraicGeometry.Space.NoetherianLimitSystem.isNoetherian_chart` discharges it in the
étale case. There local Noetherianity comes from
`AlgebraicGeometry.Space.exists_atlas_iff_forall_etale`, which turns Noetherianity of the stage
into local Noetherianity of every scheme étale over it, and quasi-compactness comes from the
chart being affine. Étaleness of the chart of a later stage is étaleness of the chosen point of
`B_i` base changed along the transition morphism, which is
`AlgebraicGeometry.Space.presheaf_of_isPullback`.

The limit of a chart system needs the slice `Over (op i)` to have fewer objects than the
cofinality of the site's size cutoff, which
`AlgebraicGeometry.Space.AffineChartSystem.limitBridge` asks for as two bounds, on the objects
and on the hom types of the index category. The second is automatic here: the hom types of a
preorder are subsingletons, so they are smaller than `ℵ₀`, which is below the cutoff's
cofinality. Only the bound on the index type itself survives into
`AlgebraicGeometry.Space.NoetherianLimitSystem.chartLimitBridge`.

The chart system sees the limit of the system of presheaves formed by
`CategoryTheory.Limits.limit`, whereas a Noetherian limit system carries a chosen limiting
cone; `AlgebraicGeometry.Space.NoetherianLimitSystem.limitIso` mediates, and the fibre product
statement is transported along it.

## References

* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CP9](https://stacks.math.columbia.edu/tag/0CP9)
* [Stacks Project, Tag 0CNM](https://stacks.math.columbia.edu/tag/0CNM)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe v u

/-! ### The stages above an index -/

/-- The elements of a directed preorder above a given one are again directed: an upper bound
of two of them in the ambient preorder lies above the given element. -/
instance Set.Ici.instIsDirectedOrder {I : Type v} [Preorder I] [IsDirectedOrder I] (i : I) :
    IsDirectedOrder (Set.Ici i) where
  directed a b := by
    obtain ⟨c, hac, hbc⟩ := exists_ge_ge a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩

/-! ### The index equivalence -/

namespace CategoryTheory

variable {I : Type v} [Preorder I]

/-- The stages above `i`, read as the slice of `Iᵒᵖ` over `op i`: an element `i' ≥ i` is sent
to the morphism `op i' ⟶ op i` of the inequality `i ≤ i'`. -/
def iciOpToOverOp (i : I) : (Set.Ici i)ᵒᵖ ⥤ Over (op i) where
  obj j := Over.mk (homOfLE j.unop.property).op
  map f := Over.homMk (homOfLE (show _ ≤ _ from leOfHom f.unop)).op (Subsingleton.elim _ _)
  map_id _ := Over.OverMorphism.ext (Subsingleton.elim _ _)
  map_comp _ _ := Over.OverMorphism.ext (Subsingleton.elim _ _)

/-- The slice of `Iᵒᵖ` over `op i`, read as the stages above `i`: an object of the slice is a
stage together with a morphism to `op i`, that is, with an inequality `i ≤ ·`. -/
def overOpToIciOp (i : I) : Over (op i) ⥤ (Set.Ici i)ᵒᵖ where
  obj j := op ⟨j.left.unop, leOfHom j.hom.unop⟩
  map f := (homOfLE (show (⟨_, _⟩ : Set.Ici i) ≤ ⟨_, _⟩ from leOfHom f.left.unop)).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The stages above `i` are the slice of `Iᵒᵖ` over `op i`: a morphism `op i' ⟶ op i` of `Iᵒᵖ`
is exactly an inequality `i ≤ i'`, and both categories are thin. -/
def iciOpEquivalenceOverOp (i : I) : (Set.Ici i)ᵒᵖ ≌ Over (op i) where
  functor := iciOpToOverOp i
  inverse := overOpToIciOp i
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ Subsingleton.elim _ _
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦
    Over.OverMorphism.ext (Subsingleton.elim _ _)

/-- The functor of `CategoryTheory.iciOpEquivalenceOverOp i` is
`CategoryTheory.iciOpToOverOp i`. -/
@[simp]
lemma iciOpEquivalenceOverOp_functor (i : I) :
    (iciOpEquivalenceOverOp i).functor = iciOpToOverOp i :=
  rfl

end CategoryTheory

/-! ### A limit-Noetherian situation from a diagram over a slice -/

namespace AlgebraicGeometry

namespace LimitNoetherianSituation

variable {I : Type v} [Preorder I] [IsDirectedOrder I] (i : I) (F : Over (op i) ⥤ Scheme.{u})
  (hNoetherian : ∀ j : Over (op i), IsNoetherian (F.obj j))
  (hAffine : ∀ {j k : Over (op i)} (g : j ⟶ k), IsAffineHom (F.map g))
  {c : Cone F}

/-- A diagram of Noetherian schemes with affine transition morphisms indexed by the slice of
`Iᵒᵖ` over `op i`, together with a limit cone for it, is a limit-Noetherian situation on the
stages above `i`. -/
def ofOverOp (hc : IsLimit c) : LimitNoetherianSituation.{v, u} (Set.Ici i) where
  system := iciOpToOverOp i ⋙ F
  noetherian _ := hNoetherian _
  transition_affine _ := hAffine _
  limitCone := c.whisker (iciOpToOverOp i)
  isLimit := hc.whiskerEquivalence (iciOpEquivalenceOverOp i)

/-- The system of `AlgebraicGeometry.LimitNoetherianSituation.ofOverOp` is the diagram `F`
restricted along `CategoryTheory.iciOpToOverOp i`. -/
@[simp]
lemma ofOverOp_system (hc : IsLimit c) :
    (ofOverOp i F hNoetherian hAffine hc).system = iciOpToOverOp i ⋙ F :=
  rfl

/-- The limit scheme of `AlgebraicGeometry.LimitNoetherianSituation.ofOverOp` is the cone point
of `c`. -/
@[simp]
lemma ofOverOp_limitScheme (hc : IsLimit c) :
    (ofOverOp i F hNoetherian hAffine hc).limitScheme = c.pt :=
  rfl

/-- The projection of the limit cone of `AlgebraicGeometry.LimitNoetherianSituation.ofOverOp` to
the stage `j` is the projection of `c` to the corresponding object of `Over (op i)`. -/
@[simp]
lemma ofOverOp_limitCone_π_app (hc : IsLimit c) (j : (Set.Ici i)ᵒᵖ) :
    (ofOverOp i F hNoetherian hAffine hc).limitCone.π.app j =
      c.π.app ((iciOpToOverOp i).obj j) :=
  rfl

end LimitNoetherianSituation

/-! ### The chart situation at a stage of a Noetherian limit system -/

namespace Space

namespace NoetherianLimitSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
  (D : NoetherianLimitSystem B S hS hZ I) (i : I)

/-- The limit of the system of presheaves of a Noetherian limit system, identified with the
chosen limit space. -/
noncomputable def limitIso : limit D.system ≅ D.limitCone.pt :=
  (limit.isLimit D.system).conePointUniqueUpToIso D.isLimit

/-- The comparison isomorphism `AlgebraicGeometry.Space.NoetherianLimitSystem.limitIso` commutes
with the projections to each stage. -/
@[reassoc (attr := simp)]
lemma limitIso_hom_comp_π (j : Iᵒᵖ) :
    D.limitIso.hom ≫ D.limitCone.π.app j = limit.π D.system j :=
  (limit.isLimit D.system).conePointUniqueUpToIso_hom_comp D.isLimit j

variable {U₀ : BigAffineFppf B S hS}
  (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.system.obj (op i))

/-- The system of affine charts of a Noetherian limit system at the stage `i` and the affine
scheme-valued point `f₀` of that stage: the stage `B_{i'}` above `i` is sent to an affine
object of the site representing `B_{i'} ×_{B_i} U_i`. -/
noncomputable def chartSystem : AffineChartSystem B S hS (op i) D.system U₀ f₀ :=
  affineChartSystem B S hS (op i) D.system U₀ f₀ D.transition_affine

variable {C : AffineChartSystem B S hS (op i) D.system U₀ f₀}

/-- The system of affine charts at a stage, as a limit-Noetherian situation on the stages above
that stage. Its limit scheme is the chart `B ×_{B_i} U_i` of the limit space, by
`AlgebraicGeometry.Space.NoetherianLimitSystem.isPullback_chartToLimit`. -/
noncomputable def chartSituation (L : AffineChartSystem.LimitBridge C)
    (hNoetherian : ∀ j : Over (op i),
      _root_.AlgebraicGeometry.IsNoetherian (C.schemeDiagram.obj j)) :
    LimitNoetherianSituation.{u, u} (Set.Ici i) :=
  LimitNoetherianSituation.ofOverOp i C.schemeDiagram hNoetherian
    (fun g ↦ C.isAffineHom_map g) L.schemeIsLimit

/-- The limit scheme of the chart situation is the scheme underlying the cone point of the limit
of the chart system. -/
@[simp]
lemma chartSituation_limitScheme (L : AffineChartSystem.LimitBridge C)
    (hNoetherian : ∀ j : Over (op i),
      _root_.AlgebraicGeometry.IsNoetherian (C.schemeDiagram.obj j)) :
    (chartSituation D i f₀ L hNoetherian).limitScheme =
      (BigFppfOver.toScheme B S hS).obj L.cone.pt :=
  rfl

/-- The limit scheme of the chart situation at a stage is affine. -/
theorem isAffine_chartSituation_limitScheme (L : AffineChartSystem.LimitBridge C)
    (hNoetherian : ∀ j : Over (op i),
      _root_.AlgebraicGeometry.IsNoetherian (C.schemeDiagram.obj j)) :
    IsAffine (chartSituation D i f₀ L hNoetherian).limitScheme :=
  L.isAffine_pt

/-- The morphism from the chart of the limit space to the limit space itself. -/
noncomputable def chartToLimit (L : AffineChartSystem.LimitBridge C) :
    yoneda.obj L.cone.pt ⟶ D.limitCone.pt :=
  L.toLimit ≫ D.limitIso.hom

/-- The morphism from the chart of the limit space to the limit space itself. -/
noncomputable def chartLimitToLimit (L : AffineChartSystem.ChartLimit C) :
    yoneda.obj L.cone.pt ⟶ D.limitCone.pt :=
  L.toLimit ≫ D.limitIso.hom

/-- A pullback square over the limit of the system of presheaves stays a pullback square after
composing with `AlgebraicGeometry.Space.NoetherianLimitSystem.limitIso`. -/
private theorem isPullback_comp_limitIso {X : _ ⥤ Type u} {g : X ⟶ limit D.system}
    {b : X ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
    (h : IsPullback g b (limit.π D.system (op i)) f₀) :
    IsPullback (g ≫ D.limitIso.hom) b (D.limitCone.π.app (op i)) f₀ :=
  h.of_iso' (Iso.refl _) D.limitIso.symm (Iso.refl _) (Iso.refl _)
    (by simp) (by simp)
    (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.inv_comp_eq,
      D.limitIso_hom_comp_π])
    (by simp)

/-- The limit of the chart system at the stage `i` is the chart `B ×_{B_i} U_i` of the limit
space: it is the fibre product of the limit space with `U_i` over the stage `B_i`. -/
theorem isPullback_chartToLimit (L : AffineChartSystem.LimitBridge C) :
    IsPullback (chartToLimit D i f₀ L) L.toBase (D.limitCone.π.app (op i)) f₀ :=
  isPullback_comp_limitIso D i f₀ L.isPullback

/-- The limit of the chart system at the stage `i` is the chart `B ×_{B_i} U_i` of the limit
space: it is the fibre product of the limit space with `U_i` over the stage `B_i`. -/
theorem isPullback_chartLimitToLimit (L : AffineChartSystem.ChartLimit C) :
    IsPullback (chartLimitToLimit D i f₀ L) L.toBase (D.limitCone.π.app (op i)) f₀ :=
  isPullback_comp_limitIso D i f₀ L.isPullback

/-- A chart of a stage of a Noetherian limit system is a Noetherian scheme when the chosen
scheme-valued point of the stage is étale: the chart is étale over the stage, which is
Noetherian, hence locally Noetherian, and it is affine, hence quasi-compact. -/
theorem isNoetherian_chart
    (hf₀ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f₀)
    (C : AffineChartSystem B S hS (op i) D.system U₀ f₀) (j : Over (op i)) :
    _root_.AlgebraicGeometry.IsNoetherian (C.schemeDiagram.obj j) :=
  have : IsAffine (C.schemeDiagram.obj j) := C.isAffine_obj j
  have : IsLocallyNoetherian (C.schemeDiagram.obj j) :=
    (exists_atlas_iff_forall_etale B S hS (D.system.obj j.left)
          (fun X : Scheme.{u} ↦ IsLocallyNoetherian X)
          (D.system_isAlgebraicSpace j.left.unop)).mp
      (D.noetherian j.left.unop).2.2 (C.siteDiagram.obj j) (C.stageMap j)
      (presheaf_of_isPullback B S hS (C.isPullback j).flip hf₀)
  { }

/-- The limit of the chart system at a stage, available as soon as the index type is small
enough for the site: the hom types of a preorder are subsingletons, so no separate bound on
them is needed. -/
noncomputable def chartLimitBridge (hSize : #I < B.cutoff.ord.cof) :
    AffineChartSystem.LimitBridge (D.chartSystem i f₀) :=
  have hop : #(Iᵒᵖ) < B.cutoff.ord.cof := by
    rwa [Cardinal.mk_congr (show Iᵒᵖ ≃ I from ⟨unop, op, fun _ ↦ rfl, fun _ ↦ rfl⟩)]
  (D.chartSystem i f₀).limitBridge hop fun _ _ ↦
    (Cardinal.le_one_iff_subsingleton.2 inferInstance).trans_lt
      (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof)

/-- The affine charts of the stages above `i` cut out by an affine *étale* scheme-valued point
of the stage `i`, as a limit-Noetherian situation on those stages. Its limit scheme is the
chart `B ×_{B_i} U_i` of the limit space, by
`AlgebraicGeometry.Space.NoetherianLimitSystem.isPullback_chartToLimit`. -/
noncomputable def etaleChartSituation
    (hf₀ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f₀)
    (hSize : #I < B.cutoff.ord.cof) : LimitNoetherianSituation.{u, u} (Set.Ici i) :=
  chartSituation D i f₀ (D.chartLimitBridge i f₀ hSize) fun j ↦
    D.isNoetherian_chart i f₀ hf₀ _ j

/-- The limit scheme of the étale chart situation is the scheme underlying the cone point of
`AlgebraicGeometry.Space.NoetherianLimitSystem.chartLimitBridge`. -/
@[simp]
lemma etaleChartSituation_limitScheme
    (hf₀ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f₀)
    (hSize : #I < B.cutoff.ord.cof) :
    (etaleChartSituation D i f₀ hf₀ hSize).limitScheme =
      (BigFppfOver.toScheme B S hS).obj (D.chartLimitBridge i f₀ hSize).cone.pt :=
  rfl

end NoetherianLimitSystem

end Space

end AlgebraicGeometry

end
