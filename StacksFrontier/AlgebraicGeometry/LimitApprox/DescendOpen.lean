module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.CompatibleOpens
public import StacksFrontier.AlgebraicGeometry.NoetherianApproximation.Comp

/-!
# Descending a quasi-compact open to a finite stage of an affine-transition limit

Let `D : Iᵒᵈ ⥤ Scheme` be a directed inverse system of schemes with affine transition
morphisms, let `S` be a quasi-separated scheme, let `U ⊆ S` be a quasi-compact open realized
as the inverse limit of `D`, and let `W ⊆ S` be a further quasi-compact open.  The first step
of the one-affine-open induction proving Noetherian approximation relative to `U` (Tag 07RN)
asks for `U ⊓ W`, read inside `U`, to be the inverse image of an open at a *finite stage* of
`D`, together with the resulting compatible family of opens at the later stages and the
identification of `U ⊓ W` as its inverse limit.

This file supplies exactly that, and the one general limit statement it needs.

## Main results

* `AlgebraicGeometry.isLimitCompatibleOpensCone` is the general statement: the restriction of
  a *limiting* cone over a cofiltered diagram of schemes to a transition-compatible family of
  opens is again limiting.  Proved by `CategoryTheory.Limits.isLimitOfIsPullbackOfIsConnected`
  from the fact that each square cut out by an open immersion is cartesian, exactly as
  Mathlib's `AlgebraicGeometry.isLimitOpensCone` is proved for its own `opensCone`.
  It supplies the `IsLimit (compatibleOpensCone ..)` hypotheses of the results in
  `FiniteTypeApproximation.CompatibleOpens`.

* `AlgebraicGeometry.exists_stage_preimage_eq_inf` is the descent step itself.  It is
  `AlgebraicGeometry.exists_preimage_eq`, Mathlib's form of Tag
  01Z4 (1), applied to the cone `Cone.mk U p` and to the open `U.ι ⁻¹ᵁ W` of `U`.  The remaining
  point is that this open is quasi-compact, which is where the quasi-separatedness
  of `S` is spent: `U ⊓ W` is an intersection of two quasi-compact opens of `S`, and `U.ι` is
  an open embedding.

* `AlgebraicGeometry.laterStages`, `AlgebraicGeometry.laterDiagram`,
  `AlgebraicGeometry.laterPreimage` reindex onto the stages above the one produced, and
  `AlgebraicGeometry.isLimitLaterCompatibleOpensCone` identifies `U ⊓ W` as the inverse limit
  of the resulting system of opens.  `AlgebraicGeometry.exists_le_laterStages` is the
  cofinality of the reindexing, which is what
  `AlgebraicGeometry.Scheme.FiniteTypeApproximation.comp` asks of an index map.

* `AlgebraicGeometry.isLocallyNoetherian_of_locallyOfFiniteType_terminal` records that a
  scheme locally of finite type over the terminal scheme is locally Noetherian, hence
  quasi-separated.  Every stage of a finite-type system is of this kind, and the Mathlib
  limit machinery for affine-transition systems asks for quasi-separatedness of the stages at
  almost every step, so this is the instance that unlocks it.

## Implementation notes

The reindexing is onto `↥(Set.Ici i₀)`, a *preorder* in `Type u`, rather than onto
`CategoryTheory.Over i₀`.  This is deliberate and is the reason Mathlib's `opensDiagram` and
`opensCone` are not used directly: `AlgebraicGeometry.Scheme.FiniteTypeApproximation` requires
its `indexType` to be a `Preorder` in the scheme universe, and `Over i₀` is a category whose
objects carry a proof field.  The index universe stays tied to the scheme universe throughout,
as it must: `CommRingCat` in one universe has no colimits over a larger index universe, so
freeing the index universe breaks the colimit synthesis the affine-transition limit results
rest on.

Transparency gotchas:

* `compatibleOpensDiagram` and `compatibleOpensCone` are `@[reducible]`, and that is
  load-bearing here: the cartesian squares fed to `isLimitOfIsPullbackOfIsConnected` are
  recognized only because the cone's legs unfold to `Scheme.Hom.resLE` applications.  This
  avoids the backward-compatibility transparency option that Mathlib's own
  file switches off for the same purpose.

* The homs of a preorder category are a subsingleton, so every triangle over `i₀` commutes by
  `Subsingleton.elim`; no coherence data is carried by `laterPreimage`.

* `IsCofiltered.isConnected` and the directedness of `↥(Set.Ici i₀)` are introduced as
  section-local instances; neither is a global instance in Mathlib.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w u

namespace Stacks.Order

variable {I : Type u} [Preorder I]

/-- The stages of a preorder above a given one form a nonempty type. -/
lemma nonempty_Ici (i₀ : I) : Nonempty ↥(Set.Ici i₀) := ⟨⟨i₀, le_rfl⟩⟩

/-- An upper set of a directed preorder is directed. -/
lemma isDirected_Ici [IsDirected I (· ≤ ·)] (i₀ : I) : IsDirected ↥(Set.Ici i₀) (· ≤ ·) := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
  exact ⟨⟨c, le_trans a.2 hac⟩, hac, hbc⟩

end Stacks.Order

namespace AlgebraicGeometry

attribute [local instance] IsCofiltered.isConnected Stacks.Order.nonempty_Ici
  Stacks.Order.isDirected_Ici

/-! ### Limiting restricted cones -/

section CompatibleOpens

variable {J : Type w} [Category.{v} J] {D : J ⥤ Scheme.{u}} {c : Cone D}

/-- **The restriction of a limiting cone to a compatible family of opens is limiting.**
Let `c` be a limiting cone over a cofiltered diagram of schemes `D`, let `V j ≤ D.obj j` be a
transition-compatible family of opens, and let `U` be an open of the vertex with
`c.π.app j ⁻¹ᵁ V j = U` for every `j`.  Then `U` is the inverse limit of the `V j`.

This is the converse direction to `AlgebraicGeometry.isLimitOfCompatibleOpensCover`, and the
result which supplies that lemma's hypotheses. -/
noncomputable def isLimitCompatibleOpensCone [IsCofiltered J] (hc : IsLimit c)
    (V : ∀ j, (D.obj j).Opens) (hV : ∀ ⦃j k : J⦄ (f : j ⟶ k), D.map f ⁻¹ᵁ V k = V j)
    (U : c.pt.Opens) (hU : ∀ j, c.π.app j ⁻¹ᵁ V j = U) :
    IsLimit (compatibleOpensCone D c V hV U hU) :=
  isLimitOfIsPullbackOfIsConnected
    (F := compatibleOpensDiagram D V hV)
    { app := fun j ↦ (V j).ι
      naturality := fun {_ _} f ↦ Scheme.Hom.resLE_comp_ι (D.map f) (hV f).ge }
    _ c
    { hom := U.ι
      w := fun j ↦ (Scheme.Hom.resLE_comp_ι (c.π.app j) (hU j).ge).symm }
    (fun j ↦ IsOpenImmersion.isPullback _ _ _ _
      (Scheme.Hom.resLE_comp_ι (c.π.app j) (hU j).ge).symm (by simpa using hU j))
    hc

end CompatibleOpens

/-! ### Stages of a finite-type system -/

/-- A scheme locally of finite type over the terminal scheme is locally Noetherian.  Together
with `AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace` this makes every stage of a
finite-type inverse system quasi-separated, which is what the Mathlib results on
affine-transition limits ask of the stages. -/
lemma isLocallyNoetherian_of_locallyOfFiniteType_terminal (X : Scheme.{u})
    [LocallyOfFiniteType (terminal.from X)] : IsLocallyNoetherian X := by
  let e := specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  exact LocallyOfFiniteType.isLocallyNoetherian (terminal.from X ≫ e.inv)

/-- A scheme locally of finite type over the terminal scheme is quasi-separated. -/
lemma quasiSeparatedSpace_of_locallyOfFiniteType_terminal (X : Scheme.{u})
    [LocallyOfFiniteType (terminal.from X)] : QuasiSeparatedSpace X :=
  have := isLocallyNoetherian_of_locallyOfFiniteType_terminal X
  inferInstance

/-! ### Descending a quasi-compact open to a finite stage -/

section Descend

variable {I : Type u} [Preorder I] (D : Iᵒᵈ ⥤ Scheme.{u})

/-- **Step (i) of the one-affine-open step of Tag 07RN.**  Let `U ⊆ S` be a quasi-compact open
of a quasi-separated scheme, realized by `p` as the inverse limit of a directed system `D` with
affine transition morphisms, and let `W ⊆ S` be a further quasi-compact open.  Then `U ⊓ W`,
read as an open of `U`, is the inverse image of a quasi-compact open at a finite stage of `D`.

This is `AlgebraicGeometry.exists_preimage_eq` — Mathlib's form of Tag 01Z4 (1) — applied to
the cone `Cone.mk U p`.  The quasi-separatedness of `S` is spent on the quasi-compactness of
`U.ι ⁻¹ᵁ W`, which is that result's one hypothesis beyond the system. -/
theorem exists_stage_preimage_eq_inf [Nonempty I] [IsDirected I (· ≤ ·)]
    [∀ {i j : Iᵒᵈ} (f : i ⟶ j), IsAffineHom (D.map f)]
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (U : S.Opens)
    [CompactSpace U] (p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D)
    (hp : IsLimit (Cone.mk (U : Scheme.{u}) p)) (W : S.Opens) (hW : IsCompact (W : Set S)) :
    ∃ (i : I) (V : (D.obj (OrderDual.toDual i)).Opens),
      IsCompact (V : Set (D.obj (OrderDual.toDual i))) ∧
        p.app (OrderDual.toDual i) ⁻¹ᵁ V = U.ι ⁻¹ᵁ W := by
  have hUc : IsCompact (U : Set S) := isCompact_iff_compactSpace.mpr ‹_›
  have hinter : IsCompact ((W : Set S) ∩ (U : Set S)) :=
    QuasiSeparatedSpace.inter_isCompact _ _ W.2 hW U.2 hUc
  have hpre : IsCompact ((U.ι ⁻¹ᵁ W : (U : Scheme.{u}).Opens) : Set (U : Scheme.{u})) := by
    rw [show ((U.ι ⁻¹ᵁ W : (U : Scheme.{u}).Opens) : Set (U : Scheme.{u}))
        = U.ι.base ⁻¹' (W : Set S) from rfl,
      U.ι.isOpenEmbedding.isEmbedding.isCompact_iff, Set.image_preimage_eq_inter_range]
    simpa using hinter
  obtain ⟨i, V, hVc, hV⟩ := exists_preimage_eq D (Cone.mk (U : Scheme.{u}) p) hp _ hpre
  exact ⟨OrderDual.ofDual i, V, hVc, hV⟩

/-- The stages of a directed system which lie above a given stage `i₀`, as an index preorder
in the universe of the schemes.  The one-affine-open step of Tag 07RN reindexes onto these. -/
def laterStages (i₀ : I) : ↥(Set.Ici i₀) →o I := ⟨Subtype.val, fun _ _ h ↦ h⟩

/-- The reindexing onto the stages above `i₀` is cofinal.  This is the hypothesis
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.comp` asks of an index map. -/
lemma exists_le_laterStages [IsDirected I (· ≤ ·)] (i₀ : I) (i : I) :
    ∃ k, i ≤ laterStages i₀ k := by
  obtain ⟨c, hic, h0c⟩ := directed_of (· ≤ ·) i i₀
  exact ⟨⟨c, h0c⟩, hic⟩

/-- A directed system restricted to the stages above `i₀`. -/
noncomputable abbrev laterDiagram (i₀ : I) : (↥(Set.Ici i₀))ᵒᵈ ⥤ Scheme.{u} :=
  (laterStages i₀).monotone.dual.functor ⋙ D

/-- The transition morphism from a stage above `i₀` down to `i₀`. -/
def laterStageHom {i₀ : I} (k : (↥(Set.Ici i₀))ᵒᵈ) :
    (laterStages i₀).monotone.dual.functor.obj k ⟶ OrderDual.toDual i₀ :=
  homOfLE (OrderDual.toDual_le_toDual.mpr (OrderDual.ofDual k).2)

/-- The inverse images at the later stages of an open given at the stage `i₀`. -/
noncomputable def laterPreimage {i₀ : I} (V₀ : (D.obj (OrderDual.toDual i₀)).Opens)
    (k : (↥(Set.Ici i₀))ᵒᵈ) : ((laterDiagram D i₀).obj k).Opens :=
  D.map (laterStageHom k) ⁻¹ᵁ V₀

/-- The family `AlgebraicGeometry.laterPreimage` is compatible with the transition
morphisms. -/
lemma laterPreimage_compatible {i₀ : I} (V₀ : (D.obj (OrderDual.toDual i₀)).Opens)
    ⦃k l : (↥(Set.Ici i₀))ᵒᵈ⦄ (f : k ⟶ l) :
    (laterDiagram D i₀).map f ⁻¹ᵁ laterPreimage D V₀ l = laterPreimage D V₀ k := by
  show D.map ((laterStages i₀).monotone.dual.functor.map f) ⁻¹ᵁ
    (D.map (laterStageHom l) ⁻¹ᵁ V₀) = D.map (laterStageHom k) ⁻¹ᵁ V₀
  rw [← Scheme.Hom.comp_preimage, ← D.map_comp,
    Subsingleton.elim ((laterStages i₀).monotone.dual.functor.map f ≫ laterStageHom l)
      (laterStageHom k)]

/-- Each member of the family `AlgebraicGeometry.laterPreimage` is quasi-compact. -/
lemma isCompact_laterPreimage [∀ {i j : Iᵒᵈ} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i₀ : I} (V₀ : (D.obj (OrderDual.toDual i₀)).Opens)
    (hV₀ : IsCompact (V₀ : Set (D.obj (OrderDual.toDual i₀))))
    (k : (↥(Set.Ici i₀))ᵒᵈ) :
    IsCompact ((laterPreimage D V₀ k : ((laterDiagram D i₀).obj k).Opens) :
      Set ((laterDiagram D i₀).obj k)) :=
  QuasiCompact.isCompact_preimage (f := D.map (laterStageHom k)) _ V₀.2 hV₀

/-- The legs of the restricted cone all cut out the same open of `U`. -/
lemma laterPreimage_preimage_eq {S : Scheme.{u}} (U : S.Opens)
    (p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D) {i₀ : I}
    (V₀ : (D.obj (OrderDual.toDual i₀)).Opens) {T : (U : Scheme.{u}).Opens}
    (hT : p.app (OrderDual.toDual i₀) ⁻¹ᵁ V₀ = T) (k : (↥(Set.Ici i₀))ᵒᵈ) :
    ((Cone.mk (U : Scheme.{u}) p).whisker
      (laterStages i₀).monotone.dual.functor).π.app k ⁻¹ᵁ laterPreimage D V₀ k = T := by
  have hn : p.app ((laterStages i₀).monotone.dual.functor.obj k) ≫ D.map (laterStageHom k) =
      p.app (OrderDual.toDual i₀) :=
    ((Category.id_comp _).symm.trans (p.naturality (laterStageHom k))).symm
  show p.app ((laterStages i₀).monotone.dual.functor.obj k) ⁻¹ᵁ
    (D.map (laterStageHom k) ⁻¹ᵁ V₀) = T
  rw [← Scheme.Hom.comp_preimage, hn, hT]

/-- **`U ⊓ W` is the inverse limit of its models at the later stages.**  With `V₀` the open at
the stage `i₀` produced by `AlgebraicGeometry.exists_stage_preimage_eq_inf`, the open
`T = U.ι ⁻¹ᵁ W` of `U` is the inverse limit of the family
`AlgebraicGeometry.laterPreimage D V₀`. -/
noncomputable def isLimitLaterCompatibleOpensCone [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (U : S.Opens)
    (p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D)
    (hp : IsLimit (Cone.mk (U : Scheme.{u}) p)) {i₀ : I}
    (V₀ : (D.obj (OrderDual.toDual i₀)).Opens) {T : (U : Scheme.{u}).Opens}
    (hT : p.app (OrderDual.toDual i₀) ⁻¹ᵁ V₀ = T) :
    IsLimit (compatibleOpensCone (laterDiagram D i₀)
      ((Cone.mk (U : Scheme.{u}) p).whisker (laterStages i₀).monotone.dual.functor)
      (laterPreimage D V₀) (laterPreimage_compatible D V₀) T
      (laterPreimage_preimage_eq D U p V₀ hT)) :=
  have : ((laterStages i₀).monotone.dual.functor).Initial :=
    initial_dual_functor_of_cofinal _ (exists_le_laterStages i₀)
  isLimitCompatibleOpensCone
    ((Functor.Initial.isLimitWhiskerEquiv
      (laterStages i₀).monotone.dual.functor _).symm hp) _ _ _ _

end Descend

end AlgebraicGeometry
