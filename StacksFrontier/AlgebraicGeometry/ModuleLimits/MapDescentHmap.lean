module

public import StacksFrontier.AlgebraicGeometry.Coherent.FiniteTypeSubobjectLimits.DirectedColimit
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineFaithful
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.DescendUpToIso
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MapDescentGlue
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MapDescentOverlap
/-!
# Descent of a morphism of modules through a cofiltered limit

[Stacks Project, Tag 01ZR] (2) is proved for a cofiltered diagram of *affine* schemes by
`Stacks.AlgebraicGeometry.ModuleLimits.exists_map_of_pullback_canonical_of_isAffine'`.  This file
carries out the Zariski glueing that deduces it for a diagram of arbitrary schemes, over a stage
indexed by `CategoryTheory.Over i`; the form at an unrestricted index morphism universe is
`...ModuleLimits.exists_map_of_pullback_canonical_of_isLimit'`.

Let `V` be a finite affine open covering of the stage `D.obj i`.  The three steps are:

* over each member of the covering the restriction of the given morphism `φ` descends, at every
  sufficiently late stage, to a morphism of the restrictions satisfying
  `Stacks.AlgebraicGeometry.ModuleLimits.IsChartDescent`
  (`Stacks.AlgebraicGeometry.ModuleLimits.exists_isChartDescent_of_isAffineOpen`); the finitely
  many stages so obtained are refined to one;
* two such data agree on the overlap of their opens *after pullback to the limit*
  (`Stacks.AlgebraicGeometry.ModuleLimits.pullback_map_restrictHomOfLE_eq_of_isChartDescent`), so
  part (3) of the tag — applied to the diagram of preimages of the overlap — makes them agree
  already at a later stage, and a second refinement, taken in `CategoryTheory.Over` of the first
  stage, produces one stage at which *all* the overlaps agree;
* the data, transported to that stage, glue
  (`Stacks.AlgebraicGeometry.ModuleLimits.exists_restrictFunctor_map_eq_of_cover_of_inf`), and the
  glued morphism satisfies the canonical descent equation because an equality of morphisms of
  sheaves is local.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_chartDescent_family`,
  `Stacks.AlgebraicGeometry.ModuleLimits.exists_agreeing_chartDescent_family` and
  `Stacks.AlgebraicGeometry.ModuleLimits.canonical_of_agreeing_chartDescent_family`: the three
  steps above.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_over_pullback_resLE_map_eq`: Tag 01ZR (3) for the
  diagram of preimages of an open of a stage, with the opens spelled as preimages rather than as
  values of `AlgebraicGeometry.EventualLimit.preimageDiagram`.

## Implementation notes

The whole argument is carried out in the uniform spelling of
`Stacks.AlgebraicGeometry.ModuleLimits.coneProj` and
`Stacks.AlgebraicGeometry.ModuleLimits.stageHom`, for the reason recorded in the implementation
notes of `StacksFrontier/AlgebraicGeometry/ModuleLimits/MapDescentOverlap.lean`: a statement
mentioning two projections of the cone is otherwise not uniform in the scheme they start from, and
instantiating a lemma quantified over morphisms with a common source then forces the kernel through
a conversion inside `AlgebraicGeometry.Scheme.Modules.pullback`.

`exists_over_pullback_resLE_map_eq` exists for the analogous reason on the typeclass side rather
than the kernel side.  The modules in it live on `D.map k.hom ⁻¹ᵁ U`, whereas
`Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isLimit'` applied to
`AlgebraicGeometry.EventualLimit.preimageDiagram D i U` asks for modules on
`(preimageDiagram D i U).obj k`.  The two schemes are definitionally equal, but
`AlgebraicGeometry.EventualLimit.preimageDiagram` is not reducible, so a finite-presentation
instance proved for the first spelling is invisible to instance search at the second.  Stating the
clause once with the first spelling lets every later use discharge those instances by ordinary
search.

The identification `f ⁻¹ᵁ (U ⊓ U') = f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ U'` holds by `rfl`, and the proof of the
pairwise agreement uses it in that form: the glueing hypothesis of
`exists_restrictFunctor_map_eq_of_cover_of_inf` is stated at the intersection of two members of the
covering, while part (3) of the tag produces the agreement at the preimage of the intersection of
the two opens downstairs.  Only the `TopologicalSpace.Opens` argument differs between the two, so
the conversion is settled argument-wise and never descends into the pullback.

The *second* refinement is taken in `CategoryTheory.Over k₀` rather than by
`CategoryTheory.IsCofiltered.inf_exists` in `CategoryTheory.Over i`: an object of `Over k₀` is a
stage together with a morphism to `k₀`, so one application of
`CategoryTheory.IsCofiltered.inf_objs_exists` there yields a single transition morphism to `k₀`
through which every one of the finitely many pairwise agreements factors.  That single morphism is
what the transport of
`Stacks.AlgebraicGeometry.ModuleLimits.IsStageTransport` is taken along.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Scheme.Modules

section Assemble

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Limits.Cone D)

/-! ### Comparisons of opens along the stages over a fixed stage -/

/-- The preimage in the limit of an open `V` of the stage `D.obj i` is contained in the preimage
of the preimage of `V` at any stage over `i`.  The two opens are in fact equal; the inequality is
the form in which `IsChartDescent` takes it. -/
theorem coneProj_preimage_le (i : I) (k : Over i) (V : (D.obj i).Opens) :
    coneProj D c i ⁻¹ᵁ V ≤ coneProj D c k.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ V) := by
  change c.π.app i ⁻¹ᵁ V ≤ c.π.app k.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ V)
  rw [← Scheme.Hom.comp_preimage, c.w k.hom]

/-- The preimage of `V` at a stage over `i` is contained in the preimage of the preimage of `V` at
an earlier such stage.  This is the comparison of opens built into
`AlgebraicGeometry.EventualLimit.preimageDiagram`. -/
theorem preimage_le_of_overHom {i : I} {k' k : Over i} (e : k' ⟶ k) (V : (D.obj i).Opens) :
    D.map k'.hom ⁻¹ᵁ V ≤ D.map e.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, ← D.map_comp, Over.w e]

/-- The projection at a stage over `i`, followed by the transition morphism of a morphism of
stages over `i`, is the projection at the earlier stage. -/
theorem coneProj_comp_map_left {i : I} {k' k : Over i} (e : k' ⟶ k) :
    coneProj D c k'.left ≫ D.map e.left = coneProj D c k.left := c.w e.left

/-- The transition morphism of a morphism of stages over `i`, followed by the morphism to `i` of
the later stage, is the morphism to `i` of the earlier one.  The two morphisms to
`CategoryTheory.Over.mk (𝟙 i)` involved agree by `over_hom_terminal_ext`. -/
theorem stageHom_comp_of_overHom {i : I} {k' k : Over i} (e : k' ⟶ k)
    (hk : k ⟶ Over.mk (𝟙 i)) (hk' : k' ⟶ Over.mk (𝟙 i)) :
    D.map e.left ≫ stageHom D hk = stageHom D hk' := by
  have hb : e ≫ hk = hk' := over_hom_terminal_ext _ _
  rw [stageHom, stageHom, ← D.map_comp]
  exact congrArg D.map (by rw [← hb]; rfl)

/-- An equality of the pullbacks of two morphisms along the transition morphism of a morphism of
stages over `i` persists after precomposing that morphism with another one. -/
theorem pullback_resLE_map_eq_of_overHom_comp {i : I} {k₂ k₁ k₀ : Over i}
    (g : k₂ ⟶ k₁) (e : k₁ ⟶ k₀) (b : k₂ ⟶ k₀) (hb : g ≫ e = b) (U : (D.obj i).Opens)
    {M N : (D.map k₀.hom ⁻¹ᵁ U).toScheme.Modules} {ψ₁ ψ₂ : M ⟶ N}
    (h : (pullback ((D.map e.left).resLE (D.map k₀.hom ⁻¹ᵁ U) (D.map k₁.hom ⁻¹ᵁ U)
          (preimage_le_of_overHom D e U))).map ψ₁ =
      (pullback ((D.map e.left).resLE (D.map k₀.hom ⁻¹ᵁ U) (D.map k₁.hom ⁻¹ᵁ U)
          (preimage_le_of_overHom D e U))).map ψ₂) :
    (pullback ((D.map b.left).resLE (D.map k₀.hom ⁻¹ᵁ U) (D.map k₂.hom ⁻¹ᵁ U)
        (preimage_le_of_overHom D b U))).map ψ₁ =
      (pullback ((D.map b.left).resLE (D.map k₀.hom ⁻¹ᵁ U) (D.map k₂.hom ⁻¹ᵁ U)
        (preimage_le_of_overHom D b U))).map ψ₂ := by
  subst hb
  have hcc := pullback_map_eq_of_precomp ((EventualLimit.preimageDiagram D i U).map g)
    ((EventualLimit.preimageDiagram D i U).map e) h
  rw [← (EventualLimit.preimageDiagram D i U).map_comp] at hcc
  exact hcc

variable [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

/-! ### The charts of a covering, descended at one common stage -/

/-- **The chart data of a finite family of affine opens of a stage, at one common later stage.**
For each member `V a` of the family the restriction of `φ` descends to a morphism `χ a` of the
restrictions to the preimage of `V a`, satisfying `IsChartDescent`, and the finitely many stages
over which the `χ a` are obtained are refined to a single stage `k`.

This is `exists_isChartDescent_of_isAffineOpen` together with
`CategoryTheory.IsCofiltered.inf_objs_exists`. -/
theorem exists_chartDescent_family (hc : Limits.IsLimit c) (i : I)
    {ι : Type u} [Finite ι] (V : ι → (D.obj i).Opens) (hV : ∀ a, IsAffineOpen (V a))
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (pullback (coneProj D c i)).obj F ⟶ (pullback (coneProj D c i)).obj G) :
    ∃ (k : Over i) (hk : k ⟶ Over.mk (𝟙 i))
      (χ : ∀ a, (restrictFunctor (D.map k.hom ⁻¹ᵁ V a).ι).obj
            ((pullback (stageHom D hk)).obj F) ⟶
          (restrictFunctor (D.map k.hom ⁻¹ᵁ V a).ι).obj ((pullback (stageHom D hk)).obj G)),
      ∀ a, IsChartDescent (coneProj D c k.left) (stageHom D hk) (coneProj D c i)
        (coneProj_comp_stageHom D c hk) (coneProj_preimage_le D c i k (V a)) φ (χ a) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  choose jj hjj using fun a => exists_isChartDescent_of_isAffineOpen D c i hc (hV a) F G φ
  obtain ⟨k, hks⟩ := IsCofiltered.inf_objs_exists (Finset.image jj Finset.univ)
  have hkm : ∀ a, k ⟶ jj a := fun a =>
    (hks (Finset.mem_image_of_mem _ (Finset.mem_univ a))).some
  obtain ⟨hk⟩ : Nonempty (k ⟶ Over.mk (𝟙 i)) := ⟨Over.homMk k.hom (by simp)⟩
  refine ⟨k, hk, ?_⟩
  choose χ hχ using fun a =>
    hjj a k hk (hkm a) (coneProj_preimage_le D c i k (V a))
  exact ⟨χ, hχ⟩

/-! ### The overlaps, made to agree at one common stage -/

/-- **Stacks Project, Tag 01ZR (3) for the diagram of preimages of an open of a stage.**  Two
morphisms of finitely presented modules on the preimage of a quasi-compact open `U` of `D.obj i` at
a stage `k` over `i`, whose pullbacks to the preimage of `U` in the limit agree, already have equal
pullbacks to the preimage of `U` at some stage over `k`.

This is `exists_pullback_map_eq_of_isLimit'` for
`AlgebraicGeometry.EventualLimit.preimageDiagram D i U`, restated with the preimages spelled
directly; see the implementation notes. -/
theorem exists_over_pullback_resLE_map_eq (hc : Limits.IsLimit c) (i : I) (k : Over i)
    {U : (D.obj i).Opens} (hU : IsCompact (U : Set (D.obj i)))
    (M N : (D.map k.hom ⁻¹ᵁ U).toScheme.Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation] (ψ₁ ψ₂ : M ⟶ N)
    (h : (pullback ((coneProj D c k.left).resLE (D.map k.hom ⁻¹ᵁ U)
          (coneProj D c i ⁻¹ᵁ U) (coneProj_preimage_le D c i k U))).map ψ₁ =
      (pullback ((coneProj D c k.left).resLE (D.map k.hom ⁻¹ᵁ U)
          (coneProj D c i ⁻¹ᵁ U) (coneProj_preimage_le D c i k U))).map ψ₂) :
    ∃ (k' : Over i) (e : k' ⟶ k),
      (pullback ((D.map e.left).resLE (D.map k.hom ⁻¹ᵁ U) (D.map k'.hom ⁻¹ᵁ U)
          (preimage_le_of_overHom D e U))).map ψ₁ =
        (pullback ((D.map e.left).resLE (D.map k.hom ⁻¹ᵁ U) (D.map k'.hom ⁻¹ᵁ U)
          (preimage_le_of_overHom D e U))).map ψ₂ :=
  @exists_pullback_map_eq_of_isLimit'.{u, u} (Over i) inferInstance inferInstance
    (EventualLimit.preimageDiagram D i U)
    (fun {_ _} g => EventualLimit.preimageDiagram_isAffineHom D i U g)
    (EventualLimit.preimageCone D c i U)
    (EventualLimit.isLimitPreimageCone D c hc i U) k
    (isCompact_iff_compactSpace.mp
      (QuasiCompact.isCompact_preimage (f := D.map k.hom) _ U.2 hU))
    M N ‹_› ‹_› ψ₁ ψ₂ h

/-- **The chart data of a finite family of affine opens of a stage, at a stage where they agree on
the overlaps.**  Given chart data `χ` over a common stage `k₀`, there is a stage `k` over `i` and
chart data `χ'` there, still satisfying `IsChartDescent`, such that the restrictions of `χ' a` and
`χ' b` to the intersection of their opens agree for every pair `a`, `b`.

The agreement after pullback to the limit is
`pullback_map_restrictHomOfLE_eq_of_isChartDescent`; `exists_over_pullback_resLE_map_eq` turns it
into an agreement at a later stage for each pair; a refinement in `CategoryTheory.Over k₀` makes
one stage serve for all pairs, and `isStageTransport_restrictHomOfLE` together with
`eq_of_isStageTransport` carries the verdict there. -/
theorem exists_agreeing_chartDescent_family (hc : Limits.IsLimit c) (i : I)
    [QuasiSeparatedSpace (D.obj i)]
    {ι : Type u} [Finite ι] (V : ι → (D.obj i).Opens)
    (hVc : ∀ a, IsCompact (V a : Set (D.obj i)))
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (pullback (coneProj D c i)).obj F ⟶ (pullback (coneProj D c i)).obj G)
    (k₀ : Over i) (hk₀ : k₀ ⟶ Over.mk (𝟙 i))
    (χ : ∀ a, (restrictFunctor (D.map k₀.hom ⁻¹ᵁ V a).ι).obj
          ((pullback (stageHom D hk₀)).obj F) ⟶
        (restrictFunctor (D.map k₀.hom ⁻¹ᵁ V a).ι).obj ((pullback (stageHom D hk₀)).obj G))
    (hχ : ∀ a, IsChartDescent (coneProj D c k₀.left) (stageHom D hk₀) (coneProj D c i)
      (coneProj_comp_stageHom D c hk₀) (coneProj_preimage_le D c i k₀ (V a)) φ (χ a)) :
    ∃ (k : Over i) (hk : k ⟶ Over.mk (𝟙 i))
      (χ' : ∀ a, (restrictFunctor (D.map k.hom ⁻¹ᵁ V a).ι).obj
            ((pullback (stageHom D hk)).obj F) ⟶
          (restrictFunctor (D.map k.hom ⁻¹ᵁ V a).ι).obj ((pullback (stageHom D hk)).obj G)),
      (∀ a, IsChartDescent (coneProj D c k.left) (stageHom D hk) (coneProj D c i)
        (coneProj_comp_stageHom D c hk) (coneProj_preimage_le D c i k (V a)) φ (χ' a)) ∧
      ∀ a b, restrictHomOfLE (inf_le_left :
            D.map k.hom ⁻¹ᵁ V a ⊓ D.map k.hom ⁻¹ᵁ V b ≤ D.map k.hom ⁻¹ᵁ V a) (χ' a) =
          restrictHomOfLE (inf_le_right :
            D.map k.hom ⁻¹ᵁ V a ⊓ D.map k.hom ⁻¹ᵁ V b ≤ D.map k.hom ⁻¹ᵁ V b) (χ' b) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hpF : ((pullback (stageHom D hk₀)).obj F).IsFinitePresentation :=
    isFinitePresentation_pullback _ F
  have hpG : ((pullback (stageHom D hk₀)).obj G).IsFinitePresentation :=
    isFinitePresentation_pullback _ G
  have h3 : ∀ p : ι × ι, ∃ (k' : Over i) (e : k' ⟶ k₀),
      (pullback ((D.map e.left).resLE (D.map k₀.hom ⁻¹ᵁ (V p.1 ⊓ V p.2))
          (D.map k'.hom ⁻¹ᵁ (V p.1 ⊓ V p.2))
          (preimage_le_of_overHom D e (V p.1 ⊓ V p.2)))).map
          (restrictHomOfLE (Scheme.Hom.preimage_mono (D.map k₀.hom) inf_le_left) (χ p.1)) =
        (pullback ((D.map e.left).resLE (D.map k₀.hom ⁻¹ᵁ (V p.1 ⊓ V p.2))
          (D.map k'.hom ⁻¹ᵁ (V p.1 ⊓ V p.2))
          (preimage_le_of_overHom D e (V p.1 ⊓ V p.2)))).map
          (restrictHomOfLE (Scheme.Hom.preimage_mono (D.map k₀.hom) inf_le_right) (χ p.2)) := by
    intro p
    have hrF : (Scheme.Modules.restrict ((pullback (stageHom D hk₀)).obj F)
        (D.map k₀.hom ⁻¹ᵁ (V p.1 ⊓ V p.2)).ι).IsFinitePresentation :=
      isFinitePresentation_restrict _ _
    have hrG : (Scheme.Modules.restrict ((pullback (stageHom D hk₀)).obj G)
        (D.map k₀.hom ⁻¹ᵁ (V p.1 ⊓ V p.2)).ι).IsFinitePresentation :=
      isFinitePresentation_restrict _ _
    exact exists_over_pullback_resLE_map_eq D c hc i k₀
      ((hVc p.1).inter_of_isOpen (hVc p.2) (V p.1).2 (V p.2).2) _ _ _ _
      (pullback_map_restrictHomOfLE_eq_of_isChartDescent (coneProj D c k₀.left)
        (stageHom D hk₀) (coneProj D c i) (coneProj_comp_stageHom D c hk₀)
        (coneProj_preimage_le D c i k₀ (V p.1)) (coneProj_preimage_le D c i k₀ (V p.2))
        (coneProj_preimage_le D c i k₀ (V p.1 ⊓ V p.2))
        (Scheme.Hom.preimage_mono (D.map k₀.hom) inf_le_left)
        (Scheme.Hom.preimage_mono (D.map k₀.hom) inf_le_right)
        (Scheme.Hom.preimage_mono (coneProj D c i) inf_le_left)
        (Scheme.Hom.preimage_mono (coneProj D c i) inf_le_right) φ (hχ p.1) (hχ p.2))
  choose kk ee hee using h3
  obtain ⟨mm, hmms⟩ := IsCofiltered.inf_objs_exists
    (Finset.image (fun p : ι × ι => Over.mk (ee p)) Finset.univ)
  have gg : ∀ p : ι × ι, mm ⟶ Over.mk (ee p) := fun p =>
    (hmms (Finset.mem_image_of_mem _ (Finset.mem_univ p))).some
  obtain ⟨hk₁⟩ : Nonempty (mm.left ⟶ Over.mk (𝟙 i)) := ⟨Over.homMk mm.left.hom (by simp)⟩
  have hb := fun p : ι × ι => pullback_resLE_map_eq_of_overHom_comp D (gg p).left (ee p) mm.hom
    (Over.w (gg p)) (V p.1 ⊓ V p.2) (hee p)
  have hs := stageHom_comp_of_overHom D mm.hom hk₀ hk₁
  choose χ' hχ' using fun a => exists_isStageTransport (D.map mm.hom.left) (stageHom D hk₀)
    (stageHom D hk₁) hs
    (preimage_le_of_overHom D mm.hom (V a)) (χ a)
  refine ⟨mm.left, hk₁, χ', fun a => ?_, fun a b => ?_⟩
  · exact isChartDescent_of_isStageTransport (coneProj D c k₀.left)
      (coneProj D c mm.left.left) (D.map mm.hom.left) (stageHom D hk₀) (stageHom D hk₁)
      (coneProj D c i) (coneProj_comp_map_left D c mm.hom) hs
      (coneProj_comp_stageHom D c hk₀) (coneProj_comp_stageHom D c hk₁)
      (coneProj_preimage_le D c i k₀ (V a)) (preimage_le_of_overHom D mm.hom (V a))
      (coneProj_preimage_le D c i mm.left (V a)) φ (hχ a) (hχ' a)
  · have eWab : D.map mm.left.hom ⁻¹ᵁ V a ⊓ D.map mm.left.hom ⁻¹ᵁ V b ≤
        D.map mm.hom.left ⁻¹ᵁ (D.map k₀.hom ⁻¹ᵁ (V a ⊓ V b)) :=
      preimage_le_of_overHom D mm.hom (V a ⊓ V b)
    have key : ∀ x (hx : V a ⊓ V b ≤ V x), IsStageTransport (D.map mm.hom.left) (stageHom D hk₀)
        (stageHom D hk₁) hs eWab
        (restrictHomOfLE (Scheme.Hom.preimage_mono (D.map k₀.hom) hx) (χ x))
        (restrictHomOfLE (Scheme.Hom.preimage_mono (D.map mm.left.hom) hx) (χ' x)) :=
      fun x hx => isStageTransport_restrictHomOfLE _ _ _ hs _ _
        (preimage_le_of_overHom D mm.hom (V x)) eWab (hχ' x)
    exact eq_of_isStageTransport (D.map mm.hom.left) (stageHom D hk₀) (stageHom D hk₁) hs eWab
      (key a inf_le_left) (key b inf_le_right) (hb (a, b))

/-! ### Glueing the charts and checking the canonical descent equation -/

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- **Chart data agreeing on the overlaps of a covering glue to a canonical descent of `φ`.**
Given chart data `χ` over a covering `V` of the stage, satisfying `IsChartDescent` and agreeing on
the intersections, there is a morphism of the pullbacks of `F` and `G` to `D.obj k.left` whose
pullback to the limit is `φ` through the canonical identifications.

The glueing is `exists_restrictFunctor_map_eq_of_cover_of_inf`, and the descent equation is checked
over the members of the covering by `hom_ext_of_restrict_cover`: restricted to the preimage of
`V a`, it is exactly `IsChartDescent` for `χ a`, by the naturality
`pullbackHomOfRestrict_restrictFunctor_map`. -/
theorem canonical_of_agreeing_chartDescent_family (i : I)
    {ι : Type u} (V : ι → (D.obj i).Opens) (hcov : ∀ x : D.obj i, ∃ a, x ∈ V a)
    (F G : (D.obj i).Modules)
    (φ : (pullback (coneProj D c i)).obj F ⟶ (pullback (coneProj D c i)).obj G)
    (k : Over i) (hk : k ⟶ Over.mk (𝟙 i))
    (χ : ∀ a, (restrictFunctor (D.map k.hom ⁻¹ᵁ V a).ι).obj
          ((pullback (stageHom D hk)).obj F) ⟶
        (restrictFunctor (D.map k.hom ⁻¹ᵁ V a).ι).obj ((pullback (stageHom D hk)).obj G))
    (hχ : ∀ a, IsChartDescent (coneProj D c k.left) (stageHom D hk) (coneProj D c i)
      (coneProj_comp_stageHom D c hk) (coneProj_preimage_le D c i k (V a)) φ (χ a))
    (hagree : ∀ a b, restrictHomOfLE (inf_le_left :
          D.map k.hom ⁻¹ᵁ V a ⊓ D.map k.hom ⁻¹ᵁ V b ≤ D.map k.hom ⁻¹ᵁ V a) (χ a) =
        restrictHomOfLE (inf_le_right :
          D.map k.hom ⁻¹ᵁ V a ⊓ D.map k.hom ⁻¹ᵁ V b ≤ D.map k.hom ⁻¹ᵁ V b) (χ b)) :
    ∃ φk : (pullback (stageHom D hk)).obj F ⟶ (pullback (stageHom D hk)).obj G,
      (pullback (coneProj D c k.left)).map φk ≫
          canHom (coneProj D c k.left) (stageHom D hk) (coneProj D c i)
            (coneProj_comp_stageHom D c hk) G =
        canHom (coneProj D c k.left) (stageHom D hk) (coneProj D c i)
          (coneProj_comp_stageHom D c hk) F ≫ φ := by
  obtain ⟨φk, hφk⟩ := exists_restrictFunctor_map_eq_of_cover_of_inf
    (fun a => D.map k.hom ⁻¹ᵁ V a)
    (fun x => by obtain ⟨a, ha⟩ := hcov ((D.map k.hom).base x); exact ⟨a, ha⟩) χ hagree
  refine ⟨φk, ?_⟩
  refine hom_ext_of_restrict_cover (fun a => coneProj D c i ⁻¹ᵁ V a) (fun x => ?_) (fun a => ?_)
  · obtain ⟨a, ha⟩ := hcov ((coneProj D c i).base x)
    exact ⟨a, ha⟩
  · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      ← pullbackHomOfRestrict_restrictFunctor_map (coneProj D c k.left)
        (coneProj_preimage_le D c i k (V a)) φk, hφk a]
    exact hχ a

/-! ### Tag 01ZR (2) in the general case -/

/-- **Stacks Project, Tag 01ZR (2)** for an index category whose morphisms live in the universe of
the schemes.  A morphism between the pullbacks to the limit of two finitely presented modules on a
quasi-compact quasi-separated stage is, through the canonical identifications, the pullback of a
morphism at some later stage.

The affine open covering of the stage is `(D.obj i).affineCover.finiteSubcover`; its finiteness is
what makes the stages produced over the different members, and over the different overlaps,
refinable to a single one. -/
theorem exists_canonical_map_of_isLimit (hc : Limits.IsLimit c) (i : I)
    [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (pullback (c.π.app i)).obj F ⟶ (pullback (c.π.app i)).obj G) :
    ∃ (j : I) (e : j ⟶ i) (φj : (pullback (D.map e)).obj F ⟶ (pullback (D.map e)).obj G),
      (pullback (c.π.app j)).map φj ≫ canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) G =
        canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) F ≫ φ := by
  classical
  obtain ⟨ι, _, V, hVaff, hcov⟩ :
      ∃ (ι : Type u) (_ : Finite ι) (V : ι → (D.obj i).Opens),
        (∀ a, IsAffineOpen (V a)) ∧ ∀ x : D.obj i, ∃ a, x ∈ V a :=
    ⟨((D.obj i).affineCover.finiteSubcover).I₀, inferInstance,
      fun a => (((D.obj i).affineCover.finiteSubcover).f a).opensRange,
      fun a => isAffineOpen_opensRange _, fun x =>
        ((D.obj i).affineCover.finiteSubcover).isOpenCover_opensRange.exists_mem x⟩
  obtain ⟨k₀, hk₀, χ, hχ⟩ := exists_chartDescent_family D c hc i V hVaff F G φ
  obtain ⟨k, hk, χ', hχ', hagree⟩ := exists_agreeing_chartDescent_family D c hc i V
    (fun a => (hVaff a).isCompact) F G φ k₀ hk₀ χ hχ
  obtain ⟨φk, hφk⟩ :=
    canonical_of_agreeing_chartDescent_family D c i V hcov F G φ k hk χ' hχ' hagree
  exact ⟨k.left, hk.left, φk, hφk⟩

end Assemble

end Stacks.AlgebraicGeometry.ModuleLimits

end
