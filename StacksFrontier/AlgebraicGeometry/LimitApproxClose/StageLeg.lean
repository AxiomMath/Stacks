module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.Inclusion
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.StageCharted
public import StacksFrontier.AlgebraicGeometry.LimitApproxJoin.Shrink

/-!
# The second leg of the glueing: the overlap models inside the spectra of the subalgebras

This is the natural transformation `β` of gap (b) of Tag 07RN.  Its source is the system of
models of the overlap, reindexed onto the pairs `(k, A)` of a stage and a distinguished
subalgebra; its target is the system of spectra of those subalgebras, which is
`Stacks.StageSubalgebra.specDiagram`.  Each component is the canonical composite
`W_k ⟶ Spec B_k ⟶ Spec A`, so it carries no choice: the first factor is given with the stage and
the second is the spectrum of the inclusion.

The hypothesis `hβ` that `AlgebraicGeometry.gluePairFunctor` consumes — that the images of the
components are inverse images of one another along the transition morphisms — is the one that
needed the image equality `AlgebraicGeometry.exists_isFiniteTypeOpenModel_opensRange_eq`, which
is why this leg could not be built before.  With a *stagewise-compatible* charting family it now
follows: each image is the union of the standard opens of the family read inside the spectrum of
the subalgebra, and the
inverse image of a union of standard opens is the union of the standard opens of the images
(`AlgebraicGeometry.SpecMap_preimage_iSup_basicOpen`).

## What is built, and the route

* `Stacks.StageSubalgebra.overlapDiagram` reindexes the system of overlap models onto the pairs,
  along the projection `Stacks.StageSubalgebra.proj`.

* `Stacks.StageSubalgebra.inclusionHom_comp_val` is the one ring identity the construction
  needs: the inclusion of a subalgebra into a later one, followed by the inclusion into the ring
  at the later stage, is the inclusion into the ring at the earlier stage followed by the
  transition.  It holds by reflexivity on elements, since that is how the transition map of the
  diagram of subalgebras was defined.

* `Stacks.StageSubalgebra.specLeg` is the transformation.  Naturality is the compatibility of
  the given family of morphisms to the spectra of the rings, plus that identity; the transition
  used is reached by `Subsingleton.elim`, the homs of a preorder being a subsingleton.

* `Stacks.StageSubalgebra.isOpenImmersion_specLeg_app` and
  `Stacks.StageSubalgebra.opensRange_specLeg_app` are the two conclusions of
  `AlgebraicGeometry.IsChartedSubalgebra` read at a pair, and
  `Stacks.StageSubalgebra.preimage_opensRange_specLeg` is `hβ`.

* `Stacks.StageSubalgebra.openInclusionLeg` is the *first* leg over the same index: the inclusion
  of the compatible family of opens `AlgebraicGeometry.compatibleOpensInclusion`, whiskered along
  the projection to the stages, and
  `Stacks.StageSubalgebra.preimage_opensRange_openInclusionLeg` is
  `hα`.  `AlgebraicGeometry.gluePairFunctor` takes both legs out of **one** diagram over **one**
  index, which is why the first leg has to be reindexed too; with these two, that functor and all
  five of its conditions apply.

## Universe situation

The stages, the rings and the schemes share the universe `u`, as the index requires of
its index type.  Nothing here forms a limit or a colimit, so the index universe is not tied down
any further than the index already ties it.

## Transparency gotchas

* An inequality in the *opposite* preorder is extracted by the named
  `Stacks.StageSubalgebra.le_ofDual_of_hom` rather than by `CategoryTheory.leOfHom` in place; see
  the discussion at `Stacks.StageSubalgebra.le_of_dual_hom`, where the same shape made a functor
  identity fail its motive check.

* The charting family at a pair is the family at its stage, and the predicate carried by the
  pair is the charted condition for that family; both are reached through the accessors
  `Stacks.StageSubalgebra.stage` and `Stacks.StageSubalgebra.sub`, never by projecting the pair.

* The two hypotheses on the family — that its standard opens lie inside the image of the given
  morphism and cover it — are *stagewise* and are hypotheses here.  At the fibre-product rings of
  the one-affine-open step they are supplied by
  `AlgebraicGeometry.opensRange_iSup_basicOpen_comp_SpecMap_snd`.

## What is NOT done here

The compatible charting family is a hypothesis and is not constructed; at the fibre-product
rings it is the family of compatible pairs built from one stage-independent family in the ring
of the affine open being added, and nothing here says such a family exists.  Nothing here glues,
produces a cone, a limit, or an inhabitant of
`AlgebraicGeometry.Scheme.FiniteTypeApproximation`.  Tag 07RN is not proved and no tag attribute
is attached to anything in this file.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z7](https://stacks.math.columbia.edu/tag/01Z7)
* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.StageSubalgebra

variable {K : Type u} [Preorder K] {F : K ⥤ CommRingCat.{u}}
  {P : ∀ k : K, Subalgebra ℤ (F.obj k) → Prop}

/-- The inclusion of a subalgebra into a later one, followed by the inclusion into the ring at
the later stage, is the inclusion into the ring at the earlier stage followed by the
transition. -/
lemma inclusionHom_comp_val {j k : StageSubalgebra F P} (h : j ≤ k) :
    CommRingCat.ofHom ((sub j).val : sub j →+* F.obj (stage j)) ≫
        F.map (homOfLE (le_stage h)) =
      inclusionHom h ≫ CommRingCat.ofHom ((sub k).val : sub k →+* F.obj (stage k)) := by
  apply CommRingCat.hom_ext
  refine RingHom.ext fun a ↦ ?_
  change F.map (homOfLE (le_stage h)) (a : F.obj (stage j)) =
    ((inclusionAlgHom h a : sub k) : F.obj (stage k))
  rw [inclusionAlgHom_coe]

/-- The system of models of the overlap, reindexed onto the pairs of a stage and a distinguished
subalgebra. -/
noncomputable abbrev overlapDiagram (Dw : Kᵒᵈ ⥤ Scheme.{u})
    (P : ∀ k : K, Subalgebra ℤ (F.obj k) → Prop) :
    (StageSubalgebra F P)ᵒᵈ ⥤ Scheme.{u} :=
  (proj (F := F) (P := P)).monotone.dual.functor ⋙ Dw

variable {Dw : Kᵒᵈ ⥤ Scheme.{u}}

/-- **The second leg of the glueing.**  Its components are the canonical composites
`W_k ⟶ Spec B_k ⟶ Spec A`: the given morphism to the spectrum of the ring at the stage, then the
spectrum of the inclusion of the subalgebra.  No choice is made. -/
noncomputable def specLeg
    (γ : ∀ k : K, Dw.obj (OrderDual.toDual k) ⟶ Spec (CommRingCat.of (F.obj k)))
    (hγ : ∀ {k k' : K} (h : k ≤ k'),
      Dw.map (homOfLE (OrderDual.toDual_le_toDual.mpr h)) ≫ γ k =
        γ k' ≫ Spec.map (F.map (homOfLE h))) :
    overlapDiagram Dw P ⟶ specDiagram F P where
  app j := γ (stage (OrderDual.ofDual j)) ≫ Spec.map (CommRingCat.ofHom
    ((sub (OrderDual.ofDual j)).val : sub (OrderDual.ofDual j) →+*
      F.obj (stage (OrderDual.ofDual j))))
  naturality {j k} u := by
    have hu : OrderDual.ofDual k ≤ OrderDual.ofDual j := leOfHom u
    have key : Dw.map (homOfLE (OrderDual.toDual_le_toDual.mpr (le_stage hu))) ≫
        (γ (stage (OrderDual.ofDual k)) ≫ Spec.map (CommRingCat.ofHom
          ((sub (OrderDual.ofDual k)).val : sub (OrderDual.ofDual k) →+*
            F.obj (stage (OrderDual.ofDual k))))) =
        (γ (stage (OrderDual.ofDual j)) ≫ Spec.map (CommRingCat.ofHom
          ((sub (OrderDual.ofDual j)).val : sub (OrderDual.ofDual j) →+*
            F.obj (stage (OrderDual.ofDual j))))) ≫ Spec.map (inclusionHom hu) := by
      rw [← Category.assoc, hγ (le_stage hu), Category.assoc, Category.assoc,
        ← Spec.map_comp, ← Spec.map_comp, ← inclusionHom_comp_val hu]
    exact key

/-- The component of `specLeg` at a pair is the given morphism at its stage followed by the
spectrum of the inclusion of the subalgebra. -/
@[simp]
lemma specLeg_app (γ : ∀ k : K, Dw.obj (OrderDual.toDual k) ⟶ Spec (CommRingCat.of (F.obj k)))
    (hγ : ∀ {k k' : K} (h : k ≤ k'),
      Dw.map (homOfLE (OrderDual.toDual_le_toDual.mpr h)) ≫ γ k =
        γ k' ≫ Spec.map (F.map (homOfLE h)))
    (j : (StageSubalgebra F P)ᵒᵈ) :
    (specLeg (Dw := Dw) (P := P) γ hγ).app j = γ (stage (OrderDual.ofDual j)) ≫
      Spec.map (CommRingCat.ofHom ((sub (OrderDual.ofDual j)).val :
        sub (OrderDual.ofDual j) →+* F.obj (stage (OrderDual.ofDual j)))) := rfl

/-! ### The two conclusions at a pair, and the inverse-image condition -/

section Charted

variable {n : ℕ} (b : ∀ k : K, Fin n → F.obj k)

/-- The distinguished predicate of the index of pairs for the one-affine-open step: the
subalgebra is charted by the family at its stage. -/
def ChartedAt (k : K) (A : Subalgebra ℤ (F.obj k)) : Prop := IsChartedSubalgebra A (b k)

/-- The charted condition carried by a pair of the index. -/
lemma isChartedSubalgebra_sub (j : StageSubalgebra F (ChartedAt b)) :
    IsChartedSubalgebra (sub j) (b (stage j)) := j.2.2

/-- **Each component of the second leg is an open immersion.**  This is the open-model half of
`AlgebraicGeometry.IsChartedSubalgebra`, read at a pair. -/
lemma isOpenImmersion_specLeg_app
    (γ : ∀ k : K, Dw.obj (OrderDual.toDual k) ⟶ Spec (CommRingCat.of (F.obj k)))
    [∀ k : K, IsOpenImmersion (γ k)]
    (hγ : ∀ {k k' : K} (h : k ≤ k'),
      Dw.map (homOfLE (OrderDual.toDual_le_toDual.mpr h)) ≫ γ k =
        γ k' ≫ Spec.map (F.map (homOfLE h)))
    (hrU : ∀ (k : K) (l : Fin n),
      (PrimeSpectrum.basicOpen (b k l) : (Spec (CommRingCat.of (F.obj k))).Opens) ≤
        (γ k).opensRange)
    (hcover : ∀ k : K, (γ k).opensRange ≤
      ⨆ l, (PrimeSpectrum.basicOpen (b k l) : (Spec (CommRingCat.of (F.obj k))).Opens))
    (j : (StageSubalgebra F (ChartedAt b))ᵒᵈ) :
    IsOpenImmersion ((specLeg (Dw := Dw) (P := ChartedAt b) γ hγ).app j) :=
  (isChartedSubalgebra_sub b (OrderDual.ofDual j)).isOpenImmersion_comp_SpecMap_val
    (f := γ (stage (OrderDual.ofDual j))) (hrU _) (hcover _)

/-- **The image of a component of the second leg.**  It is the union of the standard opens of
the charting family, read inside the spectrum of the subalgebra. -/
lemma opensRange_specLeg_app
    (γ : ∀ k : K, Dw.obj (OrderDual.toDual k) ⟶ Spec (CommRingCat.of (F.obj k)))
    [∀ k : K, IsOpenImmersion (γ k)]
    (hγ : ∀ {k k' : K} (h : k ≤ k'),
      Dw.map (homOfLE (OrderDual.toDual_le_toDual.mpr h)) ≫ γ k =
        γ k' ≫ Spec.map (F.map (homOfLE h)))
    (hrU : ∀ (k : K) (l : Fin n),
      (PrimeSpectrum.basicOpen (b k l) : (Spec (CommRingCat.of (F.obj k))).Opens) ≤
        (γ k).opensRange)
    (hcover : ∀ k : K, (γ k).opensRange ≤
      ⨆ l, (PrimeSpectrum.basicOpen (b k l) : (Spec (CommRingCat.of (F.obj k))).Opens))
    (j : (StageSubalgebra F (ChartedAt b))ᵒᵈ) :
    haveI := isOpenImmersion_specLeg_app b γ hγ hrU hcover j
    ((specLeg (Dw := Dw) (P := ChartedAt b) γ hγ).app j).opensRange =
      (⨆ l, PrimeSpectrum.basicOpen (⟨b (stage (OrderDual.ofDual j)) l,
          (isChartedSubalgebra_sub b (OrderDual.ofDual j)).mem l⟩ :
            sub (OrderDual.ofDual j)) :
        (Spec (CommRingCat.of (sub (OrderDual.ofDual j)))).Opens) :=
  (isChartedSubalgebra_sub b (OrderDual.ofDual j)).opensRange_comp_SpecMap_val
    (f := γ (stage (OrderDual.ofDual j))) (hrU _) (hcover _)

/-- **The inverse-image condition for the second leg.**  This is the hypothesis `hβ` of
`AlgebraicGeometry.gluePairFunctor`, and with it
`AlgebraicGeometry.isPullback_gluePairFunctorInl_app` gives the cartesianness that the open
subsystem of an approximating inverse system has to satisfy.

The charting family has to be *stagewise compatible*, which is the hypothesis `hb`: that is what
makes the standard opens at a later stage the inverse images of those at an earlier one. -/
lemma preimage_opensRange_specLeg
    (γ : ∀ k : K, Dw.obj (OrderDual.toDual k) ⟶ Spec (CommRingCat.of (F.obj k)))
    [∀ k : K, IsOpenImmersion (γ k)]
    (hγ : ∀ {k k' : K} (h : k ≤ k'),
      Dw.map (homOfLE (OrderDual.toDual_le_toDual.mpr h)) ≫ γ k =
        γ k' ≫ Spec.map (F.map (homOfLE h)))
    (hrU : ∀ (k : K) (l : Fin n),
      (PrimeSpectrum.basicOpen (b k l) : (Spec (CommRingCat.of (F.obj k))).Opens) ≤
        (γ k).opensRange)
    (hcover : ∀ k : K, (γ k).opensRange ≤
      ⨆ l, (PrimeSpectrum.basicOpen (b k l) : (Spec (CommRingCat.of (F.obj k))).Opens))
    (hb : ∀ {k k' : K} (h : k ≤ k') (l : Fin n), F.map (homOfLE h) (b k l) = b k' l)
    ⦃j k : (StageSubalgebra F (ChartedAt b))ᵒᵈ⦄ (u : j ⟶ k) :
    haveI := isOpenImmersion_specLeg_app b γ hγ hrU hcover j
    haveI := isOpenImmersion_specLeg_app b γ hγ hrU hcover k
    (specDiagram F (ChartedAt b)).map u ⁻¹ᵁ
        ((specLeg (Dw := Dw) (P := ChartedAt b) γ hγ).app k).opensRange =
      ((specLeg (Dw := Dw) (P := ChartedAt b) γ hγ).app j).opensRange := by
  have hu : OrderDual.ofDual k ≤ OrderDual.ofDual j := leOfHom u
  have hij := isOpenImmersion_specLeg_app b γ hγ hrU hcover j
  have hik := isOpenImmersion_specLeg_app b γ hγ hrU hcover k
  rw [opensRange_specLeg_app b γ hγ hrU hcover j, opensRange_specLeg_app b γ hγ hrU hcover k,
    specDiagram_map, SpecMap_preimage_iSup_basicOpen]
  refine iSup_congr fun l ↦ congrArg PrimeSpectrum.basicOpen (Subtype.ext ?_)
  change ((inclusionAlgHom hu ⟨b (stage (OrderDual.ofDual k)) l,
    (isChartedSubalgebra_sub b (OrderDual.ofDual k)).mem l⟩ :
      sub (OrderDual.ofDual j)) : F.obj (stage (OrderDual.ofDual j))) = _
  rw [inclusionAlgHom_coe]
  exact hb (le_stage hu) l

end Charted

/-! ### The first leg over the same index -/

section FirstLeg

variable {Dv : Kᵒᵈ ⥤ Scheme.{u}}

/-- **The first leg of the glueing, over the index of pairs.**  It is the inclusion of a
compatible family of opens — `AlgebraicGeometry.compatibleOpensInclusion` — reindexed along the
projection to the stages, so that both legs of the glueing live over one index, which is what
`AlgebraicGeometry.gluePairFunctor` requires. -/
noncomputable def openInclusionLeg (V : ∀ a, (Dv.obj a).Opens)
    (hV : ∀ ⦃a a' : Kᵒᵈ⦄ (v : a ⟶ a'), Dv.map v ⁻¹ᵁ V a' = V a)
    (P : ∀ k : K, Subalgebra ℤ (F.obj k) → Prop) :
    overlapDiagram (compatibleOpensDiagram Dv V hV) P ⟶ overlapDiagram Dv P :=
  Functor.whiskerLeft (proj (F := F) (P := P)).monotone.dual.functor
    (compatibleOpensInclusion Dv V hV)

/-- The component of `openInclusionLeg` at a pair is the inclusion of the open at its stage. -/
@[simp]
lemma openInclusionLeg_app (V : ∀ a, (Dv.obj a).Opens)
    (hV : ∀ ⦃a a' : Kᵒᵈ⦄ (v : a ⟶ a'), Dv.map v ⁻¹ᵁ V a' = V a)
    (P : ∀ k : K, Subalgebra ℤ (F.obj k) → Prop) (j : (StageSubalgebra F P)ᵒᵈ) :
    (openInclusionLeg V hV P).app j =
      (V (OrderDual.toDual (stage (OrderDual.ofDual j)))).ι := rfl

/-- Each component of `openInclusionLeg` is an open immersion. -/
instance isOpenImmersion_openInclusionLeg_app (V : ∀ a, (Dv.obj a).Opens)
    (hV : ∀ ⦃a a' : Kᵒᵈ⦄ (v : a ⟶ a'), Dv.map v ⁻¹ᵁ V a' = V a)
    (P : ∀ k : K, Subalgebra ℤ (F.obj k) → Prop) (j : (StageSubalgebra F P)ᵒᵈ) :
    IsOpenImmersion ((openInclusionLeg V hV P).app j) :=
  inferInstanceAs (IsOpenImmersion (V (OrderDual.toDual (stage (OrderDual.ofDual j)))).ι)

/-- **The inverse-image condition for the first leg**, which is the hypothesis `hα` of
`AlgebraicGeometry.gluePairFunctor`.  It is the compatibility of the family of opens, read at the
reindexed transition morphism. -/
lemma preimage_opensRange_openInclusionLeg (V : ∀ a, (Dv.obj a).Opens)
    (hV : ∀ ⦃a a' : Kᵒᵈ⦄ (v : a ⟶ a'), Dv.map v ⁻¹ᵁ V a' = V a)
    (P : ∀ k : K, Subalgebra ℤ (F.obj k) → Prop)
    ⦃j k : (StageSubalgebra F P)ᵒᵈ⦄ (u : j ⟶ k) :
    (overlapDiagram Dv P).map u ⁻¹ᵁ ((openInclusionLeg V hV P).app k).opensRange =
      ((openInclusionLeg V hV P).app j).opensRange :=
  preimage_opensRange_compatibleOpensInclusion Dv V hV
    ((proj (F := F) (P := P)).monotone.dual.functor.map u)

end FirstLeg

end Stacks.StageSubalgebra
