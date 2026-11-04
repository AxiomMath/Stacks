module

public import StacksFrontier.AlgebraicGeometry.LimitApproxJoin.Shrink
public import StacksFrontier.AlgebraicGeometry.LimitApproxJoin.StepTwo

/-!
# The geometric join: step (ii) of the one-affine-open step, from geometric hypotheses

Let `D` be a cofiltered diagram of quasi-compact quasi-separated schemes with affine transition
morphisms, let `c` be a limiting cone, and let the vertex sit inside an affine scheme `Y` by an
open immersion.  Suppose finitely many `g : Fin n → Γ(Y, ⊤)` have their standard opens inside
that open and covering it.  Then some stage of the diagram maps by an open immersion into the
spectrum of the fibre product `Γ(Y, ⊤) ×_{Γ(c.pt, ⊤)} Γ(D.obj j, ⊤)`.

This is step (ii) of the one-affine-open step of Tag 07RN with no hypothesis left at a finite
stage.  In the argument `Y` is the affine open being added, the vertex is its overlap with the
part of the scheme already approximated, `D` is the system of models of that part, and the two
hypotheses on the `g` are the shrinking condition: the standard opens `D(g l)` lie inside the
overlap and cover it, which is possible because the overlap is a quasi-compact open of the
affine `Y`.

## Main results

`AlgebraicGeometry.exists_stage_isOpenImmersion_toSpecΓ_comp_SpecMap_snd` chains the three
pieces of this directory:

* the shrinking condition on the `g` gives the hypotheses of the geometric join *at the limit* —
  each `c.pt.basicOpen (jVY.appTop (g l))` is the preimage of `Y.basicOpen (g l)`, hence affine
  because the standard open lies inside the image of an open immersion, and the family covers
  because the standard opens cover that image;

* `AlgebraicGeometry.exists_stage_affine_basicOpen_cover` moves those two hypotheses to a finite
  stage, by Tags 01Z0, 01Z4 and 01Z5;

* `AlgebraicGeometry.isOpenImmersion_toSpecΓ_comp_SpecMap_snd_of_basicOpen_le` is step (ii) at
  that stage, with its localization hypothesis discharged by the qcqs lemma, Tag 01P7, applied
  twice, and with the identification of the stage with the union of standard opens supplied by
  the geometric join.

Quasi-affineness of the vertex, needed by the shrinking step, comes from Mathlib's
`AlgebraicGeometry.Scheme.IsQuasiAffine.of_isImmersion`: the vertex is a quasi-compact open
subscheme of an affine scheme.  Its quasi-compactness is
`AlgebraicGeometry.Scheme.compactSpace_of_isLimit`.  Quasi-affineness of the chosen stage is not
assumed: it is recovered from the covering family of affine basic opens by
`AlgebraicGeometry.Scheme.isQuasiAffine_of_iSup_basicOpen_eq_top`.

## Implementation notes

The cocone of rings whose fibre product is taken is `AlgebraicGeometry.Scheme.Γ.mapCocone` of the
opposite of the limiting cone; that it is a colimit is Tag 01Z0, and it is the cocone the
ring half of step (ii) consumes.  Its component at a stage is the map on global sections induced
by the cone leg, definitionally, which is what lets the lifts produced by the shrinking step be
handed straight to the ring half.

The index universe is tied to the scheme universe, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/LimitApproxJoin/Shrink.lean`: the colimit of the rings of sections
lives over the opposite index category and `CommRingCat` in one universe has no colimits over a
larger index universe.

Transparency gotchas:

* The two shrinking hypotheses are stated as `Y.basicOpen (g l) ≤ jVY.opensRange` and
  `jVY.opensRange ≤ ⨆ l, Y.basicOpen (g l)` rather than as an equality of the open with the
  union.  The first is what makes each basic open of the vertex affine and is also exactly the
  hypothesis of the localization half; the second is only needed for the covering.  An equality
  would conflate them and hide that the localization half uses only one.

* The affineness of a preimage is read through
  `AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion`, whose two sides are the
  image of an open and that open; the image of the preimage of `Y.basicOpen (g l)` is
  `Y.basicOpen (g l)` itself only because the standard open lies inside the image of the open
  immersion, and that step is where the first hypothesis is spent.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 01Z5](https://stacks.math.columbia.edu/tag/01Z5)
* [Stacks Project, Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- **Step (ii) of the one-affine-open step of Tag 07RN, from the shrinking condition.**  Let the
vertex of a limiting cone over a cofiltered diagram of qcqs schemes with affine transitions be an
open subscheme of an affine scheme `Y`, and let the standard opens of finitely many
`g : Fin n → Γ(Y, ⊤)` lie inside it and cover it.  Then some stage of the diagram maps by an open
immersion into the spectrum of the fibre product of `Γ(Y, ⊤)` with the sections of that stage
over the sections of the vertex. -/
lemma exists_stage_isOpenImmersion_toSpecΓ_comp_SpecMap_snd {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {Y : Scheme.{u}} [IsAffine Y] (jVY : c.pt ⟶ Y) [IsOpenImmersion jVY]
    {n : ℕ} (g : Fin n → Γ(Y, ⊤)) (hin : ∀ l, Y.basicOpen (g l) ≤ jVY.opensRange)
    (hcover : jVY.opensRange ≤ ⨆ l, Y.basicOpen (g l)) :
    ∃ (j : I) (f : Fin n → Γ(D.obj j, ⊤)),
      (∀ l, (c.π.app j).appTop (f l) = jVY.appTop (g l)) ∧
        IsOpenImmersion ((D.obj j).toSpecΓ ≫ Spec.map (Stacks.FibreProduct.snd jVY.appTop
          ((Scheme.Γ.mapCocone c.op).ι.app (op j)))) := by
  have hcpt : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  have : c.pt.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion jVY
  have haff : ∀ l, IsAffineOpen (c.pt.basicOpen (jVY.appTop (g l))) := fun l ↦ by
    rw [← Scheme.preimage_basicOpen_top,
      ← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion jVY,
      show jVY ''ᵁ (jVY ⁻¹ᵁ Y.basicOpen (g l)) = Y.basicOpen (g l) from
        Opens.ext (Set.image_preimage_eq_of_subset fun x hx ↦ hin l hx)]
    exact (isAffineOpen_top Y).basicOpen (g l)
  have hcov : ⨆ l, c.pt.basicOpen (jVY.appTop (g l)) = ⊤ := by
    refine top_unique fun x _ ↦ Opens.mem_iSup.mpr ?_
    obtain ⟨l, hl⟩ := Opens.mem_iSup.mp (hcover ⟨x, rfl⟩)
    exact ⟨l, (Scheme.preimage_basicOpen_top jVY (g l)).le hl⟩
  obtain ⟨j, f, hf, haff', hcov'⟩ :=
    exists_stage_affine_basicOpen_cover D c hc (fun l ↦ jVY.appTop (g l)) haff hcov
  have : (D.obj j).IsQuasiAffine :=
    Scheme.isQuasiAffine_of_iSup_basicOpen_eq_top (D.obj j) f haff' hcov'
  exact ⟨j, f, hf, isOpenImmersion_toSpecΓ_comp_SpecMap_snd_of_basicOpen_le jVY
    (Scheme.Γ.mapCocone c.op).ι j g hin f hf haff' hcov'⟩

end AlgebraicGeometry
