module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.LimitFPObjectDescent.Retract

/-!
# Two objects isomorphic over the limit are isomorphic at a later stage

Let `D` be a cofiltered inverse system of quasi-compact, quasi-separated schemes with affine
transition morphisms and let `c` be a limit cone over it.  If two schemes of finite presentation
over one stage `D.obj i` become isomorphic after base change to `c.pt`, then their base changes
to some later stage are already isomorphic.

This is the second residue item of [Stacks, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA):
there the two objects over a stage `W` are the restriction of the given scheme over the open
complement and the model of the given scheme over the local ring, and the isomorphism over the
limit is the one carried by the gluing datum.

## The route, and a correction to the record

One might assemble this from parts (2) and (3) of
[Stacks, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM).  **It needs part (2) only**: the
upgrade from a descended morphism to a descended *isomorphism* is
`AlgebraicGeometry.exists_isIso_baseChange_of_isIso_limitBaseChange`, which is
[Stacks, Tag 081E](https://stacks.math.columbia.edu/tag/081E), proved and tagged in
`StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Isomorphism`.  So the composition is

1. `AlgebraicGeometry.exists_morphism_after_baseChange` (Tag 01ZM, part (2)) descends the
   underlying morphism of the isomorphism to a stage `j`, together with two transport
   isomorphisms and the equation relating them;
2. that equation exhibits the base change of the descended morphism to `c.pt` as a composite of
   three isomorphisms, hence as an isomorphism;
3. Tag 081E then produces a stage `k` later than `j` at which the descended morphism is already
   an isomorphism;
4. `CategoryTheory.Over.pullback` of the transition `k ⟶ j` composed with the transition
   `j ⟶ i` carries both objects to stage `k`, and the base-change associativity isomorphism
   `AlgebraicGeometry.overPullbackCompIso` identifies the iterated base change with the
   single one, so the isomorphism lands on the objects the statement asks about.

Step 4 is the only bookkeeping, and it is one isomorphism of functors.

## Main results

* `AlgebraicGeometry.compactSpace_and_quasiSeparatedSpace_left`: the hypothesis bundle that
  Tag 081E asks of its two objects, from finite presentation over a quasi-compact and
  quasi-separated base.
* `AlgebraicGeometry.exists_iso_after_baseChange`: the statement above.

## Implementation notes

The conclusion is a `Nonempty` of an isomorphism of `CategoryTheory.Over` objects, which is the
form Tag 01ZM part (1) (`AlgebraicGeometry.exists_model_of_finitePresentation`) already uses,
so a consumer that has one of the two can consume the other without a translation.

Compatibility of the descended isomorphism with the given one over `c.pt` is *not* asserted.
It is available in principle — step 1 provides the equation at stage `j` — but transporting it
across the stage change of step 3 needs the coherence of `AlgebraicGeometry.overPullbackCompIso`
with the cone, which is the bookkeeping that the construction direction of Tag 0E8Q's
`glueingData` needs anyway and which is not done here.

No `@[stacks]` attribute is attached: Tag 0BPA is not carded in this repository, Tag 081E is
already tagged at its own statement, and Tag 0E8Q's `equivalence` label has a single
`CategoryTheory.Functor.IsEquivalence` assertion as its covering set.

## References

* [Stacks Project, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 081E](https://stacks.math.columbia.edu/tag/081E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

/-- An object of finite presentation over a quasi-compact, quasi-separated base is itself
quasi-compact and quasi-separated as a space.  This is the hypothesis bundle that
`AlgebraicGeometry.exists_isIso_baseChange_of_isIso_limitBaseChange` asks for on both of its
objects, and each of the two stages of the proof below has to supply it. -/
lemma compactSpace_and_quasiSeparatedSpace_left {T : Scheme.{u}} [CompactSpace T]
    [QuasiSeparatedSpace T] (X : Over T) (hX : FinitePresentation X.hom) :
    CompactSpace X.left ∧ QuasiSeparatedSpace X.left := by
  have : QuasiCompact X.hom := hX.2.1
  have : QuasiSeparated X.hom := hX.2.2
  exact ⟨QuasiCompact.compactSpace_of_compactSpace X.hom,
    quasiSeparatedSpace_of_quasiSeparated X.hom⟩

section

variable {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- **Two schemes of finite presentation over one stage which become isomorphic over the limit
are isomorphic at a later stage.**

This is residue item (2) of Tag 0BPA.  Part (2) of Tag 01ZM descends the underlying morphism of
the given isomorphism; its own transport equation makes the base change of the descended
morphism to the limit a composite of three isomorphisms, and Tag 081E then makes the descended
morphism itself an isomorphism at a yet later stage. -/
theorem exists_iso_after_baseChange (i : I) (X Y : Over (D.obj i))
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom)
    (φ : (Over.pullback (c.π.app i)).obj X ≅ (Over.pullback (c.π.app i)).obj Y) :
    ∃ (j : I) (e : j ⟶ i),
      Nonempty ((Over.pullback (D.map e)).obj X ≅ (Over.pullback (D.map e)).obj Y) := by
  obtain ⟨j, e, g, α, β, -, -, hcomm⟩ :=
    exists_morphism_after_baseChange D c hc i X Y hX hY φ.hom
  -- Step 2: the base change of `g` to the limit is `α.hom ≫ φ.hom ≫ β.inv`, hence invertible.
  have hge : (Over.pullback (c.π.app j)).map g = (α.hom ≫ φ.hom) ≫ β.inv := by
    rw [hcomm, Category.assoc, β.hom_inv_id, Category.comp_id]
  have hgiso : IsIso ((Over.pullback (c.π.app j)).map g) := by
    rw [hge]; infer_instance
  -- `CategoryTheory.Over.forget` is a `def`, so `(Over.forget _).map h` is not unified with
  -- `h.left` by instance search; the bridge is Mathlib's own equation `Over.forget_map`.
  have hleft : IsIso ((Over.pullback (c.π.app j)).map g).left := by
    have h := (Over.forget c.pt).map_isIso ((Over.pullback (c.π.app j)).map g)
    rwa [Over.forget_map] at h
  -- Step 3: Tag 081E upgrades it to an isomorphism at a later stage.
  have hfp : ∀ Z : Over (D.obj i), FinitePresentation Z.hom →
      FinitePresentation ((Over.pullback (D.map e)).obj Z).hom ∧
        CompactSpace ((Over.pullback (D.map e)).obj Z).left ∧
        QuasiSeparatedSpace ((Over.pullback (D.map e)).obj Z).left := fun Z hZ =>
    have hZj := LimitFPObjectDescent.finitePresentation_overPullback (D.map e) Z hZ
    ⟨hZj, compactSpace_and_quasiSeparatedSpace_left _ hZj⟩
  obtain ⟨hXj, hXjc, hXjq⟩ := hfp X hX
  obtain ⟨hYj, hYjc, hYjq⟩ := hfp Y hY
  have : LocallyOfFinitePresentation ((Over.pullback (D.map e)).obj Y).hom := hYj.1
  have : LocallyOfFinitePresentation g.left := by
    have : LocallyOfFinitePresentation (g.left ≫ ((Over.pullback (D.map e)).obj Y).hom) := by
      rw [Over.w g]; exact hXj.1
    exact locallyOfFinitePresentation_of_comp g.left ((Over.pullback (D.map e)).obj Y).hom
  obtain ⟨k, m, hk⟩ := exists_isIso_baseChange_of_isIso_limitBaseChange D c hc j
    ((Over.pullback (D.map e)).obj X) ((Over.pullback (D.map e)).obj Y) g
  -- Step 4: transport the isomorphism at `k` from the iterated base change to the single one.
  have : IsIso ((Over.pullback (D.map m)).map g).left := hk
  refine ⟨k, m ≫ e, ⟨?_⟩⟩
  exact (overPullbackCompIso (D.map e) (D.map m) (D.map (m ≫ e))
        (D.map_comp m e).symm X).symm ≪≫
      Over.isoMk (asIso ((Over.pullback (D.map m)).map g).left) (Over.w _) ≪≫
      overPullbackCompIso (D.map e) (D.map m) (D.map (m ≫ e)) (D.map_comp m e).symm Y

end

end AlgebraicGeometry

end
