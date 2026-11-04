module

public import StacksFrontier.AlgebraicGeometry.Gluing.IsoDescent

/-!
# Descending an isomorphism along a cofiltered limit, together with its compatibility

Let `D` be a cofiltered inverse system of quasi-compact, quasi-separated schemes with affine
transition morphisms and let `c` be a limit cone over it.  If two schemes of finite presentation
over one stage `D.obj i` become isomorphic after base change to `c.pt`, then their base changes
to some later stage are already isomorphic — and the isomorphism at that later stage *base
changes back to the given one*.

## Why this file exists, and the claim it refutes

`StacksFrontier.AlgebraicGeometry.Gluing.IsoDescent` proves the existence half
(`AlgebraicGeometry.exists_iso_after_baseChange`) and says in its own implementation notes that
compatibility of the descended isomorphism with the given one is *not* asserted.  That is not an
optional extra for Tag 0E8Q: the gluing-data isomorphism of
`AlgebraicGeometry.isoCanonicalRestrictionFunctorObjMk` has to commute with
`AlgebraicGeometry.canonicalRestrictionComparison`, and the content of that square is exactly
that the isomorphism the charts are glued along is the one the gluing datum supplies.  So the
existence statement alone cannot close the `equivalence` label, and this file supplies the
missing half.

The compatibility is stated in the *same form* as Tag 01ZM part (2) states it
(`AlgebraicGeometry.exists_morphism_after_baseChange`): two comparison isomorphisms pinned by
their compatibility with the first pullback projections, and one commuting square.  Stated that
way, the extra content costs three rewrites, because

* the two comparison isomorphisms produced by part (2) are already fst-compatible, and
  fst-compatibility composes with
  `AlgebraicGeometry.overPullbackCompIso_fst` and
  `AlgebraicGeometry.overPullback_map_left_fst`;
* part (2)'s own square transports across the stage change of Tag 081E by
  `AlgebraicGeometry.overPullbackCompIso_naturality`, because the isomorphism Tag 081E produces
  is *literally* the base change of part (2)'s descended morphism.

The second point is the reason the compatibility was available all along: Tag 081E does not
build a new isomorphism, it proves that an existing morphism is invertible.

## Main results

* `AlgebraicGeometry.overPullbackCompIso_inv_fst`: the inverse of the iterated-base-change
  comparison carries the composite of the two first projections to the single one.
* `AlgebraicGeometry.exists_iso_after_baseChange_compat`: the statement above.

## References

* [Stacks Project, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 081E](https://stacks.math.columbia.edu/tag/081E)
* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

/-- The inverse of the comparison between an iterated base change and the direct base change
carries the composite of the two first projections to the single first projection.  This is the
inverse form of `AlgebraicGeometry.overPullbackCompIso_fst`, and it is what makes
fst-compatibility composable along a stage change. -/
lemma overPullbackCompIso_inv_fst {S S' T : Scheme.{u}} (p : S ⟶ T) (q : S' ⟶ S) (r : S' ⟶ T)
    (h : q ≫ p = r) (X : Over T) :
    (overPullbackCompIso p q r h X).inv.left ≫
        pullback.fst ((Over.pullback p).obj X).hom q ≫ pullback.fst X.hom p =
      pullback.fst X.hom r := by
  have hid : (overPullbackCompIso p q r h X).inv.left ≫
      (overPullbackCompIso p q r h X).hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  rw [← overPullbackCompIso_fst p q r h X, ← Category.assoc, hid, Category.id_comp]

section

variable {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- **Two schemes of finite presentation over one stage which become isomorphic over the limit
are isomorphic at a later stage, compatibly with the given isomorphism.**

This strengthens `AlgebraicGeometry.exists_iso_after_baseChange` by the conjunct that file
declines to prove, and the conjunct is what Tag 0E8Q's gluing-data square needs: the descended
isomorphism `χ` base changes to the given `φ`, up to the two comparison isomorphisms `α` and
`β`, which are pinned down by their compatibility with the first pullback projections exactly as
in Tag 01ZM part (2). -/
theorem exists_iso_after_baseChange_compat (i : I) (X Y : Over (D.obj i))
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom)
    (φ : (Over.pullback (c.π.app i)).obj X ≅ (Over.pullback (c.π.app i)).obj Y) :
    ∃ (j : I) (e : j ⟶ i)
      (χ : (Over.pullback (D.map e)).obj X ≅ (Over.pullback (D.map e)).obj Y)
      (α : (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj X) ≅
        (Over.pullback (c.π.app i)).obj X)
      (β : (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj Y) ≅
        (Over.pullback (c.π.app i)).obj Y),
      α.hom.left ≫ pullback.fst X.hom (c.π.app i) =
          pullback.fst ((Over.pullback (D.map e)).obj X).hom (c.π.app j) ≫
            pullback.fst X.hom (D.map e) ∧
        β.hom.left ≫ pullback.fst Y.hom (c.π.app i) =
          pullback.fst ((Over.pullback (D.map e)).obj Y).hom (c.π.app j) ≫
            pullback.fst Y.hom (D.map e) ∧
        α.hom ≫ φ.hom = (Over.pullback (c.π.app j)).map χ.hom ≫ β.hom := by
  obtain ⟨j, e, g, α₀, β₀, hα₀, hβ₀, hcomm⟩ :=
    exists_morphism_after_baseChange D c hc i X Y hX hY φ.hom
  -- The base change of `g` to the limit is an isomorphism, because part (2)'s own square
  -- exhibits it as a composite of three.
  have hge : (Over.pullback (c.π.app j)).map g = (α₀.hom ≫ φ.hom) ≫ β₀.inv := by
    rw [hcomm, Category.assoc, β₀.hom_inv_id, Category.comp_id]
  have hgiso : IsIso ((Over.pullback (c.π.app j)).map g) := by
    rw [hge]; infer_instance
  have hleft : IsIso ((Over.pullback (c.π.app j)).map g).left := by
    have h := (Over.forget c.pt).map_isIso ((Over.pullback (c.π.app j)).map g)
    rwa [Over.forget_map] at h
  obtain ⟨hXc, hXq⟩ := compactSpace_and_quasiSeparatedSpace_left X hX
  obtain ⟨hYc, hYq⟩ := compactSpace_and_quasiSeparatedSpace_left Y hY
  have hXj : FinitePresentation ((Over.pullback (D.map e)).obj X).hom :=
    LimitFPObjectDescent.finitePresentation_overPullback (D.map e) X hX
  have hYj : FinitePresentation ((Over.pullback (D.map e)).obj Y).hom :=
    LimitFPObjectDescent.finitePresentation_overPullback (D.map e) Y hY
  obtain ⟨hXjc, hXjq⟩ :=
    compactSpace_and_quasiSeparatedSpace_left ((Over.pullback (D.map e)).obj X) hXj
  obtain ⟨hYjc, hYjq⟩ :=
    compactSpace_and_quasiSeparatedSpace_left ((Over.pullback (D.map e)).obj Y) hYj
  have : LocallyOfFinitePresentation ((Over.pullback (D.map e)).obj Y).hom := hYj.1
  have : LocallyOfFinitePresentation g.left := by
    have : LocallyOfFinitePresentation (g.left ≫ ((Over.pullback (D.map e)).obj Y).hom) := by
      rw [Over.w g]; exact hXj.1
    exact locallyOfFinitePresentation_of_comp g.left ((Over.pullback (D.map e)).obj Y).hom
  obtain ⟨k, m, hk⟩ := exists_isIso_baseChange_of_isIso_limitBaseChange D c hc j
    ((Over.pullback (D.map e)).obj X) ((Over.pullback (D.map e)).obj Y) g
  have hkiso : IsIso ((Over.pullback (D.map m)).map g).left := hk
  -- Name the comparison isomorphisms opaquely, with their defining equations, so that the
  -- rewrites below cannot unfold them.
  obtain ⟨L, hL⟩ : ∃ L : ∀ Z : Over (D.obj i), (Over.pullback (D.map m)).obj
      ((Over.pullback (D.map e)).obj Z) ≅ (Over.pullback (D.map (m ≫ e))).obj Z,
      ∀ Z, L Z = overPullbackCompIso (D.map e) (D.map m) (D.map (m ≫ e)) (D.map_comp m e).symm Z :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ∀ Z : Over (D.obj j), (Over.pullback (c.π.app k)).obj
      ((Over.pullback (D.map m)).obj Z) ≅ (Over.pullback (c.π.app j)).obj Z,
      ∀ Z, M Z = overPullbackCompIso (D.map m) (c.π.app k) (c.π.app j) (c.w m) Z :=
    ⟨_, fun _ => rfl⟩
  -- The first-projection compatibility of the new comparison isomorphisms, for both `X` and `Y`.
  have key : ∀ (Z : Over (D.obj i))
      (a : (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj Z) ≅
        (Over.pullback (c.π.app i)).obj Z),
      a.hom.left ≫ pullback.fst Z.hom (c.π.app i) =
        pullback.fst ((Over.pullback (D.map e)).obj Z).hom (c.π.app j) ≫
          pullback.fst Z.hom (D.map e) →
      (((Over.pullback (c.π.app k)).mapIso (L Z)).symm ≪≫ M _ ≪≫ a).hom.left ≫
          pullback.fst Z.hom (c.π.app i) =
        pullback.fst ((Over.pullback (D.map (m ≫ e))).obj Z).hom (c.π.app k) ≫
          pullback.fst Z.hom (D.map (m ≫ e)) := by
    intro Z a ha
    rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Over.comp_left,
      Over.comp_left, Category.assoc, Category.assoc, ha, hM,
      reassoc_of% overPullbackCompIso_fst, overPullback_map_left_fst_assoc, hL,
      overPullbackCompIso_inv_fst]
  refine ⟨k, m ≫ e, (L X).symm ≪≫ Over.isoMk (asIso ((Over.pullback (D.map m)).map g).left)
      (Over.w _) ≪≫ L Y,
    ((Over.pullback (c.π.app k)).mapIso (L X)).symm ≪≫ M _ ≪≫ α₀,
    ((Over.pullback (c.π.app k)).mapIso (L Y)).symm ≪≫ M _ ≪≫ β₀, key X _ hα₀, key Y _ hβ₀, ?_⟩
  have hgiso' : (Over.isoMk (asIso ((Over.pullback (D.map m)).map g).left)
      (Over.w ((Over.pullback (D.map m)).map g)) :
        (Over.pullback (D.map m)).obj ((Over.pullback (D.map e)).obj X) ≅
          (Over.pullback (D.map m)).obj ((Over.pullback (D.map e)).obj Y)).hom =
    (Over.pullback (D.map m)).map g := Over.OverMorphism.ext (by simp)
  have hnat : (Over.pullback (c.π.app k)).map ((Over.pullback (D.map m)).map g) ≫ (M _).hom =
      (M _).hom ≫ (Over.pullback (c.π.app j)).map g := by
    rw [hM, hM, ← overPullbackCompIso_naturality (D.map m) (c.π.app k) (c.π.app j) (c.w m) g]
  have hcancel : ∀ {Z : Over c.pt}
      (f : (Over.pullback (c.π.app k)).obj
        ((Over.pullback (D.map m)).obj ((Over.pullback (D.map e)).obj Y)) ⟶ Z),
      (Over.pullback (c.π.app k)).map (L Y).hom ≫
        (Over.pullback (c.π.app k)).map (L Y).inv ≫ f = f := by
    intro Z f
    rw [← Category.assoc, ← Functor.map_comp (Over.pullback (c.π.app k)), (L Y).hom_inv_id,
      (Over.pullback (c.π.app k)).map_id, Category.id_comp]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, hgiso',
    Functor.map_comp (Over.pullback (c.π.app k)), Category.assoc, hcancel]
  rw [reassoc_of% hnat, ← hcomm]

end

end AlgebraicGeometry

end
