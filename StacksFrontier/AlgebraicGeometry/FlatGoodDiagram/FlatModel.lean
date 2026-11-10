module

public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic
public import StacksFrontier.AlgebraicGeometry.LimitSmallDominantIndex.Uniqueness
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat

/-!
# A flat model of finite presentation over a stage

A flat morphism of finite presentation into the limit of an inverse system of schemes is the base
change of a flat morphism of finite presentation over some stage. This is Stacks 01ZM part (1)
followed by Stacks 04AI, and this file arranges the two so that the conclusion is available with
the index type at a universe independent of the scheme universe and with *no* smallness
hypothesis on it — which is what Stacks 0CNT's statement of the flat case of a good diagram
needs, since it carries none.

## Main results

* `AlgebraicGeometry.exists_flat_model_of_small_limit`: the statement for a `u`-small cofiltered
  index category, directly from Stacks 01ZM part (1) and Stacks 04AI.
* `AlgebraicGeometry.exists_flat_model_of_affine_dominant_limit`: the statement for an index
  preorder at an arbitrary universe, for a system in an overcategory whose stages are affine over
  the base and whose limit projections are quasi-compact and scheme-theoretically dominant.
* `AlgebraicGeometry.exists_flat_model_of_noetherian_limit`: the statement for an inverse system
  of Noetherian schemes with affine transitions whose limit projections are
  scheme-theoretically dominant.

## Route

Stacks 01ZM part (1) and Stacks 04AI both carry `CategoryTheory.EssentiallySmall.{u}` on the
index, so they apply only to the first of the three. The second removes that hypothesis with
`AlgebraicGeometry.exists_small_limit_of_affine_of_dominant`, which replaces the index preorder by
a `u`-small directed preorder with the *same* limit: the hypotheses it needs — affine over a fixed
base, quasi-compact and scheme-theoretically dominant projections — are exactly what the system of
scheme-theoretic images of a good diagram has, which is why the chain is set up in an
overcategory. The third reduces to the second by restricting to the stages above an arbitrary
index, where the limit becomes affine over that stage by
`AlgebraicGeometry.EventualLimit.isAffineHom_π_app`; `AlgebraicGeometry.tailToOver` is initial, so
restricting keeps the cone limiting.

Stacks 04AI is a statement about a *morphism* over a stage becoming flat, so flatness of a single
`Z ⟶ D i` is obtained by applying it to the morphism from `Z` to the terminal object `𝟙 (D i)` of
the overcategory, and reading the two sides back with
`AlgebraicGeometry.flat_overPullback_terminal_iff`.

## Universe situation

`exists_flat_model_of_small_limit` has its index category at the scheme universe `u`, because
Stacks 01ZM is only available there. The other two have an index preorder at an arbitrary
universe `v`, with nothing relating `v` to `u` and no smallness instance; the `u`-small index
produced inside the proof is internal to it.

## Transparency gotchas

The objects of `CategoryTheory.Over.pullback b` are pullbacks wrapped in the overcategory, so
`((Over.pullback b).map t).left` and `((Over.pullback b).obj Z).hom` are two morphisms that differ
by a projection of a pullback along an identity. `flat_overPullback_terminal_iff` cancels that
projection as an isomorphism rather than unfolding the wrapper.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM), part (1).
* [Stacks Project, Tag 04AI](https://stacks.math.columbia.edu/tag/04AI).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

/-- **A flat model over a stage, small index.** A flat morphism of finite presentation into the
limit of a `u`-small cofiltered system of Noetherian schemes with affine transitions is the base
change of a flat morphism of finite presentation over some stage. -/
public lemma exists_flat_model_of_small_limit {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) [∀ i, IsNoetherian (D.obj i)]
    [∀ {i j : J} (a : i ⟶ j), IsAffineHom (D.map a)]
    {X : Scheme.{u}} (f : X ⟶ c.pt) [Flat f] (hfp : FinitePresentation f) :
    ∃ (i : J) (Z : Over (D.obj i)), FinitePresentation Z.hom ∧ Flat Z.hom ∧
      Nonempty (Over.mk f ≅ (Over.pullback (c.π.app i)).obj Z) := by
  obtain ⟨i, Z, hZ, ⟨e⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation D c hc (Over.mk f) hfp
  have ⟨_, _, _⟩ := hZ
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  let t : Z ⟶ Over.mk (𝟙 (D.obj i)) := Over.homMk Z.hom
  have hri : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have ht : Flat ((Over.pullback (c.π.app i)).map t).left := by
    apply (flat_overPullback_terminal_iff _ Z).mpr
    have : IsIso e.hom.left := (Over.forget c.pt).map_isIso e.hom
    rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := (@Flat : MorphismProperty Scheme.{u})) e.hom.left, e.hom.w]
    exact inferInstanceAs (Flat f)
  have : LocallyOfFinitePresentation t.left := hZ.1
  have : CompactSpace (Over.mk (𝟙 (D.obj i))).left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  obtain ⟨j, a, ha⟩ :=
    exists_flat_baseChange_of_limitBaseChange D c i Z (Over.mk (𝟙 (D.obj i))) t hc
  have hZ' : FinitePresentation ((Over.pullback (D.map a)).obj Z).hom := by
    change FinitePresentation (pullback.snd Z.hom (D.map a))
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  refine ⟨j, (Over.pullback (D.map a)).obj Z, hZ',
    (flat_overPullback_terminal_iff _ Z).mp ha, ⟨?_⟩⟩
  exact e ≪≫ (eqToIso (by rw [c.w a]) :
      (Over.pullback (c.π.app i)).obj Z ≅ (Over.pullback (c.π.app j ≫ D.map a)).obj Z) ≪≫
    (Over.pullbackComp (c.π.app j) (D.map a)).app Z

attribute [local instance] IsCofiltered.isConnected in
/-- **A flat model over a stage, free index universe, system in an overcategory.** The same
conclusion as `AlgebraicGeometry.exists_flat_model_of_small_limit` for an index preorder at an
arbitrary universe, provided the stages are affine over a fixed base and the limit projections
are quasi-compact and scheme-theoretically dominant: those hypotheses let
`AlgebraicGeometry.exists_small_limit_of_affine_of_dominant` replace the index by a `u`-small
directed preorder with the same limit. -/
public lemma exists_flat_model_of_affine_dominant_limit {I : Type v} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] {S : Scheme.{u}} (D : Iᵒᵖ ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsNoetherian (D.obj i).left] [∀ i, IsAffineHom (D.obj i).hom] [IsAffineHom c.pt.hom]
    [∀ i, QuasiCompact (c.π.app i).left] [∀ i, IsSchemeTheoreticallyDominant (c.π.app i).left]
    {X : Scheme.{u}} (f : X ⟶ c.pt.left) [Flat f] (hfp : FinitePresentation f) :
    ∃ (i : Iᵒᵖ) (Z : Over (D.obj i).left), FinitePresentation Z.hom ∧ Flat Z.hom ∧
      Nonempty (Over.mk f ≅ (Over.pullback (c.π.app i).left).obj Z) := by
  classical
  obtain ⟨J, _, _, _, e, _, _, ⟨he⟩⟩ :=
    exists_small_limit_of_affine_of_dominant (α := PUnit.{u + 1})
      (fun _ => Classical.arbitrary I) D c hc
  let E := e.monotone.functor.op
  let A := (E ⋙ D) ⋙ Over.forget S
  let c' := (Over.forget S).mapCone (c.whisker E)
  have (j : Jᵒᵖ) : IsNoetherian (A.obj j) :=
    inferInstanceAs (IsNoetherian (D.obj (E.obj j)).left)
  have {j k : Jᵒᵖ} (a : j ⟶ k) : IsAffineHom (A.map a) := by
    change IsAffineHom (D.map (E.map a)).left
    have : IsAffineHom ((D.map (E.map a)).left ≫ (D.obj (E.obj k)).hom) := by
      rw [(D.map (E.map a)).w]
      infer_instance
    exact IsAffineHom.of_comp _ (D.obj (E.obj k)).hom
  let f' : X ⟶ c'.pt := f
  have : Flat f' := inferInstanceAs (Flat f)
  have hfp' : FinitePresentation f' := hfp
  obtain ⟨j, Z, hZ, hflat, hIso⟩ :=
    exists_flat_model_of_small_limit A c' (isLimitOfPreserves (Over.forget S) he) f' hfp'
  exact ⟨E.obj j, Z, hZ, hflat, hIso⟩

attribute [local instance] IsCofiltered.isConnected in
/-- **A flat model over a stage, free index universe.** A flat morphism of finite presentation
into the limit of an inverse system of Noetherian schemes with affine transition morphisms, whose
limit projections are scheme-theoretically dominant, is the base change of a flat morphism of
finite presentation over some stage. No smallness hypothesis on the index.

The dominance hypothesis is what replaces smallness; it holds for the system of scheme-theoretic
images attached to a good diagram by
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.isSchemeTheoreticallyDominant_π`. -/
public lemma exists_flat_model_of_noetherian_limit {I : Type v} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsNoetherian (D.obj i)] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i, IsSchemeTheoreticallyDominant (c.π.app i)]
    {X : Scheme.{u}} (f : X ⟶ c.pt) [Flat f] (hfp : FinitePresentation f) :
    ∃ (i : Iᵒᵖ) (Z : Over (D.obj i)), FinitePresentation Z.hom ∧ Flat Z.hom ∧
      Nonempty (Over.mk f ≅ (Over.pullback (c.π.app i)).obj Z) := by
  classical
  let i : I := Classical.arbitrary I
  have : Nonempty (Set.Ici i) := ⟨⟨i, le_rfl⟩⟩
  have := directed_tail (I := I) i
  have := initial_tailToOver (I := I) i
  let E := tailToOver i
  let A := E ⋙ Over.post D
  let c' := ((Over.conePost D (op i)).obj c).whisker E
  have hc' : IsLimit c' :=
    (Functor.Initial.isLimitWhiskerEquiv E _).symm (Over.isLimitConePost (op i) hc)
  have (j : (Set.Ici i)ᵒᵖ) : IsNoetherian (A.obj j).left :=
    inferInstanceAs (IsNoetherian (D.obj (E.obj j).left))
  have (j : (Set.Ici i)ᵒᵖ) : IsAffineHom (A.obj j).hom :=
    inferInstanceAs (IsAffineHom (D.map (E.obj j).hom))
  have : IsAffineHom c'.pt.hom := EventualLimit.isAffineHom_π_app D c hc (op i)
  have (j : (Set.Ici i)ᵒᵖ) : QuasiCompact (c'.π.app j).left := by
    change QuasiCompact (c.π.app (E.obj j).left)
    have := EventualLimit.isAffineHom_π_app D c hc (E.obj j).left
    infer_instance
  have (j : (Set.Ici i)ᵒᵖ) : IsSchemeTheoreticallyDominant (c'.π.app j).left :=
    inferInstanceAs (IsSchemeTheoreticallyDominant (c.π.app (E.obj j).left))
  let f' : X ⟶ c'.pt.left := f
  have : Flat f' := inferInstanceAs (Flat f)
  have hfp' : FinitePresentation f' := hfp
  obtain ⟨j, Z, hZ, hflat, hIso⟩ :=
    exists_flat_model_of_affine_dominant_limit A c' hc' f' hfp'
  exact ⟨(E.obj j).left, Z, hZ, hflat, hIso⟩

end AlgebraicGeometry
