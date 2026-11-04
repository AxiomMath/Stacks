module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Base change of a cofiltered limit of schemes to a fixed stage

Let `D : I ⥤ Scheme` be a cofiltered diagram with limit cone `c`, let `i : I` be a stage and let
`X` be a scheme over `D i`.  The schemes `X ×_{D i} D j`, for `j` an object of `I` over `i`, form
a diagram indexed by `Over i`, and this file identifies its limit with `X ×_{D i} c.pt`.

This is the geometric input which turns a statement about a cofiltered limit of schemes into a
statement about the diagram of base changes of a *fixed* scheme over a stage, which is the shape
in which the descent lemmas of Stacks chapter 32 are stated.  No smallness hypothesis on the
index is needed; the limit cone of `D` is given, so nothing has to be constructed.

The pullbacks are written in the order `pullback X.hom (D.map _)`, which is the order in which
`CategoryTheory.Over.pullback` produces them.

## Main definitions

* `AlgebraicGeometry.LimitDescent.bcMap`: the transition morphism `X ×_{D i} D j ⟶ X ×_{D i} D k`.
* `AlgebraicGeometry.LimitDescent.bcDiagram`: the diagram `j ↦ X ×_{D i} D j` of schemes, indexed
  by the objects of `I` over `i`.
* `AlgebraicGeometry.LimitDescent.bcπ` and `AlgebraicGeometry.LimitDescent.bcCone`: the cone on it
  with vertex `X ×_{D i} c.pt`.
* `AlgebraicGeometry.LimitDescent.bcToBase`: the natural family of morphisms to `D i`.

## Main results

* `AlgebraicGeometry.LimitDescent.isLimitBcCone`: `bcCone` is a limit cone.
* `AlgebraicGeometry.LimitDescent.isAffineHom_bcMap`,
  `AlgebraicGeometry.LimitDescent.compactSpace_bcDiagram_obj` and
  `AlgebraicGeometry.LimitDescent.quasiSeparatedSpace_bcDiagram_obj`: the diagram of base changes
  again has affine transition morphisms, and its stages are again quasi-compact and
  quasi-separated as soon as `X` is.

## Implementation notes

The diagram is built by hand out of `CategoryTheory.Limits.pullback.lift` rather than as
`Over.pullback X.hom` applied to the diagram of stages.  With the functorial definition the
objects of the diagram are no longer syntactically pullbacks, which makes every subsequent
statement about them awkward to even write down.  For the same reason the diagram and the two
cones are `@[reducible]`: `rw` and `simp` assemble congruences at reducible transparency only,
and without that they fail to relate `(bcDiagram D i X).obj j` with the pullback it is.

The limit property is proved from the fact that `Over.forget i` is initial for cofiltered `I`,
which identifies cones on the stages over `i` with cones on `D` itself.  The component of a cone
towards `X` is read off at the terminal object `Over.mk (𝟙 i)` of `Over i`.

## References

* [Stacks Project, Tag 01YX](https://stacks.math.columbia.edu/tag/01YX)
-/

@[expose] public section

universe v uI u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.LimitDescent

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

variable {I : Type uI} [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I)
  (X : Over (D.obj i))

/-! ### The diagram of base changes -/

/-- The transition morphism `X ×_{D i} D j ⟶ X ×_{D i} D k` of the diagram of base changes of
`X` along the stages of `D` over `i`. -/
noncomputable def bcMap {j k : Over i} (g : j ⟶ k) :
    pullback X.hom (D.map j.hom) ⟶ pullback X.hom (D.map k.hom) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ D.map g.left)
    (by rw [Category.assoc, ← D.map_comp, Over.w g]; exact pullback.condition)

/-- The transition morphism `bcMap D i X g` commutes with the projections to `X`. -/
@[reassoc (attr := simp)]
lemma bcMap_fst {j k : Over i} (g : j ⟶ k) :
    bcMap D i X g ≫ pullback.fst X.hom (D.map k.hom) = pullback.fst X.hom (D.map j.hom) :=
  pullback.lift_fst _ _ _

/-- The transition morphism `bcMap D i X g` followed by the projection to `D k` is the projection
to `D j` followed by `D.map g.left`. -/
@[reassoc (attr := simp)]
lemma bcMap_snd {j k : Over i} (g : j ⟶ k) :
    bcMap D i X g ≫ pullback.snd X.hom (D.map k.hom) =
      pullback.snd X.hom (D.map j.hom) ≫ D.map g.left :=
  pullback.lift_snd _ _ _

/-- The diagram of base changes `j ↦ X ×_{D i} D j`, indexed by the objects of `I` over `i`. -/
@[reducible]
noncomputable def bcDiagram : Over i ⥤ Scheme.{u} where
  obj j := pullback X.hom (D.map j.hom)
  map g := bcMap D i X g
  map_id j := pullback.hom_ext (by simp) (by simp)
  map_comp f g := pullback.hom_ext (by simp) (by simp)

/-- The object of `bcDiagram D i X` at `j` is the pullback `X ×_{D i} D j`. -/
lemma bcDiagram_obj (j : Over i) :
    (bcDiagram D i X).obj j = pullback X.hom (D.map j.hom) := rfl

/-- The morphism of `bcDiagram D i X` at `g` is `bcMap D i X g`. -/
lemma bcDiagram_map {j k : Over i} (g : j ⟶ k) :
    (bcDiagram D i X).map g = bcMap D i X g := rfl

/-! ### The limit cone -/

/-- The projection `X ×_{D i} c.pt ⟶ X ×_{D i} D j`. -/
noncomputable def bcπ (j : Over i) :
    pullback X.hom (c.π.app i) ⟶ pullback X.hom (D.map j.hom) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ c.π.app j.left)
    (by rw [Category.assoc, c.w j.hom]; exact pullback.condition)

/-- The projection `bcπ D c i X j` commutes with the projections to `X`. -/
@[reassoc (attr := simp)]
lemma bcπ_fst (j : Over i) :
    bcπ D c i X j ≫ pullback.fst X.hom (D.map j.hom) = pullback.fst X.hom (c.π.app i) :=
  pullback.lift_fst _ _ _

/-- The projection `bcπ D c i X j` followed by the projection to `D j` is the projection to
`c.pt` followed by `c.π.app j.left`. -/
@[reassoc (attr := simp)]
lemma bcπ_snd (j : Over i) :
    bcπ D c i X j ≫ pullback.snd X.hom (D.map j.hom) =
      pullback.snd X.hom (c.π.app i) ≫ c.π.app j.left :=
  pullback.lift_snd _ _ _

/-- The projections `bcπ D c i X j` are compatible with the transition morphisms `bcMap D i X g`.
-/
@[reassoc (attr := simp)]
lemma bcπ_bcMap {j k : Over i} (g : j ⟶ k) :
    bcπ D c i X j ≫ bcMap D i X g = bcπ D c i X k :=
  pullback.hom_ext (by simp) (by simp [c.w g.left])

/-- The projections `bcπ D c i X` form a natural transformation from the constant functor at
`X ×_{D i} c.pt` to `bcDiagram D i X`. -/
lemma bcπ_naturality {j k : Over i} (g : j ⟶ k) :
    𝟙 (pullback X.hom (c.π.app i)) ≫ bcπ D c i X k = bcπ D c i X j ≫ bcMap D i X g := by
  rw [Category.id_comp, bcπ_bcMap]

/-- The cone on `AlgebraicGeometry.LimitDescent.bcDiagram` with vertex `X ×_{D i} c.pt`. -/
@[reducible]
noncomputable def bcCone : Cone (bcDiagram D i X) where
  pt := pullback X.hom (c.π.app i)
  π := { app := bcπ D c i X, naturality := fun _ _ g ↦ bcπ_naturality D c i X g }

/-- The vertex of `bcCone D c i X` is `X ×_{D i} c.pt`. -/
lemma bcCone_pt : (bcCone D c i X).pt = pullback X.hom (c.π.app i) := rfl

/-- The component of `bcCone D c i X` at `j` is `bcπ D c i X j`. -/
lemma bcCone_π_app (j : Over i) : (bcCone D c i X).π.app j = bcπ D c i X j := rfl

/-- The components of a cone on `bcDiagram D i X`, followed by the projections to the stages
`D j`, are natural in `j`. -/
lemma bcToStages_naturality (s : Cone (bcDiagram D i X)) {j k : Over i} (g : j ⟶ k) :
    𝟙 s.pt ≫ (s.π.app k ≫ pullback.snd X.hom (D.map k.hom)) =
      (s.π.app j ≫ pullback.snd X.hom (D.map j.hom)) ≫ D.map ((Over.forget i).map g) := by
  rw [Category.id_comp, ← s.w g, Category.assoc, bcMap_snd, Category.assoc]
  rfl

/-- The cone on `Over.forget i ⋙ D` obtained from a cone on
`AlgebraicGeometry.LimitDescent.bcDiagram` by projecting to the stages. -/
@[reducible]
noncomputable def bcToStages (s : Cone (bcDiagram D i X)) : Cone (Over.forget i ⋙ D) where
  pt := s.pt
  π :=
  { app j := s.π.app j ≫ pullback.snd X.hom (D.map j.hom)
    naturality := fun _ _ g ↦ bcToStages_naturality D i X s g }

/-- The component of a cone on the diagram of base changes towards `X` does not depend on the
stage: `Over i` has the terminal object `Over.mk (𝟙 i)`, at which it may be computed. -/
lemma bcπ_app_fst_const (s : Cone (bcDiagram D i X)) (j : Over i) :
    s.π.app j ≫ pullback.fst X.hom (D.map j.hom) =
      s.π.app (Over.mk (𝟙 i)) ≫ pullback.fst X.hom (D.map (Over.mk (𝟙 i) : Over i).hom) := by
  rw [← s.w (Over.mkIdTerminal.from j), Category.assoc, bcMap_fst]

section IsLimit

variable [IsCofiltered I] (hc : IsLimit c)

/-- A limit cone on `D` restricts to a limit cone on the stages over `i`, because `Over.forget i`
is initial for cofiltered `I`. -/
noncomputable def isLimitWhiskerForget : IsLimit (c.whisker (Over.forget i)) :=
  (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc

include hc in
/-- The morphism to `c.pt` induced by `bcToStages D i X s`, followed by `c.π.app j.left`, is the
component of `s` at `j` followed by the projection to `D j`. -/
lemma bcLift_fac (s : Cone (bcDiagram D i X)) (j : Over i) :
    (isLimitWhiskerForget D c i hc).lift (bcToStages D i X s) ≫ c.π.app j.left =
      s.π.app j ≫ pullback.snd X.hom (D.map j.hom) :=
  (isLimitWhiskerForget D c i hc).fac (bcToStages D i X s) j

include hc in
/-- The component of `s` at `j` towards `X` and the morphism to `c.pt` induced by
`bcToStages D i X s` agree over `D i`. -/
lemma bcLift_condition (s : Cone (bcDiagram D i X)) (j : Over i) :
    (s.π.app j ≫ pullback.fst X.hom (D.map j.hom)) ≫ X.hom =
      (isLimitWhiskerForget D c i hc).lift (bcToStages D i X s) ≫ c.π.app i := by
  rw [← c.w j.hom, ← Category.assoc, bcLift_fac D c i X hc s j]
  simp only [Category.assoc, pullback.condition]

include hc in
/-- `AlgebraicGeometry.LimitDescent.bcCone` is a limit cone. -/
noncomputable def isLimitBcCone : IsLimit (bcCone D c i X) where
  lift s := pullback.lift
    (s.π.app (Over.mk (𝟙 i)) ≫ pullback.fst X.hom (D.map (Over.mk (𝟙 i) : Over i).hom))
    ((isLimitWhiskerForget D c i hc).lift (bcToStages D i X s))
    (bcLift_condition D c i X hc s (Over.mk (𝟙 i)))
  fac s j := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, bcCone_π_app, bcπ_fst, pullback.lift_fst]
      exact (bcπ_app_fst_const D i X s j).symm
    · rw [Category.assoc, bcCone_π_app, bcπ_snd, pullback.lift_snd_assoc,
        bcLift_fac D c i X hc s j]
  uniq s m hm := by
    refine pullback.hom_ext ?_ ?_
    · have hm' : m ≫ bcπ D c i X (Over.mk (𝟙 i)) = s.π.app (Over.mk (𝟙 i)) := hm _
      rw [pullback.lift_fst, ← bcπ_fst D c i X (Over.mk (𝟙 i)), ← Category.assoc, hm']
    · rw [pullback.lift_snd]
      refine (isLimitWhiskerForget D c i hc).hom_ext fun j ↦ ?_
      have hm' : m ≫ bcπ D c i X j = s.π.app j := hm j
      have h2 : (m ≫ pullback.snd X.hom (c.π.app i)) ≫ c.π.app j.left =
          (isLimitWhiskerForget D c i hc).lift (bcToStages D i X s) ≫ c.π.app j.left := by
        rw [bcLift_fac D c i X hc s j, Category.assoc, ← bcπ_snd D c i X j, ← Category.assoc,
          hm']
      exact h2

end IsLimit

/-! ### The transition morphisms and the stages of the base-changed diagram -/

/-- The square exhibiting a transition morphism of the diagram of base changes as the base change
of the corresponding transition morphism of `D`. -/
lemma isPullback_bcMap {j k : Over i} (g : j ⟶ k) :
    IsPullback (pullback.snd X.hom (D.map j.hom)) (bcMap D i X g)
      (D.map g.left) (pullback.snd X.hom (D.map k.hom)) := by
  refine IsPullback.of_bot ?_ (by rw [bcMap_snd])
    (IsPullback.of_hasPullback X.hom (D.map k.hom)).flip
  rw [bcMap_fst, ← D.map_comp, Over.w g]
  exact (IsPullback.of_hasPullback X.hom (D.map j.hom)).flip

/-- If the transition morphisms of `D` are affine, then so are those of the diagram of base
changes. -/
instance isAffineHom_bcMap [∀ {j k : I} (g : j ⟶ k), IsAffineHom (D.map g)]
    {j k : Over i} (g : j ⟶ k) : IsAffineHom (bcMap D i X g) :=
  MorphismProperty.of_isPullback (isPullback_bcMap D i X g) inferInstance

/-- If the transition morphisms of `D` are affine, then so are those of `bcDiagram D i X`. -/
instance isAffineHom_bcDiagram_map [∀ {j k : I} (g : j ⟶ k), IsAffineHom (D.map g)]
    {j k : Over i} (g : j ⟶ k) : IsAffineHom ((bcDiagram D i X).map g) :=
  isAffineHom_bcMap D i X g

/-- If the transition morphisms of `D` are affine and `X` is quasi-compact, then every stage of
`bcDiagram D i X` is quasi-compact. -/
instance compactSpace_bcDiagram_obj [∀ {j k : I} (g : j ⟶ k), IsAffineHom (D.map g)]
    [CompactSpace X.left] (j : Over i) : CompactSpace ((bcDiagram D i X).obj j) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.fst X.hom (D.map j.hom))

/-- If the transition morphisms of `D` are affine and `X` is quasi-separated, then every stage of
`bcDiagram D i X` is quasi-separated. -/
instance quasiSeparatedSpace_bcDiagram_obj [∀ {j k : I} (g : j ⟶ k), IsAffineHom (D.map g)]
    [QuasiSeparatedSpace X.left] (j : Over i) :
    QuasiSeparatedSpace ((bcDiagram D i X).obj j) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst X.hom (D.map j.hom))

/-- The natural family of morphisms from the base-changed diagram to the stage `D i`. -/
@[simps]
noncomputable def bcToBase : bcDiagram D i X ⟶ (Functor.const (Over i)).obj (D.obj i) where
  app j := pullback.fst X.hom (D.map j.hom) ≫ X.hom
  naturality j k g := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    rw [← Category.assoc, bcMap_fst]

end AlgebraicGeometry.LimitDescent
