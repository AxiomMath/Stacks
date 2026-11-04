module

public import StacksFrontier.AlgebraicGeometry.LimitApproxFinish.StageLimits
public import StacksFrontier.AlgebraicGeometry.LimitApproxFunctor.Glue

/-!
# The functor of glued stages

Let `Dw`, `Dx`, `Dy` be diagrams of schemes over one index category and let `α : Dw ⟶ Dx`,
`β : Dw ⟶ Dy` be natural transformations whose components are open immersions. Glueing
`Dx.obj j` to `Dy.obj j` along `Dw.obj j`, stage by stage, produces a diagram of schemes
`AlgebraicGeometry.gluePairFunctor` on the same index category, and the two legs of the glueing
become natural transformations into it, with open-immersion components.

If the opens of each diagram are cut out of each other by the transition morphisms, then each leg
is cut out of the glued stages by the transition morphisms, and the transition morphisms of the
glued stages are affine as soon as those of `Dx` and `Dy` are. If every stage of `Dx` and `Dy` is
quasi-compact, or locally of finite type, then so is every glued stage.

## Main definitions

* `AlgebraicGeometry.gluePairFunctor`: the diagram of schemes obtained by glueing `Dx.obj j` and
  `Dy.obj j` along `Dw.obj j` at every stage `j`.
* `AlgebraicGeometry.gluePairFunctorInl`, `AlgebraicGeometry.gluePairFunctorInr`: the two legs
  of the glueing, as natural transformations into `AlgebraicGeometry.gluePairFunctor`.

## Main results

* `AlgebraicGeometry.preimage_opensRange_of_isPullback`: in a cartesian square whose two vertical
  legs are open immersions, the upper open is the inverse image of the lower one.
* `AlgebraicGeometry.isPullback_gluePairFunctorInl_app`,
  `AlgebraicGeometry.isPullback_gluePairFunctorInr_app`: each leg is cut out of the glued stages
  by the transition morphisms.
* `AlgebraicGeometry.isAffineHom_gluePairFunctor_map`: the transition morphisms of the glued
  stages are affine.
* `AlgebraicGeometry.compactSpace_gluePairFunctor_obj`,
  `AlgebraicGeometry.locallyOfFiniteType_terminal_from_gluePairFunctor_obj`,
  `AlgebraicGeometry.quasiCompact_terminal_from_gluePairFunctor_obj`: each glued stage is
  quasi-compact, respectively locally of finite type, over the terminal scheme.

## Implementation notes

The index category is left free: its objects live in `w`, its morphisms in `v`, and the schemes
in `u`, with no relation imposed.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v w u

namespace AlgebraicGeometry

/-- The inverse of `AlgebraicGeometry.IsOpenImmersion.isPullback`: in a cartesian square whose
two vertical legs are open immersions, the upper open is the inverse image of the lower one. -/
lemma preimage_opensRange_of_isPullback {A B A' B' : Scheme.{u}} {iA : A' ⟶ A} {iB : B' ⟶ B}
    [IsOpenImmersion iA] [IsOpenImmersion iB] {m : A ⟶ B} {m' : A' ⟶ B'}
    (h : IsPullback iA m' m iB) : m ⁻¹ᵁ iB.opensRange = iA.opensRange := by
  have : HasPullback m iB := h.hasPullback
  calc m ⁻¹ᵁ iB.opensRange
      = (pullback.fst m iB).opensRange := (Scheme.Hom.opensRange_pullbackFst iB m).symm
    _ = (h.isoPullback.hom ≫ pullback.fst m iB).opensRange :=
        (Scheme.Hom.opensRange_comp_of_isIso _ _).symm
    _ = iA.opensRange := by simp only [h.isoPullback_hom_fst]

section Functor

variable {J : Type w} [Category.{v} J] {Dw Dx Dy : J ⥤ Scheme.{u}} (α : Dw ⟶ Dx) (β : Dw ⟶ Dy)
  [∀ j, IsOpenImmersion (α.app j)] [∀ j, IsOpenImmersion (β.app j)]

/-- **The functor of glued stages.** Two natural transformations out of one diagram of schemes
with open-immersion components glue, stage by stage, into a diagram of schemes. -/
@[simps obj]
noncomputable def gluePairFunctor : J ⥤ Scheme.{u} where
  obj j := Scheme.gluePair (α.app j) (β.app j)
  map {_ _} u := Scheme.gluePairMap (Dw.map u) (Dx.map u) (Dy.map u)
    (α.naturality u).symm (β.naturality u).symm
  map_id _ := Scheme.gluePair_hom_ext _ _ (by simp) (by simp)
  map_comp _ _ := Scheme.gluePair_hom_ext _ _ (by simp) (by simp)

/-- The value of `AlgebraicGeometry.gluePairFunctor` on a morphism `u` is the morphism of
glueings induced by the transition morphisms of the three diagrams along `u`. -/
@[simp]
lemma gluePairFunctor_map {j k : J} (u : j ⟶ k) :
    (gluePairFunctor α β).map u = Scheme.gluePairMap (Dw.map u) (Dx.map u) (Dy.map u)
      (α.naturality u).symm (β.naturality u).symm :=
  rfl

/-- The first leg of the glueing, as a natural transformation into the functor of glued
stages. -/
noncomputable def gluePairFunctorInl : Dx ⟶ gluePairFunctor α β where
  app j := Scheme.gluePairInl (α.app j) (β.app j)
  naturality {_ _} u := (Scheme.gluePairInl_gluePairMap (Dw.map u) (Dx.map u) (Dy.map u)
    (α.naturality u).symm (β.naturality u).symm).symm

/-- The component of `AlgebraicGeometry.gluePairFunctorInl` at `j` is the first leg of the
glueing at `j`. -/
@[simp]
lemma gluePairFunctorInl_app (j : J) :
    (gluePairFunctorInl α β).app j = Scheme.gluePairInl (α.app j) (β.app j) := rfl

/-- The second leg of the glueing, as a natural transformation into the functor of glued
stages. -/
noncomputable def gluePairFunctorInr : Dy ⟶ gluePairFunctor α β where
  app j := Scheme.gluePairInr (α.app j) (β.app j)
  naturality {_ _} u := (Scheme.gluePairInr_gluePairMap (Dw.map u) (Dx.map u) (Dy.map u)
    (α.naturality u).symm (β.naturality u).symm).symm

/-- The component of `AlgebraicGeometry.gluePairFunctorInr` at `j` is the second leg of the
glueing at `j`. -/
@[simp]
lemma gluePairFunctorInr_app (j : J) :
    (gluePairFunctorInr α β).app j = Scheme.gluePairInr (α.app j) (β.app j) := rfl

/-- Each component of `AlgebraicGeometry.gluePairFunctorInl` is an open immersion. -/
instance isOpenImmersion_gluePairFunctorInl_app (j : J) :
    IsOpenImmersion ((gluePairFunctorInl α β).app j) :=
  inferInstanceAs (IsOpenImmersion (Scheme.gluePairInl (α.app j) (β.app j)))

/-- Each component of `AlgebraicGeometry.gluePairFunctorInr` is an open immersion. -/
instance isOpenImmersion_gluePairFunctorInr_app (j : J) :
    IsOpenImmersion ((gluePairFunctorInr α β).app j) :=
  inferInstanceAs (IsOpenImmersion (Scheme.gluePairInr (α.app j) (β.app j)))

variable (hα : ∀ ⦃j k : J⦄ (u : j ⟶ k), Dx.map u ⁻¹ᵁ (α.app k).opensRange = (α.app j).opensRange)
  (hβ : ∀ ⦃j k : J⦄ (u : j ⟶ k), Dy.map u ⁻¹ᵁ (β.app k).opensRange = (β.app j).opensRange)

include hβ in
/-- **The first leg is cut out of the glued stages by the transition morphisms.** -/
lemma isPullback_gluePairFunctorInl_app ⦃j k : J⦄ (u : j ⟶ k) :
    IsPullback (Dx.map u) ((gluePairFunctorInl α β).app j)
      ((gluePairFunctorInl α β).app k) ((gluePairFunctor α β).map u) :=
  Scheme.isPullback_gluePairInl_gluePairMap (Dw.map u) (Dx.map u) (Dy.map u)
    (α.naturality u).symm (β.naturality u).symm (hβ u)

include hα in
/-- **The second leg is cut out of the glued stages by the transition morphisms.** -/
lemma isPullback_gluePairFunctorInr_app ⦃j k : J⦄ (u : j ⟶ k) :
    IsPullback (Dy.map u) ((gluePairFunctorInr α β).app j)
      ((gluePairFunctorInr α β).app k) ((gluePairFunctor α β).map u) :=
  Scheme.isPullback_gluePairInr_gluePairMap (Dw.map u) (Dx.map u) (Dy.map u)
    (α.naturality u).symm (β.naturality u).symm (hα u)

include hα hβ in
/-- **The transition morphisms of the glued stages are affine** as soon as those of the two
diagrams being glued are. -/
lemma isAffineHom_gluePairFunctor_map
    [∀ {j k : J} (u : j ⟶ k), IsAffineHom (Dx.map u)]
    [∀ {j k : J} (u : j ⟶ k), IsAffineHom (Dy.map u)] {j k : J} (u : j ⟶ k) :
    IsAffineHom ((gluePairFunctor α β).map u) :=
  Scheme.isAffineHom_gluePairMap (Dw.map u) (Dx.map u) (Dy.map u)
    (α.naturality u).symm (β.naturality u).symm (hα u) (hβ u)

/-- Each glued stage is quasi-compact. -/
lemma compactSpace_gluePairFunctor_obj [∀ j, CompactSpace (Dx.obj j)]
    [∀ j, CompactSpace (Dy.obj j)] (j : J) : CompactSpace ((gluePairFunctor α β).obj j) :=
  Scheme.compactSpace_gluePair _ _

/-- Each glued stage is locally of finite type over the terminal scheme. -/
lemma locallyOfFiniteType_terminal_from_gluePairFunctor_obj
    [∀ j, LocallyOfFiniteType (terminal.from (Dx.obj j))]
    [∀ j, LocallyOfFiniteType (terminal.from (Dy.obj j))] (j : J) :
    LocallyOfFiniteType (terminal.from ((gluePairFunctor α β).obj j)) :=
  Scheme.locallyOfFiniteType_terminal_from_gluePair _ _

/-- Each glued stage is quasi-compact over the terminal scheme. -/
lemma quasiCompact_terminal_from_gluePairFunctor_obj [∀ j, CompactSpace (Dx.obj j)]
    [∀ j, CompactSpace (Dy.obj j)] (j : J) :
    QuasiCompact (terminal.from ((gluePairFunctor α β).obj j)) :=
  Scheme.quasiCompact_terminal_from_gluePair _ _

end Functor

end AlgebraicGeometry
