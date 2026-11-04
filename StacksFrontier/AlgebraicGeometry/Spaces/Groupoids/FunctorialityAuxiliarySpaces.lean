module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct

/-!
# The auxiliary spaces of a morphism of groupoids in algebraic spaces

Let `φ : G ⟶ G'` be a morphism of groupoids in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, in the sense of Stacks 043W part (2), written `f : U ⟶ U'` on
objects and `f : R ⟶ R'` on arrows. Section 78.21 of the Stacks project attaches to `φ` two
further algebraic spaces,

```
U'' = U ×_{f, U', t'} R',      R'' = R ×_{f ∘ s, U', t'} R',
```

and makes them into a groupoid in algebraic spaces whose quotient stack is the 2-fibre product of
`[f] : [U/R] ⟶ [U'/R']` with the projection `S_{U'} ⟶ [U'/R']`. This file builds the two spaces,
their projections, the source map `s''` of that groupoid, and identifies `R''` with fibre products
of `R` over `U`.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.objectsMap` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.arrowsMap`: the maps on objects and on arrows of
  a morphism of groupoids in algebraic spaces, as morphisms of algebraic spaces rather than of the
  underlying presheaves.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxObjects` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxArrows`: the spaces `U''` and `R''`, with their
  projections and the cartesian squares defining them.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxSource`: the map `s'' : R'' ⟶ U''`, which on
  points sends `(r, r')` to `(s(r), r')`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.toAuxObjects`: the map `(t, f) : R ⟶ U''`.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isPullback_auxSource`: `R'' = R ×_{s, U} U''`, the
  square formed by `s''`, the first projection of `R''`, the source map of `G` and the first
  projection of `U''` is cartesian. This holds for every `φ`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isIso_toAuxObjects` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.arrowsIsoAuxObjects`: when the square formed by the
  two **target** maps and `φ` is cartesian, `(t, f) : R ⟶ U''` is an isomorphism.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isPullback_auxSource_of_isPullback_target`: under
  that same hypothesis, `R'' = R ×_{s, U, t} R`.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 04Y4](https://stacks.math.columbia.edu/tag/04Y4)
* [Stacks Project, Tag 04ZN](https://stacks.math.columbia.edu/tag/04ZN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B}

/-- The map on objects of a morphism of groupoids in algebraic spaces, as a morphism of algebraic
spaces. -/
def Hom.objectsMap (φ : Hom G G') : G.objects ⟶ G'.objects :=
  ObjectProperty.homMk φ.toGroupoidHom.mapObjects

/-- The map on arrows of a morphism of groupoids in algebraic spaces, as a morphism of algebraic
spaces. -/
def Hom.arrowsMap (φ : Hom G G') : G.arrows ⟶ G'.arrows :=
  ObjectProperty.homMk φ.toGroupoidHom.mapArrows

/-- A morphism of groupoids in algebraic spaces commutes with the source maps. -/
theorem Hom.arrowsMap_comp_source (φ : Hom G G') :
    φ.arrowsMap ≫ G'.source = G.source ≫ φ.objectsMap := by
  ext T a
  exact φ.toGroupoidHom.map_source T a

/-- A morphism of groupoids in algebraic spaces commutes with the target maps. -/
theorem Hom.arrowsMap_comp_target (φ : Hom G G') :
    φ.arrowsMap ≫ G'.target = G.target ≫ φ.objectsMap := by
  ext T a
  exact φ.toGroupoidHom.map_target T a

section AuxObjects

/-- The space `U'' = U ×_{f, U', t'} R'`. -/
noncomputable def auxObjects (φ : Hom G G') : AlgebraicSpaces C S hS :=
  AlgebraicSpaces.fiberProduct C S hS φ.objectsMap G'.target

/-- The projection `U'' ⟶ U`. -/
noncomputable def auxObjectsFst (φ : Hom G G') : auxObjects φ ⟶ G.objects :=
  ObjectProperty.homMk (pullback.fst φ.objectsMap.hom G'.target.hom)

/-- The projection `U'' ⟶ R'`. -/
noncomputable def auxObjectsSnd (φ : Hom G G') : auxObjects φ ⟶ G'.arrows :=
  ObjectProperty.homMk (pullback.snd φ.objectsMap.hom G'.target.hom)

/-- `U''` is the fibre product of `f : U ⟶ U'` and `t' : R' ⟶ U'`. -/
theorem isPullback_auxObjects (φ : Hom G G') :
    IsPullback (auxObjectsFst φ) (auxObjectsSnd φ) φ.objectsMap G'.target :=
  AlgebraicSpaces.isPullback_fiberProduct C S hS φ.objectsMap G'.target

/-- The space `R'' = R ×_{f ∘ s, U', t'} R'`. -/
noncomputable def auxArrows (φ : Hom G G') : AlgebraicSpaces C S hS :=
  AlgebraicSpaces.fiberProduct C S hS (G.source ≫ φ.objectsMap) G'.target

/-- The projection `R'' ⟶ R`. -/
noncomputable def auxArrowsFst (φ : Hom G G') : auxArrows φ ⟶ G.arrows :=
  ObjectProperty.homMk (pullback.fst (G.source ≫ φ.objectsMap).hom G'.target.hom)

/-- The projection `R'' ⟶ R'`. -/
noncomputable def auxArrowsSnd (φ : Hom G G') : auxArrows φ ⟶ G'.arrows :=
  ObjectProperty.homMk (pullback.snd (G.source ≫ φ.objectsMap).hom G'.target.hom)

/-- `R''` is the fibre product of `f ∘ s : R ⟶ U'` and `t' : R' ⟶ U'`. -/
theorem isPullback_auxArrows (φ : Hom G G') :
    IsPullback (auxArrowsFst φ) (auxArrowsSnd φ) (G.source ≫ φ.objectsMap) G'.target :=
  AlgebraicSpaces.isPullback_fiberProduct C S hS (G.source ≫ φ.objectsMap) G'.target

/-- The source map `s'' : R'' ⟶ U''`. On points it sends a pair
`(r, r')` with `t'(r') = f(s(r))` to the pair `(s(r), r')`. -/
noncomputable def auxSource (φ : Hom G G') : auxArrows φ ⟶ auxObjects φ :=
  (isPullback_auxObjects φ).lift (auxArrowsFst φ ≫ G.source) (auxArrowsSnd φ)
    (by rw [Category.assoc]; exact (isPullback_auxArrows φ).w)

/-- `s''` followed by the projection `U'' ⟶ U` is `s` after the projection `R'' ⟶ R`. -/
@[simp]
theorem auxSource_comp_auxObjectsFst (φ : Hom G G') :
    auxSource φ ≫ auxObjectsFst φ = auxArrowsFst φ ≫ G.source :=
  (isPullback_auxObjects φ).lift_fst _ _ _

/-- `s''` followed by the projection `U'' ⟶ R'` is the projection `R'' ⟶ R'`. -/
@[simp]
theorem auxSource_comp_auxObjectsSnd (φ : Hom G G') :
    auxSource φ ≫ auxObjectsSnd φ = auxArrowsSnd φ :=
  (isPullback_auxObjects φ).lift_snd _ _ _

/-- `R'' = R ×_{s, U} U''`: the square formed by the source map `s''`, the projection `R'' ⟶ R`,
the source map of `G` and the projection `U'' ⟶ U` is cartesian. -/
theorem isPullback_auxSource (φ : Hom G G') :
    IsPullback (auxArrowsFst φ) (auxSource φ) G.source (auxObjectsFst φ) :=
  IsPullback.of_bot
    (by rw [auxSource_comp_auxObjectsSnd]; exact isPullback_auxArrows φ)
    (auxSource_comp_auxObjectsFst φ).symm (isPullback_auxObjects φ)

end AuxObjects

section Cartesian

/-- The map `(t, f) : R ⟶ U''`, which on points sends an arrow `r` of `G` to the pair
`(t(r), f(r))`. -/
noncomputable def toAuxObjects (φ : Hom G G') : G.arrows ⟶ auxObjects φ :=
  (isPullback_auxObjects φ).lift G.target φ.arrowsMap (φ.arrowsMap_comp_target).symm

/-- `(t, f)` followed by the projection `U'' ⟶ U` is `t`. -/
@[simp]
theorem toAuxObjects_comp_auxObjectsFst (φ : Hom G G') :
    toAuxObjects φ ≫ auxObjectsFst φ = G.target :=
  (isPullback_auxObjects φ).lift_fst _ _ _

/-- `(t, f)` followed by the projection `U'' ⟶ R'` is `f`. -/
@[simp]
theorem toAuxObjects_comp_auxObjectsSnd (φ : Hom G G') :
    toAuxObjects φ ≫ auxObjectsSnd φ = φ.arrowsMap :=
  (isPullback_auxObjects φ).lift_snd _ _ _

/-- The isomorphism `R ≅ U''`, when the square formed by the two target maps and `φ` is
cartesian. -/
noncomputable def arrowsIsoAuxObjects (φ : Hom G G')
    (h : IsPullback G.target φ.arrowsMap φ.objectsMap G'.target) : G.arrows ≅ auxObjects φ :=
  h.isoIsPullback _ _ (isPullback_auxObjects φ)

/-- The isomorphism `arrowsIsoAuxObjects φ h` is `(t, f) : R ⟶ U''`. -/
@[simp]
theorem arrowsIsoAuxObjects_hom (φ : Hom G G')
    (h : IsPullback G.target φ.arrowsMap φ.objectsMap G'.target) :
    (arrowsIsoAuxObjects φ h).hom = toAuxObjects φ := by
  refine (isPullback_auxObjects φ).hom_ext ?_ ?_ <;> simp [arrowsIsoAuxObjects]

/-- `(t, f) : R ⟶ U''` is an isomorphism when the square formed by the two target maps and `φ` is
cartesian. -/
theorem isIso_toAuxObjects (φ : Hom G G')
    (h : IsPullback G.target φ.arrowsMap φ.objectsMap G'.target) : IsIso (toAuxObjects φ) := by
  rw [← arrowsIsoAuxObjects_hom φ h]
  infer_instance

/-- The first projection `U'' ⟶ U` read through the isomorphism `(t, f) : R ⟶ U''` is the target
map of `G`. -/
theorem auxObjectsFst_eq (φ : Hom G G')
    (h : IsPullback G.target φ.arrowsMap φ.objectsMap G'.target) :
    (arrowsIsoAuxObjects φ h).inv ≫ G.target = auxObjectsFst φ := by
  rw [Iso.inv_comp_eq, arrowsIsoAuxObjects_hom, toAuxObjects_comp_auxObjectsFst]

/-- `R'' = R ×_{s, U, t} R`: when the square formed by the two target maps and `φ` is cartesian,
the square formed by the two projections of `R''`, read through the isomorphism
`(t, f) : R ⟶ U''`, the source map and the target map is cartesian. -/
theorem isPullback_auxSource_of_isPullback_target (φ : Hom G G')
    (h : IsPullback G.target φ.arrowsMap φ.objectsMap G'.target) :
    IsPullback (auxArrowsFst φ) (auxSource φ ≫ (arrowsIsoAuxObjects φ h).inv) G.source G.target :=
  (isPullback_auxSource φ).of_iso (Iso.refl _) (Iso.refl _) (arrowsIsoAuxObjects φ h).symm
    (Iso.refl _) (by simp) (by simp) (by simp)
    (by simpa using (auxObjectsFst_eq φ h).symm)

end Cartesian

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
