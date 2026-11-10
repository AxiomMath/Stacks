module

public import StacksFrontier.CategoryTheory.Adjunction.TripleGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMate
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineLegs

/-!
# Modules on a space over a thickening-and-affine pushout, and triples of modules

Let `i : X ⟶ X'` be a thickening and `f : X ⟶ Y` an affine morphism of algebraic spaces over
`S`, let `Y' = Y ⨿_X X'` be their pushout (Stacks 07VX) and let `g : V' ⟶ Y'` be a morphism of
algebraic spaces.  Write `V = Y ×_{Y'} V'`, `U' = X' ×_{Y'} V'` and `U = X ×_{Y'} V'`.
Stacks 08KV compares modules on `V'` with *triples* `(𝒢, ℱ', φ)` of a module `𝒢` on `V`, a module
`ℱ'` on `U'` and an isomorphism `φ` of their pullbacks to `U`.

This file sets up that comparison: the spaces and morphisms of the situation, their affineness,
and — for an arbitrary commuting square `U ⟶ V ⟶ V'`, `U ⟶ U' ⟶ V'` of algebraic spaces — the
category of triples (`CategoryTheory.TripleGluing.Triple` for the two pullbacks to `U`), the
comparison functor `𝒢' ↦ ((V ⟶ V')^*𝒢', (U' ⟶ V')^*𝒢', can)`, where `can` is the composite of the
comparisons of Stacks 03LU for the two factorizations of `U ⟶ V'`, and its right adjoint, the
gluing functor `(V ⟶ V')_*𝒢 ×_{(U ⟶ V')_*ℱ} (U' ⟶ V')_*ℱ'` (`CategoryTheory.TripleGluing`).  The
comparison of the two direct images to `V'` which enters the gluing functor is identified with
the composite of the comparisons of Stacks 03LU for direct images
(`AlgebraicGeometry.Space.PushoutModules.compTransport_eq_rightComparison`), which is what makes
it computable on sections.  The functors of the tag are the instances at the square of the
situation; stating everything for a square keeps the pullbacks of the situation out of the
computations.

## Main definitions

* `AlgebraicGeometry.Space.PushoutModules.targetRestriction`,
  `AlgebraicGeometry.Space.PushoutModules.ambientRestriction`,
  `AlgebraicGeometry.Space.PushoutModules.commonRestriction`: the three projections
  `V ⟶ V'`, `U' ⟶ V'` and `U ⟶ V'`.
* `AlgebraicGeometry.Space.PushoutModules.commonToTarget` and
  `AlgebraicGeometry.Space.PushoutModules.commonToAmbient`: the morphisms `U ⟶ V` and `U ⟶ U'`.
* `AlgebraicGeometry.Space.PushoutModules.squareOverlap` and
  `AlgebraicGeometry.Space.PushoutModules.squareGluingFunctor`: the overlap comparison and the
  gluing functor over a commuting square; the adjunction between restriction and gluing is
  `CategoryTheory.TripleGluing.adjunction` at these data.
* `AlgebraicGeometry.Space.PushoutModules.GluingTriple`: the category of triples.
* `AlgebraicGeometry.Space.PushoutModules.restrictionFunctor`: the comparison functor of the tag.
* `AlgebraicGeometry.Space.PushoutModules.gluingFunctor`: its right adjoint.

## References

* [Stacks Project, Tag 08KV](https://stacks.math.columbia.edu/tag/08KV)
* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.PushoutModules

section Transport

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {U U' V' : AlgebraicSpaces B S hS} (a : U ⟶ U') (u' : U' ⟶ V') (k : U ⟶ V')

/-- The comparison of the direct image along `U ⟶ U' ⟶ V'` with the direct image along a morphism
`k` equal to the composite: the comparison of Stacks 03LU followed by the transport along the
equality. -/
noncomputable def compTransport (h : a ≫ u' = k) :
    modulePushforward B S hS a ⋙ modulePushforward B S hS u' ⟶ modulePushforward B S hS k :=
  (modulePushforwardCompIso B S hS a u').hom ≫
    eqToHom (congrArg (fun k => modulePushforward B S hS k) h)

end Transport

/-! ### Gluing along a commuting square of spaces -/

section Square

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {U V U' V' : AlgebraicSpaces B S hS} (t : U ⟶ V) (v : V ⟶ V') (a : U ⟶ U') (u' : U' ⟶ V')

/-- Triples over a square: a module on `V`, a module on `U'` and an isomorphism of their
pullbacks to `U`. -/
abbrev SquareTriple :=
  TripleGluing.Triple (modulePullback B S hS t) (modulePullback B S hS a)

variable (h : a ≫ u' = t ≫ v)

/-- The canonical comparison of the two pullbacks to `U` along the two sides of a commuting
square: the comparisons of Stacks 03LU for the two factorizations of `U ⟶ V'`. -/
noncomputable def squareOverlap :
    modulePullback B S hS v ⋙ modulePullback B S hS t ≅
      modulePullback B S hS u' ⋙ modulePullback B S hS a :=
  modulePullbackCompIso B S hS t v ≪≫
    eqToIso (congrArg (fun k => modulePullback B S hS k) h).symm ≪≫
    (modulePullbackCompIso B S hS a u').symm

/-- The restriction of a module on `V'` to a triple over the square. -/
noncomputable abbrev squareRestrictionFunctor :=
  TripleGluing.restrictFunctor (squareOverlap t v a u' h)

/-- **The comparison of the two direct images to `V'` is the conjugate of the overlap
comparison**, read through the comparison of Stacks 03LU along `U ⟶ V ⟶ V'`. -/
theorem compTransport_eq_rightComparison :
    compTransport a u' (t ≫ v) h =
      (TripleGluing.rightComparison (modulePullbackAdjunction B S hS v)
        (modulePullbackAdjunction B S hS u') (modulePullbackAdjunction B S hS t)
        (modulePullbackAdjunction B S hS a) (squareOverlap t v a u' h)).hom ≫
      (modulePushforwardCompIso B S hS t v).hom := by
  simp only [TripleGluing.rightComparison, conjugateIsoEquiv_apply_hom, squareOverlap,
    Iso.trans_hom, Iso.symm_hom, eqToIso.hom, compTransport]
  rw [← conjugateEquiv_comp _ (modulePullbackAdjunction B S hS (t ≫ v)) _,
    ← conjugateEquiv_comp _ (modulePullbackAdjunction B S hS (a ≫ u')) _,
    conjugateEquiv_modulePullbackCompIso_inv, conjugateEquiv_eqToHom_modulePullback,
    conjugateEquiv_modulePullbackCompIso_hom, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  exact h

/-- The gluing functor over a square: a triple `(𝒢, ℱ', φ)` goes to the fibre product of
`v_*𝒢` and `u'_*ℱ'` over the direct image along `U ⟶ V ⟶ V'`. -/
noncomputable abbrev squareGluingFunctor :=
  TripleGluing.glueFunctor (qV := modulePushforward B S hS v)
    (qA := modulePushforward B S hS u')
    (modulePullbackAdjunction B S hS t) (modulePullbackAdjunction B S hS a)
    (modulePushforwardCompIso B S hS t v) (compTransport a u' (t ≫ v) h)

end Square

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y) [HasPushout i f]
    {V' : AlgebraicSpaces B S hS} (g : V' ⟶ pushout i f)

/-! ### The spaces and morphisms of the situation -/

/-- `V = Y ×_{Y'} V'`. -/
abbrev targetSpace : AlgebraicSpaces B S hS := pullback (pushout.inr i f) g

/-- `U' = X' ×_{Y'} V'`. -/
abbrev ambientSpace : AlgebraicSpaces B S hS := pullback (pushout.inl i f) g

/-- `U = X ×_{Y'} V'`. -/
abbrev commonSpace : AlgebraicSpaces B S hS := pullback (i ≫ pushout.inl i f) g

/-- The projection `V ⟶ V'`. -/
abbrev targetRestriction : targetSpace i f g ⟶ V' := pullback.snd _ _

/-- The projection `U' ⟶ V'`. -/
abbrev ambientRestriction : ambientSpace i f g ⟶ V' := pullback.snd _ _

/-- The projection `U ⟶ V'`. -/
abbrev commonRestriction : commonSpace i f g ⟶ V' := pullback.snd _ _

/-- The morphism `U ⟶ V` over `f : X ⟶ Y`. -/
noncomputable def commonToTarget : commonSpace i f g ⟶ targetSpace i f g :=
  pullback.lift (pullback.fst (i ≫ pushout.inl i f) g ≫ f) (pullback.snd _ _) (by
    rw [Category.assoc, ← pushout.condition]
    exact pullback.condition)

/-- The morphism `U ⟶ U'` over `i : X ⟶ X'`. -/
noncomputable def commonToAmbient : commonSpace i f g ⟶ ambientSpace i f g :=
  pullback.lift (pullback.fst (i ≫ pushout.inl i f) g ≫ i) (pullback.snd _ _) (by
    rw [Category.assoc]
    exact pullback.condition)

/-- The morphism `U ⟶ V` commutes with the projections of `U` and `V` to `V'`. -/
@[reassoc (attr := simp)]
theorem commonToTarget_restriction :
    commonToTarget i f g ≫ pullback.snd (pushout.inr i f) g =
      pullback.snd (i ≫ pushout.inl i f) g :=
  pullback.lift_snd _ _ _

/-- The morphism `U ⟶ U'` commutes with the projections of `U` and `U'` to `V'`. -/
@[reassoc (attr := simp)]
theorem commonToAmbient_restriction :
    commonToAmbient i f g ≫ pullback.snd (pushout.inl i f) g =
      pullback.snd (i ≫ pushout.inl i f) g :=
  pullback.lift_snd _ _ _

/-- The composite `U ⟶ V ⟶ Y` is the projection `U ⟶ X` followed by `f`. -/
@[reassoc (attr := simp)]
theorem commonToTarget_fst :
    commonToTarget i f g ≫ pullback.fst _ _ = pullback.fst (i ≫ pushout.inl i f) g ≫ f :=
  pullback.lift_fst _ _ _

/-- The composite `U ⟶ U' ⟶ X'` is the projection `U ⟶ X` followed by `i`. -/
@[reassoc (attr := simp)]
theorem commonToAmbient_fst :
    commonToAmbient i f g ≫ pullback.fst _ _ = pullback.fst (i ≫ pushout.inl i f) g ≫ i :=
  pullback.lift_fst _ _ _

/-- The two factorizations of `U ⟶ V'` agree. -/
theorem commonToAmbient_comp_eq :
    commonToAmbient i f g ≫ ambientRestriction i f g =
      commonToTarget i f g ≫ targetRestriction i f g := by
  simp

/-- `U = X ×_Y V`: the square `U ⟶ V` over `f` is cartesian. -/
theorem isPullback_commonToTarget :
    IsPullback (pullback.fst (i ≫ pushout.inl i f) g) (commonToTarget i f g) f
      (pullback.fst (pushout.inr i f) g) := by
  refine IsPullback.of_bot ?_ (commonToTarget_fst i f g).symm
    (IsPullback.of_hasPullback (pushout.inr i f) g)
  rw [commonToTarget_restriction, ← pushout.condition]
  exact IsPullback.of_hasPullback (i ≫ pushout.inl i f) g

/-- `U = X ×_{X'} U'`: the square `U ⟶ U'` over `i` is cartesian. -/
theorem isPullback_commonToAmbient :
    IsPullback (pullback.fst (i ≫ pushout.inl i f) g) (commonToAmbient i f g) i
      (pullback.fst (pushout.inl i f) g) := by
  refine IsPullback.of_bot ?_ (commonToAmbient_fst i f g).symm
    (IsPullback.of_hasPullback (pushout.inl i f) g)
  rw [commonToAmbient_restriction]
  exact IsPullback.of_hasPullback (i ≫ pushout.inl i f) g

/-! ### Affineness -/

/-- Affineness passes to the projection of a cartesian square of algebraic spaces. -/
private theorem isAffineHom_snd_of_isPullback {P A C D : AlgebraicSpaces B S hS}
    {fst : P ⟶ A} {snd : P ⟶ D} {f : A ⟶ C} {g : D ⟶ C} (sq : IsPullback fst snd f g)
    (hf : IsAffineHom B S hS f.hom) : IsAffineHom B S hS snd.hom :=
  IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom B S hS sq) hf

section Affine

variable (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
include hi hf

/-- If `i` is a thickening and `f` is affine, then the projection `V ⟶ V'` is affine. -/
theorem isAffineHom_targetRestriction : IsAffineHom B S hS (targetRestriction i f g).hom :=
  isAffineHom_snd_of_isPullback (IsPullback.of_hasPullback (pushout.inr i f) g)
    (isAffineHom_pushout_inr i f hi hf)

/-- If `i` is a thickening and `f` is affine, then the projection `U' ⟶ V'` is affine. -/
theorem isAffineHom_ambientRestriction : IsAffineHom B S hS (ambientRestriction i f g).hom :=
  isAffineHom_snd_of_isPullback (IsPullback.of_hasPullback (pushout.inl i f) g)
    (isAffineHom_pushout_inl i f hi hf)

/-- If `i` is a thickening and `f` is affine, then the projection `U ⟶ V'` is affine. -/
theorem isAffineHom_commonRestriction : IsAffineHom B S hS (commonRestriction i f g).hom := by
  rw [commonRestriction, ← commonToAmbient_restriction]
  exact isAffineHom_comp B S hS _ _
    (isAffineHom_snd_of_isPullback (isPullback_commonToAmbient i f g)
      (isAffineHom_of_isThickeningHom B S hS i hi))
    (isAffineHom_ambientRestriction i f g hi hf)

omit hi in
/-- If `f` is affine, then the morphism `U ⟶ V` over `f` is affine. -/
theorem isAffineHom_commonToTarget : IsAffineHom B S hS (commonToTarget i f g).hom :=
  isAffineHom_snd_of_isPullback (isPullback_commonToTarget i f g) hf

omit hf in
/-- If `i` is a thickening, then the morphism `U ⟶ U'` is affine. -/
theorem isAffineHom_commonToAmbient : IsAffineHom B S hS (commonToAmbient i f g).hom :=
  isAffineHom_snd_of_isPullback (isPullback_commonToAmbient i f g)
    (isAffineHom_of_isThickeningHom B S hS i hi)

end Affine

/-! ### Triples, the comparison functor and the gluing functor -/

/-- **The category of triples of Stacks 08KV**: a module `𝒢` on `V`, a module `ℱ'` on `U'` and an
isomorphism `(U ⟶ V)^*𝒢 ≅ (U ⟶ U')^*ℱ'`. -/
abbrev GluingTriple :=
  SquareTriple (commonToTarget i f g) (commonToAmbient i f g)

/-- The canonical comparison `(U ⟶ V)^*(V ⟶ V')^* ≅ (U ⟶ U')^*(U' ⟶ V')^*` of the two pullbacks
to `U`: the comparisons of Stacks 03LU for the two factorizations of `U ⟶ V'`. -/
noncomputable abbrev overlapComparison :
    modulePullback B S hS (targetRestriction i f g) ⋙ modulePullback B S hS (commonToTarget i f g)
      ≅ modulePullback B S hS (ambientRestriction i f g) ⋙
        modulePullback B S hS (commonToAmbient i f g) :=
  squareOverlap (commonToTarget i f g) (targetRestriction i f g) (commonToAmbient i f g)
    (ambientRestriction i f g) (commonToAmbient_comp_eq i f g)

/-- **The comparison functor of Stacks 08KV**: `𝒢' ↦ ((V ⟶ V')^*𝒢', (U' ⟶ V')^*𝒢', can)`. -/
noncomputable abbrev restrictionFunctor : Modules.{u, u} B S hS V'.1 V'.2 ⥤ GluingTriple i f g :=
  squareRestrictionFunctor (commonToTarget i f g) (targetRestriction i f g)
    (commonToAmbient i f g) (ambientRestriction i f g) (commonToAmbient_comp_eq i f g)

/-- **The gluing functor**: a triple `(𝒢, ℱ', φ)` goes to the fibre product
`(V ⟶ V')_*𝒢 ×_{(U ⟶ V')_*ℱ} (U' ⟶ V')_*ℱ'`, the common target being the direct image along
`U ⟶ V ⟶ V'`. -/
noncomputable abbrev gluingFunctor : GluingTriple i f g ⥤ Modules.{u, u} B S hS V'.1 V'.2 :=
  squareGluingFunctor (commonToTarget i f g) (targetRestriction i f g)
    (commonToAmbient i f g) (ambientRestriction i f g) (commonToAmbient_comp_eq i f g)

end AlgebraicGeometry.Space.PushoutModules

end
