module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# The equalizer attached to a descent datum for small étale sheaves

Let `f : X ⟶ Y` be a morphism of a big étale site, let `p` and `q` be the two projections of
`X₁ = X ×_Y X` and let `f₁ = p ≫ f`. A descent datum for `{X ⟶ Y}` consists of a sheaf `F` on
the small étale site of `X` together with an isomorphism `φ : p^{-1}F ≅ q^{-1}F` satisfying the
cocycle condition. The source attaches to it the sheaf on the small étale site of `Y`
$$
G = \operatorname{Equalizer}(f_*F \rightrightarrows f_{1,*}p^{-1}F)
$$
whose two arrows are built from the units of the two adjunctions `p^{-1} ⊣ p_*` and
`q^{-1} ⊣ q_*`, the second one corrected by `φ`. This file constructs `G`, the two arrows, the
inclusion of `G` into `f_*F` and the resulting comparison `f^{-1}G ⟶ F`, together with the
canonical descent datum carried by the inverse image of a sheaf on `Y`.

The cocycle condition is not needed for any of this, so it is not assumed: it is needed only to
prove that the construction is a quasi-inverse of the descent functor, which is not done here.

## Main definitions

* `AlgebraicGeometry.smallEtaleCanonicalDescentIso` — the canonical descent datum of an inverse
  image, that is the comparison `p^{-1}f^{-1}G ≅ q^{-1}f^{-1}G`.
* `AlgebraicGeometry.smallEtaleDescentArrowFst` and
  `AlgebraicGeometry.smallEtaleDescentArrowSnd` — the two arrows `f_*F ⟶ f_{1,*}p^{-1}F`.
* `AlgebraicGeometry.smallEtaleDescentSheaf` — their equalizer `G`, with its inclusion
  `AlgebraicGeometry.smallEtaleDescentSheafι` into `f_*F`.
* `AlgebraicGeometry.smallEtaleDescentComparison` — the comparison `f^{-1}G ⟶ F` obtained from
  that inclusion by adjunction.

## Main results

* `AlgebraicGeometry.smallEtaleDescentSheafι_arrow` — the inclusion equalizes the two arrows.
* `AlgebraicGeometry.smallEtaleDescentComparison_adjoint` — the comparison is the adjoint of the
  inclusion, which is what identifies it.

## Implementation notes

Direct and inverse images along base change, and their adjunction, are those of
`AlgebraicGeometry.BigEtaleSite.smallPushforward`,
`AlgebraicGeometry.BigEtaleSite.smallInverseImage` and
`AlgebraicGeometry.BigEtaleSite.smallPullbackAdjunction`; the identifications
`f_*p_* ≅ f_{1,*}` and `p^{-1}f^{-1} ≅ f_1^{-1}` are the composition comparisons
`AlgebraicGeometry.smallEtaleMorphism_comp_pushforwardIso` and
`AlgebraicGeometry.smallEtaleMorphism_comp_inverseImageIso`. Since the fibre products are
chosen, `q ≫ f` and `p ≫ f` are equal but not definitionally so, and the second arrow and the
canonical descent datum carry the corresponding transport along
`CategoryTheory.Limits.pullback.condition`.

## References

* [Stacks Project, Tag 0GEZ](https://stacks.math.columbia.edu/tag/0GEZ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- The unit of the adjunction along a composite `g ≫ f` is the composite of the units along `f`
and along `g`, read through the two composition comparisons. This is the mate compatibility of
`AlgebraicGeometry.smallEtaleMorphism_comp_inverseImageIso` with
`AlgebraicGeometry.smallEtaleMorphism_comp_pushforwardIso`, and it is what lets a section over
`Y` be recognised after base change to a fibre product. -/
public theorem smallPullbackAdjunction_unit_app_comp {W : B.Scheme} (g : W ⟶ X)
    (G : Sheaf (SmallEtale.topology B Y.1 Y.property) (Type (u + 1))) :
    (BigEtaleSite.smallPullbackAdjunction B f (Type (u + 1))).unit.app G ≫
        (BigEtaleSite.smallPushforward B f (Type (u + 1))).map
          ((BigEtaleSite.smallPullbackAdjunction B g (Type (u + 1))).unit.app
            ((BigEtaleSite.smallInverseImage B f (Type (u + 1))).obj G)) ≫
        (BigEtaleSite.smallPushforward B f (Type (u + 1))).map
          ((BigEtaleSite.smallPushforward B g (Type (u + 1))).map
            ((smallEtaleMorphism_comp_inverseImageIso B W X Y g f).hom.app G)) ≫
        (smallEtaleMorphism_comp_pushforwardIso B W X Y g f).hom.app
          ((BigEtaleSite.smallInverseImage B (g ≫ f) (Type (u + 1))).obj G) =
      (BigEtaleSite.smallPullbackAdjunction B (g ≫ f) (Type (u + 1))).unit.app G := by
  have bridge :
      (conjugateEquiv (BigEtaleSite.smallPullbackAdjunction B (g ≫ f) (Type (u + 1)))
          ((BigEtaleSite.smallPullbackAdjunction B f (Type (u + 1))).comp
            (BigEtaleSite.smallPullbackAdjunction B g (Type (u + 1))))).symm
        (smallEtaleMorphism_comp_pushforwardIso B W X Y g f).inv =
      (smallEtaleMorphism_comp_inverseImageIso B W X Y g f).hom := rfl
  have key := unit_conjugateEquiv_symm
    (BigEtaleSite.smallPullbackAdjunction B (g ≫ f) (Type (u + 1)))
    ((BigEtaleSite.smallPullbackAdjunction B f (Type (u + 1))).comp
      (BigEtaleSite.smallPullbackAdjunction B g (Type (u + 1))))
    (smallEtaleMorphism_comp_pushforwardIso B W X Y g f).inv G
  rw [bridge] at key
  simp only [Adjunction.comp_unit_app, Functor.comp_obj, Functor.comp_map] at key
  simp only [← Category.assoc] at key ⊢
  rw [← key]
  simp

/-- The canonical descent datum of an inverse image: for a sheaf `G` on the small étale site of
`Y`, the two inverse images of `f^{-1}G` along the projections of `X ×_Y X` are canonically
isomorphic, both being an inverse image along the common composite with `f`. -/
public def smallEtaleCanonicalDescentIso
    (G : Sheaf (SmallEtale.topology B Y.1 Y.property) (Type (u + 1))) :
    (BigEtaleSite.smallInverseImage B (pullback.fst f f) (Type (u + 1))).obj
        ((BigEtaleSite.smallInverseImage B f (Type (u + 1))).obj G) ≅
      (BigEtaleSite.smallInverseImage B (pullback.snd f f) (Type (u + 1))).obj
        ((BigEtaleSite.smallInverseImage B f (Type (u + 1))).obj G) :=
  (smallEtaleMorphism_comp_inverseImageIso B (pullback f f) X Y
      (pullback.fst f f) f).app G ≪≫
    eqToIso (congrArg (fun h : pullback f f ⟶ Y =>
      (BigEtaleSite.smallInverseImage B h (Type (u + 1))).obj G) pullback.condition) ≪≫
    ((smallEtaleMorphism_comp_inverseImageIso B (pullback f f) X Y
      (pullback.snd f f) f).app G).symm

variable (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1)))

/-- The first of the two arrows `f_*F ⟶ f_{1,*}p^{-1}F` of the equalizer presentation: the unit
of `p^{-1} ⊣ p_*`, pushed forward along `f` and read through `f_*p_* ≅ f_{1,*}`. -/
public def smallEtaleDescentArrowFst :
    (BigEtaleSite.smallPushforward B f (Type (u + 1))).obj F ⟶
      (BigEtaleSite.smallPushforward B (pullback.fst f f ≫ f) (Type (u + 1))).obj
        ((BigEtaleSite.smallInverseImage B (pullback.fst f f) (Type (u + 1))).obj F) :=
  (BigEtaleSite.smallPushforward B f (Type (u + 1))).map
      ((BigEtaleSite.smallPullbackAdjunction B (pullback.fst f f) (Type (u + 1))).unit.app F) ≫
    (smallEtaleMorphism_comp_pushforwardIso B (pullback f f) X Y
      (pullback.fst f f) f).hom.app
        ((BigEtaleSite.smallInverseImage B (pullback.fst f f) (Type (u + 1))).obj F)

variable (φ : (BigEtaleSite.smallInverseImage B (pullback.fst f f) (Type (u + 1))).obj F ≅
  (BigEtaleSite.smallInverseImage B (pullback.snd f f) (Type (u + 1))).obj F)

/-- The second of the two arrows `f_*F ⟶ f_{1,*}p^{-1}F` of the equalizer presentation: the unit
of `q^{-1} ⊣ q_*` corrected by `φ`, pushed forward along `f`, read through `f_*q_* ≅ (q ≫ f)_*`
and transported along `q ≫ f = p ≫ f`. -/
public def smallEtaleDescentArrowSnd :
    (BigEtaleSite.smallPushforward B f (Type (u + 1))).obj F ⟶
      (BigEtaleSite.smallPushforward B (pullback.fst f f ≫ f) (Type (u + 1))).obj
        ((BigEtaleSite.smallInverseImage B (pullback.fst f f) (Type (u + 1))).obj F) :=
  (BigEtaleSite.smallPushforward B f (Type (u + 1))).map
      ((BigEtaleSite.smallPullbackAdjunction B (pullback.snd f f) (Type (u + 1))).unit.app F ≫
        (BigEtaleSite.smallPushforward B (pullback.snd f f) (Type (u + 1))).map φ.inv) ≫
    (smallEtaleMorphism_comp_pushforwardIso B (pullback f f) X Y
        (pullback.snd f f) f).hom.app
          ((BigEtaleSite.smallInverseImage B (pullback.fst f f) (Type (u + 1))).obj F) ≫
      eqToHom (congrArg (fun h : pullback f f ⟶ Y =>
        (BigEtaleSite.smallPushforward B h (Type (u + 1))).obj
          ((BigEtaleSite.smallInverseImage B (pullback.fst f f) (Type (u + 1))).obj F))
        pullback.condition.symm)

/-- The sheaf on the small étale site of `Y` attached to a descent datum `(F, φ)`: the equalizer
of the two arrows `f_*F ⟶ f_{1,*}p^{-1}F`. -/
public def smallEtaleDescentSheaf :
    Sheaf (SmallEtale.topology B Y.1 Y.property) (Type (u + 1)) :=
  equalizer (smallEtaleDescentArrowFst B f F) (smallEtaleDescentArrowSnd B f F φ)

/-- The inclusion of the sheaf attached to a descent datum into the direct image of the datum. -/
public def smallEtaleDescentSheafι :
    smallEtaleDescentSheaf B f F φ ⟶ (BigEtaleSite.smallPushforward B f (Type (u + 1))).obj F :=
  equalizer.ι _ _

/-- The inclusion equalizes the two arrows of the equalizer presentation. -/
public theorem smallEtaleDescentSheafι_arrow :
    smallEtaleDescentSheafι B f F φ ≫ smallEtaleDescentArrowFst B f F =
      smallEtaleDescentSheafι B f F φ ≫ smallEtaleDescentArrowSnd B f F φ :=
  equalizer.condition _ _

/-- The inclusion of the sheaf attached to a descent datum is a monomorphism. -/
public instance mono_smallEtaleDescentSheafι : Mono (smallEtaleDescentSheafι B f F φ) :=
  equalizer.ι_mono

/-- The comparison `f^{-1}G ⟶ F` attached to a descent datum, adjoint to the inclusion of the
sheaf it produces into the direct image of the datum. -/
public def smallEtaleDescentComparison :
    (BigEtaleSite.smallInverseImage B f (Type (u + 1))).obj (smallEtaleDescentSheaf B f F φ) ⟶
      F :=
  ((BigEtaleSite.smallPullbackAdjunction B f (Type (u + 1))).homEquiv _ _).symm
    (smallEtaleDescentSheafι B f F φ)

/-- The comparison attached to a descent datum is the adjoint of the inclusion, which pins it
down. -/
public theorem smallEtaleDescentComparison_adjoint :
    (BigEtaleSite.smallPullbackAdjunction B f (Type (u + 1))).homEquiv _ _
        (smallEtaleDescentComparison B f F φ) =
      smallEtaleDescentSheafι B f F φ :=
  Equiv.apply_symm_apply _ _

end AlgebraicGeometry

end
