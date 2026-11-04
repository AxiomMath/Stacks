module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsEtaleRestriction

/-!
# The strict transform of a module and étale restriction

Let `S` be a scheme, let `b : A' ⟶ A` be a morphism of algebraic spaces over `S`, let
`E ⊆ A'` be a subspace of its source and let `f : X ⟶ A` be an algebraic space over `A`.  The
strict transform of an `𝒪_X`-module `F` with respect to the pair `(b, E)`, Stacks 0862 in the
form `AlgebraicGeometry.Space.strictTransformSheaf`, lives on `X ×_A A'`.

Suppose given a second such situation `w : U ⟶ V`, `v' : V' ⟶ V`, `E' ⊆ V'` mapping to the
first by an étale `u : U ⟶ X` and a morphism `m : V' ⟶ A'`, and let
`can : U ×_V V' ⟶ X ×_A A'` be the induced morphism.  If `can` is étale and the points of `E'`
are the inverse image under `|m|` of the points of `E`, then the restriction of the strict
transform of `F` to `U ×_V V'` is the strict transform of `F|_U`.

This is the geometry-free core of part (3) of Stacks 0863, where `b` is the blowup of `A` in a
closed subspace `Z`, `E = b^{-1}Z` its exceptional divisor, `v'` the blowup of `V` in `Z ×_A V`
and `E'` its exceptional divisor; the hypotheses on `can` and on the points of `E'` are then
supplied by part (1) of that tag.  See
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupEtaleLocalization.lean`.

## Main definitions

* `AlgebraicGeometry.Space.strictTransformInnerModulePullbackIso` compares the two readings of
  the pullback of `F` to `U ×_V V'`, through `X ×_A A'` and through `U`.
* `AlgebraicGeometry.Space.strictTransformSheafEtaleRestrictionIso` is the comparison of the
  restriction of the strict transform with the strict transform of the restriction.

## Main results

* `AlgebraicGeometry.Space.exceptionalPreimageSet_eq_preimage_of_comp_eq`: the supported set of
  the second situation is the inverse image under `|can|` of the supported set of the first.

## Implementation notes

The strict transform of a module is the quotient of a pullback of `F` by its sections supported
on `|pr_{A'}^{-1}E|`, so the comparison is the composite of three steps.

The first is that the quotient by the supported sections commutes with pullback along an étale
morphism, `AlgebraicGeometry.Space.modulePullbackSupportedSectionsQuotientIso`, applied to
`can`.  It produces the quotient by the sections supported on `|can|⁻¹|pr_{A'}^{-1}E|`.

The second identifies that set with `|pr_{V'}^{-1}E'|`, which is
`AlgebraicGeometry.Space.exceptionalPreimageSet_eq_preimage_of_comp_eq`: both sets are inverse
images of the points of `E`, by
`AlgebraicGeometry.Space.exceptionalPreimageSet_eq_preimage`, along the
two sides of the commuting square `can ≫ pr_{A'} = pr_{V'} ≫ m`, and the hypothesis on the
points of `E'` matches the two.  This is the only place where a hypothesis on `E'` is used, and
it is a hypothesis on the *point sets* and not on the subspaces: the strict transform sees `E`
only through its points.

The third moves the ambient module from `can^*pr_X^*F` to `pr_U^*u^*F`, which is
`AlgebraicGeometry.Space.supportedSectionsQuotientMapIso` applied to
`AlgebraicGeometry.Space.strictTransformInnerModulePullbackIso`; the latter is the composition
comparison of Stacks 03LU, `AlgebraicGeometry.Space.modulePullbackCompIso`, at the two
factorizations of `can ≫ pr_X = pr_U ≫ u`.

Neither quasi-coherence of `F` nor quasi-coherence of the strict transform is involved, and
none is assumed; the construction of Stacks 0862 uses nothing of `F`, as the implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/StrictTransform.lean` record.

## References

* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A X A' U V V' : AlgebraicSpaces B S hS}

/-- **The supported set of the second situation is the inverse image of the supported set of the
first.**  If `can ≫ pr_{A'} = pr_{V'} ≫ m` and the points of `E'` are the inverse image under
`|m|` of the points of `E`, then `|pr_{V'}^{-1}E'| = |can|^{-1}|pr_{A'}^{-1}E|`.

Both sides are computed by `AlgebraicGeometry.Space.exceptionalPreimageSet_eq_preimage` as
inverse images of the points of `E` along the two equal composites. -/
theorem exceptionalPreimageSet_eq_preimage_of_comp_eq (f : X ⟶ A) (b : A' ⟶ A)
    (E : Subfunctor A'.1)
    (w : U ⟶ V) (v' : V' ⟶ V) (E' : Subfunctor V'.1) (m : V' ⟶ A')
    (can : strictTransformPullback B S hS w v' ⟶ strictTransformPullback B S hS f b)
    (hcanB : can ≫ strictTransformPullbackToBlowUp B S hS f b =
      strictTransformPullbackToBlowUp B S hS w v' ≫ m)
    (hE : Set.range (pointsMap B S hS E'.toFunctor E'.ι) =
      pointsMap B S hS V'.1 m.hom ⁻¹' Set.range (pointsMap B S hS E.toFunctor E.ι)) :
    exceptionalPreimageSet B S hS w v' E' =
      pointsMap B S hS (strictTransformPullback B S hS w v').1 can.hom ⁻¹'
        exceptionalPreimageSet B S hS f b E := by
  rw [exceptionalPreimageSet_eq_preimage, exceptionalPreimageSet_eq_preimage, hE,
    ← Set.preimage_comp, ← Set.preimage_comp,
    ← pointsMap_comp B S hS (strictTransformPullback B S hS w v').1 can.hom
      (strictTransformPullbackToBlowUp B S hS f b).hom,
    ← pointsMap_comp B S hS (strictTransformPullback B S hS w v').1
      (strictTransformPullbackToBlowUp B S hS w v').hom m.hom]
  exact congrArg (fun g => pointsMap B S hS (strictTransformPullback B S hS w v').1 g ⁻¹'
    Set.range (pointsMap B S hS E.toFunctor E.ι))
    (congrArg (fun g : strictTransformPullback B S hS w v' ⟶ A' => g.hom) hcanB).symm

/-- **The two readings of the pullback of `F` to `U ×_V V'` agree.**  Along
`can ≫ pr_X = pr_U ≫ u` the pullback of `pr_X^*F` by `can` is the pullback of `u^*F` by `pr_U`.

This is the composition comparison of Stacks 03LU,
`AlgebraicGeometry.Space.modulePullbackCompIso`, applied to both factorizations of the common
composite. -/
def strictTransformInnerModulePullbackIso (f : X ⟶ A) (b : A' ⟶ A) (u : U ⟶ X) (w : U ⟶ V)
    (v' : V' ⟶ V)
    (can : strictTransformPullback B S hS w v' ⟶ strictTransformPullback B S hS f b)
    (hcanS : can ≫ strictTransformPullbackToSource B S hS f b =
      strictTransformPullbackToSource B S hS w v' ≫ u)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS can).obj
        ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj F) ≅
      (modulePullback B S hS (strictTransformPullbackToSource B S hS w v')).obj
        ((modulePullback B S hS u).obj F) :=
  ((modulePullbackCompIso B S hS can
      (strictTransformPullbackToSource B S hS f b)).app F).trans
    ((eqToIso (congrArg (fun g : strictTransformPullback B S hS w v' ⟶ X =>
        (modulePullback B S hS g).obj F) hcanS)).trans
      ((modulePullbackCompIso B S hS
        (strictTransformPullbackToSource B S hS w v') u).app F).symm)

/-- **The restriction of the strict transform of a module is the strict transform of its
restriction.**  Let `(b, E)` and `(v', E')` be two morphisms with a subspace of the source, let
`f : X ⟶ A` and `w : U ⟶ V` be algebraic spaces over their targets and let `u : U ⟶ X` and
`m : V' ⟶ A'` be morphisms over them in the sense that the induced
`can : U ×_V V' ⟶ X ×_A A'` satisfies `can ≫ pr_X = pr_U ≫ u` and
`can ≫ pr_{A'} = pr_{V'} ≫ m`.  If `can` is étale and the points of `E'` are the inverse image
under `|m|` of the points of `E`, then pulling the strict transform of `F` back along `can`
gives the strict transform of `F|_U`.

See the module documentation for the three steps. -/
def strictTransformSheafEtaleRestrictionIso (f : X ⟶ A) (b : A' ⟶ A) (E : Subfunctor A'.1)
    (u : U ⟶ X) (w : U ⟶ V) (v' : V' ⟶ V) (E' : Subfunctor V'.1) (m : V' ⟶ A')
    (can : strictTransformPullback B S hS w v' ⟶ strictTransformPullback B S hS f b)
    (hcan : IsEtale B S hS can.hom)
    (hcanS : can ≫ strictTransformPullbackToSource B S hS f b =
      strictTransformPullbackToSource B S hS w v' ≫ u)
    (hcanB : can ≫ strictTransformPullbackToBlowUp B S hS f b =
      strictTransformPullbackToBlowUp B S hS w v' ≫ m)
    (hE : Set.range (pointsMap B S hS E'.toFunctor E'.ι) =
      pointsMap B S hS V'.1 m.hom ⁻¹' Set.range (pointsMap B S hS E.toFunctor E.ι))
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS can).obj (strictTransformSheaf B S hS f b E F) ≅
      strictTransformSheaf B S hS w v' E' ((modulePullback B S hS u).obj F) :=
  (modulePullbackSupportedSectionsQuotientIso B S hS can hcan
      (exceptionalPreimageSet B S hS f b E)
      ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj F)).trans
    ((eqToIso (congrArg (fun T₀ : Set (points B S hS (strictTransformPullback B S hS w v').1) =>
          cokernel (supportedSectionsSubmodule B S hS
            (strictTransformPullback B S hS w v').1
            (strictTransformPullback B S hS w v').2 T₀
            ((modulePullback B S hS can).obj
              ((modulePullback B S hS
                (strictTransformPullbackToSource B S hS f b)).obj F))).ι)
        (exceptionalPreimageSet_eq_preimage_of_comp_eq B S hS f b E w v' E' m can hcanB
          hE).symm)).trans
      (supportedSectionsQuotientMapIso B S hS (strictTransformPullback B S hS w v').1
        (strictTransformPullback B S hS w v').2 (exceptionalPreimageSet B S hS w v' E')
        (strictTransformInnerModulePullbackIso B S hS f b u w v' can hcanS F)))

end AlgebraicGeometry.Space

end
