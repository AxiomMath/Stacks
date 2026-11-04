module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Pushout.FiniteType
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FromThickeningPushouts

/-!
# Finite type of the fourth corner of a square of condition (RS*)

Let `S` be a locally Noetherian scheme and let `A → B ← B'` be maps of `S`-algebras with
`B' → B` surjective, and `A' = A ×_B B'`. If `A` and `B'` are of finite type over `S` and `B`
is finite over `A`, then `A'` is of finite type over `S`. This is observation (3) of the
section of the source introducing condition (RS*) ([Stacks Project, Tag 0CXN]).

## Main results

* `Deformation.Artin.locallyOfFiniteType_and_quasiCompact_of_isPullback_appTop` — the
  observation, for a square of four affine schemes whose global sections form the fibre
  product, in the presentation used by `Deformation.Artin.SatisfiesRSStar`.

## Implementation notes

The square is presented as in `Deformation.Artin.SatisfiesRSStar`: affine schemes `U = Spec B`,
`V = Spec A`, `W = Spec B'` and `Z = Spec A'` with morphisms `f : U ⟶ V`, `g : U ⟶ W`,
`i : V ⟶ Z`, `j : W ⟶ Z` whose square of global sections is cartesian and with `g` surjective
on global sections. The `S`-algebra structure of `A'` is a morphism `t : Z ⟶ S`; those of `A`,
`B'` and `B` are its composites. This loses nothing: by
`Deformation.Artin.isPushout_of_isPullback_appTop` (observation (1)), a compatible pair of
structure morphisms on `V` and `W` comes from exactly one such `t`.

The source's hypothesis that `B` is of finite type over `S` is not used: it follows from the
other two, since `U ⟶ W` is a closed immersion. Quasi-compactness of the structure morphisms of
`A` and `B'` is not asked for either; it is automatic, since an affine scheme is quasi-compact
and a locally Noetherian scheme is quasi-separated.

The source's footnote argues on affine opens of `S` with [Stacks Project, Tag 00IT] and
[Stacks Project, Tag 01Z8]. Here the localization step is already packaged: `g` is a closed
immersion and `f` a finite, hence integral, morphism, so the square is a square of the pushout
situation of [Stacks Project, Tag 0ECI], all of whose fibres lie in the affine scheme `W`. Its
pushout is locally of finite type over `S` by [Stacks Project, Tag 0E27]
(`AlgebraicGeometry.pushoutToBase_locallyOfFiniteType`, itself proved from Tag 00IT), and `Z` is
that pushout by observation (1).

## References

* [Stacks Project, Tag 0CXN](https://stacks.math.columbia.edu/tag/0CXN)
* [Stacks Project, Tag 0E27](https://stacks.math.columbia.edu/tag/0E27)
* [Stacks Project, Tag 00IT](https://stacks.math.columbia.edu/tag/00IT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Artin

/-- **Observation (3) of the section on condition (RS\*).** Let `S` be locally Noetherian, and
let `U = Spec B`, `V = Spec A`, `W = Spec B'`, `Z = Spec A'` be affine schemes with morphisms
`f : U ⟶ V`, `g : U ⟶ W`, `i : V ⟶ Z`, `j : W ⟶ Z` whose square of global sections exhibits
`A' = A ×_B B'`, with `B' → B` surjective, and let `t : Z ⟶ S` give the `S`-algebra structures.
If `A` and `B'` are of finite type over `S` and `B` is finite over `A`, then `A'` is of finite
type over `S`. -/
@[stacks 0CXN "observation (3): if S is locally Noetherian, A, B, B' are of finite type over S \
and B is finite over A, then A' = A ×_B B' is of finite type over S"]
public theorem locallyOfFiniteType_and_quasiCompact_of_isPullback_appTop
    {S U V W Z : Scheme.{u}} [IsLocallyNoetherian S]
    [IsAffine U] [IsAffine V] [IsAffine W] [IsAffine Z]
    (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (t : Z ⟶ S)
    (hsq : IsPullback i.appTop j.appTop f.appTop g.appTop)
    (hsurj : Function.Surjective g.appTop.hom) (hfin : f.appTop.hom.Finite)
    [LocallyOfFiniteType (i ≫ t)] [LocallyOfFiniteType (j ≫ t)] :
    LocallyOfFiniteType t ∧ QuasiCompact t := by
  refine ⟨?_, inferInstance⟩
  have : IsClosedImmersion g := IsClosedImmersion.of_surjective_of_isAffine g hsurj
  have : IsFinite f := by
    have : IsFinite (Spec.map f.appTop) := (IsFinite.SpecMap_iff _).mpr hfin
    rw [show f = U.isoSpec.hom ≫ Spec.map f.appTop ≫ V.isoSpec.inv by
      rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]]
    infer_instance
  have hpo : IsPushout f g i j := isPushout_of_isPullback_appTop f g i j hsq hsurj
  let s : PushoutAlongClosedImmersionAndIntegralSituation.{u} :=
    { S := S, X := W, Y := V, Z := U
      pX := j ≫ t, pY := i ≫ t, pZ := g ≫ j ≫ t
      i := g, j := f
      i_over := rfl
      j_over := by rw [← Category.assoc, hpo.w, Category.assoc]
      fiber_preimage_subset_affine := fun _ => ⟨⊤, isAffineOpen_top W, fun _ _ => trivial⟩ }
  have : LocallyOfFiniteType s.pX := inferInstanceAs (LocallyOfFiniteType (j ≫ t))
  have : LocallyOfFiniteType s.pY := inferInstanceAs (LocallyOfFiniteType (i ≫ t))
  have : LocallyOfFiniteType s.pZ := inferInstanceAs (LocallyOfFiniteType (g ≫ j ≫ t))
  have : IsLocallyNoetherian s.S := inferInstanceAs (IsLocallyNoetherian S)
  let e : pushoutScheme s ≅ Z :=
    (pushoutAlongClosedImmersionAndIntegral s).isPushout.isoIsPushout _ _ hpo.flip
  have ht : t = e.inv ≫ pushoutToBase s := by
    refine hpo.flip.hom_ext ?_ ?_
    · rw [← Category.assoc, IsPushout.inl_isoIsPushout_inv]
      exact ((pushoutAlongClosedImmersionAndIntegral s).isPushout.inl_desc _ _ _).symm
    · rw [← Category.assoc, IsPushout.inr_isoIsPushout_inv]
      exact ((pushoutAlongClosedImmersionAndIntegral s).isPushout.inr_desc _ _ _).symm
  rw [ht]
  infer_instance

end Deformation.Artin
