module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ResidueFieldFactor
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.PointsResidueFieldIso

/-!
# Base changing an étale morphism of schemes over a base

Let `a : U ⟶ A` be an étale morphism of schemes, let `pA : A ⟶ B` and let `i : V ⟶ B`. Then the
morphism `U ×_B V ⟶ A ×_B V` induced by `a` is again étale: writing `U ×_B V` as
`U ×_A (A ×_B V)` exhibits it as the base change of `a` along `A ×_B V ⟶ A`.

## Main results

* `AlgebraicGeometry.etale_pullbackMapOver`: the induced morphism of fibre products is étale.
* `AlgebraicGeometry.isOpenImmersion_pullbackMapOver`: the induced morphism of fibre products is an
  open immersion when `a` is.
* `AlgebraicGeometry.pullbackMapOver_fst`, `AlgebraicGeometry.pullbackMapOver_snd`: its two
  characterizing identities.
* `AlgebraicGeometry.isIso_residueFieldMap_pullbackMapOver`: the induced morphism is trivial on
  residue fields wherever the original is.
* `AlgebraicGeometry.pullbackComparison`: the comparison morphism between the base changes of one
  morphism along a composite and along its second factor, with its two identities and its
  triviality on residue fields.

## Implementation notes

The structure morphism of the source is given as a separate morphism together with the triangle
`a ≫ pA = pU`, and the two statements with content are proved by substituting that equation, which
is what keeps the fibre product `U ×_B V` from having to be transported along it.
`CategoryTheory.Limits.pullbackRightPullbackFstIso` is the identification
`U ×_A (A ×_B V) ≅ U ×_B V`, and the induced map is read off from its two characterizing
identities. The morphism is built with `CategoryTheory.Limits.pullback.lift` rather than with
`CategoryTheory.Limits.pullback.map`, whose definition `simp` does not unfold.

## References

* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B U A V : Scheme.{u}} (pA : A ⟶ B) (pU : U ⟶ B) (a : U ⟶ A) (ha : a ≫ pA = pU)
  (i : V ⟶ B)

/-- The canonical morphism `U ×_B V ⟶ A ×_B V` induced by a morphism `a : U ⟶ A` over `B`, where
`pU = a ≫ pA` is the structure morphism of `U`. -/
public abbrev pullbackMapOver : pullback pU i ⟶ pullback pA i :=
  pullback.lift (pullback.fst pU i ≫ a) (pullback.snd pU i)
    (by rw [Category.assoc, ha]; exact pullback.condition)

/-- The induced morphism followed by the first projection is the first projection followed by
`a`. -/
@[simp]
public lemma pullbackMapOver_fst :
    pullbackMapOver pA pU a ha i ≫ pullback.fst pA i = pullback.fst pU i ≫ a :=
  pullback.lift_fst _ _ _

/-- The induced morphism commutes with the second projections to `V`. -/
@[simp]
public lemma pullbackMapOver_snd :
    pullbackMapOver pA pU a ha i ≫ pullback.snd pA i = pullback.snd pU i :=
  pullback.lift_snd _ _ _

/-- `U ×_B V` is `U ×_A (A ×_B V)`, and under that identification the induced morphism to
`A ×_B V` is the base change of `a` along `A ×_B V ⟶ A`. -/
public theorem pullbackMapOver_eq :
    pullbackMapOver pA (a ≫ pA) a rfl i =
      (pullbackRightPullbackFstIso pA i a).inv ≫ pullback.snd a (pullback.fst pA i) := by
  refine pullback.hom_ext ?_ ?_
  · rw [pullbackMapOver_fst, Category.assoc, ← pullback.condition,
      pullbackRightPullbackFstIso_inv_fst_assoc]
  · rw [pullbackMapOver_snd, Category.assoc,
      pullbackRightPullbackFstIso_inv_snd_snd]

/-- **The base change of an étale morphism of schemes over `B` along `i : V ⟶ B` is étale.** -/
public theorem etale_pullbackMapOver [Etale a] : Etale (pullbackMapOver pA pU a ha i) := by
  subst ha
  rw [pullbackMapOver_eq]
  have : Etale (pullback.snd a (pullback.fst pA i)) := inferInstance
  infer_instance

/-- **The base change of an open immersion of schemes over `B` along `i : V ⟶ B` is an open
immersion.** -/
public theorem isOpenImmersion_pullbackMapOver [IsOpenImmersion a] :
    IsOpenImmersion (pullbackMapOver pA pU a ha i) := by
  subst ha
  rw [pullbackMapOver_eq]
  have : IsOpenImmersion (pullback.snd a (pullback.fst pA i)) := inferInstance
  infer_instance

/-- **The base change of a morphism trivial on residue fields stays trivial on residue fields**, at
any point of the base change lying over the given point of the source. -/
public theorem isIso_residueFieldMap_pullbackMapOver (u : U)
    (w : ↥(pullback pU i)) (hw : pullback.fst pU i w = u)
    (hres : IsIso (a.residueFieldMap u)) :
    IsIso ((pullbackMapOver pA pU a ha i).residueFieldMap w) := by
  subst ha
  set h := pullback.fst pA i with hh
  set ee : pullback (a ≫ pA) i ⟶ pullback a h := (pullbackRightPullbackFstIso pA i a).inv with hee
  have hfactor : pullbackMapOver pA (a ≫ pA) a rfl i =
      ee ≫ (pullbackSymmetry a h).hom ≫ pullback.fst h a := by
    rw [hee, pullbackMapOver_eq, pullbackSymmetry_hom_comp_fst]
  have hpt : pullback.snd h a ((pullbackSymmetry a h).hom (ee w)) = u := by
    rw [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_snd, ← Scheme.Hom.comp_apply, hee,
      pullbackRightPullbackFstIso_inv_fst, hw]
  have hmain : IsIso ((pullback.fst h a).residueFieldMap
      ((pullbackSymmetry a h).hom (ee w))) :=
    Scheme.Pullback.isIso_residueFieldMap_fst_of_isIso_residueFieldMap h a _ u hres _ rfl hpt
  have hsym : IsIso ((pullbackSymmetry a h).hom.residueFieldMap (ee w)) := inferInstance
  have hee' : IsIso (ee.residueFieldMap w) := by
    rw [hee]; infer_instance
  rw [hfactor, Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' (IsIso.comp_isIso' hmain hsym) hee'

section Comparison

variable {X S C Dj : Scheme.{u}} (f : X ⟶ S) (pj : Dj ⟶ S) (pi : C ⟶ Dj)

/-- The comparison morphism `X ×_S C ⟶ X ×_S D` attached to a factorization `C ⟶ D ⟶ S` of the
second leg. -/
public abbrev pullbackComparison : pullback f (pi ≫ pj) ⟶ pullback f pj :=
  pullback.lift (pullback.fst f (pi ≫ pj)) (pullback.snd f (pi ≫ pj) ≫ pi)
    (by rw [Category.assoc]; exact pullback.condition)

/-- The comparison morphism commutes with the first projections to `X`. -/
@[simp]
public lemma pullbackComparison_fst :
    pullbackComparison f pj pi ≫ pullback.fst f pj = pullback.fst f (pi ≫ pj) :=
  pullback.lift_fst _ _ _

/-- The comparison morphism followed by the second projection is the second projection followed
by `pi`. -/
@[simp]
public lemma pullbackComparison_snd :
    pullbackComparison f pj pi ≫ pullback.snd f pj = pullback.snd f (pi ≫ pj) ≫ pi :=
  pullback.lift_snd _ _ _

/-- The comparison morphism is trivial on residue fields wherever the first projection from the
base change along the composite is. -/
public theorem isIso_residueFieldMap_pullbackComparison (w : ↥(pullback f (pi ≫ pj)))
    (h : IsIso ((pullback.fst f (pi ≫ pj)).residueFieldMap w)) :
    IsIso ((pullbackComparison f pj pi).residueFieldMap w) := by
  refine isIso_residueFieldMap_left_of_isIso_residueFieldMap_comp
    (pullbackComparison f pj pi) (pullback.fst f pj) w ?_
  rwa [pullbackComparison_fst]

end Comparison

end AlgebraicGeometry

end
