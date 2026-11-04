module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatRankOpenUnconditional
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyOpenSubfunctor

/-!
# The locus where the derived pushforward is invertible in degree zero

Let `f : X ⟶ S` be flat, proper and locally of finite presentation with a section `σ`, for
instance a smooth projective curve over a field `k` with a `k`-rational point. For an
`S`-scheme `T` let `F(T) ⊆ Pic_{X/S,σ}(T)` be the set of rigidified classes `ℒ` with `Rf_{T,*}ℒ`
isomorphic to an invertible `𝒪_T`-module placed in degree `0`. Then `F` is a subfunctor of the
rigidified Picard functor `Pic_{X/S,σ}` and the inclusion is representable by open immersions
([Stacks, Tag 0B9V]). Here `Pic_{X/S,σ}` is `Stacks.RigidifiedPicard.functor`, on all
`S`-schemes, `T ↦ Ker(Pic(X_T) ⟶ Pic(T))`.

## Main definitions

* `Stacks.RigidifiedPicard.cohomologyLocus`: the subfunctor `F`.

## Main results

* `Stacks.RigidifiedPicard.mem_cohomologyLocus_iff`: a class lies in `F(T)` exactly when
  `Rf_{T,*}` of its representative is finite locally free of rank one in degree `0`.
* `Stacks.RigidifiedPicard.isOpenSubfunctor_cohomologyLocus`: the inclusion `F ⊆ Pic_{X/S,σ}` is
  representable by open immersions, in the elementwise form of [Stacks, Tag 01JI].
* `Stacks.RigidifiedPicard.isOpenImmersion_presheaf_cohomologyLocus`: the same, in Mathlib's
  form of representability by open immersions.

## References

* [Stacks Project, Tag 0B9V](https://stacks.math.columbia.edu/tag/0B9V)
* [Stacks Project, Tag 01JI](https://stacks.math.columbia.edu/tag/01JI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace Stacks.RigidifiedPicard

variable {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] [IsProper f]
  (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)

/-- The rigidified classes `ℒ ∈ Pic_{X/S,σ}(T)` with `Rf_{T,*}ℒ` isomorphic to an invertible
`𝒪_T`-module placed in degree `0`, as a subfunctor of `Pic_{X/S,σ}`. -/
@[stacks 0B9V "F is a subfunctor, for f flat, proper and locally of finite presentation with a \
section (the source's smooth projective curve over a field with a rational point is a special \
case)"]
def cohomologyLocus : Subfunctor (functor f σ hσ ⋙ forget GrpCat) :=
  cohomologySubfunctor f σ hσ (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward)
    baseChangeDerivedPushforward 0

/-- A class lies in `F(T)` if and only if `Rf_{T,*}ℒ` is a finite locally free module of rank one
placed in degree `0`, for the representative `ℒ` of the class. -/
theorem mem_cohomologyLocus_iff (T : Over S) (x : (functor f σ hσ ⋙ forget GrpCat).obj (op T)) :
    x ∈ (cohomologyLocus f σ hσ).obj (op T) ↔
      HasDerivedPushforwardRank (bcProj f T) (Stacks.Picard.picardRepresentative _
        (smallEquiv _ ((Multiplicative.toAdd x : group f σ hσ T) :
          Stacks.Picard.smallOfScheme (bc f T)))).obj 0 1 := by
  show IsCohomologyClass f 0 T _ ↔ _
  rw [IsCohomologyClass, show Stacks.Picard.schemePullbackClass (pullback.fst f T.hom) 0 = 0 from
    map_zero (Stacks.Picard.schemePullbackClassHom _), add_zero]

/-- The inclusion `F ⊆ Pic_{X/S,σ}` is representable by open immersions, in the elementwise form
of [Stacks, Tag 01JI]: for every `S`-scheme `T` and every `ℒ ∈ Pic_{X/S,σ}(T)` there is an open
`U ⊆ T` such that for every `g : T' ⟶ T` over `S`, the restriction of `ℒ` to `T'` lies in `F(T')`
exactly when `g` maps `T'` into `U`. -/
@[stacks 0B9V "the inclusion is representable by open immersions, for f flat, proper and locally \
of finite presentation with a section"]
theorem isOpenSubfunctor_cohomologyLocus : IsOpenSubfunctor (cohomologyLocus f σ hσ) :=
  isOpenSubfunctor_cohomologySubfunctor f σ hσ
    (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward)
    baseChangeDerivedPushforward 0

/-- The inclusion `F ⊆ Pic_{X/S,σ}` is representable by open immersions, in Mathlib's form. -/
theorem isOpenImmersion_presheaf_cohomologyLocus :
    (IsOpenImmersion.over (X := S)).presheaf (cohomologyLocus f σ hσ).ι :=
  (isOpenSubfunctor_cohomologyLocus f σ hσ).isOpenImmersion_presheaf_ι

end Stacks.RigidifiedPicard

end
