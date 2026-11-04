module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite limits of affine schemes are limits of locally ringed spaces

The category of affine schemes has all (small) limits, in particular finite products and fibre
products, because it is anti-equivalent to the category of commutative rings, which has all
colimits. These limits are also limits in the category of locally ringed spaces: the forgetful
functor from affine schemes to locally ringed spaces preserves all limits, since up to the
anti-equivalence it is the functor `Spec`, which is right adjoint to the global sections functor.

Concretely, in the category of locally ringed spaces we have
`Spec R × Spec S ≅ Spec (R ⊗[ℤ] S)`, and for ring maps `R → A`, `R → B` we have
`Spec A ×_{Spec R} Spec B ≅ Spec (A ⊗[R] B)`, the projections being induced by the canonical
maps into the tensor product.

## Main results

* `AlgebraicGeometry.AffineScheme.preservesLimits_forgetToLocallyRingedSpace`: the forgetful
  functor from affine schemes to locally ringed spaces preserves all limits.
* `AlgebraicGeometry.LocallyRingedSpace.prodSpecIso`: in locally ringed spaces,
  `Spec R × Spec S ≅ Spec (R ⊗[ℤ] S)`.
* `AlgebraicGeometry.LocallyRingedSpace.pullbackSpecIso`: in locally ringed spaces,
  `Spec A ×_{Spec R} Spec B ≅ Spec (A ⊗[R] B)`.

The existence of all limits in the category of affine schemes is
`AlgebraicGeometry.AffineScheme.hasLimits`.

## References

* [Stacks Project, Tag 01I4](https://stacks.math.columbia.edu/tag/01I4)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u

add_to_stacks 01I4 "finite products and fibre products exist"
  AlgebraicGeometry.AffineScheme.hasLimits

namespace AlgebraicGeometry

namespace AffineScheme

/-- The forgetful functor from affine schemes to locally ringed spaces preserves all limits:
limits of affine schemes, in particular products and fibre products, are the same as those
computed in locally ringed spaces. -/
@[stacks 01I4 "limits agree with those of locally ringed spaces"]
instance preservesLimits_forgetToLocallyRingedSpace :
    PreservesLimits (forgetToScheme.{u} ⋙ Scheme.forgetToLocallyRingedSpace) := by
  apply +allowSynthFailures @preservesLimits_of_natIso _ _ _ _ _ _
    (Functor.isoWhiskerRight equivCommRingCat.unitIso
      (forgetToScheme ⋙ Scheme.forgetToLocallyRingedSpace)).symm
  change PreservesLimits (equivCommRingCat.functor ⋙ Spec.toLocallyRingedSpace)
  infer_instance

/-- A diagram of affine schemes has a limit in locally ringed spaces. -/
instance hasLimit_comp_forgetToLocallyRingedSpace {J : Type u} [Category.{u} J]
    (F : J ⥤ AffineScheme.{u}) :
    HasLimit (F ⋙ forgetToScheme ⋙ Scheme.forgetToLocallyRingedSpace) :=
  HasLimit.mk ⟨_, isLimitOfPreserves _ (limit.isLimit F)⟩

end AffineScheme

namespace LocallyRingedSpace

open TensorProduct Algebra.TensorProduct CommRingCat

section Product

variable (R S : Type u) [CommRing R] [CommRing S]

/-- The locally ringed space `Spec (R ⊗[ℤ] S)` with its projections to `Spec R` and `Spec S` is a
product of `Spec R` and `Spec S` in the category of locally ringed spaces. -/
noncomputable def isLimitSpecTensorBinaryFan :
    IsLimit (BinaryFan.mk (X := Spec.locallyRingedSpaceObj (.of R))
      (Y := Spec.locallyRingedSpaceObj (.of S))
      (Spec.locallyRingedSpaceMap (coproductCocone (.of R) (.of S)).inl)
      (Spec.locallyRingedSpaceMap (coproductCocone (.of R) (.of S)).inr)) :=
  mapIsLimitOfPreservesOfIsLimit Spec.toLocallyRingedSpace _ _
    (BinaryCofan.IsColimit.op (coproductCoconeIsColimit (.of R) (.of S)))

/-- `Spec R` and `Spec S` have a product in locally ringed spaces. -/
instance : HasBinaryProduct (Spec.locallyRingedSpaceObj (.of R))
    (Spec.locallyRingedSpaceObj (.of S)) :=
  HasLimit.mk ⟨_, isLimitSpecTensorBinaryFan R S⟩

/-- In the category of locally ringed spaces, `Spec R × Spec S ≅ Spec (R ⊗[ℤ] S)`. -/
@[stacks 01I4 "products in locally ringed spaces"]
noncomputable def prodSpecIso :
    Spec.locallyRingedSpaceObj (.of R) ⨯ Spec.locallyRingedSpaceObj (.of S) ≅
      Spec.locallyRingedSpaceObj (.of (R ⊗[ℤ] S)) :=
  limit.isoLimitCone ⟨_, isLimitSpecTensorBinaryFan R S⟩

/-- Under `prodSpecIso`, the first projection is induced by `r ↦ r ⊗ₜ 1`. -/
@[reassoc (attr := simp)]
lemma prodSpecIso_inv_fst :
    (prodSpecIso R S).inv ≫ prod.fst =
      Spec.locallyRingedSpaceMap (ofHom (includeLeft (S := ℤ) (A := R) (B := S)).toRingHom) :=
  limit.isoLimitCone_inv_π _ _

/-- Under `prodSpecIso`, the second projection is induced by `s ↦ 1 ⊗ₜ s`. -/
@[reassoc (attr := simp)]
lemma prodSpecIso_inv_snd :
    (prodSpecIso R S).inv ≫ prod.snd =
      Spec.locallyRingedSpaceMap (ofHom (includeRight (R := ℤ) (A := R) (B := S)).toRingHom) :=
  limit.isoLimitCone_inv_π _ _

end Product

section FibreProduct

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The locally ringed space `Spec (A ⊗[R] B)` with its projections to `Spec A` and `Spec B` is a
fibre product of `Spec A` and `Spec B` over `Spec R` in the category of locally ringed spaces. -/
noncomputable def isLimitSpecTensorPullbackCone :
    IsLimit (PullbackCone.mk
      (f := Spec.locallyRingedSpaceMap (ofHom (algebraMap R A)))
      (g := Spec.locallyRingedSpaceMap (ofHom (algebraMap R B)))
      (Spec.locallyRingedSpaceMap (pushoutCocone R A B).inl)
      (Spec.locallyRingedSpaceMap (pushoutCocone R A B).inr)
      (by rw [← Spec.locallyRingedSpaceMap_comp, ← Spec.locallyRingedSpaceMap_comp,
        (pushoutCocone R A B).condition])) :=
  isLimitPullbackConeMapOfIsLimit Spec.toLocallyRingedSpace _
    (IsLimit.equivIsoLimit (PullbackCone.eta _)
      (PushoutCocone.isColimitEquivIsLimitOp _ (pushoutCoconeIsColimit R A B)))

/-- `Spec A` and `Spec B` have a fibre product over `Spec R` in locally ringed spaces. -/
instance : HasPullback (Spec.locallyRingedSpaceMap (ofHom (algebraMap R A)))
    (Spec.locallyRingedSpaceMap (ofHom (algebraMap R B))) :=
  HasLimit.mk ⟨_, isLimitSpecTensorPullbackCone R A B⟩

/-- In the category of locally ringed spaces, `Spec A ×_{Spec R} Spec B ≅ Spec (A ⊗[R] B)`. -/
@[stacks 01I4 "fibre products in locally ringed spaces"]
noncomputable def pullbackSpecIso :
    pullback (Spec.locallyRingedSpaceMap (ofHom (algebraMap R A)))
      (Spec.locallyRingedSpaceMap (ofHom (algebraMap R B))) ≅
      Spec.locallyRingedSpaceObj (.of (A ⊗[R] B)) :=
  limit.isoLimitCone ⟨_, isLimitSpecTensorPullbackCone R A B⟩

/-- Under `pullbackSpecIso`, the first projection is induced by `a ↦ a ⊗ₜ 1`. -/
@[reassoc (attr := simp)]
lemma pullbackSpecIso_inv_fst :
    (pullbackSpecIso R A B).inv ≫ pullback.fst _ _ =
      Spec.locallyRingedSpaceMap (ofHom (includeLeftRingHom (R := R) (A := A) (B := B))) :=
  limit.isoLimitCone_inv_π _ _

/-- Under `pullbackSpecIso`, the second projection is induced by `b ↦ 1 ⊗ₜ b`. -/
@[reassoc (attr := simp)]
lemma pullbackSpecIso_inv_snd :
    (pullbackSpecIso R A B).inv ≫ pullback.snd _ _ =
      Spec.locallyRingedSpaceMap (ofHom (includeRight (R := R) (A := A) (B := B)).toRingHom) :=
  limit.isoLimitCone_inv_π _ _

end FibreProduct

end LocallyRingedSpace

end AlgebraicGeometry
