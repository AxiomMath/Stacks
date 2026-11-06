module

public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve

/-!
# The twists an exceptional curve of the first kind cuts out on itself

Let `E ⊆ X` be an exceptional curve of the first kind and let `e : 𝐏¹_k ≅ E` be the isomorphism
under which the normal sheaf `N_{E/X}` pulls back to `𝒪(-1)`. For every `d` the restriction
`𝒪_X(-dE)|_E` of the ideal sheaf of the `d`-fold divisor then pulls back along `e` to the `d`-th
twist of the structure sheaf of the projective line,

`e^*(𝒪_X(-dE)|_E) ≅ 𝒪_{𝐏¹_k}(d)`.

The identity is read off in `Pic(𝐏¹_k)`. Pullback of invertible modules is a homomorphism of
Picard groups, the class of `𝒪_X(-dD)` is `-d` times the class of `𝒪_X(D)`, and the defining
hypothesis says that the latter pulls back to the class of `𝒪(-1)`, which is `-1` times the
class of `𝒪(1)`; multiplying out leaves `d` times the class of `𝒪(1)`, the class of `𝒪(d)`.
Equality of Picard classes is isomorphism of invertible modules, so the isomorphism follows.

The only input not already available is additivity of the twist classes in `Pic(𝐏¹_k)`, which is
Equation 01MO: the multiplication `𝒪(m) ⊗ 𝒪(m') ⟶ 𝒪(m + m')` is an isomorphism because a
polynomial ring is generated in degree one.

## Main definitions

* `AlgebraicGeometry.twistingSheafPicardClass` — the class of `𝒪(m)` in `Pic(𝐏¹_k)`.
* `AlgebraicGeometry.twistingSheafPicardHom` — that class as a homomorphism `ℤ ⟶ Pic(𝐏¹_k)`.

## Main results

* `AlgebraicGeometry.twistingSheafPicardClass_add` and
  `AlgebraicGeometry.twistingSheafPicardClass_eq_zsmul` — the class of `𝒪(m)` is additive in
  `m`, hence `m` times the class of `𝒪(1)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.pullbackPicardClass_invertibleSheaf` — `𝒪_X(E)` pulls back to the class of `𝒪(-1)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.nonempty_pullback_negativeTwist_pow_iso_twistingSheaf` — `e^*(𝒪_X(-dE)|_E) ≅ 𝒪_{𝐏¹_k}(d)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.nonempty_pullback_negativeTwist_iso_twistingSheaf` — the case `d = 1`, the dual of the
  defining hypothesis.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open CategoryTheory RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-! ### The classes of the twists in the Picard group of the projective line -/

/-- Every twist `𝒪(m)` on the projective line is invertible, the polynomial ring `k[T₀, T₁]`
being generated in degree one. -/
public theorem isInvertible_twistingSheaf_projectiveLineProj (m : ℤ) :
    Stacks.SheafOfModules.IsInvertible (projectiveLineProj k).toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf (projectiveLineProj k).toRingedSpace)
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) m) :=
  Stacks.PicardUFD.isInvertible_twistingSheaf k 1 m

/-- The class of the twist `𝒪(m)` in the Picard group of the projective line. -/
public abbrev twistingSheafPicardClass (m : ℤ) : Stacks.Picard.ofScheme (projectiveLineProj k) :=
  Stacks.SheafOfModules.picardClass _ _
    (ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) k) m)
    (isInvertible_twistingSheaf_projectiveLineProj k m)

/-- **The class of `𝒪(m)` in `Pic(𝐏¹_k)` is additive in `m`**: the multiplication map of
Equation 01MO is an isomorphism `𝒪(m) ⊗ 𝒪(m') ≅ 𝒪(m + m')`. -/
public theorem twistingSheafPicardClass_add (m m' : ℤ) :
    twistingSheafPicardClass k (m + m') =
      twistingSheafPicardClass k m + twistingSheafPicardClass k m' := by
  have hm := isInvertible_twistingSheaf_projectiveLineProj k m
  have hm' := isInvertible_twistingSheaf_projectiveLineProj k m'
  have htens := Stacks.SheafOfModules.isInvertible_tensorSheaf
    (projectiveLineProj k).toRingedSpace.presheaf
    (Stacks.RingedSpace.structureIsSheaf (projectiveLineProj k).toRingedSpace)
    (ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) k) m)
    (ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) k) m')
  refine Eq.trans ?_ (Stacks.SheafOfModules.picardClass_tensorSheaf _ _ _ _ hm hm' htens).symm
  refine (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨?_⟩
  exact (Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.twistMultiplicationIso
    (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    (Stacks.PicardUFD.degreeOneCover k 1) m m').symm

/-- **The homomorphism `ℤ ⟶ Pic(𝐏¹_k)`, `m ↦ 𝒪(m)`.** -/
public def twistingSheafPicardHom : ℤ →+ Stacks.Picard.ofScheme (projectiveLineProj k) :=
  AddMonoidHom.mk' (twistingSheafPicardClass k) (twistingSheafPicardClass_add k)

/-- The homomorphism `twistingSheafPicardHom` sends `m` to the class of `𝒪(m)`. -/
@[simp]
public theorem twistingSheafPicardHom_apply (m : ℤ) :
    twistingSheafPicardHom k m = twistingSheafPicardClass k m := rfl

/-- The class of `𝒪(m)` is `m` times the class of `𝒪(1)`. -/
public theorem twistingSheafPicardClass_eq_zsmul (m : ℤ) :
    twistingSheafPicardClass k m = m • twistingSheafPicardClass k 1 := by
  have h : twistingSheafPicardHom k (m • (1 : ℤ)) = m • twistingSheafPicardHom k 1 :=
    map_zsmul _ _ _
  simpa using h

/-! ### The twists cut out by an exceptional curve of the first kind -/

/-- Pulling back twice sends the class of an invertible module to the class of its double
pullback. -/
private theorem pullbackClass_pullbackClass_picardClass {A B C : RingedSpace.{u, u}}
    (f : A ⟶ B) (g : B ⟶ C)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf C.presheaf
      (Stacks.RingedSpace.structureIsSheaf C)))
    (hL : Stacks.SheafOfModules.IsInvertible C.presheaf (Stacks.RingedSpace.structureIsSheaf C) L) :
    Stacks.Picard.pullbackClass f
        (Stacks.Picard.pullbackClass g (Stacks.SheafOfModules.picardClass _ _ L hL)) =
      Stacks.SheafOfModules.picardClass _ _
        ((Stacks.RingedSpace.pullbackFunctor f).obj ((Stacks.RingedSpace.pullbackFunctor g).obj L))
        (Stacks.RingedSpace.modulePullback_isInvertible_of f _
          (Stacks.RingedSpace.modulePullback_isInvertible_of g L hL)) :=
  (congrArg _ (Stacks.Picard.pullbackClass_classOf g L hL)).trans
    (Stacks.Picard.pullbackClass_classOf f _ _)

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}} {D : X.IdealSheafData} {k}
  {e : projectiveLineProj k ≅ D.subscheme}

/-- **Pulled back to the projective line, `𝒪_X(E)` has the class of `𝒪(-1)`.** This is the
defining hypothesis of an exceptional curve of the first kind, read in the Picard group: the
normal sheaf of `E` is the restriction of `𝒪_X(E)` to `E` by Tag 0B3P. -/
public theorem IsExceptionalCurveOfFirstKind.pullbackPicardClass_invertibleSheaf
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hE : IsExceptionalCurveOfFirstKind D k e) :
    Stacks.Picard.pullbackClass e.hom.toLRSHom.toShHom
        (Stacks.Picard.pullbackClass D.subschemeι.toLRSHom.toShHom
          (Stacks.Divisors.picardClass D)) =
      twistingSheafPicardClass k (-1) := by
  refine Eq.trans (pullbackClass_pullbackClass_picardClass _ _ _ _) ?_
  refine (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨?_⟩
  exact ((modulePullback e.hom.toLRSHom.toShHom).mapIso
    (Stacks.Divisors.normalSheafIsoInvertibleSheaf D)).symm ≪≫ hE.2.some

/-- **Pulled back to the projective line, `𝒪_X(-dE)` has the class of `𝒪(d)`.** The class of
`𝒪_X(-dD)` is `-d` times the class of `𝒪_X(D)`, and pullback is a homomorphism of Picard
groups. -/
public theorem IsExceptionalCurveOfFirstKind.pullbackPicardClass_negativeTwist_pow
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hE : IsExceptionalCurveOfFirstKind D k e) (d : ℕ) :
    Stacks.Picard.pullbackClass e.hom.toLRSHom.toShHom
        (Stacks.Picard.pullbackClass D.subschemeι.toLRSHom.toShHom
          (Stacks.Divisors.negativeTwistPicardClass (D ^ d))) =
      twistingSheafPicardClass k (d : ℤ) := by
  have hcomp : ∀ x : Stacks.Picard.ofScheme X,
      Stacks.Picard.pullbackClass e.hom.toLRSHom.toShHom
          (Stacks.Picard.pullbackClass D.subschemeι.toLRSHom.toShHom x) =
        ((Stacks.Picard.schemePullbackClassHom e.hom).comp
          (Stacks.Picard.schemePullbackClassHom D.subschemeι)) x := fun _ => rfl
  rw [hcomp, Stacks.Divisors.negativeTwistPicardClass_eq_neg,
    Stacks.Divisors.picardClass_pow, map_neg, map_zsmul, ← hcomp,
    hE.pullbackPicardClass_invertibleSheaf, twistingSheafPicardClass_eq_zsmul k (-1),
    twistingSheafPicardClass_eq_zsmul k (d : ℤ)]
  rw [neg_one_zsmul, smul_neg, neg_neg]

/-- **The twist an exceptional curve of the first kind cuts out on itself.** For an exceptional
curve of the first kind `E ⊆ X` with `e : 𝐏¹_k ≅ E`, the restriction of `𝒪_X(-dE)` to `E` pulls
back along `e` to the `d`-th twist, `e^*(𝒪_X(-dE)|_E) ≅ 𝒪_{𝐏¹_k}(d)`. -/
public theorem
    IsExceptionalCurveOfFirstKind.nonempty_pullback_negativeTwist_pow_iso_twistingSheaf
    (hE : IsExceptionalCurveOfFirstKind D k e) (d : ℕ) :
    Nonempty ((modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback D.subschemeι.toLRSHom.toShHom).obj
          (Stacks.Divisors.negativeTwist' (D ^ d))) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (d : ℤ)) := by
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor D := hE.1
  have h := hE.pullbackPicardClass_negativeTwist_pow d
  refine (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ ?_).1
    (Eq.trans (pullbackClass_pullbackClass_picardClass _ _ _
      (Stacks.Divisors.isInvertible_negativeTwist_picard (D ^ d))).symm h)
  exact isInvertible_twistingSheaf_projectiveLineProj k (d : ℤ)

/-- **The defining hypothesis of an exceptional curve of the first kind, dualized.** The
restriction `𝒪_X(-E)|_E` of the ideal sheaf — the conormal sheaf of `E` in `X`, by Tag 0B3P —
pulls back along `e` to `𝒪(1)`, the dual of the twist the normal sheaf pulls back to. -/
public theorem IsExceptionalCurveOfFirstKind.nonempty_pullback_negativeTwist_iso_twistingSheaf
    (hE : IsExceptionalCurveOfFirstKind D k e) :
    Nonempty ((modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback D.subschemeι.toLRSHom.toShHom).obj
          (Stacks.Divisors.negativeTwist' D)) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1) := by
  have h := hE.nonempty_pullback_negativeTwist_pow_iso_twistingSheaf 1
  rw [pow_one] at h
  simpa using h

end Scheme.IdealSheafData

end AlgebraicGeometry
