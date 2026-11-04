module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningBlowupEtaleCover

/-!
# Flattening blowups on a surjective étale cover of the base

Let `φ : W ⟶ A` be surjective and étale and let `b : A' ⟶ A` be a morphism.  For an algebraic
space `f : X ⟶ A` over `A`, write `X_W = X ×_A W` and `W' = W ×_A A'`.  The ambient base change
`X_W ×_W W'` of the strict transform along `W' ⟶ W` is a surjective étale cover of the ambient
base change `X ×_A A'` of the strict transform along `b`, and the strict transform of the
pullback of `F` to `X_W` along `W' ⟶ W`, relative to the inverse image of the exceptional
subspace, is the pullback of the strict transform of `F` (Stacks 0863, part (3)).  Hence a
flattening blowup may be recognized after an étale surjective base change, which is the last
step of the proof of Stacks 087C.

## Main definitions

* `AlgebraicGeometry.Space.strictTransformPullbackMapBase`: the morphism
  `X_W ×_W W' ⟶ X ×_A A'`, for any commutative square `W' ⟶ W`, `W' ⟶ A'` over `A`.

## Main results

* `AlgebraicGeometry.Space.isPullback_strictTransformPullbackMapBase`: when the square is
  cartesian, it is the base change of `W' ⟶ A'` along `X ×_A A' ⟶ A'`.
* `AlgebraicGeometry.Space.isFlatteningBlowup_of_baseChange`: if the strict transform of the
  pullback of `F` along `W' ⟶ W` is of finite presentation and flat over `W'`, then the strict
  transform of `F` along `b` is of finite presentation and flat over `A'`.

## References

* [Stacks Project, Tag 087C](https://stacks.math.columbia.edu/tag/087C)
* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {A X W A' : AlgebraicSpaces B S hS} (f : X ⟶ A) (φ : W ⟶ A) (b : A' ⟶ A)

/-- The base change `X_W = X ×_A W ⟶ W` of `f` along `φ`. -/
noncomputable abbrev baseChangeHom : AlgebraicSpaces.fiberProduct B S hS f φ ⟶ W :=
  ObjectProperty.homMk (pullback.snd f.hom φ.hom)

/-- The projection `X_W ⟶ X`. -/
noncomputable abbrev baseChangeProj : AlgebraicSpaces.fiberProduct B S hS f φ ⟶ X :=
  ObjectProperty.homMk (pullback.fst f.hom φ.hom)

variable {W' : AlgebraicSpaces B S hS} (v : W' ⟶ W) (m : W' ⟶ A')

/-- The morphism `X_W ×_W W' ⟶ X ×_A A'` of ambient base changes, for a commutative square
`v ≫ φ = m ≫ b`. -/
noncomputable def strictTransformPullbackMapBase (hw : v ≫ φ = m ≫ b) :
    strictTransformPullback B S hS (baseChangeHom f φ) v ⟶
      strictTransformPullback B S hS f b :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).lift
    (strictTransformPullbackToSource B S hS _ _ ≫ baseChangeProj f φ)
    (strictTransformPullbackToBlowUp B S hS _ _ ≫ m)
    (by
      have h1 := (AlgebraicSpaces.isPullback_fiberProduct B S hS f φ).w
      have h3 := (AlgebraicSpaces.isPullback_fiberProduct B S hS (baseChangeHom f φ) v).w
      rw [Category.assoc, Category.assoc, h1, ← hw, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ φ) h3)

variable {f φ b v m}

/-- `AlgebraicGeometry.Space.strictTransformPullbackMapBase` lies over `X_W ⟶ X`. -/
theorem strictTransformPullbackMapBase_toSource (hw : v ≫ φ = m ≫ b) :
    strictTransformPullbackMapBase f φ b v m hw ≫ strictTransformPullbackToSource B S hS f b =
      strictTransformPullbackToSource B S hS _ _ ≫ baseChangeProj f φ :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).lift_fst _ _ _

/-- `AlgebraicGeometry.Space.strictTransformPullbackMapBase` lies over `m : W' ⟶ A'`. -/
theorem strictTransformPullbackMapBase_toBlowUp (hw : v ≫ φ = m ≫ b) :
    strictTransformPullbackMapBase f φ b v m hw ≫ strictTransformPullbackToBlowUp B S hS f b =
      strictTransformPullbackToBlowUp B S hS _ _ ≫ m :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).lift_snd _ _ _

/-- **For a cartesian square `W' = W ×_A A'`, the morphism `X_W ×_W W' ⟶ X ×_A A'` is the base
change of `m : W' ⟶ A'`.**  Pasting the cartesian squares of `X_W ×_W W'` over `W'`, of `X_W`
over `W` and of `W'` over `A'` exhibits `X_W ×_W W'` as `X ×_A W'`, which is
`(X ×_A A') ×_{A'} W'`. -/
theorem isPullback_strictTransformPullbackMapBase (hsq : IsPullback v m φ b) :
    IsPullback (strictTransformPullbackMapBase f φ b v m hsq.w)
      (strictTransformPullbackToBlowUp B S hS _ _)
      (strictTransformPullbackToBlowUp B S hS f b) m := by
  have outer := (AlgebraicSpaces.isPullback_fiberProduct B S hS (baseChangeHom f φ) v).paste_horiz
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f φ)
  refine IsPullback.of_right ?_ (strictTransformPullbackMapBase_toBlowUp hsq.w)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f b)
  rw [strictTransformPullbackMapBase_toSource, ← hsq.w]
  exact outer

/-- **A flattening blowup may be recognized after a surjective étale base change.**  Let
`φ : W ⟶ A` be surjective and étale, let `b : A' ⟶ A` be the blowup of `A` in a finitely
presented closed subspace `Z` whose points avoid those of `U`, and let `W'` with `v : W' ⟶ W`
and `m : W' ⟶ A'` be a fibre product `W ×_A A'`.  If the strict transform of the pullback of
`F` to `X_W` along `v`, relative to the inverse image in `W'` of the exceptional divisor, is of
finite presentation and flat over `W'`, then `b` is a flattening blowup for `f` and `F`.

The cover `X_W ×_W W' ⟶ X ×_A A'` is surjective and étale, being a base change of `m`
(`AlgebraicGeometry.Space.isPullback_strictTransformPullbackMapBase`); along it the strict
transform of `F` pulls back to the strict transform on `X_W` (Stacks 0863, part (3)); flatness
over `W'` gives flatness over `A'` because `m` is étale (Stacks 05VX), and finite presentation
and flatness descend along the cover. -/
theorem isFlatteningBlowup_of_baseChange (hφ : IsEtale B S hS φ.hom)
    (hφs : IsSurjective B S hS φ.hom) (hsq : IsPullback v m φ b)
    {F : Modules.{u, u} B S hS X.1 X.2}
    {U : OpenSubspaces B S hS A.1} {Z : ClosedSubspaces B S hS A.1}
    (hZ : IsFinitePresentation B S hS Z.1.ι)
    (hUZ : Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1))
    (hb : IsBlowupAlong B S hS Z b)
    (hfp : (strictTransformSheaf B S hS (baseChangeHom f φ) v ((Z.1.preimage b.hom).preimage m.hom)
      ((modulePullback B S hS (baseChangeProj f φ)).obj F)).IsFinitePresentationOnSite)
    (hflat : IsFlatOver B S hS (strictTransformPullback B S hS (baseChangeHom f φ) v).2
      (strictTransformPullbackToBlowUp B S hS (baseChangeHom f φ) v).hom
      (strictTransformSheaf B S hS (baseChangeHom f φ) v ((Z.1.preimage b.hom).preimage m.hom)
        ((modulePullback B S hS (baseChangeProj f φ)).obj F))) :
    IsFlatteningBlowup f F U Z b := by
  have hm : IsEtale B S hS m.hom := isEtale_of_isPullback B S hS _ _ _ _ hsq hφ
  have sq := isPullback_strictTransformPullbackMapBase (f := f) hsq
  have hcan : IsEtale B S hS (strictTransformPullbackMapBase f φ b v m hsq.w).hom :=
    isEtale_of_isPullback B S hS _ _ _ _ sq.flip hm
  have hcans : IsSurjective B S hS (strictTransformPullbackMapBase f φ b v m hsq.w).hom :=
    isSurjective_of_isPullback B S hS sq.flip (isSurjective_of_isPullback B S hS hsq hφs)
  have e := strictTransformSheafEtaleRestrictionIso B S hS f b (Z.1.preimage b.hom)
    (baseChangeProj f φ) (baseChangeHom f φ) v ((Z.1.preimage b.hom).preimage m.hom) m
    (strictTransformPullbackMapBase f φ b v m hsq.w) hcan
    (strictTransformPullbackMapBase_toSource hsq.w)
    (strictTransformPullbackMapBase_toBlowUp hsq.w)
    (range_pointsMap_preimage_ι B S hS _ (Z.1.preimage b.hom)) F
  have hfpX : (strictTransformSheaf B S hS f b (Z.1.preimage b.hom) F).IsFinitePresentationOnSite :=
    isFinitePresentationOnSite_of_modulePullback_of_isEtale _ hcan hcans _
      (SheafOfModules.IsFinitePresentationOnSite.of_iso e.symm hfp)
  refine ⟨hZ, hUZ, hb, hfpX, ?_⟩
  refine isFlatOver_of_modulePullback_of_isEtale _ hcan hcans _ _ inferInstance ?_
  rw [strictTransformPullbackMapBase_toBlowUp]
  refine (isFlatOver_iff_of_iso B S hS _ _ e).2 ?_
  exact isFlatOver_comp_of_isFlat B S hS _ _ _ hflat (isFlat_of_isEtale B S hS hm)

end AlgebraicGeometry.Space

end
