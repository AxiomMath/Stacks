module

public import StacksFrontier.AlgebraicGeometry.Algebraization
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingFormalLift
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingProper
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Cartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeFromThickening
public import StacksFrontier.Deformation.Examples.Geometric.OpenSubschemes

/-!
# The tower of schemes of a formal deformation over the formal disc

A formal object `ξ` of the deformation category `Def_X` of a scheme `X` over a field `k`, whose
base is identified with `k⟦t⟧`, is a tower of flat schemes `X_n` over the thickenings
`Spec (k⟦t⟧ / (t)^{n+1})` with cartesian transition squares and `X_0 ≅ X`. This is the passage, in
the proof of [Stacks, Tag 0E7Y], from the formal object `(X_n)` of `Def_X` to the input of the
algebraization [Stacks, Tag 0E7R].

## Main definitions

* `Deformation.Examples.Smoothing.towerBaseHom`: the identification of the `n`-th thickening of the
  formal disc with the base of `ξ_n`.
* `Deformation.Examples.Smoothing.towerHom`: the structure morphism
  `X_n ⟶ Spec (k⟦t⟧ / (t)^{n+1})`.

## Main results

* `Deformation.Examples.Smoothing.isPullback_towerHom`: the transition squares are cartesian.
* `Deformation.Examples.Smoothing.flat_towerHom`: each `X_n` is flat over its thickening.
* `Deformation.Examples.Smoothing.exists_iso_towerHom_zero`: `X ≅ X_0` over `Spec k`.

## References

* [Stacks Project, Tag 0E7Y](https://stacks.math.columbia.edu/tag/0E7Y)
* [Stacks Project, Tag 0E7R](https://stacks.math.columbia.edu/tag/0E7R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples.Smoothing

variable {k : Type u} [Field k]

/-- The `n`-th thickening of the formal disc, written with `(t)`, is the `n`-th adic truncation of
`k⟦t⟧`, written with its maximal ideal. -/
def discTruncEquiv (n : ℕ) :
    (PowerSeries k ⧸ discIdeal k ^ (n + 1)) ≃+*
      (AdicTruncation.functor n).obj (powerSeriesObject k) :=
  Ideal.quotEquivOfEq (by rw [discIdeal_eq_maximalIdeal])

/-- `discTruncEquiv` sends the class of a power series `a` to the class of `a`. -/
theorem discTruncEquiv_mk (n : ℕ) (a : PowerSeries k) :
    discTruncEquiv n (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk (truncIdeal k n) a := rfl

section Tower

variable (X : Over (Spec (.of k)))
  (ξ : FormalObject (schemeDeformationCategoryProjection (Λ := k) (k := k) X))
  (σ : powerSeriesObject k ≅ ξ.base)

/-- The identification of the `n`-th adic truncation of `k⟦t⟧` with the base of `ξ_n`, as a
morphism of `𝒞_k`. -/
def towerBaseHom (n : ℕ) :
    (AdicTruncation.functor n).obj (powerSeriesObject k) ⟶ (ξ.level n).base :=
  (AdicTruncation.functor n).map σ.hom ≫ eqToHom (ξ.level_eq n).symm

/-- The morphism `towerBaseHom X ξ σ n` is an isomorphism. -/
instance isIso_towerBaseHom (n : ℕ) : IsIso (towerBaseHom X ξ σ n) := by
  unfold towerBaseHom; infer_instance

/-- The transition maps of the truncations of `k⟦t⟧` and of the bases of `ξ` correspond. -/
theorem transitionNat_comp_towerBaseHom (n : ℕ) :
    (AdicTruncation.transitionNat n).app (powerSeriesObject k) ≫ towerBaseHom X ξ σ n =
      towerBaseHom X ξ σ (n + 1) ≫ (ξ.transition n).base := by
  have hlift := ξ.transition_lift n
  have hfac := IsHomLift.fac' (schemeDeformationCategoryProjection (Λ := k) (k := k) X)
    ((AdicTruncation.transitionNat n).app ξ.base) (ξ.transition n)
  change (ξ.transition n).base = _ at hfac
  rw [hfac, towerBaseHom, towerBaseHom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, ← (AdicTruncation.transitionNat n).naturality σ.hom, Category.assoc]

/-- The ring map from the `n`-th thickening of the formal disc to the base of `ξ_n`. -/
def towerRingHom (n : ℕ) : PowerSeries k ⧸ discIdeal k ^ (n + 1) →+* (ξ.level n).base :=
  (towerBaseHom X ξ σ n).hom.toRingHom.comp (discTruncEquiv n).toRingHom

/-- The ring map `towerRingHom X ξ σ n` is bijective. -/
theorem bijective_towerRingHom (n : ℕ) : Function.Bijective (towerRingHom X ξ σ n) := by
  have h : Function.Bijective (towerBaseHom X ξ σ n).hom := by
    have hiso : IsIso (towerBaseHom X ξ σ n) := inferInstance
    refine ⟨fun a b hab => ?_, fun b => ⟨(inv (towerBaseHom X ξ σ n)).hom b, ?_⟩⟩
    · have := congrArg (inv (towerBaseHom X ξ σ n)).hom hab
      change ((towerBaseHom X ξ σ n) ≫ inv (towerBaseHom X ξ σ n)).hom a =
        ((towerBaseHom X ξ σ n) ≫ inv (towerBaseHom X ξ σ n)).hom b at this
      simpa using this
    · change ((inv (towerBaseHom X ξ σ n)) ≫ towerBaseHom X ξ σ n).hom b = b
      simp
  exact h.comp (discTruncEquiv n).bijective

/-- **The structure morphism of the tower**: `ξ_n` lies over the base of `ξ_n`, which is the
`n`-th thickening of the formal disc. -/
def towerHom (n : ℕ) :
    (ξ.level n).scheme ⟶ adicThickening (PowerSeries k) (discIdeal k) n :=
  (ξ.level n).toBase ≫ Spec.map (CommRingCat.ofHom (towerRingHom X ξ σ n))

/-- The morphism of spectra induced by `towerRingHom X ξ σ n` is an isomorphism. -/
instance isIso_specMap_towerRingHom (n : ℕ) :
    IsIso (Spec.map (CommRingCat.ofHom (towerRingHom X ξ σ n))) := by
  have : IsIso (CommRingCat.ofHom (towerRingHom X ξ σ n)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_towerRingHom X ξ σ n)
  infer_instance

/-- **Each member of the tower is flat over its thickening.** -/
theorem flat_towerHom (n : ℕ) : Flat (towerHom X ξ σ n) := by
  have : Flat (ξ.level n).toBase := (ξ.level n).flat
  unfold towerHom
  infer_instance

/-- The transition maps of the thickenings and of the bases of `ξ` correspond, on spectra. -/
theorem baseSpecMap_comp_towerRingHom (n : ℕ) :
    baseSpecMap (ξ.transition n).base ≫ Spec.map (CommRingCat.ofHom (towerRingHom X ξ σ (n + 1))) =
      Spec.map (CommRingCat.ofHom (towerRingHom X ξ σ n)) ≫
        adicThickeningSucc (PowerSeries k) (discIdeal k) n := by
  rw [baseSpecMap, adicThickeningSucc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  have h := congrArg (fun f => f.hom (Ideal.Quotient.mk (truncIdeal k (n + 1)) a))
    (transitionNat_comp_towerBaseHom X ξ σ n)
  exact h.symm

/-- **The transition squares of the tower are cartesian.** -/
theorem isPullback_towerHom (n : ℕ) :
    IsPullback (ξ.transition n).map (towerHom X ξ σ n) (towerHom X ξ σ (n + 1))
      (adicThickeningSucc (PowerSeries k) (discIdeal k) n) :=
  (ξ.transition n).cartesian.paste_vert
    (IsPullback.of_vert_isIso ⟨baseSpecMap_comp_towerRingHom X ξ σ n⟩)

/-- The residue map of the base of `ξ_0`, read on the bottom thickening of the formal disc, is the
constant coefficient. -/
theorem residueMap_comp_towerRingHom_zero :
    (Deformation.Artin.residueMap (ξ.level 0).base).comp (towerRingHom X ξ σ 0) =
      quotientConstantCoeff k := by
  ext a
  change (ξ.level 0).base.residueEquiv (IsLocalRing.residue _
      ((towerBaseHom X ξ σ 0).hom (Ideal.Quotient.mk (truncIdeal k 0) a))) =
    PowerSeries.constantCoeff a
  exact ((towerBaseHom X ξ σ 0).residue_comm (Ideal.Quotient.mk (truncIdeal k 0) a)).trans
    ((AdicTruncation.residueEquiv_residue_mk (powerSeriesObject k) 0 a).trans
      (powerSeriesResidueEquiv_residue k a))

include σ in
/-- The closed point of the spectrum of the base of `ξ_0` is an isomorphism, that is, the base of
`ξ_0` is the residue field `k`. -/
theorem isIso_residueSpecMap_level_zero : IsIso (residueSpecMap (ξ.level 0).base) := by
  have hq : Function.Bijective (quotientConstantCoeff k) :=
    ⟨fun a b h => by
      rw [← algebraMap_quotientConstantCoeff k a, ← algebraMap_quotientConstantCoeff k b, h],
     fun c => ⟨_, quotientConstantCoeff_algebraMap k c⟩⟩
  have hr : Function.Bijective (Deformation.Artin.residueMap (ξ.level 0).base) := by
    rw [← Function.Bijective.of_comp_iff _ (bijective_towerRingHom X ξ σ 0), ← RingHom.coe_comp,
      residueMap_comp_towerRingHom_zero]
    exact hq
  have : IsIso (CommRingCat.ofHom (Deformation.Artin.residueMap (ξ.level 0).base)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hr
  exact inferInstanceAs (IsIso (Spec.map _))

/-- **The special fibre of the tower is `X`.** -/
theorem exists_iso_towerHom_zero :
    ∃ e₀ : X.left ≅ (ξ.level 0).scheme,
      e₀.hom ≫ towerHom X ξ σ 0 ≫
          Spec.map (CommRingCat.ofHom (algebraMap k (PowerSeries k ⧸ discIdeal k ^ (0 + 1)))) =
        X.hom := by
  have := isIso_residueSpecMap_level_zero X ξ σ
  have hiso : IsIso (ξ.level 0).specialMap :=
    (ξ.level 0).specialCartesian.isIso_fst_of_isIso
  refine ⟨asIso (ξ.level 0).specialMap, ?_⟩
  rw [asIso_hom, towerHom, ← Category.assoc, ← Category.assoc,
    (ξ.level 0).specialCartesian.w, Category.assoc, Category.assoc]
  conv_rhs => rw [← Category.comp_id X.hom]
  congr 1
  rw [residueSpecMap, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext c
  change (Deformation.Artin.residueMap (ξ.level 0).base)
      (towerRingHom X ξ σ 0 (algebraMap k _ c)) = c
  rw [← RingHom.comp_apply, residueMap_comp_towerRingHom_zero, quotientConstantCoeff_algebraMap]

/-- The closed point of the spectrum of an object of `𝒞_k` is a thickening of finite order. -/
theorem isFiniteOrderThickening_residueSpecMap (A : ArtinianLocalAlgCat.{u, u, u} k k) :
    Stacks.Thickenings.IsFiniteOrderThickening (residueSpecMap A) := by
  have hA : IsNoetherianRing Γ(baseSpec A, ⊤) :=
    isNoetherianRing_of_ringEquiv _
      (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm
  exact Stacks.Thickenings.isFiniteOrderThickening_of_isThickening_of_isNoetherianRing
    ⟨residueSpecMap_isClosedImmersion A, residueSpecMap_surjective A⟩ hA

/-- **Each member of the tower is locally of finite type over its thickening** when `X` is locally
of finite type over `k`: local finite type ascends along the cartesian square of the special
fibre ([Stacks, Tag 09ZW]). -/
theorem locallyOfFiniteType_towerHom [LocallyOfFiniteType X.hom] (n : ℕ) :
    LocallyOfFiniteType (towerHom X ξ σ n) := by
  have h := (Stacks.Thickenings.locallyOfFiniteType_iff_of_isFiniteOrderThickening
    (ξ.level n).specialMap (residueSpecMap (ξ.level n).base) X.hom (ξ.level n).toBase
    (isFiniteOrderThickening_residueSpecMap _) (ξ.level n).specialCartesian).mp inferInstance
  unfold towerHom
  infer_instance

end Tower

end Deformation.Examples.Smoothing

end
