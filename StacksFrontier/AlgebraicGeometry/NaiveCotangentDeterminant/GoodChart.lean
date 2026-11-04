module

public import StacksFrontier.AlgebraicGeometry.NaiveCotangentDeterminant.Charts
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentFlatAlgebraBaseChangeStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Good charts over a commutative square with an open immersion into the fibre product

Let

```
Y' --b--> Y
|         |
f'        f
v         v
X' --a--> X
```

be a commutative square of schemes whose comparison map `Y' ⟶ X' ×_X Y` is an open immersion,
with `f` syntomic. Given a chart `(U, V)` of `f` and a point `y'` of `Y'` over `V`, this file
produces, inside any prescribed neighbourhood of `y'`, a chart `(U', V')` of `f'` over `(U, V)`
whose square of rings is good for the naive cotangent complex
(`AlgebraicGeometry.Scheme.Hom.IsGoodChartSquare`).

## Main results

* `AlgebraicGeometry.IsAffineOpen.isLocalization_away_appLE_preimage_basicOpen`: the sections of
  an open immersion over the preimage of a basic open `D(g)` of an affine open, contained in its
  range, are the localization away from `g`.
* `AlgebraicGeometry.Scheme.Hom.exists_isGoodChartSquare`: good charts exist around every point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- Let `j : Y' ⟶ P` be an open immersion, `Z` an affine open of `P` and `g ∈ Γ(P, Z)` with
`D(g)` inside the range of `j`. Then `Γ(Y', j⁻¹ D(g))` is the localization of `Γ(P, Z)` away
from `g`, along `j.appLE`. -/
theorem IsAffineOpen.isLocalization_away_appLE_preimage_basicOpen {Y' P : Scheme.{u}}
    (j : Y' ⟶ P) [IsOpenImmersion j] {Z : P.Opens} (hZ : IsAffineOpen Z) (g : Γ(P, Z))
    (hg : P.basicOpen g ≤ j.opensRange) :
    letI := (j.appLE Z (j ⁻¹ᵁ P.basicOpen g) (j.preimage_mono (P.basicOpen_le g))).hom.toAlgebra
    IsLocalization.Away g Γ(Y', j ⁻¹ᵁ P.basicOpen g) := by
  have hloc := hZ.isLocalization_basicOpen g
  have := j.isIso_app _ hg
  have h := (IsLocalization.isLocalization_iff_of_ringEquiv (Submonoid.powers g)
    (asIso (j.app (P.basicOpen g))).commRingCatIsoToRingEquiv).mp hloc
  have e : (asIso (j.app (P.basicOpen g))).commRingCatIsoToRingEquiv.toRingHom.comp
      (algebraMap Γ(P, Z) Γ(P, P.basicOpen g)) =
      (j.appLE Z (j ⁻¹ᵁ P.basicOpen g) (j.preimage_mono (P.basicOpen_le g))).hom := by
    ext x
    show (P.presheaf.map (homOfLE (P.basicOpen_le g)).op ≫ j.app (P.basicOpen g)) x = _
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]
  rwa [e] at h

namespace Scheme.Hom

/-- **Good charts exist around every point.** Let `b ≫ f = f' ≫ a` be a commutative square of
schemes whose comparison map `Y' ⟶ X' ×_X Y` is an open immersion, with `f` syntomic. For every
chart `(U, V)` of `f`, every point `y'` of `Y'` over `V` and every open neighbourhood `W` of `y'`,
there is a chart `(U', V')` of `f'` over `(U, V)` with `y' ∈ V' ⊆ W` whose square of rings is good
for the naive cotangent complex. -/
theorem exists_isGoodChartSquare {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'}
    {a : X' ⟶ X} {b : Y' ⟶ Y} (w : b ≫ f = f' ≫ a) [IsOpenImmersion (pullback.lift b f' w)]
    (hf : Syntomic f) (U : X.affineOpens) (V : Y.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1)
    {y' : Y'} (hy : y' ∈ b ⁻¹ᵁ V.1) {W : Y'.Opens} (hyW : y' ∈ W) :
    ∃ (U' : X'.affineOpens) (V' : Y'.affineOpens) (e' : V'.1 ≤ f' ⁻¹ᵁ U'.1)
      (hU : U'.1 ≤ a ⁻¹ᵁ U.1) (hV : V'.1 ≤ b ⁻¹ᵁ V.1),
      IsGoodChartSquare f w e e' hU hV ∧ y' ∈ V'.1 ∧ V'.1 ≤ W := by
  set j := pullback.lift b f' w with hj
  have hfy : f' y' ∈ a ⁻¹ᵁ U.1 := by
    show a (f' y') ∈ U.1
    rw [← Scheme.Hom.comp_apply, ← w, Scheme.Hom.comp_apply]
    exact e hy
  obtain ⟨_, ⟨U', hU'aff, rfl⟩, hyU', hU'le⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open hfy (a ⁻¹ᵁ U.1).isOpen
  replace hU'le : U' ≤ a ⁻¹ᵁ U.1 := hU'le
  have H := IsPullback.of_hasPullback f a
  let Z : (pullback f a).Opens := pullback.fst f a ⁻¹ᵁ V.1 ⊓ pullback.snd f a ⁻¹ᵁ U'
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine V.1.toScheme := V.2
  have : IsAffine _ := hU'aff
  have hZ : IsAffineOpen Z := IsAffine.of_isPullback (Scheme.Hom.isPullback_resLE H hU'le e rfl)
  have hpush := (isIso_pushoutSection_iff H hU'le e (UY := Z) rfl).mp
    (isIso_pushoutSection_of_isAffineOpen H hU'le e rfl U.2 hU'aff V.2)
  have hjy : j y' ∈ Z := by
    refine ⟨?_, ?_⟩
    · show (pullback.fst f a) (j y') ∈ V.1
      rw [← Scheme.Hom.comp_apply, hj, pullback.lift_fst]
      exact hy
    · show (pullback.snd f a) (j y') ∈ U'
      rw [← Scheme.Hom.comp_apply, hj, pullback.lift_snd]
      exact hyU'
  let O : (pullback f a).Opens := j ''ᵁ (W ⊓ f' ⁻¹ᵁ U' ⊓ b ⁻¹ᵁ V.1)
  have hjyO : j y' ∈ O := ⟨y', ⟨⟨hyW, hyU'⟩, hy⟩, rfl⟩
  obtain ⟨g, hgO, hjg⟩ := hZ.exists_basicOpen_le ⟨j y', hjyO⟩ hjy
  have hgrange : (pullback f a).basicOpen g ≤ j.opensRange := hgO.trans (j.image_le_opensRange _)
  let V' : Y'.Opens := j ⁻¹ᵁ (pullback f a).basicOpen g
  have hV'aff : IsAffineOpen V' := (hZ.basicOpen g).preimage_of_isOpenImmersion j hgrange
  have hV'O : V' ≤ W ⊓ f' ⁻¹ᵁ U' ⊓ b ⁻¹ᵁ V.1 :=
    (j.preimage_mono hgO).trans (j.preimage_image_eq _).le
  have e' : V' ≤ f' ⁻¹ᵁ U' := hV'O.trans (inf_le_left.trans inf_le_right)
  have hV' : V' ≤ b ⁻¹ᵁ V.1 := hV'O.trans inf_le_right
  refine ⟨⟨U', hU'aff⟩, ⟨V', hV'aff⟩, e', hU'le, hV', ?_, hjg, hV'O.trans
    (inf_le_left.trans inf_le_left)⟩
  let := f.chartAlgebra e
  let := f'.chartAlgebra e'
  let := a.chartAlgebra hU'le
  let := b.chartAlgebra hV'
  let := squareAlgebra f' a hU'le e'
  have := isScalarTower_squareAlgebra_left hU'le e'
  have := f.isScalarTower_squareAlgebra_right w e hU'le hV' e'
  have : Algebra.Syntomic Γ(X, U.1) Γ(Y, V.1) := f.syntomic_chartAlgebra hf U V e
  let : Algebra Γ(Y, V.1) Γ(pullback f a, Z) := (pullback.fst f a).chartAlgebra inf_le_left
  let : Algebra Γ(X', U') Γ(pullback f a, Z) := (pullback.snd f a).chartAlgebra inf_le_right
  let : Algebra Γ(X, U.1) Γ(pullback f a, Z) :=
    (f.appLE U.1 V.1 e ≫ (pullback.fst f a).appLE V.1 Z inf_le_left).hom.toAlgebra
  have : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(pullback f a, Z) :=
    .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ(X, U.1) Γ(X', U') Γ(pullback f a, Z) :=
    .of_algebraMap_eq fun x => congr($(hpush.w).hom x)
  have : Algebra.IsPushout Γ(X, U.1) Γ(Y, V.1) Γ(X', U') Γ(pullback f a, Z) :=
    CommRingCat.isPushout_iff_isPushout.mp hpush
  have : Algebra.IsPushout Γ(X, U.1) Γ(X', U') Γ(Y, V.1) Γ(pullback f a, Z) := this.symm
  let ε := Algebra.IsPushout.equiv Γ(X, U.1) Γ(X', U') Γ(Y, V.1) Γ(pullback f a, Z)
  have hV'Z : V' ≤ j ⁻¹ᵁ Z := j.preimage_mono ((pullback f a).basicOpen_le g)
  let ψ := (j.appLE Z V' hV'Z).hom.comp ε.toRingEquiv.toRingHom
  have hLR : ψ.comp Algebra.TensorProduct.includeLeftRingHom = algebraMap Γ(X', U') Γ(Y', V') ∧
      ψ.comp Algebra.TensorProduct.includeRight.toRingHom = algebraMap Γ(Y, V.1) Γ(Y', V') := by
    refine ⟨?_, ?_⟩ <;> ext x <;>
    · simp only [ψ, ε, RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
        RingEquiv.toRingHom_eq_coe, AlgEquiv.coe_ringEquiv, Algebra.IsPushout.equiv_tmul,
        map_one, one_mul, mul_one, RingHom.algebraMap_toAlgebra]
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
      simp only [hj, pullback.lift_fst, pullback.lift_snd]
  let : Algebra Γ(pullback f a, Z) Γ(Y', V') := (j.appLE Z V' hV'Z).hom.toAlgebra
  have := hZ.isLocalization_away_appLE_preimage_basicOpen j g hgrange
  have hM : let := ψ.toAlgebra
      IsLocalization ((Submonoid.powers g).map ε.toRingEquiv.symm) Γ(Y', V') :=
    IsLocalization.isLocalization_of_base_ringEquiv (Submonoid.powers g) Γ(Y', V')
      ε.toRingEquiv.symm
  exact Stacks.NaiveCotangentFlatAlgebraBaseChangeStalk.isQuasiIso_of_localization_data ψ hLR.1
    hLR.2 _ hM

end Scheme.Hom

end AlgebraicGeometry
