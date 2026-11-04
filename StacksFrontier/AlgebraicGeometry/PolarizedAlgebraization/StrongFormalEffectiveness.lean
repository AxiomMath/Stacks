module

public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.Algebraization
import StacksCore.Tactic.StacksAttribute

/-!
# Strong formal effectiveness for polarized schemes

[Stacks, Tag 0D4T]: let `(R_n)` be an inverse system of rings with surjective transition maps
whose kernels are locally nilpotent, `R = lim R_n`, and `X_n ⟶ Spec R_n` proper, flat and of
finite presentation with cartesian transition squares `i_n : X_n ⟶ X_{n + 1}`, together with
invertible `ℒ_n` and isomorphisms `φ_n : i_n^* ℒ_{n + 1} ≅ ℒ_n`, `ℒ_0` ample. Then there is a
proper, flat, finitely presented `X ⟶ Spec R` with an ample invertible `ℒ`, and identifications
`X_n ≅ X ×_{Spec R} Spec R_n` and `ℒ|_{X_n} ≅ ℒ_n` compatible with the `i_n` and `φ_n`.

The index `n : ℕ` stands for the source's `n + 1`.

## Main results

* `Stacks.PolarizedAlgebraization.exists_algebraization`: a compatible system of proper, flat,
  finitely presented polarized schemes over `Spec R_n` with `ℒ_0` ample algebraizes to a proper,
  flat, finitely presented scheme over `Spec R` with an ample invertible sheaf.

## References

* [Stacks Project, Tag 0D4T](https://stacks.math.columbia.edu/tag/0D4T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ProjectiveDeformation
open Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily
open Stacks.AlgebraicGeometry.Tag07ZGTwist
open Stacks.Ample (IsAmple IsInvertibleModule)

universe u

namespace Stacks.PolarizedAlgebraization

namespace PolarizedTower

variable (T : PolarizedTower.{u})

/-- `lim Γ(Spec R_n, 𝒪) ≅ lim R_n`. -/
def limitGlobalRingIso : limit T.globalRing ≅ limit T.R :=
  HasLimit.isoOfNatIso (Functor.isoWhiskerLeft T.R Scheme.SpecΓIdentity ≪≫ Functor.rightUnitor T.R)

/-- Under `limitGlobalRingIso`, the map `lim Γ(Spec R_m, 𝒪) ⟶ R_n` is the limit projection
`lim R_m ⟶ R_n`. -/
theorem limitGlobalRingIso_inv_levelMap (n : ℕ) :
    T.limitGlobalRingIso.inv ≫ T.levelMap n = limit.π T.R (op n) := by
  ext x
  have h := congrArg (fun φ => φ.hom x) (HasLimit.isoOfNatIso_inv_π
    (Functor.isoWhiskerLeft T.R Scheme.SpecΓIdentity ≪≫ Functor.rightUnitor T.R) (op n))
  refine (congrArg (Scheme.ΓSpecIso (T.R.obj (op n))).hom.hom h).trans ?_
  exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (T.R.obj (op n))) _

/-- **Strong formal effectiveness for a polarized tower.** There are a proper, flat, finitely
presented `X ⟶ Spec (lim R_n)`, an ample invertible `ℒ` on `X`, cartesian squares through
`j_n : X_n ⟶ X` over `Spec R_n ⟶ Spec (lim R_n)`, and isomorphisms `e_n : ℒ|_{X_n} ≅ ℒ_n`
compatible with the `i_n` and the `φ_n`. -/
theorem exists_algebraization_of_tower :
    ∃ (X : Scheme.{u}) (g : X ⟶ Spec (limit T.R)) (ℒ : X.Modules) (_ : IsInvertibleModule X ℒ)
      (j : ∀ n : ℕ, T.X n ⟶ X) (hj : ∀ n : ℕ, T.i n ≫ j (n + 1) = j n)
      (e : ∀ n : ℕ, (Scheme.Modules.pullback (j n)).obj ℒ ⟶ T.L n),
      IsProper g ∧ Flat g ∧ _root_.AlgebraicGeometry.FinitePresentation g ∧ IsAmple X ℒ ∧
      (∀ n : ℕ, IsPullback (j n) (T.f n) g (Spec.map (limit.π T.R (op n)))) ∧
      (∀ n : ℕ, IsIso (e n)) ∧
      ∀ n : ℕ, (Scheme.Modules.pullbackComp (T.i n) (j (n + 1))).hom.app ℒ ≫
          (Scheme.Modules.pullbackCongr (hj n)).hom.app ℒ ≫ e n =
        (Scheme.Modules.pullback (T.i n)).map (e (n + 1)) ≫ (T.φ n).hom := by
  obtain ⟨d₀, hd₀, hD, hφ⟩ := exists_uniform_degreeBound_functorial T.family
  have hiso : ∀ (n : ℕ) (k : ℤ),
      IsIso ((AdmissibleDeformation.algebraPullbackHom (T.deformationHom n) d₀ hd₀).app k) :=
    fun n => (hφ _ _ (T.deformationHom n)).fst
  have hθ : ∀ n : ℕ, IsIso ((T.deformation n).canonicalTwistMap d₀ hd₀) :=
    fun n => (hD (T.deformation n)).2.2.2.2.1
  have hT : (T.tow d₀ hd₀).IsAdmissible :=
    T.isAdmissible_sectionTower d₀ hd₀ (fun n => (hD (T.deformation n)).2.1)
      (fun n => (hD (T.deformation n)).2.2.1.2.2 ⊤ (isAffineOpen_top _)) hiso
  have := T.isInvertibleModule_limitTwist d₀ hd₀ hT hθ
  have hinv := isInvertibleModule_relativeTwist_one (T.tow d₀ hd₀).limGrading
  have hample := isAmple_relativeTwist_one (T.tow d₀ hd₀).limGrading
    (T.isAmple_limitTwist d₀ hd₀ hT hθ)
  have := T.isProper_toBase d₀ hd₀ hT
  have := T.flat_toBase d₀ hd₀ hT
  obtain ⟨h1, h2, h3⟩ := T.finitePresentation_toBase d₀ hd₀ hT
  refine ⟨(relativeProj (T.limitAlgebra d₀ hd₀)).scheme,
    (relativeProj (T.limitAlgebra d₀ hd₀)).toBase ≫ Spec.map T.limitGlobalRingIso.inv,
    (twistAlgebra (T.limitAlgebra d₀ hd₀)).piece 1, hinv, T.levelInclusion d₀ hd₀ hT,
    T.i_comp_levelInclusion d₀ hd₀ hT hiso, T.levelTwistMor d₀ hd₀ hT, inferInstance,
    inferInstance, ⟨inferInstance, inferInstance, inferInstance⟩, hample, fun n => ?_,
    T.isIso_levelTwistMor d₀ hd₀ hT hθ, T.levelTwistMor_compat d₀ hd₀ hT hiso⟩
  have hsq : IsPullback (𝟙 _) (relativeProj (T.limitAlgebra d₀ hd₀)).toBase
      ((relativeProj (T.limitAlgebra d₀ hd₀)).toBase ≫ Spec.map T.limitGlobalRingIso.inv)
      (Spec.map T.limitGlobalRingIso.inv) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp]⟩
  have h := (T.isPullback_levelInclusion d₀ hd₀ hT n).paste_horiz hsq
  rwa [Category.comp_id, levelBase, ← Spec.map_comp, limitGlobalRingIso_inv_levelMap] at h

end PolarizedTower

/-- **Strong formal effectiveness for polarized schemes.** Let `(R_n)` be an inverse system of
rings with surjective transition maps whose kernels are locally nilpotent, and `R = lim R_n`. Let
`X_n ⟶ Spec R_n` be schemes with cartesian squares over the transitions
`Spec R_n ⟶ Spec R_{n + 1}`, `ℒ_n` invertible `𝒪_{X_n}`-modules and `φ_n : i_n^* ℒ_{n + 1} ≅ ℒ_n`.
If every `X_n ⟶ Spec R_n` is proper, flat and of finite presentation, and `ℒ_0` is ample, then
there are a proper, flat, finitely presented `X ⟶ Spec R`, an ample invertible `ℒ` on `X`,
identifications `X_n ≅ X ×_{Spec R} Spec R_n` (cartesian squares through `j_n : X_n ⟶ X`) and
isomorphisms `e_n : ℒ|_{X_n} ≅ ℒ_n`, compatible with the `i_n` and the `φ_n`. The index `n : ℕ`
stands for the source's `n + 1`. -/
@[stacks 0D4T, sga "7 IX 7.1.3" "partial"]
theorem exists_algebraization (R : ℕᵒᵖ ⥤ CommRingCat.{u})
    (hsurj : ∀ n : ℕ, Function.Surjective (R.map (homOfLE (Nat.le_succ n)).op).hom)
    (hnil : ∀ n : ℕ,
      RingHom.ker (R.map (homOfLE (Nat.le_succ n)).op).hom ≤ nilradical (R.obj (op (n + 1))))
    (X : ℕ → Scheme.{u}) (f : ∀ n : ℕ, X n ⟶ Spec (R.obj (op n)))
    (i : ∀ n : ℕ, X n ⟶ X (n + 1))
    (hpb : ∀ n : ℕ,
      IsPullback (i n) (f n) (f (n + 1)) (Spec.map (R.map (homOfLE (Nat.le_succ n)).op)))
    (L : ∀ n : ℕ, (X n).Modules) [hL : ∀ n : ℕ, IsInvertibleModule (X n) (L n)]
    (φ : ∀ n : ℕ, (Scheme.Modules.pullback (i n)).obj (L (n + 1)) ≅ L n)
    [hproper : ∀ n : ℕ, IsProper (f n)] [hflat : ∀ n : ℕ, Flat (f n)]
    (hfp : ∀ n : ℕ, _root_.AlgebraicGeometry.FinitePresentation (f n))
    (hample : IsAmple (X 0) (L 0)) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (limit R)) (ℒ : Y.Modules) (_ : IsInvertibleModule Y ℒ)
      (j : ∀ n : ℕ, X n ⟶ Y) (hj : ∀ n : ℕ, i n ≫ j (n + 1) = j n)
      (e : ∀ n : ℕ, (Scheme.Modules.pullback (j n)).obj ℒ ⟶ L n),
      IsProper g ∧ Flat g ∧ _root_.AlgebraicGeometry.FinitePresentation g ∧ IsAmple Y ℒ ∧
      (∀ n : ℕ, IsPullback (j n) (f n) g (Spec.map (limit.π R (op n)))) ∧
      (∀ n : ℕ, IsIso (e n)) ∧
      ∀ n : ℕ, (Scheme.Modules.pullbackComp (i n) (j (n + 1))).hom.app ℒ ≫
          (Scheme.Modules.pullbackCongr (hj n)).hom.app ℒ ≫ e n =
        (Scheme.Modules.pullback (i n)).map (e (n + 1)) ≫ (φ n).hom :=
  PolarizedTower.exists_algebraization_of_tower
    { R := R
      surjective := hsurj
      ker_le_nilradical := hnil
      X := X
      f := f
      i := i
      isPullback := hpb
      L := L
      invertible := hL
      φ := φ
      isProper := hproper
      flat := hflat
      finitePresentation := hfp
      isAmple := hample }

end Stacks.PolarizedAlgebraization

end
