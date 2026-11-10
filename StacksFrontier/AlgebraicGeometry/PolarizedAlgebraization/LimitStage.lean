module

public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.SectionTower
public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.SpecGradedAlgebra
public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.TwistTransition
public import StacksFrontier.RingTheory.GradedTowerLimit.BaseChange
public import StacksFrontier.RingTheory.GradedTowerLimit.FinitePresentation

/-!
# The algebraization of a polarized tower: the relative `Proj` over the limit

Let `(X_n ⟶ Spec R_n, ℒ_n)` be a polarized tower and `A_n = Γ(Spec R_n, 𝒜'_n)` the graded rings of
global sections of its truncated section algebras (`PolarizedTower.sectionTower`). Their graded
inverse limit `B` is a graded algebra over `R = lim Γ(Spec R_n, 𝒪)`, and `𝓑 = B̃` is a
quasi-coherent graded algebra on `Spec R`. This file builds, for every level, the homomorphism
`ψ_n : (Spec R_n ⟶ Spec R)^* 𝓑 ⟶ 𝒜'_n` (an isomorphism), the morphism
`c'_n : Proj_{R_n}(𝒜'_n) ⟶ Proj_R(𝓑)`, and proves that the `c'_n` are compatible with the
transitions of the tower, on the schemes and on the Serre twists.

## Main definitions

* `Stacks.PolarizedAlgebraization.PolarizedTower.limitAlgebra`: `𝓑` on `Spec R`.
* `Stacks.PolarizedAlgebraization.PolarizedTower.levelMap`: the ring map `R ⟶ R_n`.
* `Stacks.PolarizedAlgebraization.PolarizedTower.levelHom`: `ψ_n`.

## References

* [Stacks Project, Tag 0D4T](https://stacks.math.columbia.edu/tag/0D4T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.ProjectiveDeformation
open Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily
open scoped TensorProduct Stacks.GradedTowerLimit

universe u

namespace Stacks.PolarizedAlgebraization

namespace PolarizedTower

variable (T : PolarizedTower.{u}) (d₀ : ℕ) (hd₀ : 0 < d₀)

/-- The tower of graded rings of global sections. -/
abbrev tow : Stacks.GradedTowerLimit.GradedTower T.globalRing := T.sectionTower d₀ hd₀

/-- **`𝓑 = B̃`**, for `B` the graded inverse limit of the tower of global sections. -/
abbrev limitAlgebra : SheafGradedAlgebra (Spec (limit T.globalRing)) :=
  specSheafGradedAlgebra (T.tow d₀ hd₀).limGrading

/-- The ring map `R = lim Γ(Spec R_m, 𝒪) ⟶ R_n`. -/
def levelMap (n : ℕ) : limit T.globalRing ⟶ T.R.obj (op n) :=
  limit.π T.globalRing (op n) ≫ (Scheme.ΓSpecIso (T.R.obj (op n))).hom

/-- The projection `B ⟶ A_n`, as a homomorphism of graded rings. -/
def levelProj (n : ℕ) : (T.tow d₀ hd₀).limGrading →+*ᵍ (T.alg d₀ hd₀ n).grading ⊤ where
  __ := (T.tow d₀ hd₀).proj n
  map_mem hx := (T.tow d₀ hd₀).proj_mem n hx

/-- `levelProj` agrees with the projection `B ⟶ A_n` of the tower. -/
theorem levelProj_apply (n : ℕ) (b : (T.tow d₀ hd₀).Lim) :
    T.levelProj d₀ hd₀ n b = (T.tow d₀ hd₀).proj n b := rfl

/-- The inverse of `Γ(Spec R_n) ≅ R_n` sends the image of `r ∈ R` in `R_n` to its image in
`Γ(Spec R_n)`. -/
private theorem inv_levelMap (n : ℕ) (r : (limit T.globalRing : CommRingCat.{u})) :
    (Scheme.ΓSpecIso (T.R.obj (op n))).inv (T.levelMap n r) =
      (limit.π T.globalRing (op n)).hom r :=
  Iso.hom_inv_id_apply (Scheme.ΓSpecIso (T.R.obj (op n))) ((limit.π T.globalRing (op n)).hom r)

/-- `levelProj` sends the image of `r ∈ R` in `B` to the image of `r` under `R ⟶ R_n` in `A_n`. -/
theorem levelProj_algebraMap (n : ℕ) (r : (limit T.globalRing : CommRingCat.{u})) :
    T.levelProj d₀ hd₀ n (algebraMap _ _ r) =
      (T.alg d₀ hd₀ n).strHom ⊤ ((Scheme.ΓSpecIso (T.R.obj (op n))).inv (T.levelMap n r)) := by
  rw [inv_levelMap, levelProj_apply, Stacks.GradedTowerLimit.GradedTower.proj_algebraMap]
  rfl

/-- **`ψ_n : (Spec R_n ⟶ Spec R)^* 𝓑 ⟶ 𝒜'_n`**, the homomorphism of graded algebras which on
global sections is the projection `B ⟶ A_n`. -/
def levelHom (n : ℕ) :
    SheafGradedAlgebraHom ((T.limitAlgebra d₀ hd₀).pullback (Spec.map (T.levelMap n)))
      (T.alg d₀ hd₀ n) :=
  specGradedHom (T.tow d₀ hd₀).limGrading (T.levelMap n) (T.alg d₀ hd₀ n) (T.levelProj d₀ hd₀ n)
    (T.levelProj_algebraMap d₀ hd₀ n)

/-- **`ψ_n` is an isomorphism in every degree**, for an admissible tower: the base change of
`B` to `R_n` is `A_n`. -/
theorem isIso_levelHom_app (hT : (T.tow d₀ hd₀).IsAdmissible) (n : ℕ) (k : ℤ) :
    IsIso ((T.levelHom d₀ hd₀ n).app k) := by
  refine isIso_specGradedHom_app _ _ _ _ _ (fun d => ?_) k
  let := (T.levelMap n).hom.toAlgebra
  obtain ⟨-, -, he⟩ := (T.tow d₀ hd₀).finite_projective_baseChange_piece hT d
  obtain ⟨e, he⟩ := he n
  let iR := Scheme.ΓSpecIso (T.R.obj (op n))
  let eR : T.R.obj (op n) ≃ₗ[(limit T.globalRing : CommRingCat.{u})] T.globalRing.obj (op n) :=
    { iR.commRingCatIsoToRingEquiv.symm with
      map_smul' := fun r s => by
        change iR.inv (T.levelMap n r * s) =
          (show Γ(Spec (T.R.obj (op n)), ⊤) from (limit.π T.globalRing (op n)).hom r) * iR.inv s
        rw [map_mul]
        congr 1
        exact T.inv_levelMap n r }
  let T1 := TensorProduct.congr eR ((T.tow d₀ hd₀).limGradingEquiv d).symm
  let φ3 : (T.tow d₀ hd₀).𝒜 n d → Γ((T.alg d₀ hd₀ n).piece (d : ℤ), ⊤) :=
    fun x => (show (T.alg d₀ hd₀ n).sectionRing ⊤ from x.1) d
  have hφ3 : Function.Bijective φ3 := by
    refine ⟨fun x y hxy => ?_, fun y => ⟨⟨DirectSum.of _ d y, ⟨y, rfl⟩⟩, by simp [φ3]⟩⟩
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    simp only [φ3, DirectSum.of_eq_same] at hxy
    rw [hxy]
  have heq : ⇑(pieceBaseChangeMap (T.tow d₀ hd₀).limGrading (T.levelMap n) (T.alg d₀ hd₀ n)
      (T.levelProj d₀ hd₀ n) (T.levelProj_algebraMap d₀ hd₀ n) d) = φ3 ∘ e ∘ T1 := by
    funext x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      refine (AddMonoidHom.map_add _ x y).trans ?_
      rw [hx, hy]
      change _ = φ3 (e (T1 (x + y)))
      rw [T1.map_add, e.map_add]
      rfl
    | tmul s b =>
      have h3 : ∀ (a : T.globalRing.obj (op n)) (w : (T.tow d₀ hd₀).𝒜 n d),
          φ3 (a • w) = (show Γ(Spec (T.R.obj (op n)), ⊤) from a) • φ3 w := fun a w =>
        SheafGradedAlgebra.strHom_mul_apply (T.alg d₀ hd₀ n) ⊤ a
          (show (T.alg d₀ hd₀ n).sectionRing ⊤ from w.1) d
      have h4 : ((T.tow d₀ hd₀).pieceProj d n (((T.tow d₀ hd₀).limGradingEquiv d).symm b) :
          (T.tow d₀ hd₀).A n) = T.levelProj d₀ hd₀ n (b : (T.tow d₀ hd₀).Lim) := by
        rw [levelProj_apply, Stacks.GradedTowerLimit.GradedTower.coe_pieceProj,
          ← Stacks.GradedTowerLimit.GradedTower.proj_of]
        exact congrArg _ (congrArg Subtype.val
          (((T.tow d₀ hd₀).limGradingEquiv d).apply_symm_apply b))
      have h5 : φ3 ((T.tow d₀ hd₀).pieceProj d n (((T.tow d₀ hd₀).limGradingEquiv d).symm b)) =
          (show (T.alg d₀ hd₀ n).sectionRing ⊤ from
            T.levelProj d₀ hd₀ n (b : (T.tow d₀ hd₀).Lim)) d :=
        congrArg (fun z : (T.tow d₀ hd₀).A n =>
          (show (T.alg d₀ hd₀ n).sectionRing ⊤ from z) d) h4
      refine Eq.trans ?_ (congrArg φ3 (he (eR s) (((T.tow d₀ hd₀).limGradingEquiv d).symm b))).symm
      refine Eq.trans ?_ (h3 _ _).symm
      exact (congrArg (fun z => iR.inv s • z) h5.symm)
  rw [heq]
  exact hφ3.comp (e.bijective.comp T1.bijective)

end PolarizedTower

end Stacks.PolarizedAlgebraization

end
