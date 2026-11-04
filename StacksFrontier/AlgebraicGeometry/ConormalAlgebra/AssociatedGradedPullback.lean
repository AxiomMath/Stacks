module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Affine
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AssociatedGradedPackaging
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.PiecesBijective

/-!
# The pullback of the associated graded algebra, chart by chart

Let `ℐ` be a quasi-coherent ideal sheaf on a scheme `X` and let `g : Z ⟶ X` be a morphism of
schemes.  The pullback `g^*(⨁ₙ ℐⁿ/ℐⁿ⁺¹)` of the associated graded algebra of
`Stacks.Conormal.grGradedAlgebra` is a sheaf of graded algebras on `Z` by
`Stacks.Conormal.gradedPullback`.  This file describes it over an affine chart `V` of `X`: an
element of `ℐ(V)ⁿ` gives a degree-`n` section over `g⁻¹V`, and that assignment is additive,
linear over `Γ(X, V)` acting through `g`, compatible with restriction between charts, and turns
multiplication of ideal elements into the graded multiplication and `1` into the graded unit.

On a chart on which the preimage is affine and the functions surject with kernel `ℐ(V)` it is
moreover surjective with kernel exactly `ℐ(V)ⁿ⁺¹`.  This is the local description, on one chart,
of the second identity `𝒞_{Z/X,*} = i^{-1}(⨁ₙ ℐⁿ/ℐⁿ⁺¹)` of [Stacks, Tag 0633] part (1).

## Main definitions

* `Stacks.Conormal.grSection`: an element of `ℐ(V)ⁿ`, as a degree-`n` section of
  `⨁ₙ ℐⁿ/ℐⁿ⁺¹` over an affine open `V` — its class mod `ℐ(V)ⁿ⁺¹`.
* `Stacks.Conormal.grPullbackMap`: its pullback, a degree-`n` section of `g^*(⨁ₙ ℐⁿ/ℐⁿ⁺¹)` over
  `g⁻¹V`.

## Main results

* `Stacks.Conormal.grSection_restrict`, `_smul`, `_mul`, `_one`, `_eq_zero_iff` and
  `grSection_surjective`: the local description of `⨁ₙ ℐⁿ/ℐⁿ⁺¹` on an affine chart.
* `Stacks.Conormal.smul_top_eq_bot_grSection`: `ℐ(V)` annihilates the sections of `ℐⁿ/ℐⁿ⁺¹`
  over an affine open.
* `Stacks.Conormal.grPullbackMap_naturality`, `_smul`, `_mul`, `_one`: the same compatibilities
  for the pullback.
* `Stacks.Conormal.grPullbackMap_eq_zero_iff` and `grPullbackMap_surjective`: on a chart whose
  preimage is affine and on which the functions surject with kernel `ℐ(V)`, the degree-`n`
  sections of `g^*(⨁ₙ ℐⁿ/ℐⁿ⁺¹)` over `g⁻¹V` are `ℐ(V)ⁿ/ℐ(V)ⁿ⁺¹`.

## Implementation notes

`Stacks.Conormal.grSection` is `Stacks.Conormal.grPieceSectionsMk` with its source spelled
`↥(ℐ(V) ^ n)` rather than `↥(AssociatedGraded.power (ℐ(V)) n)`, transported along
`Stacks.Conormal.powEquivPower`.  The two submodules of `Γ(X, V)` are equal but not
definitionally so.

## References

* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.GabberColimit Stacks.AlgebraicGeometry.IdealPowerSmul

universe u

namespace Stacks.Conormal

/-! ### Local sections of the associated graded algebra -/

section Gr

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The function underlying the section of `ℐⁿ · 𝒪_X` that an element of the degree-`n` term of
the algebraic filtration gives is the element itself. -/
@[simp] theorem ambient_idealPowerSectionsEquiv (n : ℕ) (V : X.affineOpens)
    (x : ↥(AssociatedGraded.power (M := Γ(X, V.1)) (I.ideal V) n)) :
    ambient I n (idealPowerSectionsEquiv I n V x) = (x : Γ(X, V.1)) := rfl

/-- An element of `ℐ(V)ⁿ`, as a degree-`n` section of `⨁ₙ ℐⁿ/ℐⁿ⁺¹` over the affine open `V`: its
class mod `ℐ(V)ⁿ⁺¹`. -/
def grSection (n : ℕ) (V : X.affineOpens) : ↥(I.ideal V ^ n) →+ Γ(grPiece I n, V.1) :=
  (grPieceSectionsMk I n V).comp
    (powEquivPower (I.ideal V) n).toLinearMap.toAddMonoidHom

/-- `Stacks.Conormal.grSection` is `Stacks.Conormal.grPieceSectionsMk` composed with
`Stacks.Conormal.powEquivPower`. -/
theorem grSection_eq_grPieceSectionsMk (n : ℕ) (V : X.affineOpens)
    (a : ↥(I.ideal V ^ n)) :
    grSection I n V a = grPieceSectionsMk I n V (powEquivPower (I.ideal V) n a) := rfl

/-- `Stacks.Conormal.grSection` sends an element of `ℐ(V)ⁿ` to the image under `grPieceπ` of the
corresponding section of `ℐⁿ · 𝒪_X`. -/
theorem grSection_apply (n : ℕ) (V : X.affineOpens) (a : ↥(I.ideal V ^ n)) :
    grSection I n V a =
      (grPieceπ I n).val.app (op V.1)
        (idealPowerSectionsEquiv I n V (powEquivPower (I.ideal V) n a)) := rfl

/-- The function underlying the representative of `Stacks.Conormal.grSection` is the ideal
element itself. -/
@[simp] theorem ambient_grSection_rep (n : ℕ) (V : X.affineOpens) (a : ↥(I.ideal V ^ n)) :
    ambient I n (idealPowerSectionsEquiv I n V (powEquivPower (I.ideal V) n a)) =
      (a : Γ(X, V.1)) := rfl

/-- The class of an element of `ℐ(V)ⁿ` vanishes exactly when it lies in `ℐ(V)ⁿ⁺¹`. -/
theorem grSection_eq_zero_iff (n : ℕ) (V : X.affineOpens) (a : ↥(I.ideal V ^ n)) :
    grSection I n V a = 0 ↔ (a : Γ(X, V.1)) ∈ I.ideal V ^ (n + 1) := by
  rw [grSection_eq_grPieceSectionsMk,
    grPieceSectionsMk_eq_zero_iff I n V (powEquivPower (I.ideal V) n a),
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  show ((powEquivPower (I.ideal V) n a : _) : Γ(X, V.1)) ∈
    AssociatedGraded.power (M := Γ(X, V.1)) (I.ideal V) (n + 1) ↔ _
  rw [AssociatedGraded.ring_power_eq, coe_powEquivPower]

/-- Every degree-`n` section over an affine open comes from `ℐ(V)ⁿ`. -/
theorem grSection_surjective (n : ℕ) (V : X.affineOpens) :
    Function.Surjective (grSection I n V) :=
  (surjective_grPieceSectionsMk I n V).comp (powEquivPower (I.ideal V) n).surjective

/-- The local description is linear over the functions on the chart. -/
theorem grSection_smul (n : ℕ) (V : X.affineOpens) (r : Γ(X, V.1))
    (a : ↥(I.ideal V ^ n)) :
    grSection I n V (r • a) = r • grSection I n V a := by
  have h : idealPowerSectionsEquiv I n V (powEquivPower (I.ideal V) n (r • a)) =
      r • idealPowerSectionsEquiv I n V (powEquivPower (I.ideal V) n a) := by
    rw [map_smul, map_smul]
  rw [grSection_apply, grSection_apply, h]
  exact ((grPieceπ I n).val.app (op V.1)).hom.map_smul r _

/-- Sections of `ℐⁿ · 𝒪_X` with the same underlying function have the same image in `ℐⁿ/ℐⁿ⁺¹`. -/
private theorem grPieceπ_app_congr (n : ℕ) {U : X.Opens} {s t : Γ(idealPower I n, U)}
    (h : ambient I n s = ambient I n t) :
    (grPieceπ I n).val.app (op U) s = (grPieceπ I n).val.app (op U) t :=
  congrArg _ (ambient_injective I n h)

/-- The local descriptions are compatible with restriction between affine charts. -/
theorem grSection_restrict (n : ℕ) (V W : X.affineOpens) (h : W.1 ≤ V.1)
    (a : ↥(I.ideal V ^ n)) (b : ↥(I.ideal W ^ n))
    (hb : (b : Γ(X, W.1)) = X.presheaf.map (homOfLE h).op (a : Γ(X, V.1))) :
    (grPiece I n).val.map (homOfLE h).op (grSection I n V a) = grSection I n W b := by
  rw [grSection_apply, grSection_apply]
  refine (PresheafOfModules.naturality_apply (grPieceπ I n).val (homOfLE h).op
      (idealPowerSectionsEquiv I n V (powEquivPower (I.ideal V) n a))).symm.trans ?_
  exact grPieceπ_app_congr I n hb.symm

/-- The local description turns multiplication of ideal elements into the graded
multiplication. -/
theorem grSection_mul (n m : ℕ) (V : X.affineOpens) (a : ↥(I.ideal V ^ n))
    (b : ↥(I.ideal V ^ m)) (c : ↥(I.ideal V ^ (n + m)))
    (hc : (c : Γ(X, V.1)) = (a : Γ(X, V.1)) * (b : Γ(X, V.1))) :
    grSection I (n + m) V c =
      ((grGradedAlgebra I).mul (n : ℤ) (m : ℤ)).app (op V.1)
        (grSection I n V a) (grSection I m V b) := by
  rw [grSection_apply, grSection_apply, grSection_apply]
  refine Eq.trans ?_ (grGradedAlgebra_mul_app_π I n m (op V.1) _ _).symm
  exact grPieceπ_app_congr I (n + m) (by rw [ambient_grSection_rep, ambient_mulApp,
    ambient_grSection_rep, ambient_grSection_rep, hc])

/-- The degree-zero class of `1` is the graded unit. -/
theorem grSection_one (V : X.affineOpens) (a : ↥(I.ideal V ^ 0))
    (ha : (a : Γ(X, V.1)) = 1) :
    grSection I 0 V a = (grGradedAlgebra I).one.eval (op V.1) := by
  rw [grSection_apply, grGradedAlgebra_one_eval]
  exact grPieceπ_app_congr I 0 (by rw [ambient_grSection_rep, ambient_oneIdealPowerSection, ha])

/-- The ideal `ℐ(V)` annihilates the sections of `ℐⁿ/ℐⁿ⁺¹` over an affine open `V`. -/
theorem smul_top_eq_bot_grSection (n : ℕ) (V : X.affineOpens) :
    I.ideal V • (⊤ : Submodule Γ(X, V.1) Γ(grPiece I n, V.1)) = ⊥ := by
  refine le_antisymm (Submodule.smul_le.2 fun r hr x _ => ?_) bot_le
  obtain ⟨a, rfl⟩ := grSection_surjective I n V x
  rw [← grSection_smul]
  refine Submodule.mem_bot _ |>.2 ((grSection_eq_zero_iff I n V (r • a)).2 ?_)
  rw [SetLike.val_smul, smul_eq_mul, pow_succ']
  exact Ideal.mul_mem_mul hr a.2

end Gr

/-! ### Local sections of the pulled-back associated graded algebra -/

section GrPullback

variable {Z X : Scheme.{u}} (I : X.IdealSheafData) (g : Z ⟶ X)

/-- An element of `ℐ(V)ⁿ`, as a degree-`n` section of the pullback `g^*(⨁ₙ ℐⁿ/ℐⁿ⁺¹)` of the
associated graded algebra over the preimage of the affine open `V`. -/
def grPullbackMap (n : ℕ) (V : X.affineOpens) :
    ↥(I.ideal V ^ n) →+
      ((gradedPullback g (grGradedAlgebra I)).piece (n : ℤ)).val.obj (op (g ⁻¹ᵁ V.1)) :=
  (pullbackSectionAddHom g (grPiece I n) V.1).comp (grSection I n V)

/-- `Stacks.Conormal.grPullbackMap` is the pullback section of `Stacks.Conormal.grSection`. -/
theorem grPullbackMap_apply (n : ℕ) (V : X.affineOpens) (a : ↥(I.ideal V ^ n)) :
    grPullbackMap I g n V a =
      Scheme.Modules.pullbackSection g (grPiece I n) V.1 (g ⁻¹ᵁ V.1) le_rfl
        (grSection I n V a) := rfl

/-- On a chart with affine preimage on which the functions surject with kernel `ℐ(V)`, pulling
back sections of `ℐⁿ/ℐⁿ⁺¹` over `V` is bijective. -/
private theorem bijective_pullbackSectionAddHom_grPiece (n : ℕ) (V : X.affineOpens)
    (hV : IsAffineOpen (g ⁻¹ᵁ V.1)) (hker : RingHom.ker (g.app V.1).hom = I.ideal V)
    (hsurj : Function.Surjective (g.app V.1).hom) :
    Function.Bijective (pullbackSectionAddHom g (grPiece I n) V.1) :=
  bijective_pullbackSectionAddHom_of_smul_top_eq_bot g (grPiece I n) V.1 V.2 hV hsurj
    (by rw [hker]; exact smul_top_eq_bot_grSection I n V)

/-- On a chart with affine preimage on which the functions surject with kernel `ℐ(V)`, the kernel
of `Stacks.Conormal.grPullbackMap` in degree `n` is exactly `ℐ(V)ⁿ⁺¹`. -/
theorem grPullbackMap_eq_zero_iff (n : ℕ) (V : X.affineOpens)
    (hV : IsAffineOpen (g ⁻¹ᵁ V.1)) (hker : RingHom.ker (g.app V.1).hom = I.ideal V)
    (hsurj : Function.Surjective (g.app V.1).hom) (a : ↥(I.ideal V ^ n)) :
    grPullbackMap I g n V a = 0 ↔ (a : Γ(X, V.1)) ∈ I.ideal V ^ (n + 1) := by
  rw [← grSection_eq_zero_iff I n V a]
  exact (injective_iff_map_eq_zero' _).1
    (bijective_pullbackSectionAddHom_grPiece I g n V hV hker hsurj).1 (grSection I n V a)

/-- On a chart with affine preimage on which the functions surject with kernel `ℐ(V)`, every
degree-`n` section of the pullback over the preimage comes from `ℐ(V)ⁿ`. -/
theorem grPullbackMap_surjective (n : ℕ) (V : X.affineOpens)
    (hV : IsAffineOpen (g ⁻¹ᵁ V.1)) (hker : RingHom.ker (g.app V.1).hom = I.ideal V)
    (hsurj : Function.Surjective (g.app V.1).hom) :
    Function.Surjective (grPullbackMap I g n V) :=
  (bijective_pullbackSectionAddHom_grPiece I g n V hV hker hsurj).2.comp
    (grSection_surjective I n V)

/-- The local description commutes with restriction between affine charts. -/
theorem grPullbackMap_naturality (n : ℕ) (V W : X.affineOpens) (h : W.1 ≤ V.1)
    (hZ : g ⁻¹ᵁ W.1 ≤ g ⁻¹ᵁ V.1) (a : ↥(I.ideal V ^ n)) (b : ↥(I.ideal W ^ n))
    (hb : (b : Γ(X, W.1)) = X.presheaf.map (homOfLE h).op (a : Γ(X, V.1))) :
    ((gradedPullback g (grGradedAlgebra I)).piece (n : ℤ)).val.map (homOfLE hZ).op
        (grPullbackMap I g n V a) =
      grPullbackMap I g n W b :=
  (pullbackSection_restrict g (grPiece I n) h hZ (grSection I n V a)).trans
    (congrArg (Scheme.Modules.pullbackSection g (grPiece I n) W.1 (g ⁻¹ᵁ W.1) le_rfl)
      (grSection_restrict I n V W h a b hb))

/-- The local description is linear over the map on functions. -/
theorem grPullbackMap_smul (n : ℕ) (V : X.affineOpens) (r : Γ(X, V.1))
    (a : ↥(I.ideal V ^ n)) :
    grPullbackMap I g n V (r • a) =
      (show Z.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ V.1)) from (g.app V.1).hom r) •
        grPullbackMap I g n V a :=
  (congrArg (Scheme.Modules.pullbackSection g (grPiece I n) V.1 (g ⁻¹ᵁ V.1) le_rfl)
      (grSection_smul I n V r a)).trans
    (pullbackSection_smul g (grPiece I n) V.1 r (grSection I n V a))

/-- The local description turns multiplication of ideal elements into the graded
multiplication. -/
theorem grPullbackMap_mul (n m : ℕ) (V : X.affineOpens) (a : ↥(I.ideal V ^ n))
    (b : ↥(I.ideal V ^ m)) (c : ↥(I.ideal V ^ (n + m)))
    (hc : (c : Γ(X, V.1)) = (a : Γ(X, V.1)) * (b : Γ(X, V.1))) :
    grPullbackMap I g (n + m) V c =
      ((gradedPullback g (grGradedAlgebra I)).mul (n : ℤ) (m : ℤ)).app
          (op (g ⁻¹ᵁ V.1)) (grPullbackMap I g n V a) (grPullbackMap I g m V b) :=
  (congrArg
      (Scheme.Modules.pullbackSection g ((grGradedAlgebra I).piece ((n : ℤ) + (m : ℤ)))
        V.1 (g ⁻¹ᵁ V.1) le_rfl)
      (grSection_mul I n m V a b c hc)).trans
    (gradedPullback_mul_pullbackSection g (grGradedAlgebra I) (n : ℤ) (m : ℤ) V.1
      (grSection I n V a) (grSection I m V b)).symm

/-- The local description sends `1` to the graded unit. -/
theorem grPullbackMap_one (V : X.affineOpens) (a : ↥(I.ideal V ^ 0))
    (ha : (a : Γ(X, V.1)) = 1) :
    grPullbackMap I g 0 V a =
      (gradedPullback g (grGradedAlgebra I)).one.eval (op (g ⁻¹ᵁ V.1)) :=
  (congrArg (Scheme.Modules.pullbackSection g ((grGradedAlgebra I).piece (0 : ℤ)) V.1
        (g ⁻¹ᵁ V.1) le_rfl)
      (grSection_one I V a ha)).trans
    (gradedPullback_one_eval g (grGradedAlgebra I) V.1).symm

/-- The pulled-back associated graded algebra is concentrated in nonnegative degrees. -/
theorem gradedPullback_grGradedAlgebra_negative_isZero (n : ℤ) (hn : n < 0) :
    Limits.IsZero ((gradedPullback g (grGradedAlgebra I)).piece n) :=
  gradedPullback_negative_isZero g (grGradedAlgebra I)
    (fun m hm => grGradedAlgebra_negative_isZero I m hm) n hn

end GrPullback

end Stacks.Conormal

end
