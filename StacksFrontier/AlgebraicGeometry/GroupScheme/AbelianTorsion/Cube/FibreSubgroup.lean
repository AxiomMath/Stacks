module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.CubeRelation

/-!
# The cube class of an invertible module, and the points over which it vanishes

Let `A` be a group scheme over a field `k` and `L` an invertible `𝒪_A`-module. For a scheme `B`
over `k` and morphisms `f, g, t : B ⟶ A`, write `Φ(h)` for the class of `h^*L` in `Pic(B)` and

`D_L(f, g, t) = Φ(f + g + t) + Φ(f) + Φ(g) + Φ(t) - Φ(f + g) - Φ(f + t) - Φ(g + t)`,

the group law of `A` being written multiplicatively in the group `B ⟶ A`. The cube relation of
[Stacks, Tag 0BFE](https://stacks.math.columbia.edu/tag/0BFE) says that `D_L` vanishes on the
three coordinates of `A × A × A`, and `D_L(f, g, t)` is the class of the pullback of the module
`Stacks.Groupoids.cubeModule` along `(f, g, t)`.

This file is the Picard-group algebra of the proof of the theorem of the cube over an
algebraically closed field (step 2 of the cube proof). For a `k`-point `a` of `A`, say that
the cube class of `L` vanishes at `a` when `D_L(f, g, a) = 0` for all `B, f, g` (`a` read as the
constant morphism `B ⟶ Spec k ⟶ A`); equivalently, the cube module of `L` is trivial on the
fibre `A × A × {a}`.

## Main definitions

* `Stacks.Groupoids.cubeClass`: the class `D_L(f, g, t)`.
* `Stacks.Groupoids.IsCubeTrivialAt`: the cube class of `L` vanishes at the `k`-point `a`.

## Main results

* `Stacks.Groupoids.pullbackPicardClass_cubeModule_eq_cubeClass`: `D_L(f, g, t)` is the class of
  the pullback of the cube module along `(f, g, t)`.
* `Stacks.Groupoids.cubeClass_comp_eq_zero`: the vanishing of `D_L(f, g, t)` is inherited by
  `D_L(f ∘ ψ, g ∘ ψ, t ∘ ψ)`.
* `Stacks.Groupoids.isCubeTrivialAt_one` and `Stacks.Groupoids.IsCubeTrivialAt.mul`: the
  `k`-points at which the cube class vanishes contain the unit and are closed under the group law
  (for `A` commutative).
* `Stacks.Groupoids.cubeClass_translate`: if the cube class of `L` vanishes at `a`, then
  `D_{t_a^*L}(h₁, h₂, h₃) = D_L(h₁, h₂, h₃ + a)`, for the translation `t_a = 𝟙 + a`.

## Implementation notes

Everything is an identity in the Picard group, by `abel`, after the morphisms inside `Φ` have been
put in a normal form in the commutative group `B ⟶ A`. The identity behind closure under the group
law is `D(f, g, a + b) = D(f + b, g, a) + D(f, g, b) - D(g, a, b)`, valid for all `f, g, a, b`;
the class of the pullback along a constant morphism vanishes because the Picard group of the
spectrum of a field is trivial.

## References

* [Stacks Project, Tag 0BFE](https://stacks.math.columbia.edu/tag/0BFE)
* [Stacks Project, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules (schemeTensor picardClass pullbackPicardClass)
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]
  (L : SheafOfModules.{u} (structureSheafRing A.left.toRingedSpace))
  (hL : Stacks.SheafOfModules.IsInvertible A.left.presheaf A.left.ringCatIsSheaf L)

/-- **The cube class** `D_L(f, g, t)` in `Pic(B)`: the alternating sum of the classes of the
pullbacks of `L` along the seven sums of `f`, `g` and `t`. -/
noncomputable def cubeClass {B : Over (Spec (.of k))} (f g t : B ⟶ A) :
    Stacks.SheafOfModules.PicardGroup B.left.presheaf B.left.ringCatIsSheaf :=
  pullbackPicardClass (f * g * t).left L hL + pullbackPicardClass f.left L hL +
    pullbackPicardClass g.left L hL + pullbackPicardClass t.left L hL -
    pullbackPicardClass (f * g).left L hL - pullbackPicardClass (f * t).left L hL -
    pullbackPicardClass (g * t).left L hL

/-- The cube class `cubeClass L hL f g t` equals the alternating sum of the pullback classes
of `L` along `f * g * t`, `f`, `g`, `t`, `f * g`, `f * t` and `g * t`. -/
theorem cubeClass_def {B : Over (Spec (.of k))} (f g t : B ⟶ A) :
    cubeClass L hL f g t =
      pullbackPicardClass (f * g * t).left L hL + pullbackPicardClass f.left L hL +
        pullbackPicardClass g.left L hL + pullbackPicardClass t.left L hL -
        pullbackPicardClass (f * g).left L hL - pullbackPicardClass (f * t).left L hL -
        pullbackPicardClass (g * t).left L hL := rfl

omit [GrpObj A] in
/-- **The pullback class along a constant morphism vanishes.** The pullback of `L` along a
`k`-point is an invertible module on the spectrum of a field, hence trivial, and triviality is
inherited by a further pullback. -/
theorem pullbackPicardClass_toUnit_comp {B : Over (Spec (.of k))}
    (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    pullbackPicardClass (toUnit B ≫ a).left L hL = 0 := by
  have ha := isInvertible_pullbackOver a L hL
  have hatriv : Stacks.SheafOfModules.IsTrivial
      (𝟙_ (Over (Spec (.of k)))).left.presheaf (𝟙_ (Over (Spec (.of k)))).left.ringCatIsSheaf
      (pullbackOver a L) :=
    have := ha
    Stacks.PicardUFD.isTrivial_of_isInvertible_spec k _
  rw [Stacks.SheafOfModules.pullbackPicardClass_eq_zero_iff]
  exact ⟨(RingedSpaceModuleAdjunction.modulePullbackComp
      (toUnit B : B ⟶ 𝟙_ (Over (Spec (.of k)))).left.toLRSHom.toShHom
      a.left.toLRSHom.toShHom).app L ≪≫
    (modulePullback (toUnit B : B ⟶ 𝟙_ (Over (Spec (.of k)))).left.toLRSHom.toShHom).mapIso
      hatriv.some ≪≫
    modulePullbackObjUnitIso
      (toUnit B : B ⟶ 𝟙_ (Over (Spec (.of k)))).left.toLRSHom.toShHom⟩

/-- **The cube class is the class of the pullback of the cube module** along `(f, g, t)`, for any
choice of the three tensor inverses. -/
theorem pullbackPicardClass_cubeModule_eq_cubeClass
    (N₁₂ N₁₃ N₂₃ : SheafOfModules.{u} (structureSheafRing (cubeObj A).left.toRingedSpace))
    (h₁₂ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₂)
    (h₁₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₁₃)
    (h₂₃ : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N₂₃)
    (t₁₂ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₁ A * cubeProj₂ A) L) N₁₂))
    (t₁₃ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₁ A * cubeProj₃ A) L) N₁₃))
    (t₂₃ : Stacks.SheafOfModules.IsTrivial (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf (schemeTensor (cubeObj A).left
        (pullbackOver (cubeProj₂ A * cubeProj₃ A) L) N₂₃))
    {B : Over (Spec (.of k))} (φ : B ⟶ cubeObj A) :
    pullbackPicardClass φ.left (cubeModule A L N₁₂ N₁₃ N₂₃)
        (isInvertible_cubeModule A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃) =
      cubeClass L hL (φ ≫ cubeProj₁ A) (φ ≫ cubeProj₂ A) (φ ≫ cubeProj₃ A) := by
  rw [pullbackPicardClass_cubeModule_alternating A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃ t₁₂ t₁₃ t₂₃ φ,
    cubeClass_def]
  simp only [MonObj.comp_mul]
  abel

omit [GrpObj A] in
/-- The first coordinate of `(f, g, t) : B ⟶ A × A × A`. -/
@[simp] theorem lift_lift_cubeProj₁ {B : Over (Spec (.of k))} (f g t : B ⟶ A) :
    lift (lift f g) t ≫ cubeProj₁ A = f := by simp [cubeProj₁]

omit [GrpObj A] in
/-- The second coordinate of `(f, g, t) : B ⟶ A × A × A`. -/
@[simp] theorem lift_lift_cubeProj₂ {B : Over (Spec (.of k))} (f g t : B ⟶ A) :
    lift (lift f g) t ≫ cubeProj₂ A = g := by simp [cubeProj₂]

omit [GrpObj A] in
/-- The third coordinate of `(f, g, t) : B ⟶ A × A × A`. -/
@[simp] theorem lift_lift_cubeProj₃ {B : Over (Spec (.of k))} (f g t : B ⟶ A) :
    lift (lift f g) t ≫ cubeProj₃ A = t := by simp [cubeProj₃]

/-- **The vanishing of the cube class is inherited by pullback.** If `D_L(f, g, t) = 0` in
`Pic(B)` then `D_L(f ∘ ψ, g ∘ ψ, t ∘ ψ) = 0` in `Pic(C)` for every `ψ : C ⟶ B`: both are classes of
pullbacks of the cube module, the second along `(f, g, t) ∘ ψ`. -/
theorem cubeClass_comp_eq_zero {B C : Over (Spec (.of k))} {f g t : B ⟶ A}
    (h : cubeClass L hL f g t = 0) (ψ : C ⟶ B) :
    cubeClass L hL (ψ ≫ f) (ψ ≫ g) (ψ ≫ t) = 0 := by
  obtain ⟨N₁₂, h₁₂, t₁₂⟩ := Stacks.SheafOfModules.exists_invertible_isTrivial_tensorSheaf
    (pullbackOver (cubeProj₁ A * cubeProj₂ A) L)
    (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₂ A) L hL)
  obtain ⟨N₁₃, h₁₃, t₁₃⟩ := Stacks.SheafOfModules.exists_invertible_isTrivial_tensorSheaf
    (pullbackOver (cubeProj₁ A * cubeProj₃ A) L)
    (isInvertible_pullbackOver (cubeProj₁ A * cubeProj₃ A) L hL)
  obtain ⟨N₂₃, h₂₃, t₂₃⟩ := Stacks.SheafOfModules.exists_invertible_isTrivial_tensorSheaf
    (pullbackOver (cubeProj₂ A * cubeProj₃ A) L)
    (isInvertible_pullbackOver (cubeProj₂ A * cubeProj₃ A) L hL)
  have hφ := pullbackPicardClass_cubeModule_eq_cubeClass L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃
    t₁₂ t₁₃ t₂₃ (lift (lift f g) t)
  have hψφ := pullbackPicardClass_cubeModule_eq_cubeClass L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃
    t₁₂ t₁₃ t₂₃ (ψ ≫ lift (lift f g) t)
  simp only [lift_lift_cubeProj₁, lift_lift_cubeProj₂, lift_lift_cubeProj₃, Category.assoc]
    at hφ hψφ
  rw [← hψφ, Over.comp_left, Stacks.SheafOfModules.pullbackPicardClass_comp ψ.left
    (lift (lift f g) t).left _ _
    (isInvertible_pullbackOver (lift (lift f g) t) _
      (isInvertible_cubeModule A L hL N₁₂ N₁₃ N₂₃ h₁₂ h₁₃ h₂₃))]
  rw [h, Stacks.SheafOfModules.pullbackPicardClass_eq_zero_iff] at hφ
  rw [Stacks.SheafOfModules.pullbackPicardClass_eq_zero_iff]
  exact ⟨(modulePullback ψ.left.toLRSHom.toShHom).mapIso hφ.some ≪≫
    modulePullbackObjUnitIso ψ.left.toLRSHom.toShHom⟩

/-- **The cube class of `L` vanishes at the `k`-point `a`**: `D_L(f, g, a) = 0` for all
`f, g : B ⟶ A`, the point `a` being read as the constant morphism `B ⟶ Spec k ⟶ A`. -/
def IsCubeTrivialAt (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) : Prop :=
  ∀ (B : Over (Spec (.of k))) (f g : B ⟶ A), cubeClass L hL f g (toUnit B ≫ a) = 0

/-- **The cube class vanishes at the unit**: `D(f, g, 0) = 0` identically. -/
theorem isCubeTrivialAt_one : IsCubeTrivialAt L hL η[A] := by
  intro B f g
  rw [← Hom.one_def, cubeClass_def, mul_one, mul_one, mul_one,
    pullbackPicardClass_one L hL]
  abel

variable [IsCommMonObj A]

/-- The identity behind the closure of the vanishing locus under the group law:
`D(f, g, a + b) = D(f + b, g, a) + D(f, g, b) - D(g, a, b)`. -/
theorem cubeClass_mul_right {B : Over (Spec (.of k))} (f g a b : B ⟶ A) :
    cubeClass L hL f g (a * b) =
      cubeClass L hL (f * b) g a + cubeClass L hL f g b - cubeClass L hL g a b := by
  simp only [cubeClass_def]
  simp only [mul_comm, mul_left_comm]
  abel

/-- **The `k`-points at which the cube class vanishes are closed under the group law.** -/
theorem IsCubeTrivialAt.mul {a b : 𝟙_ (Over (Spec (.of k))) ⟶ A}
    (ha : IsCubeTrivialAt L hL a) (hb : IsCubeTrivialAt L hL b) :
    IsCubeTrivialAt L hL (a * b) := by
  intro B f g
  rw [MonObj.comp_mul, cubeClass_mul_right, ha, hb, hb]
  abel

/-- The translation `t_a = 𝟙 + a : A ⟶ A` by a `k`-point `a`. -/
noncomputable def translate (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) : A ⟶ A :=
  𝟙 A * (toUnit A ≫ a)

omit [IsCommMonObj A] in
/-- Composing with the translation adds the constant. -/
theorem comp_translate {B : Over (Spec (.of k))} (h : B ⟶ A)
    (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) : h ≫ translate a = h * (toUnit B ≫ a) := by
  rw [translate, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    Subsingleton.elim (h ≫ toUnit A) (toUnit B)]

omit [IsCommMonObj A] in
/-- The pullback class of `t_a^*L` along `h` is the pullback class of `L` along `h + a`. -/
theorem pullbackPicardClass_pullbackOver_translate {B : Over (Spec (.of k))} (h : B ⟶ A)
    (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    pullbackPicardClass h.left (pullbackOver (translate a) L)
        (isInvertible_pullbackOver (translate a) L hL) =
      pullbackPicardClass (h * (toUnit B ≫ a)).left L hL := by
  rw [← comp_translate, Over.comp_left,
    Stacks.SheafOfModules.pullbackPicardClass_comp h.left (translate a).left L hL
      (isInvertible_pullbackOver (translate a) L hL)]

/-- **The translation identity.** If the cube class of `L` vanishes at `a`, then the cube class of
the translate `t_a^*L` is the cube class of `L` with the third argument translated by `a`:
`D_{t_a^*L}(h₁, h₂, h₃) = D_L(h₁, h₂, h₃ + a)`. -/
theorem cubeClass_translate {a : 𝟙_ (Over (Spec (.of k))) ⟶ A} (ha : IsCubeTrivialAt L hL a)
    {B : Over (Spec (.of k))} (h₁ h₂ h₃ : B ⟶ A) :
    cubeClass (pullbackOver (translate a) L) (isInvertible_pullbackOver (translate a) L hL)
        h₁ h₂ h₃ =
      cubeClass L hL h₁ h₂ (h₃ * (toUnit B ≫ a)) := by
  have h0 := ha B h₁ h₂
  have hc := pullbackPicardClass_toUnit_comp L hL (B := B) a
  simp only [cubeClass_def, pullbackPicardClass_pullbackOver_translate] at h0 ⊢
  simp only [mul_assoc, mul_comm, mul_left_comm] at h0 ⊢
  rw [← sub_eq_zero, ← neg_zero, ← h0, hc]
  abel

end Stacks.Groupoids

end
