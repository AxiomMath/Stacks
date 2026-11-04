module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.DeformationsOfProjectiveSchemesFunctorial
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic

/-!
# Towers of polarized schemes over thickenings of affine schemes

The data of [Stacks, Tag 0D4T]: an inverse system of rings `(R_n)` with surjective transition maps
whose kernels are locally nilpotent, and over `S_n = Spec R_n` a compatible system of proper, flat,
finitely presented schemes `X_n` with cartesian transition squares, invertible modules `ℒ_n` and
isomorphisms `φ_n : i_n^* ℒ_{n + 1} ≅ ℒ_n`, with `ℒ_0` ample. The index `n : ℕ` stands for the
source's level `n + 1`.

Each level is an admissible deformation, in the sense of [Stacks, Tag 0D4F], of the polarized
family `(X_0 ⟶ S_0, ℒ_0)` across the thickening `S_0 ⊆ S_n`, and the transition squares are
morphisms of admissible deformations. This file records that.

## Main definitions

* `Stacks.PolarizedAlgebraization.PolarizedTower`: the data and hypotheses of the tag.
* `Stacks.PolarizedAlgebraization.PolarizedTower.family`: the polarized family `(X_0, ℒ_0)`.
* `Stacks.PolarizedAlgebraization.PolarizedTower.deformation`: level `n` as an admissible
  deformation of it.
* `Stacks.PolarizedAlgebraization.PolarizedTower.deformationHom`: the transition from level `n` to
  level `n + 1` as a morphism of admissible deformations.

## References

* [Stacks Project, Tag 0D4T](https://stacks.math.columbia.edu/tag/0D4T)
* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Ample Stacks.Thickenings

universe u

namespace Stacks.PolarizedAlgebraization

open Stacks.AlgebraicGeometry.ProjectiveDeformation

/-- **The data of [Stacks, Tag 0D4T].** An inverse system of rings `R_n` whose transition maps are
surjective with locally nilpotent kernels; schemes `X_n` over `Spec R_n` with cartesian transition
squares; invertible modules `ℒ_n` with `φ_n : i_n^* ℒ_{n + 1} ≅ ℒ_n`; every `X_n ⟶ Spec R_n`
proper, flat and of finite presentation; and `ℒ_0` ample on `X_0`. -/
structure PolarizedTower where
  /-- The inverse system of rings. -/
  R : ℕᵒᵖ ⥤ CommRingCat.{u}
  /-- The transition maps of rings are surjective. -/
  surjective : ∀ n : ℕ, Function.Surjective (R.map (homOfLE (Nat.le_succ n)).op).hom
  /-- The kernels of the transition maps of rings are locally nilpotent. -/
  ker_le_nilradical : ∀ n : ℕ,
    RingHom.ker (R.map (homOfLE (Nat.le_succ n)).op).hom ≤ nilradical (R.obj (op (n + 1)))
  /-- The schemes of the system. -/
  X : ℕ → Scheme.{u}
  /-- The structure morphisms. -/
  f : ∀ n : ℕ, X n ⟶ Spec (R.obj (op n))
  /-- The transition morphisms of schemes. -/
  i : ∀ n : ℕ, X n ⟶ X (n + 1)
  /-- The transition squares are cartesian. -/
  isPullback : ∀ n : ℕ,
    IsPullback (i n) (f n) (f (n + 1)) (Spec.map (R.map (homOfLE (Nat.le_succ n)).op))
  /-- The invertible modules. -/
  L : ∀ n : ℕ, (X n).Modules
  /-- Each `ℒ_n` is invertible. -/
  invertible : ∀ n : ℕ, IsInvertibleModule (X n) (L n)
  /-- The transition isomorphisms of the modules. -/
  φ : ∀ n : ℕ, (Scheme.Modules.pullback (i n)).obj (L (n + 1)) ≅ L n
  /-- Each structure morphism is proper. -/
  isProper : ∀ n : ℕ, IsProper (f n)
  /-- Each structure morphism is flat. -/
  flat : ∀ n : ℕ, Flat (f n)
  /-- Each structure morphism is of finite presentation. -/
  finitePresentation : ∀ n : ℕ, _root_.AlgebraicGeometry.FinitePresentation (f n)
  /-- `ℒ_0` is ample on `X_0`. -/
  isAmple : IsAmple (X 0) (L 0)

namespace PolarizedTower

attribute [instance] invertible isProper flat

variable (T : PolarizedTower.{u})

/-- The ring map `R_{n + m} ⟶ R_n`. -/
abbrev ringMap {n m : ℕ} (h : n ≤ m) : T.R.obj (op m) ⟶ T.R.obj (op n) :=
  T.R.map (homOfLE h).op

/-- The closed immersion `Spec R_n ⟶ Spec R_m` for `n ≤ m`. -/
abbrev baseMap {n m : ℕ} (h : n ≤ m) : Spec (T.R.obj (op n)) ⟶ Spec (T.R.obj (op m)) :=
  Spec.map (T.ringMap h)

/-- The ring map `R_n ⟶ R_n` is the identity. -/
private theorem ringMap_refl (n : ℕ) : T.ringMap (le_refl n) = 𝟙 _ := by
  have : (homOfLE (le_refl n)).op = 𝟙 (op n) := rfl
  rw [ringMap, this, CategoryTheory.Functor.map_id]

/-- The ring maps `R_k ⟶ R_m ⟶ R_n` compose to `R_k ⟶ R_n`. -/
private theorem ringMap_comp {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) :
    T.ringMap (h.trans h') = T.ringMap h' ≫ T.ringMap h := by
  rw [ringMap, ringMap, ringMap, ← Functor.map_comp]
  rfl

/-- The closed immersions `Spec R_n ⟶ Spec R_m ⟶ Spec R_k` compose to `Spec R_n ⟶ Spec R_k`. -/
theorem baseMap_comp {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) :
    T.baseMap h ≫ T.baseMap h' = T.baseMap (h.trans h') := by
  rw [baseMap, baseMap, baseMap, ← Spec.map_comp, T.ringMap_comp h h']

/-- The closed immersion `Spec R_n ⟶ Spec R_n` is the identity. -/
theorem baseMap_refl (n : ℕ) : T.baseMap (le_refl n) = 𝟙 _ := by
  rw [baseMap, T.ringMap_refl, Spec.map_id]

/-- The ring maps `R_m ⟶ R_n`, `n ≤ m`, are surjective. -/
theorem surjective_ringMap {n m : ℕ} (h : n ≤ m) : Function.Surjective (T.ringMap h).hom := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [T.ringMap_refl]
    exact Function.surjective_id
  | succ m hnm ih =>
    rw [T.ringMap_comp hnm (Nat.le_succ m), CommRingCat.hom_comp]
    exact ih.comp (T.surjective m)

/-- The kernels of the ring maps `R_m ⟶ R_n`, `n ≤ m`, are locally nilpotent. -/
theorem ker_ringMap_le_nilradical {n m : ℕ} (h : n ≤ m) :
    RingHom.ker (T.ringMap h).hom ≤ nilradical (T.R.obj (op m)) := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [T.ringMap_refl]
    intro x hx
    rw [RingHom.mem_ker] at hx
    exact (show x = 0 from hx) ▸ zero_mem _
  | succ m hnm ih =>
    rw [T.ringMap_comp hnm (Nat.le_succ m)]
    intro x hx
    rw [RingHom.mem_ker, CommRingCat.hom_comp, RingHom.comp_apply] at hx
    obtain ⟨k, hk⟩ := mem_nilradical.mp (ih (RingHom.mem_ker.mpr hx))
    have hk' : x ^ k ∈ RingHom.ker (T.ringMap (Nat.le_succ m)).hom := by
      rw [RingHom.mem_ker, map_pow, hk]
    obtain ⟨l, hl⟩ := mem_nilradical.mp (T.ker_le_nilradical m hk')
    exact mem_nilradical.mpr ⟨k * l, by rw [pow_mul, hl]⟩

/-- `Spec R_n ⟶ Spec R_m`, `n ≤ m`, is a thickening. -/
theorem isThickening_baseMap {n m : ℕ} (h : n ≤ m) : IsThickening (T.baseMap h) := by
  refine ⟨IsClosedImmersion.spec_of_surjective _ (T.surjective_ringMap h), ?_⟩
  show Function.Surjective (PrimeSpectrum.comap (T.ringMap h).hom)
  let e := RingHom.quotientKerEquivOfSurjective (T.surjective_ringMap h)
  have hf : (T.ringMap h).hom = e.toRingHom.comp (Ideal.Quotient.mk _) := RingHom.ext fun _ ↦ rfl
  rw [hf, PrimeSpectrum.comap_comp]
  exact ((PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical
    (T.ker_ringMap_le_nilradical h)).surjective).comp
      (PrimeSpectrum.comapEquiv e.symm).surjective

/-- The immersion `X_0 ⟶ X_n`. -/
def incl : ∀ n : ℕ, T.X 0 ⟶ T.X n
  | 0 => 𝟙 _
  | n + 1 => incl n ≫ T.i n

/-- The immersion `X_0 ⟶ X_0` is the identity. -/
@[simp] theorem incl_zero : T.incl 0 = 𝟙 _ := rfl

/-- The immersion `X_0 ⟶ X_{n + 1}` is `X_0 ⟶ X_n` followed by `X_n ⟶ X_{n + 1}`. -/
@[simp] theorem incl_succ (n : ℕ) : T.incl (n + 1) = T.incl n ≫ T.i n := rfl

/-- `X_0 = X_n ×_{S_n} S_0`. -/
theorem isPullback_incl (n : ℕ) :
    IsPullback (T.incl n) (T.f 0) (T.f n) (T.baseMap (Nat.zero_le n)) := by
  induction n with
  | zero =>
    rw [incl_zero, T.baseMap_refl 0]
    exact IsPullback.id_horiz (T.f 0)
  | succ n ih =>
    rw [incl_succ, ← T.baseMap_comp (Nat.zero_le n) (Nat.le_succ n)]
    exact ih.paste_horiz (T.isPullback n)

/-- The identification of `ℒ_0` with the restriction of `ℒ_n` to `X_0`. -/
def polarization : ∀ n : ℕ, T.L 0 ≅ (Scheme.Modules.pullback (T.incl n)).obj (T.L n)
  | 0 => ((Scheme.Modules.pullbackId (T.X 0)).app (T.L 0)).symm
  | n + 1 => polarization n ≪≫ (Scheme.Modules.pullback (T.incl n)).mapIso (T.φ n).symm ≪≫
      (Scheme.Modules.pullbackComp (T.incl n) (T.i n)).app (T.L (n + 1))

/-- **The polarized family `(X_0 ⟶ S_0, ℒ_0)`** of [Stacks, Tag 0D4F]: ampleness of `ℒ_0` is
relative ampleness over the affine base `S_0` ([Stacks, Tag 01VK]). -/
def family : PolarizedFamily.{u} where
  X := T.X 0
  S := Spec (T.R.obj (op 0))
  f := T.f 0
  L := T.L 0
  isProper := T.isProper 0
  flat := T.flat 0
  finitePresentation := T.finitePresentation 0
  invertible := T.invertible 0
  isRelativelyAmple :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple (T.f 0) (T.L 0)).mpr T.isAmple
  compactSpace := inferInstance

/-- **Level `n` as an admissible deformation** of `(X_0, ℒ_0)` across the thickening
`S_0 ⊆ S_n`. -/
def deformation (n : ℕ) : T.family.AdmissibleDeformation where
  S' := Spec (T.R.obj (op n))
  X' := T.X n
  i := T.baseMap (Nat.zero_le n)
  i' := T.incl n
  f' := T.f n
  isThickening := T.isThickening_baseMap (Nat.zero_le n)
  isPullback := T.isPullback_incl n
  isProper := T.isProper n
  flat := T.flat n
  finitePresentation := T.finitePresentation n
  L' := T.L n
  invertible := T.invertible n
  polarization := T.polarization n

/-- **The transition from level `n` to level `n + 1`** as a morphism of admissible deformations:
the cartesian square of the tower, with the transition isomorphism of the modules. -/
def deformationHom (n : ℕ) :
    PolarizedFamily.AdmissibleDeformation.Hom (T.deformation n) (T.deformation (n + 1)) where
  base := T.baseMap (Nat.le_succ n)
  total := T.i n
  isPullback := T.isPullback n
  base_comm := T.baseMap_comp (Nat.zero_le n) (Nat.le_succ n)
  total_comm := rfl
  polarization := T.φ n

end PolarizedTower

end Stacks.PolarizedAlgebraization

end
