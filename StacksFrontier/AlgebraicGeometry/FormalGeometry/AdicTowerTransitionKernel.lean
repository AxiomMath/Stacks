module

public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import StacksFrontier.AlgebraicGeometry.Algebraization
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalClosedSubschemeAlgebraization
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffineFirstOrder

/-!
# The transition kernels of a cartesian tower of adic thickenings

This is the first half of the second paragraph of the proof of [Stacks, Tag 089A]. The data is
the one the theorem starts from: a Noetherian ring `A`, an ideal `I ⊆ A`, the affine thickenings
`Sₙ = Spec (A / I ^ (n + 1))` (`AlgebraicGeometry.adicThickening`, whose index `n` is the
source's `n + 1`), a tower of schemes `Xₙ` with structure morphisms `qₙ : Xₙ ⟶ Sₙ` and
transitions `tₙ : Xₙ ⟶ X_{n+1}` making every square cartesian.

The source reads off from the cartesian squares that the `tₙ` are closed immersions, that the
ideal of `X₀` inside `X_{n+1}` is `I · 𝒪_{X_{n+1}}`, that

  `𝓕ₙ = Ker(𝒪_{X_{n+1}} ⟶ 𝒪_{Xₙ})`

is `I ^ (n+1) · 𝒪_{X_{n+1}}` and hence is annihilated by the ideal of `X₀`, and therefore that
`𝓕ₙ` is a module on `X₀`.

That is what this file proves. The annihilation is **not** obtained by identifying the two ideal
sheaves with ideal powers — that identification is never needed. Both are inverse images along
`q_{n+1}` of ideal sheaves on the affine scheme `S_{n+1}`
(`Stacks.AdicTower.ker_transition` and `Stacks.AdicTower.ker_incl`), so on an affine open of
`X_{n+1}` both are extensions of ideals of `A / I ^ (n + 2)`
(`AlgebraicGeometry.Scheme.IdealSheafData.comap` and `Stacks.IdealSheaf.ideal_comap_appLE`), and
the product of the two ideals downstairs is the image of `I · I ^ (n + 1) = I ^ (n + 2)`, which
is zero. Passing from affine opens to all opens is the sheaf axiom, as in
`Stacks.Thickenings.mul_eq_zero_of_app_eq_zero`.

Once the annihilation is available, [Stacks, Tag 01QY] in the form
`Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero` identifies the ideal sheaf upstairs with
the direct image of its own inverse image on `X₀`, and `𝓕ₙ` is that inverse image.

## Main definitions

* `Stacks.AdicTower.thickeningIncl`: the closed immersion `S₀ ⟶ Sₙ`.
* `Stacks.AdicTower.incl`: the composite transition `X₀ ⟶ Xₙ`.
* `Stacks.AdicTower.transitionIdeal`: `Ker(𝒪_{X_{n+1}} ⟶ 𝒪_{Xₙ})` as an `𝒪_{X_{n+1}}`-module.
* `Stacks.AdicTower.transitionKernel`: **`𝓕ₙ`, the same sheaf read as an `𝒪_{X₀}`-module.**

## Main results

* `Stacks.AdicTower.isPullback_incl`: the composite squares are cartesian.
* `Stacks.AdicTower.mul_eq_zero_of_app_eq_zero`: a section of `𝒪_{X_{n+1}}` dying on `X₀` and a
  section dying on `Xₙ` have vanishing product — the annihilation of `𝓕ₙ` by the ideal of `X₀`.
* `Stacks.AdicTower.pushforwardTransitionKernelIso`: **`(X₀ ⟶ X_{n+1})_* 𝓕ₙ ≅ 𝓕ₙ` read
  upstairs**, i.e. `𝓕ₙ` really is the transition kernel moved across the closed immersion.
* `Stacks.AdicTower.isQuasicoherent_transitionKernel`: `𝓕ₙ` is quasi-coherent.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 01QY](https://stacks.math.columbia.edu/tag/01QY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AdicTower

variable (A : Type u) [CommRing A] (I : Ideal A)

/-! ### The tower of affine thickenings -/

/-- The canonical morphism `S₀ ⟶ Sₙ` of adic thickenings, the `n`-fold composite of
`AlgebraicGeometry.adicThickeningSucc`. -/
def thickeningIncl : (n : ℕ) → (adicThickening A I 0 ⟶ adicThickening A I n)
  | 0 => 𝟙 _
  | n + 1 => thickeningIncl n ≫ adicThickeningSucc A I n

/-- The morphism `S₀ ⟶ S₀` of the tower is the identity. -/
@[simp]
lemma thickeningIncl_zero : thickeningIncl A I 0 = 𝟙 _ := rfl

/-- The morphism `S₀ ⟶ S_{n+1}` is the composite of `S₀ ⟶ Sₙ` with the thickening
`Sₙ ⟶ S_{n+1}`. -/
@[simp]
lemma thickeningIncl_succ (n : ℕ) :
    thickeningIncl A I (n + 1) = thickeningIncl A I n ≫ adicThickeningSucc A I n := rfl

/-- `S₀ ⟶ Sₙ` is the spectrum of the canonical surjection `A / I ^ (n + 1) → A / I`. -/
lemma thickeningIncl_eq (n : ℕ) :
    thickeningIncl A I n =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factorPow I (show 0 + 1 ≤ n + 1 by omega))) := by
  induction n with
  | zero =>
    refine (Spec.map_id _).symm.trans ?_
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  | succ n ih =>
    rw [thickeningIncl_succ, ih, adicThickeningSucc, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

/-- The morphism `S₀ ⟶ Sₙ` of adic thickenings is a closed immersion. -/
instance isClosedImmersion_thickeningIncl (n : ℕ) :
    IsClosedImmersion (thickeningIncl A I n) := by
  rw [thickeningIncl_eq]
  exact IsClosedImmersion.spec_of_surjective _
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (show 0 + 1 ≤ n + 1 by omega)))

/-- **The ring-level annihilation.** In `A / I ^ (n + 2)` a function vanishing on
`Spec (A / I)` and a function vanishing on `Spec (A / I ^ (n + 1))` have vanishing product,
because their product lies in the image of `I · I ^ (n + 1) = I ^ (n + 2)`. -/
lemma mul_eq_zero_of_appTop_eq_zero (n : ℕ)
    (a b : Γ(adicThickening A I (n + 1), ⊤))
    (ha : (thickeningIncl A I (n + 1)).appTop.hom a = 0)
    (hb : (adicThickeningSucc A I n).appTop.hom b = 0) : a * b = 0 := by
  rw [thickeningIncl_eq] at ha
  rw [adicThickeningSucc] at hb
  set R : CommRingCat.{u} := .of (A ⧸ I ^ (n + 1 + 1))
  set e := Scheme.ΓSpecIso R with he
  -- Transporting a vanishing of global sections across `Γ(Spec R, ⊤) ≅ R`.
  have key : ∀ {S : CommRingCat.{u}} (φ : R ⟶ S) (x : Γ(Spec R, ⊤)),
      (Spec.map φ).appTop.hom x = 0 → φ.hom (e.hom.hom x) = 0 := by
    intro S φ x hx
    have hn := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality φ) x
    simp only [CommRingCat.comp_apply] at hn
    rw [he, ← hn, hx, map_zero]
  have ha' : e.hom.hom a ∈
      RingHom.ker (Ideal.Quotient.factorPow I (show 0 + 1 ≤ n + 1 + 1 by omega)) :=
    key _ a ha
  have hb' : e.hom.hom b ∈
      RingHom.ker (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))) := key _ b hb
  have hmem := Ideal.mul_mem_mul ha' hb'
  rw [Ideal.Quotient.factor_ker, Ideal.Quotient.factor_ker, ← Ideal.map_mul] at hmem
  have hle : (I ^ (0 + 1)) * (I ^ (n + 1)) ≤ I ^ (n + 1 + 1) := by
    rw [← pow_add]
    exact Ideal.pow_le_pow_right (by omega)
  rw [Ideal.map_mk_eq_bot_of_le hle, Ideal.mem_bot] at hmem
  have hinj : Function.Injective e.hom.hom := (ConcreteCategory.bijective_of_isIso e.hom).1
  exact hinj (by rw [map_mul, hmem, map_zero])

/-- **The kernel of a comorphism of affine schemes, transported to the ring.** The image of
`Ker(Γ(Spec R, ⊤) ⟶ Γ(Spec S, ⊤))` under `Γ(Spec R, ⊤) ≅ R` lands in `Ker(R ⟶ S)`. -/
lemma ker_appTop_map_ΓSpecIso_le {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    (RingHom.ker (Spec.map φ).appTop.hom).map (Scheme.ΓSpecIso R).hom.hom ≤
      RingHom.ker φ.hom := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  have hn := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality φ) x
  simp only [CommRingCat.comp_apply] at hn
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  rw [← hn, RingHom.mem_ker.mp hx, map_zero]

/-- **The ideal of `S₀` in `S_{n+1}` is nilpotent**, of order at most `n + 2`: it is the ideal
generated by `I` in `A / I ^ (n + 2)`. -/
lemma pow_ker_appTop_thickeningIncl (n : ℕ) :
    RingHom.ker (thickeningIncl A I (n + 1)).appTop.hom ^ (n + 2) = ⊥ := by
  rw [thickeningIncl_eq]
  set φ : CommRingCat.of (A ⧸ I ^ (n + 1 + 1)) ⟶ CommRingCat.of (A ⧸ I ^ (0 + 1)) :=
    CommRingCat.ofHom (Ideal.Quotient.factorPow I (show 0 + 1 ≤ n + 1 + 1 by omega))
  have hdown : RingHom.ker φ.hom ^ (n + 2) = ⊥ := by
    show RingHom.ker (Ideal.Quotient.factorPow I (show 0 + 1 ≤ n + 1 + 1 by omega)) ^ (n + 2) = ⊥
    rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow]
    refine Ideal.map_mk_eq_bot_of_le ?_
    rw [← pow_mul]
    exact Ideal.pow_le_pow_right (by omega)
  have hmap : (RingHom.ker (Spec.map φ).appTop.hom ^ (n + 2)).map
      (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I ^ (n + 1 + 1)))).hom.hom = ⊥ := by
    rw [Ideal.map_pow]
    refine le_bot_iff.mp ?_
    rw [← hdown]
    exact pow_le_pow_left' (ker_appTop_map_ΓSpecIso_le φ) (n + 2)
  rw [Ideal.map_eq_bot_iff_le_ker] at hmap
  refine le_bot_iff.mp fun x hx => ?_
  have hinj : Function.Injective
      (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I ^ (n + 1 + 1)))).hom.hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  exact Ideal.mem_bot.mpr (hinj (by rw [RingHom.mem_ker.mp (hmap hx), map_zero]))

/-! ### The tower of schemes -/

variable {A I}
variable {Xn : ℕ → Scheme.{u}} (q : ∀ n, Xn n ⟶ adicThickening A I n)
  (t : ∀ n, Xn n ⟶ Xn (n + 1))
  (hcart : ∀ n, IsPullback (t n) (q n) (q (n + 1)) (adicThickeningSucc A I n))

include hcart in
/-- **The transitions of the tower are closed immersions**, being base changes of the closed
immersions `Sₙ ⟶ S_{n+1}`. -/
lemma isClosedImmersion_transition (n : ℕ) : IsClosedImmersion (t n) :=
  MorphismProperty.of_isPullback (hcart n).flip
    (isClosedImmersion_adicThickeningSucc A I n)

/-- The composite transition `X₀ ⟶ Xₙ` of the tower. -/
def incl : (n : ℕ) → (Xn 0 ⟶ Xn n)
  | 0 => 𝟙 _
  | n + 1 => incl n ≫ t n

/-- The composite transition `X₀ ⟶ X₀` of the tower is the identity. -/
@[simp]
lemma incl_zero : incl t 0 = 𝟙 _ := rfl

/-- The composite transition `X₀ ⟶ X_{n+1}` is the composite of `X₀ ⟶ Xₙ` with the transition
`Xₙ ⟶ X_{n+1}` of the tower. -/
@[simp]
lemma incl_succ (n : ℕ) : incl t (n + 1) = incl t n ≫ t n := rfl

include hcart in
/-- **The composite squares of the tower are cartesian**, by pasting. -/
lemma isPullback_incl (n : ℕ) :
    IsPullback (incl t n) (q 0) (q n) (thickeningIncl A I n) := by
  induction n with
  | zero => exact IsPullback.of_id_fst
  | succ n ih => exact ih.paste_horiz (hcart n)

include hcart in
/-- `X₀ ⟶ Xₙ` is a closed immersion. -/
lemma isClosedImmersion_incl (n : ℕ) : IsClosedImmersion (incl t n) :=
  MorphismProperty.of_isPullback (isPullback_incl q t hcart n).flip
    (isClosedImmersion_thickeningIncl A I n)

/-! ### The two ideal sheaves on `X_{n+1}` -/

/-- The kernel ideal sheaf of a base-changed closed immersion is the inverse image of the
kernel ideal sheaf downstairs. -/
lemma ker_of_isPullback {V W X Y : Scheme.{u}} {f : X ⟶ Y} {f' : V ⟶ W} {g : V ⟶ X}
    {j : W ⟶ Y} [IsClosedImmersion f] (h : IsPullback f' g j f) :
    f'.ker = f.ker.comap j := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion f j,
    ← Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom, h.isoPullback_hom_fst]

include hcart in
/-- The ideal sheaf of `Xₙ` in `X_{n+1}` is the inverse image of the ideal sheaf of `Sₙ` in
`S_{n+1}`. -/
lemma ker_transition (n : ℕ) :
    (t n).ker = (adicThickeningSucc A I n).ker.comap (q (n + 1)) :=
  ker_of_isPullback (hcart n)

include hcart in
/-- The ideal sheaf of `X₀` in `X_{n+1}` is the inverse image of the ideal sheaf of `S₀` in
`S_{n+1}`. -/
lemma ker_incl (n : ℕ) :
    (incl t (n + 1)).ker = (thickeningIncl A I (n + 1)).ker.comap (q (n + 1)) :=
  ker_of_isPullback (isPullback_incl q t hcart (n + 1))

/-- The comparison map on sections from the whole of the affine base `S_{n+1}` to an affine
open of `X_{n+1}`, along which the two ideal sheaves of `X_{n+1}` are extended from
`A / I ^ (n + 2)`. -/
abbrev baseAppLE (n : ℕ) (U : (Xn (n + 1)).affineOpens) :
    Γ(adicThickening A I (n + 1), ⊤) ⟶ Γ(Xn (n + 1), (U : (Xn (n + 1)).Opens)) :=
  (q (n + 1)).appLE (⊤ : (adicThickening A I (n + 1)).Opens) (U : (Xn (n + 1)).Opens) le_top

include hcart in
/-- **The ideal of `X₀` on an affine open of `X_{n+1}`** is extended from the ideal of `S₀` in
the ring `A / I ^ (n + 2)` of the affine base. -/
lemma ideal_ker_incl (n : ℕ) (U : (Xn (n + 1)).affineOpens) :
    (incl t (n + 1)).ker.ideal U =
      (RingHom.ker (thickeningIncl A I (n + 1)).appTop.hom).map (baseAppLE q n U).hom := by
  rw [ker_incl q t hcart n]
  refine (Stacks.IdealSheaf.ideal_comap_appLE _ _ ⟨⊤, isAffineOpen_top _⟩ U le_top).trans ?_
  rw [Scheme.Hom.ker_apply]
  rfl

include hcart in
/-- **The ideal of `Xₙ` on an affine open of `X_{n+1}`** is extended from the ideal of `Sₙ` in
the ring `A / I ^ (n + 2)` of the affine base. -/
lemma ideal_ker_transition (n : ℕ) (U : (Xn (n + 1)).affineOpens) :
    (t n).ker.ideal U =
      (RingHom.ker (adicThickeningSucc A I n).appTop.hom).map (baseAppLE q n U).hom := by
  rw [ker_transition q t hcart n]
  refine (Stacks.IdealSheaf.ideal_comap_appLE _ _ ⟨⊤, isAffineOpen_top _⟩ U le_top).trans ?_
  rw [Scheme.Hom.ker_apply]
  rfl

include hcart in
/-- **The annihilation, on an affine open.** On an affine open of `X_{n+1}` the product of the
ideal of `X₀` and the ideal of `Xₙ` is zero. -/
lemma ideal_mul_ideal_eq_bot (n : ℕ) (U : (Xn (n + 1)).affineOpens) :
    (incl t (n + 1)).ker.ideal U * (t n).ker.ideal U = ⊥ := by
  rw [ideal_ker_incl q t hcart n U, ideal_ker_transition q t hcart n U, ← Ideal.map_mul]
  refine le_bot_iff.mp ?_
  rw [Ideal.map_le_iff_le_comap]
  refine Ideal.mul_le.mpr fun x hx y hy => ?_
  simp [mul_eq_zero_of_appTop_eq_zero A I n x y (RingHom.mem_ker.mp hx) (RingHom.mem_ker.mp hy)]

include hcart in
/-- **The annihilation, on an arbitrary open.** A section of `𝒪_{X_{n+1}}` which dies on `X₀`
and a section which dies on `Xₙ` have vanishing product: their germs do, because over an affine
open the two ideals multiply to zero. -/
lemma mul_eq_zero_of_app_eq_zero (n : ℕ) (U : (Xn (n + 1)).Opens)
    (a s : Γ(Xn (n + 1), U)) (ha : (incl t (n + 1)).app U a = 0)
    (hs : (t n).app U s = 0) : a * s = 0 := by
  have hci : IsClosedImmersion (incl t (n + 1)) := isClosedImmersion_incl q t hcart (n + 1)
  have hct : IsClosedImmersion (t n) := isClosedImmersion_transition q t hcart n
  apply TopCat.Presheaf.section_ext (Xn (n + 1)).sheaf U
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    (Xn (n + 1)).isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  let j : V ⟶ U := homOfLE hVU
  have hka : (Xn (n + 1)).presheaf.map j.op a ∈ (incl t (n + 1)).ker.ideal ⟨V, hV⟩ := by
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
    have hn := ConcreteCategory.congr_hom ((incl t (n + 1)).naturality j.op) a
    change (incl t (n + 1)).app V ((Xn (n + 1)).presheaf.map j.op a) =
      (Xn 0).presheaf.map _ ((incl t (n + 1)).app U a) at hn
    exact hn.trans (by rw [ha, map_zero])
  have hks : (Xn (n + 1)).presheaf.map j.op s ∈ (t n).ker.ideal ⟨V, hV⟩ := by
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
    have hn := ConcreteCategory.congr_hom ((t n).naturality j.op) s
    change (t n).app V ((Xn (n + 1)).presheaf.map j.op s) =
      (Xn n).presheaf.map _ ((t n).app U s) at hn
    exact hn.trans (by rw [hs, map_zero])
  have hz : (Xn (n + 1)).presheaf.map j.op a * (Xn (n + 1)).presheaf.map j.op s = 0 := by
    have hm := Ideal.mul_mem_mul hka hks
    rwa [ideal_mul_ideal_eq_bot q t hcart n ⟨V, hV⟩, Ideal.mem_bot] at hm
  show (Xn (n + 1)).presheaf.germ U x hx (a * s) = (Xn (n + 1)).presheaf.germ U x hx 0
  rw [← TopCat.Presheaf.germ_res_apply (Xn (n + 1)).presheaf j x hxV (a * s)]
  simp only [map_mul, hz, map_zero]

/-! ### The transition kernel as a module on the closed member -/

/-- `Ker(𝒪_{X_{n+1}} ⟶ 𝒪_{Xₙ})`, the ideal sheaf of the `n`-th transition, read as a module
over `𝒪_{X_{n+1}}`. -/
abbrev transitionIdeal (n : ℕ) : (Xn (n + 1)).Modules :=
  Stacks.Thickenings.idealSheafModule (t n)

include hcart in
/-- The ideal of `X₀` annihilates the transition kernel: this is the annihilation of a product
of sections, read through the inclusion of the ideal sheaf into the structure sheaf. -/
lemma smul_transitionIdeal_eq_zero (n : ℕ) (U : (Xn (n + 1)).Opens)
    (a : Γ(Xn (n + 1), U)) (ha : ((incl t (n + 1)).app U).hom a = 0)
    (m : Γ(transitionIdeal t n, U)) : a • m = 0 := by
  have hct : IsClosedImmersion (t n) := isClosedImmersion_transition q t hcart n
  apply Stacks.Thickenings.injective_app_idealSheafModule (t n) U
  refine Eq.trans
    (((kernel.ι (SheafOfModules.unitToPushforwardObjUnit (t n).toRingCatSheafHom)).val.app
      (Opposite.op U)).hom.map_smul a m) ?_
  refine Eq.trans ?_
    (((kernel.ι (SheafOfModules.unitToPushforwardObjUnit (t n).toRingCatSheafHom)).val.app
      (Opposite.op U)).hom.map_zero).symm
  show (a : Γ(Xn (n + 1), U)) * (show Γ(Xn (n + 1), U) from
    ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit (t n).toRingCatSheafHom)).val.app
      (Opposite.op U)) m) = 0
  exact mul_eq_zero_of_app_eq_zero q t hcart n U a _ ha
    ((Stacks.Thickenings.exact_app_idealSheafModule (t n) U).apply_apply_eq_zero m)

/-- **`𝓕ₙ`, the `n`-th transition kernel of the tower as a module on the closed member `X₀`.**
It is the inverse image along the closed immersion `X₀ ⟶ X_{n+1}` of
`Ker(𝒪_{X_{n+1}} ⟶ 𝒪_{Xₙ})`; because the ideal of `X₀` annihilates that kernel, no information
is lost, which is `Stacks.AdicTower.pushforwardTransitionKernelIso`. -/
def transitionKernel (n : ℕ) : (Xn 0).Modules :=
  (Scheme.Modules.pullback (incl t (n + 1))).obj (transitionIdeal t n)

include hcart in
/-- The unit of the pullback–pushforward adjunction at the transition kernel is an
isomorphism, by [Stacks, Tag 01QY]. -/
lemma isIso_unit_transitionIdeal (n : ℕ) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (incl t (n + 1))).unit.app (transitionIdeal t n)) :=
  have : IsClosedImmersion (incl t (n + 1)) := isClosedImmersion_incl q t hcart (n + 1)
  Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero _ _
    (smul_transitionIdeal_eq_zero q t hcart n)

include hcart in
/-- **The transition kernel really is `𝓕ₙ`**: its direct image along the closed immersion
`X₀ ⟶ X_{n+1}` is `Ker(𝒪_{X_{n+1}} ⟶ 𝒪_{Xₙ})`. -/
def pushforwardTransitionKernelIso (n : ℕ) :
    (Scheme.Modules.pushforward (incl t (n + 1))).obj (transitionKernel t n) ≅
      transitionIdeal t n :=
  haveI := isIso_unit_transitionIdeal q t hcart n
  (asIso ((Scheme.Modules.pullbackPushforwardAdjunction
    (incl t (n + 1))).unit.app (transitionIdeal t n))).symm

include hcart in
/-- **`𝓕ₙ` is quasi-coherent.** The ideal sheaf of a closed immersion is quasi-coherent, and
the inverse image of a quasi-coherent module is quasi-coherent. -/
lemma isQuasicoherent_transitionKernel (n : ℕ) :
    (transitionKernel t n).IsQuasicoherent := by
  have : IsClosedImmersion (incl t (n + 1)) := isClosedImmersion_incl q t hcart (n + 1)
  have : IsClosedImmersion (t n) := isClosedImmersion_transition q t hcart n
  exact Stacks.Modules.isQuasicoherent_pullback _ _
    (Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf (t n))

end Stacks.AdicTower

end
