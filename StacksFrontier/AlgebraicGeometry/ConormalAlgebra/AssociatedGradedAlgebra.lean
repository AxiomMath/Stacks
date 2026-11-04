module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroBilinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AssociatedGradedSheaf
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Sections

/-!
# The associated graded algebra of a quasi-coherent ideal

Let `X` be a scheme and `ℐ : X.IdealSheafData` a quasi-coherent sheaf of ideals.  The sheaves
`ℐⁿ/ℐⁿ⁺¹` of `StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AssociatedGradedSheaf` are the
homogeneous pieces of a sheaf of graded `𝒪_X`-algebras `⨁_{n ≥ 0} ℐⁿ/ℐⁿ⁺¹`.  This file supplies
the multiplication, by descending the multiplication of the Rees filtration `⨁_{n ≥ 0} ℐⁿ`
along the quotient maps.

The sections of `ℐⁿ · 𝒪_X` over an open `U` are functions on `U`, so the multiplication of the
Rees filtration is the multiplication of `Γ(X, U)`, and needs no gluing: `ℐ(W)ⁿ · ℐ(W)ᵐ ⊆
ℐ(W)ⁿ⁺ᵐ` on each affine open `W` is all that has to be checked.  Passing to the quotients is
where the sheaf theory enters: `Γ(U, ℐⁿ) ⟶ Γ(U, ℐⁿ/ℐⁿ⁺¹)` is surjective only locally.

## Main definitions

* `Stacks.Conormal.ambient`: the function underlying a section of `ℐⁿ · 𝒪_X`, with the ring of
  scalars spelled `Γ(X, U)`.
* `Stacks.Conormal.mulSection` and `Stacks.Conormal.idealPowerMul`: the multiplication
  `ℐⁿ × ℐᵐ ⟶ ℐⁿ⁺ᵐ` of the Rees filtration, as a bilinear map of `𝒪_X`-modules.
* `Stacks.Conormal.grMul`: **the multiplication `ℐⁿ/ℐⁿ⁺¹ × ℐᵐ/ℐᵐ⁺¹ ⟶ ℐⁿ⁺ᵐ/ℐⁿ⁺ᵐ⁺¹` of the
  associated graded**, the Rees multiplication descended along the quotient maps.

## Main results

* `Stacks.Conormal.exact_grPieceπ_app_opens`: **over every open** the sections of `ℐⁿ` killed in
  `ℐⁿ/ℐⁿ⁺¹` are exactly those coming from `ℐⁿ⁺¹`.
* `Stacks.Conormal.grMul_app_π`: the multiplication of the associated graded computes the
  product of representatives.  This pins it down, a bilinear map into a separated presheaf
  being determined by its restriction along a locally surjective morphism in each variable
  (`Stacks.BilinearMap.compLeft_injective`).

## Implementation notes

`Stacks.Conormal.ambient` is `Stacks.AlgebraicGeometry.GabberColimit.valSection` with the
result type declared to be `Γ(X, U)` rather than `Γ(structureModule X, U)`; the two are
definitionally equal, but only the first carries the `CommRing` instance, so only the first
admits the multiplication.  Each law of `idealPowerMul` is then the corresponding identity in
the commutative ring `Γ(X, U)`, because `ambient` is injective and carries the multiplication
of sections, the scalar action and the restriction maps of `ℐⁿ · 𝒪_X` to multiplication,
multiplication and the restriction ring homomorphism of `𝒪_X`, all three by definition.

`exact_grPieceπ_app_opens` holds over an arbitrary open, not merely an affine one, because
`Stacks.Conormal.idealPowerStepIsKernel` exhibits the step map of the filtration as a *kernel*
of the quotient map and the sections functor preserves kernels
(`Stacks.AlgebraicGeometry.QcohLimits.exact_app_kernel`).  The affine-open statement
`Stacks.Conormal.exact_grPieceπ_app` is the same fact obtained from right-exactness of
`Γ(V, -)`.

## References

* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.GabberColimit Stacks.AlgebraicGeometry.IdealPowerSmul

universe u

namespace Stacks.Conormal

variable {X : Scheme.{u}} (I : X.IdealSheafData) (n m : ℕ)

/-- The function underlying a section of `ℐⁿ · 𝒪_X`, with the ring of scalars spelled
`Γ(X, U)`. -/
def ambient {U : X.Opens} (s : Γ(idealPower I n, U)) : Γ(X, U) :=
  valSection (structureModule X) (idealPowFamily I n (structureModule X))
    (isCompatible_idealPowFamily I n (structureModule X)) s

/-- Over an affine open the function underlying a section of `ℐⁿ · 𝒪_X` lies in `ℐ(W)ⁿ`. -/
theorem ambient_mem {U : X.Opens} (s : Γ(idealPower I n, U)) (W : X.affineOpens)
    (hW : W.1 ≤ U) :
    (X.presheaf.map (homOfLE hW).op).hom (ambient I n s) ∈ I.ideal W ^ n := by
  have h := s.2 W hW
  rwa [← AssociatedGraded.ring_power_eq (I.ideal W) n, AssociatedGraded.power]

/-- A function whose restriction to every affine open lies in the corresponding power of the
ideal is a section of `ℐⁿ · 𝒪_X`. -/
theorem isLocallyIn_of_mem_pow {U : X.Opens} (a : Γ(X, U))
    (h : ∀ (W : X.affineOpens) (hW : W.1 ≤ U),
      (X.presheaf.map (homOfLE hW).op).hom a ∈ I.ideal W ^ n) :
    IsLocallyIn (structureModule X) (idealPowFamily I n (structureModule X))
      (show Γ(structureModule X, U) from a) := by
  intro W hW
  have h2 := h W hW
  rwa [← AssociatedGraded.ring_power_eq (I.ideal W) n, AssociatedGraded.power] at h2

/-- **The product of a section of `ℐⁿ` and a section of `ℐᵐ` is a section of `ℐⁿ⁺ᵐ`.** -/
def mulSection {U : X.Opens} (s : Γ(idealPower I n, U)) (t : Γ(idealPower I m, U)) :
    Γ(idealPower I (n + m), U) :=
  mkSection (structureModule X) (idealPowFamily I (n + m) (structureModule X))
    (isCompatible_idealPowFamily I (n + m) (structureModule X))
    (show Γ(structureModule X, U) from ambient I n s * ambient I m t)
    (isLocallyIn_of_mem_pow I (n + m) _ fun W hW => by
      rw [map_mul, pow_add]
      exact Ideal.mul_mem_mul (ambient_mem I n s W hW) (ambient_mem I m t W hW))

/-- The function underlying the product of two sections is the product of their functions. -/
@[simp] theorem ambient_mulSection {U : X.Opens} (s : Γ(idealPower I n, U))
    (t : Γ(idealPower I m, U)) :
    ambient I (n + m) (mulSection I n m s t) = ambient I n s * ambient I m t := rfl

/-- Sections of `ℐⁿ · 𝒪_X` are determined by the function underlying them. -/
theorem ambient_injective {U : X.Opens} : Function.Injective (ambient I n (U := U)) :=
  fun _ _ h => valSection_inj (structureModule X) _
    (isCompatible_idealPowFamily I n (structureModule X)) h

/-- The function underlying a sum of sections is the sum of their functions. -/
@[simp] theorem ambient_add {U : X.Opens} (s s' : Γ(idealPower I n, U)) :
    ambient I n (s + s') = ambient I n s + ambient I n s' := rfl

/-- The function underlying `r • s` is `r` times the function underlying `s`. -/
@[simp] theorem ambient_smul {U : X.Opens} (r : Γ(X, U)) (s : Γ(idealPower I n, U)) :
    ambient I n (r • s) = r * ambient I n s := rfl

/-! ### The multiplication of the Rees filtration -/

/-- The function underlying a restricted section is the restriction of its function. -/
@[simp] theorem ambient_map {U W : (Opens ↥X)ᵒᵖ} (f : U ⟶ W)
    (s : (idealPower I n).val.obj U) :
    ambient I n ((idealPower I n).val.map f s) = (X.presheaf.map f).hom (ambient I n s) := rfl

/-- Multiplication of sections of the filtration over a fixed open, as a biadditive map. -/
def mulApp (U : X.Opens) :
    Γ(idealPower I n, U) →+ Γ(idealPower I m, U) →+ Γ(idealPower I (n + m), U) :=
  AddMonoidHom.mk'
    (fun s => AddMonoidHom.mk' (fun t => mulSection I n m s t)
      (fun t t' => ambient_injective I (n + m)
        (mul_add (ambient I n s) (ambient I m t) (ambient I m t'))))
    (fun s s' => AddMonoidHom.ext fun t =>
      ambient_injective I (n + m)
        (add_mul (ambient I n s) (ambient I n s') (ambient I m t)))

/-- The function underlying `mulApp I n m U s t` is the product of the functions underlying `s`
and `t`. -/
@[simp] theorem ambient_mulApp (U : X.Opens) (s : Γ(idealPower I n, U))
    (t : Γ(idealPower I m, U)) :
    ambient I (n + m) (mulApp I n m U s t) = ambient I n s * ambient I m t := rfl

/-- **Multiplication of sections of the `ℐ`-adic filtration**, as a bilinear map of
`𝒪_X`-modules `ℐⁿ × ℐᵐ ⟶ ℐⁿ⁺ᵐ`. -/
def idealPowerMul : SheafOfModules.BilinearMap (idealPower I n) (idealPower I m)
    (idealPower I (n + m)) where
  app U := mulApp I n m U.unop
  map_smul_left U r s t := ambient_injective I (n + m)
    (mul_assoc (show Γ(X, U.unop) from r) (ambient I n s) (ambient I m t))
  map_smul_right U r s t := ambient_injective I (n + m)
    (mul_left_comm (ambient I n s) (show Γ(X, U.unop) from r) (ambient I m t))
  naturality f s t := ambient_injective I (n + m)
    (map_mul (X.presheaf.map f).hom (ambient I n s) (ambient I m t))

/-- The function underlying the product of two sections under `idealPowerMul` is the product of
their functions. -/
@[simp] theorem ambient_idealPowerMul (U : (Opens ↥X)ᵒᵖ) (s : (idealPower I n).val.obj U)
    (t : (idealPower I m).val.obj U) :
    ambient I (n + m) ((idealPowerMul I n m).app U s t) =
      ambient I n s * ambient I m t := rfl

/-! ### The quotient map is exact on sections over every open -/

/-- **Over every open the sections of `ℐⁿ` killed in `ℐⁿ/ℐⁿ⁺¹` are exactly those coming from
`ℐⁿ⁺¹`.** -/
theorem exact_grPieceπ_app_opens (W : X.Opens) :
    Function.Exact ((idealPowerStep I n).app W) ((grPieceπ I n).app W) := by
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' (idealPowerStepIsKernel I n)
    (kernel.ι (grPieceπ I n)) (kernel.condition (grPieceπ I n))
  have hlcomp : l ≫ idealPowerStep I n = kernel.ι (grPieceπ I n) := hl
  intro z
  constructor
  · intro hz
    obtain ⟨k, hk⟩ :=
      (Stacks.AlgebraicGeometry.QcohLimits.exact_app_kernel (grPieceπ I n) W z).mp hz
    refine ⟨l.app W k, ?_⟩
    have h0 := congrArg
      (fun φ : kernel (grPieceπ I n) ⟶ idealPower I n => Scheme.Modules.Hom.app φ W k)
      hlcomp
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h0
    rw [h0, hk]
  · rintro ⟨b, rfl⟩
    have h0 := congrArg
      (fun φ : idealPower I (n + 1) ⟶ grPiece I n => Scheme.Modules.Hom.app φ W b)
      (idealPowerStep_comp_grPieceπ I n)
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h0
    rw [h0]
    simp

/-! ### Descending the multiplication to the quotients -/

/-- A function whose restriction to every affine open lies in the corresponding power of the
ideal, read as a section of `ℐᵏ · 𝒪_X`. -/
def mkIdealPowerSection (k : ℕ) {U : X.Opens} (a : Γ(X, U))
    (h : ∀ (W : X.affineOpens) (hW : W.1 ≤ U),
      (X.presheaf.map (homOfLE hW).op).hom a ∈ I.ideal W ^ k) :
    Γ(idealPower I k, U) :=
  mkSection (structureModule X) (idealPowFamily I k (structureModule X))
    (isCompatible_idealPowFamily I k (structureModule X)) a (isLocallyIn_of_mem_pow I k a h)

/-- The function underlying `mkIdealPowerSection I k a h` is `a`. -/
@[simp] theorem ambient_mkIdealPowerSection (k : ℕ) {U : X.Opens} (a : Γ(X, U))
    (h : ∀ (W : X.affineOpens) (hW : W.1 ≤ U),
      (X.presheaf.map (homOfLE hW).op).hom a ∈ I.ideal W ^ k) :
    ambient I k (mkIdealPowerSection I k a h) = a := rfl

/-- The step map of the filtration does not change the underlying function. -/
@[simp] theorem ambient_idealPowerStep {U : X.Opens} (b : Γ(idealPower I (n + 1), U)) :
    ambient I n ((idealPowerStep I n).app U b) = ambient I (n + 1) b := rfl

/-- **The multiplication of the Rees filtration, followed by the quotient map**: the bilinear
map `ℐⁿ × ℐᵐ ⟶ ℐⁿ⁺ᵐ/ℐⁿ⁺ᵐ⁺¹`. -/
def grMulBil : SheafOfModules.BilinearMap (idealPower I n) (idealPower I m)
    (grPiece I (n + m)) :=
  SheafOfModules.bilinearPostcomp (idealPowerMul I n m) (grPieceπ I (n + m))

/-- On sections over `U`, `grMulBil` is the product `mulApp` followed by the quotient map
`ℐⁿ⁺ᵐ ⟶ ℐⁿ⁺ᵐ/ℐⁿ⁺ᵐ⁺¹`. -/
@[simp] theorem grMulBil_app (U : (Opens ↥X)ᵒᵖ) (s : (idealPower I n).val.obj U)
    (t : (idealPower I m).val.obj U) :
    (grMulBil I n m).app U s t =
      ((grPieceπ I (n + m)).val.app U).hom (mulApp I n m U.unop s t) := rfl

/-- A section of `ℐᵏ` whose function is a product of sections of `ℐⁱ` and `ℐʲ` with
`i + j = k + 1` dies in `ℐᵏ/ℐᵏ⁺¹`. -/
private theorem grPieceπ_app_eq_zero_of_mul {k i j : ℕ} (hij : i + j = k + 1) (U : X.Opens)
    (z : Γ(idealPower I k, U)) (s : Γ(idealPower I i, U)) (t : Γ(idealPower I j, U))
    (hz : ambient I k z = ambient I i s * ambient I j t) :
    (grPieceπ I k).app U z = 0 := by
  refine (exact_grPieceπ_app_opens I k U _).mpr
    ⟨mkIdealPowerSection I (k + 1) (ambient I i s * ambient I j t) ?_,
      ambient_injective I k hz.symm⟩
  intro W hW
  rw [map_mul]
  have hmem := Ideal.mul_mem_mul (ambient_mem I i s W hW) (ambient_mem I j t W hW)
  rwa [← pow_add, hij] at hmem

/-- Two sections of `ℐⁿ` with the same class in `ℐⁿ/ℐⁿ⁺¹` differ by a section of `ℐⁿ⁺¹`. -/
private theorem exists_idealPowerStep_eq_sub {U : (Opens ↥X)ᵒᵖ} {p p' : (idealPower I n).val.obj U}
    (h : (grPieceπ I n).val.app U p = (grPieceπ I n).val.app U p') :
    ∃ b, (idealPowerStep I n).app U.unop b = p - p' := by
  refine (exact_grPieceπ_app_opens I n U.unop (p - p')).mp ?_
  change (grPieceπ I n).val.app U (p - p') = 0
  rw [map_sub]
  exact sub_eq_zero_of_eq h

/-- **A section of `ℐⁿ⁺¹` multiplied by a section of `ℐᵐ` dies in `ℐⁿ⁺ᵐ/ℐⁿ⁺ᵐ⁺¹`.** -/
theorem grMulBil_app_idealPowerStep (U : X.Opens) (b : Γ(idealPower I (n + 1), U))
    (y : Γ(idealPower I m, U)) :
    (grMulBil I n m).app (op U) ((idealPowerStep I n).app U b) y = 0 :=
  grPieceπ_app_eq_zero_of_mul I (by lia) U _ b y rfl

/-- **The quotient map in the first variable does not change the product in `ℐⁿ⁺ᵐ/ℐⁿ⁺ᵐ⁺¹`.** -/
theorem factors_grMulBil (U : (Opens ↥X)ᵒᵖ) (p p' : (idealPower I n).val.obj U)
    (h : (grPieceπ I n).val.app U p = (grPieceπ I n).val.app U p')
    (y : (idealPower I m).val.obj U) :
    (grMulBil I n m).app U p y = (grMulBil I n m).app U p' y := by
  obtain ⟨b, hb⟩ := exists_idealPowerStep_eq_sub I n h
  have hzero : (grMulBil I n m).app U (p - p') y = 0 := by
    rw [← hb]
    exact grMulBil_app_idealPowerStep I n m U.unop b y
  rw [map_sub, AddMonoidHom.sub_apply] at hzero
  exact sub_eq_zero.mp hzero

/-! ### The multiplication of the associated graded -/

/-- The quotient map `ℐⁿ ⟶ ℐⁿ/ℐⁿ⁺¹` is locally surjective: it is an epimorphism of sheaves of
modules, being a cokernel projection. -/
instance isLocallySurjective_grPieceπ :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥X) (grPieceπ I n).val := by
  have : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ _ _ (grPieceπ I n) := epi_grPieceπ I n
  exact Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi (grPieceπ I n)

/-- **A section of `ℐⁿ` multiplied by a section of `ℐᵐ⁺¹` dies in `ℐⁿ⁺ᵐ/ℐⁿ⁺ᵐ⁺¹`.** -/
theorem grMulBil_app_idealPowerStep_right (U : X.Opens) (p : Γ(idealPower I n, U))
    (c : Γ(idealPower I (m + 1), U)) :
    (grMulBil I n m).app (op U) p ((idealPowerStep I m).app U c) = 0 :=
  grPieceπ_app_eq_zero_of_mul I (by lia) U _ p c rfl

/-- **The multiplication `ℐⁿ/ℐⁿ⁺¹ × ℐᵐ ⟶ ℐⁿ⁺ᵐ/ℐⁿ⁺ᵐ⁺¹`**, the Rees multiplication descended in
its first variable along `ℐⁿ ↠ ℐⁿ/ℐⁿ⁺¹`. -/
def grMulLeft : SheafOfModules.BilinearMap (grPiece I n) (idealPower I m)
    (grPiece I (n + m)) :=
  Stacks.BilinearMap.extendOfFactors (grPiece I (n + m)).isSheaf (grPieceπ I n).val (grMulBil I n m)
    (factors_grMulBil I n m)

/-- The descended multiplication computes the Rees product on a representative. -/
@[simp] theorem grMulLeft_app_π (U : (Opens ↥X)ᵒᵖ) (p : (idealPower I n).val.obj U)
    (t : (idealPower I m).val.obj U) :
    (grMulLeft I n m).app U ((grPieceπ I n).val.app U p) t = (grMulBil I n m).app U p t :=
  Stacks.BilinearMap.extendValOfFactors_app (grPiece I (n + m)).isSheaf (grPieceπ I n).val
    (grMulBil I n m) (factors_grMulBil I n m) p t

/-- **The descended multiplication does not distinguish two sections of `ℐᵐ` with the same
class mod `ℐᵐ⁺¹`.** -/
theorem factors_grMulLeft_flip (U : (Opens ↥X)ᵒᵖ) (q q' : (idealPower I m).val.obj U)
    (h : (grPieceπ I m).val.app U q = (grPieceπ I m).val.app U q')
    (y : (grPiece I n).val.obj U) :
    (grMulLeft I n m).flip.app U q y = (grMulLeft I n m).flip.app U q' y := by
  obtain ⟨c, hc⟩ := exists_idealPowerStep_eq_sub I m h
  have hzero : (grMulLeft I n m).app U y (q - q') = 0 := by
    refine Stacks.eq_of_forall_lift (grPiece I (n + m)).isSheaf.isSeparated
      (grPieceπ I n).val y _ 0 ?_
    intro Y f p hp
    have e1 : (grPiece I (n + m)).val.map f ((grMulLeft I n m).app U y (q - q')) =
        (grMulLeft I n m).app Y ((grPieceπ I n).val.app Y p)
          ((idealPower I m).val.map f (q - q')) := by
      rw [(grMulLeft I n m).naturality f y (q - q'), hp]
    have e2 : (idealPower I m).val.map f (q - q') =
        (idealPowerStep I m).app Y.unop ((idealPower I (m + 1)).val.map f c) := by
      rw [← hc]
      exact (PresheafOfModules.naturality_apply (idealPowerStep I m).val f c).symm
    have e3 : (grMulLeft I n m).app Y ((grPieceπ I n).val.app Y p)
        ((idealPower I m).val.map f (q - q')) = 0 :=
      (grMulLeft_app_π I n m Y p _).trans (by
        rw [e2]
        exact grMulBil_app_idealPowerStep_right I n m Y.unop p _)
    refine (e1.trans e3).trans ?_
    exact (map_zero (ConcreteCategory.hom ((grPiece I (n + m)).val.map f))).symm
  exact sub_eq_zero.mp
    ((map_sub ((grMulLeft I n m).app U y) q q').symm.trans hzero)

/-- **The multiplication of the associated graded algebra**, `ℐⁿ/ℐⁿ⁺¹ × ℐᵐ/ℐᵐ⁺¹ ⟶
ℐⁿ⁺ᵐ/ℐⁿ⁺ᵐ⁺¹`: the Rees multiplication descended in both variables. -/
def grMul : SheafOfModules.BilinearMap (grPiece I n) (grPiece I m) (grPiece I (n + m)) :=
  (Stacks.BilinearMap.extendOfFactors (grPiece I (n + m)).isSheaf (grPieceπ I m).val
    (grMulLeft I n m).flip (factors_grMulLeft_flip I n m)).flip

/-- **The multiplication of the associated graded computes the product of representatives.** -/
@[simp] theorem grMul_app_π (U : (Opens ↥X)ᵒᵖ) (p : (idealPower I n).val.obj U)
    (q : (idealPower I m).val.obj U) :
    (grMul I n m).app U ((grPieceπ I n).val.app U p) ((grPieceπ I m).val.app U q) =
      (grPieceπ I (n + m)).val.app U (mulApp I n m U.unop p q) :=
  (Stacks.BilinearMap.extendValOfFactors_app (grPiece I (n + m)).isSheaf (grPieceπ I m).val
    (grMulLeft I n m).flip (factors_grMulLeft_flip I n m) q
      ((grPieceπ I n).val.app U p)).trans (grMulLeft_app_π I n m U p q)

end Stacks.Conormal

end
