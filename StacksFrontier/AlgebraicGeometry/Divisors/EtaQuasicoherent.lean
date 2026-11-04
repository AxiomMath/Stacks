module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.BiproductQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherence of the Berthelot–Ogus décalage

Let `X` be a scheme, let `D ⊆ X` be an effective Cartier divisor with ideal sheaf `I ⊆ 𝒪_X`, and
let `F^•` be a complex of quasi-coherent `𝒪_X`-modules whose terms are `I`-torsion free. The
décalage `η_I F^•` has degree-`n` term the fibre product of `I^n F^n` and `I^{n+1} F^{n+1}` over
`I^n F^{n+1}`. Each of the three corners is quasi-coherent — this is where the invertibility of
`I` enters, since the exponent runs over all of `ℤ` and a negative power is a twist by the
tensor inverse of `I` — and a fibre product of quasi-coherent modules is quasi-coherent, being a
kernel of a map out of a direct sum.

## Main results

* `Stacks.Divisors.Eta.isQuasicoherent_etaObj`: every term of `η_I F^•` is quasi-coherent.

## Implementation notes

The décalage is `Stacks.IdealTorsion.Eta.etaObj`; nothing about it is redefined here. "A complex
of quasi-coherent modules" is `∀ n, (F.X n).IsQuasicoherent`, there being no bundled category of
quasi-coherent modules.

The ideal powers are the integer iterates `Stacks.IdealTorsion.Eta.idealPowerTerm` of the
autoequivalence `- ⊗ I`. Quasi-coherence of `I^n F` is proved by induction in both directions
from `n = 0`, the step up being `idealPowerSuccIso` together with Tag 01CE, and the step down
being `idealPowerPredIso`, which uses the associativity and right unit constraints of the sheaf
tensor product to untwist by a tensor inverse of `I`. That inverse exists by Tag 0B8K and is
itself invertible, hence quasi-coherent, by the converse clause of Tag 0B8M.

Several spellings of the sheaf of rings of `X` are in play:
`Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩`,
which the tensor-power calculus and the décalage use; `structureSheafRing X.toRingedSpace`, which
the ringed-space statements of Tags 01CE and 0B8M use; and `X.ringCatSheaf`, which indexes
Mathlib's `X.Modules` and hence the kernel statement of this file. These are the same sheaf of
rings, but identifying them unfolds `CategoryTheory.sheafCompose`, which does not unfold at the
transparency at which instances are synthesized. Every statement below is therefore phrased in
the first spelling — the spelling the décalage itself carries — and each appeal to a result in
another spelling passes its hypotheses explicitly, where the check runs at default transparency;
that is why `isQuasicoherent_kernel` is applied with its quasi-coherence arguments written out.
`Mono (idealSheafι D)` is supplied by hand for the same reason.

## References

* [Stacks Project, Tag 0F8M](https://stacks.math.columbia.edu/tag/0F8M)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01BF](https://stacks.math.columbia.edu/tag/01BF)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.IdealTorsion.Eta (etaObj etaTerm idealPowerTerm)
open Stacks.SheafOfModules.TensorSheafification
open Stacks.SheafOfModules.Invertible (tensorProductIso
  tensorProductAssociator tensorProductRightUnitor tensorProductBraiding)

universe u

namespace Stacks.Divisors.Eta

variable {X : Scheme.{u}}

local notation "Oₚ" => X.toRingedSpace.sheaf.obj
local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf
  (CategoryTheory.ObjectProperty.FullSubcategory.mk X.toRingedSpace.presheaf
    X.toRingedSpace.IsSheaf))

/-- The ideal sheaf of a closed subscheme `D ⊆ X`, as a sheaf of `𝒪_X`-modules: the kernel of
`𝒪_X ⟶ i_* 𝒪_D`. -/
noncomputable abbrev idealSheaf (D : X.IdealSheafData) : SheafOfModules.{u} Oₓ :=
  Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom

/-- The inclusion `I_D ⟶ 𝒪_X` of the ideal sheaf of a closed subscheme. -/
noncomputable abbrev idealSheafι (D : X.IdealSheafData) :
    idealSheaf D ⟶ SheafOfModules.unit Oₓ :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (RingedSpaceModuleAdjunction.structureSheafHom D.subschemeι.toLRSHom.toShHom))

/-- The inclusion of an ideal sheaf into the structure sheaf is a monomorphism, being a kernel
inclusion. -/
instance mono_idealSheafι (D : X.IdealSheafData) : Mono (idealSheafι D) :=
  inferInstanceAs (Mono (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (RingedSpaceModuleAdjunction.structureSheafHom D.subschemeι.toLRSHom.toShHom))))

/-- The ideal sheaf of an effective Cartier divisor is invertible, in the spelling of
[Stacks, Tag 01CS] that the tensor-power calculus uses. -/
instance isInvertible_idealSheaf (D : X.IdealSheafData)
    [hD : Stacks.Divisors.IsEffectiveCartierDivisor D] :
    Stacks.SheafOfModules.IsInvertible Oₚ (Oₓ).property (idealSheaf D) :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry Oₚ (Oₓ).property (idealSheaf D) hD

/-- An invertible sheaf of modules on a scheme is quasi-coherent: by the converse clause of
[Stacks, Tag 0B8M] it is finite locally free of rank one, hence locally free, hence
quasi-coherent. -/
theorem isQuasicoherent_of_isInvertible (L : SheafOfModules.{u} Oₓ)
    (hL : Stacks.SheafOfModules.IsInvertible Oₚ (Oₓ).property L) : L.IsQuasicoherent :=
  have : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
      L := hL
  Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible X L

/-- **[Stacks, Tag 01CE].** The sheaf tensor product of two quasi-coherent sheaves of modules on
a scheme is quasi-coherent. -/
theorem isQuasicoherent_tensorSheaf (A B : SheafOfModules.{u} Oₓ)
    (hA : A.IsQuasicoherent) (hB : B.IsQuasicoherent) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Oₚ, Presheaf.isSheaf_of_isSheaf_comp _ (Oₚ) (forget₂ CommRingCat RingCat)
        ((Oₓ).property)⟩).obj (A)).obj (B))).IsQuasicoherent :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent.{u} X.toRingedSpace A B hA hB

/-- A fibre product of quasi-coherent sheaves of modules is quasi-coherent: it is the kernel of
the map `A ⊕ B ⟶ C` with components `f` and `-g`, the direct sum is quasi-coherent by
[Stacks, Tag 01BF], and a kernel of a morphism of quasi-coherent modules is quasi-coherent. -/
theorem isQuasicoherent_pullback {A B C : SheafOfModules.{u} Oₓ} (f : A ⟶ C) (g : B ⟶ C)
    (hA : A.IsQuasicoherent) (hB : B.IsQuasicoherent) (hC : C.IsQuasicoherent) :
    (pullback f g).IsQuasicoherent := by
  have hAB : (A ⊞ B).IsQuasicoherent := AlgebraicGeometry.directSum_isQuasicoherent Oₓ A B
  let d : (A ⊞ B) ⟶ C := biprod.desc f (-g)
  have hker : (kernel d).IsQuasicoherent :=
    @Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel X _ _ d hAB hC
  have e : pullback f g ≅ kernel d :=
    (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct f g).conePointUniqueUpToIso
      (limit.isLimit _)
  exact (SheafOfModules.isQuasicoherent Oₓ).prop_of_iso e.symm hker

/-- Tensoring on the right by an invertible sheaf of modules is an autoequivalence, in the
spelling of invertibility that an ideal sheaf carries. -/
instance isEquivalence_tensorRightFunctor (I : SheafOfModules.{u} Oₓ)
    [hI : Stacks.SheafOfModules.IsInvertible Oₚ (Oₓ).property I] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Oₚ, Presheaf.isSheaf_of_isSheaf_comp _ (Oₚ) (forget₂ CommRingCat RingCat)
        ((Oₓ).property)⟩).flip.obj (I))).IsEquivalence :=
  have : AlgebraicGeometry.SheafOfModules.IsInvertible Oₚ (Oₓ).property I :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry Oₚ (Oₓ).property I hI
  Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence Oₚ (Oₓ).property I

/-- The successor comparison for the ideal powers acting on a module: twisting `I^n F` once more
by `I` gives `I^{n+1} F`. This is the successor comparison of the iterated autoequivalence
`- ⊗ I`. -/
noncomputable def idealPowerSuccIso (I : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible Oₚ (Oₓ).property I] (M : SheafOfModules.{u} Oₓ) (n : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Oₚ, Presheaf.isSheaf_of_isSheaf_comp _ (Oₚ) (forget₂ CommRingCat RingCat)
        ((Oₓ).property)⟩).obj ((idealPowerTerm X.toRingedSpace I n M))).obj (I)) ≅
      idealPowerTerm X.toRingedSpace I (n + 1) M :=
  Stacks.Equivalence.powSuccIso
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Oₚ, Presheaf.isSheaf_of_isSheaf_comp _ (Oₚ) (forget₂ CommRingCat RingCat)
        ((Oₓ).property)⟩).flip.obj (I))).asEquivalence n M

/-- The predecessor comparison for the ideal powers acting on a module: given a tensor inverse
`J` of `I`, twisting `I^{n+1} F` by `J` gives `I^n F`. -/
noncomputable def idealPowerPredIso (I J : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible Oₚ (Oₓ).property I]
    (e : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Oₚ, Presheaf.isSheaf_of_isSheaf_comp _ (Oₚ) (forget₂ CommRingCat RingCat)
        ((Oₓ).property)⟩).obj (I)).obj (J)) ≅ SheafOfModules.unit Oₓ)
    (M : SheafOfModules.{u} Oₓ) (n : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Oₚ, Presheaf.isSheaf_of_isSheaf_comp _ (Oₚ) (forget₂ CommRingCat RingCat)
        ((Oₓ).property)⟩).obj ((idealPowerTerm X.toRingedSpace I (n + 1) M))).obj (J)) ≅
      idealPowerTerm X.toRingedSpace I n M :=
  tensorProductIso Oₚ (Oₓ).property (idealPowerSuccIso I M n).symm (Iso.refl J) ≪≫
    tensorProductAssociator Oₚ (Oₓ).property (idealPowerTerm X.toRingedSpace I n M) I J ≪≫
    tensorProductIso Oₚ (Oₓ).property (Iso.refl (idealPowerTerm X.toRingedSpace I n M)) e ≪≫
    tensorProductRightUnitor Oₚ (Oₓ).property (idealPowerTerm X.toRingedSpace I n M)

/-- A tensor inverse of an invertible sheaf of modules is itself invertible: the symmetry
constraint turns `I ⊗ J ≅ 𝒪_X` into `J ⊗ I ≅ 𝒪_X`, which is the criterion of
[Stacks, Tag 0B8K]. -/
theorem isInvertible_of_tensor_iso_unit (I J : SheafOfModules.{u} Oₓ)
    (e : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Oₚ, Presheaf.isSheaf_of_isSheaf_comp _ (Oₚ) (forget₂ CommRingCat RingCat)
        ((Oₓ).property)⟩).obj (I)).obj (J)) ≅ SheafOfModules.unit Oₓ) :
    Stacks.SheafOfModules.IsInvertible Oₚ (Oₓ).property J :=
  (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := Oₚ) (hO := (Oₓ).property) J).mpr
      ⟨I, ⟨tensorProductBraiding Oₚ (Oₓ).property J I ≪≫ e⟩⟩

/-- Every non-negative ideal power of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherent_idealPowerTerm_natCast (I : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible Oₚ (Oₓ).property I] (hI : I.IsQuasicoherent)
    (M : SheafOfModules.{u} Oₓ) (hM : M.IsQuasicoherent) (n : ℕ) :
    (idealPowerTerm X.toRingedSpace I (n : ℤ) M).IsQuasicoherent := by
  induction n with
  | zero => exact hM
  | succ k ih =>
      rw [Nat.cast_succ]
      exact (SheafOfModules.isQuasicoherent Oₓ).prop_of_iso (idealPowerSuccIso I M (k : ℤ))
        (isQuasicoherent_tensorSheaf _ I ih hI)

/-- Every non-positive ideal power of a quasi-coherent module is quasi-coherent, given a
quasi-coherent tensor inverse of the ideal. -/
theorem isQuasicoherent_idealPowerTerm_neg (I J : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible Oₚ (Oₓ).property I] (hJ : J.IsQuasicoherent)
    (e : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Oₚ, Presheaf.isSheaf_of_isSheaf_comp _ (Oₚ) (forget₂ CommRingCat RingCat)
        ((Oₓ).property)⟩).obj (I)).obj (J)) ≅ SheafOfModules.unit Oₓ)
    (M : SheafOfModules.{u} Oₓ) (hM : M.IsQuasicoherent) (n : ℕ) :
    (idealPowerTerm X.toRingedSpace I (-(n : ℤ)) M).IsQuasicoherent := by
  induction n with
  | zero => rwa [Nat.cast_zero, neg_zero]
  | succ k ih =>
      have hstep :
          (idealPowerTerm X.toRingedSpace I ((-((k : ℤ) + 1)) + 1) M).IsQuasicoherent := by
        rwa [show (-((k : ℤ) + 1)) + 1 = -(k : ℤ) by ring]
      rw [Nat.cast_succ]
      exact (SheafOfModules.isQuasicoherent Oₓ).prop_of_iso
        (idealPowerPredIso I J e M (-((k : ℤ) + 1)))
        (isQuasicoherent_tensorSheaf _ J hstep hJ)

/-- Every integer ideal power of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherent_idealPowerTerm (I : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible Oₚ (Oₓ).property I] (hI : I.IsQuasicoherent)
    (M : SheafOfModules.{u} Oₓ) (hM : M.IsQuasicoherent) (n : ℤ) :
    (idealPowerTerm X.toRingedSpace I n M).IsQuasicoherent := by
  obtain ⟨J, ⟨e⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := Oₚ) (hO := (Oₓ).property) I).mp inferInstance
  have hJ : J.IsQuasicoherent :=
    isQuasicoherent_of_isInvertible J (isInvertible_of_tensor_iso_unit I J e)
  rcases le_or_gt 0 n with h | h
  · rw [show n = (n.toNat : ℤ) by omega]
    exact isQuasicoherent_idealPowerTerm_natCast I hI M hM n.toNat
  · rw [show n = -((-n).toNat : ℤ) by omega]
    exact isQuasicoherent_idealPowerTerm_neg I J hJ e M hM (-n).toNat

/-- **[Stacks, Tag 0F8M], first assertion.** Let `X` be a scheme, let `D ⊆ X` be an effective
Cartier divisor with ideal sheaf `I ⊆ 𝒪_X`, and let `F^•` be a complex of quasi-coherent
`𝒪_X`-modules whose terms are `I`-torsion free. Then `η_I F^•` is a complex of quasi-coherent
`𝒪_X`-modules. -/
@[stacks 0F8M "eta is a complex of quasi-coherent modules"]
theorem isQuasicoherent_etaObj (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hqc : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    (htf : ∀ n : ℤ,
      Stacks.IdealTorsion.IsIdealTorsionFree X.toRingedSpace (idealSheafι D) (F.X n))
    (n : ℤ) :
    ((etaObj X.toRingedSpace (idealSheaf D) (idealSheafι D) F htf).X n).IsQuasicoherent := by
  have hI : (idealSheaf D).IsQuasicoherent :=
    isQuasicoherent_of_isInvertible (idealSheaf D) inferInstance
  have hpow : ∀ i j : ℤ,
      (idealPowerTerm X.toRingedSpace (idealSheaf D) i (F.X j)).IsQuasicoherent :=
    fun i j => isQuasicoherent_idealPowerTerm (idealSheaf D) hI (F.X j) (hqc j) i
  show (etaTerm X.toRingedSpace (idealSheaf D) (idealSheafι D) F n).IsQuasicoherent
  exact isQuasicoherent_pullback _ _ (hpow n n) (hpow (n + 1) (n + 1)) (hpow n (n + 1))

end Stacks.Divisors.Eta

end
