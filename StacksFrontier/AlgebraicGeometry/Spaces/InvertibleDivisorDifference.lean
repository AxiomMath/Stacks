module

public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDenseAffineOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularSectionEffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentHomColimitBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerAffineChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleDenseAffineTrivialization

/-!
# An invertible module on a regular Noetherian space is a difference of divisors

Let `S` be a scheme and let `X` be a regular Noetherian separated algebraic space over `S`.
Every invertible `𝒪_X`-module `L` is then isomorphic to `𝒪_X(D - D')` for a pair of effective
Cartier divisors `D, D' ⊆ X`.  This is Stacks 0DMM.

## Main definitions

* `AlgebraicGeometry.Space.succMultipleClosedSubspaces` is the multiple `(n + 1) D` of a closed
  subspace, the `(n + 1)`-fold sum of `D` with itself in the sense of Stacks 083U.
* `Stacks.SheafOfModules.Invertible.tensorInverseCancel` cancels an invertible tensor factor
  against its inverse: `(Q ⊗ P) ⊗ P^{⊗ -1} ≅ Q`.

## Main results

* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_succMultipleClosedSubspaces`: a positive
  multiple of an effective Cartier divisor is an effective Cartier divisor.
* `AlgebraicGeometry.Space.definingIdealSheaf_succMultipleClosedSubspaces`: the ideal sheaf of
  `(k + 1) D` is `𝓘_D^{k + 1}`.
* `Stacks.SheafOfModules.Invertible.exists_mono_unit_tensorSheaf`: a monomorphism out of a
  module paired with an invertible module `P` is, after twisting by `P`, a regular global
  section.
* `AlgebraicGeometry.Space.exists_isEffectiveCartierDivisor_iso_differenceDivisorSheaf_of_mono`:
  a monomorphism from the ideal sheaf of an effective Cartier divisor `E` into an invertible
  module `L` exhibits `L` as `𝒪_X(D - E)` for an effective Cartier divisor `D`.
* `AlgebraicGeometry.Space.exists_mono_idealPowModule_of_iso`: on a Noetherian algebraic space a
  trivialization `𝒪_U ≅ L|_U` of a coherent module over the complement `U` of a quasi-coherent
  sheaf of ideals `ℐ` extends to a monomorphism `ℐ^{N + 1} ⟶ L`.
* `AlgebraicGeometry.Space.exists_isEffectiveCartierDivisor_iso_differenceDivisorSheaf`:
  **Stacks 0DMM**.

## The argument

The argument is the source's.  A regular Noetherian separated algebraic space `X` has a dense
affine open subspace `U` on which `L` is trivial
(`AlgebraicGeometry.Space.exists_denseAffineOpenChart_bijective_smul`), and the complement of
`U` carries an effective Cartier divisor `D₀` by Stacks 0DML.  The trivialization `𝒪_U ≅ L|_U`
extends, for some `n > 0`, to a morphism `𝒪_X(-n D₀) = 𝓘_{D₀}^n ⟶ L` by Stacks 07UM; and so does
its inverse, to `𝓘_{D₀}^m L ⟶ 𝒪_X`.  Composing the two and comparing with the inclusion
`𝓘_{D₀}^{n + m} ⊆ 𝒪_X` by the injectivity half of Stacks 07UM shows that the extension is a
monomorphism on a deeper power of `𝓘_{D₀}`.  That power is the ideal sheaf of a positive
multiple `n D₀`, an effective Cartier divisor by Stacks 083V.

The monomorphism is then twisted by `𝒪_X(n D₀)` into a global section of `L ⊗ 𝒪_X(n D₀)`, which
is a regular section; Stacks 0847, part (2) produces an effective Cartier divisor `D` with
`𝒪_X(D) ≅ L ⊗ 𝒪_X(n D₀)`, and cancelling `𝒪_X(n D₀)` gives `L ≅ 𝒪_X(D - n D₀)`.  The twist is
the composite

`𝒪_X ≅ 𝒪_X(n D₀) ⊗ 𝓘_{n D₀} ≅ 𝓘_{n D₀} ⊗ 𝒪_X(n D₀) ⟶ L ⊗ 𝒪_X(n D₀)`,

whose first isomorphism is the evaluation pairing of Stacks 0841 for the divisor `n D₀`, whose
second is the braiding, and whose last arrow is the monomorphism tensored with the invertible
module `𝒪_X(n D₀)`, hence again a monomorphism.

## References

* [Stacks Project, Tag 0DMM](https://stacks.math.columbia.edu/tag/0DMM)
* [Stacks Project, Tag 0DML](https://stacks.math.columbia.edu/tag/0DML)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 0847](https://stacks.math.columbia.edu/tag/0847)
* [Stacks Project, Tag 0841](https://stacks.math.columbia.edu/tag/0841)
* [Stacks Project, Tag 083U](https://stacks.math.columbia.edu/tag/083U)
* [Stacks Project, Tag 083V](https://stacks.math.columbia.edu/tag/083V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Invertible
open Stacks.SheafOfModules.TensorSheafification

universe w v u

/-! ### Twisting a monomorphism by an invertible module -/

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

noncomputable section

/-- **A monomorphism out of a tensor inverse is a regular global section of the twist.**  Let
`P` be an invertible module, let `I` be a module paired with it by an isomorphism
`P ⊗ I ≅ 𝒪`, and let `φ : I ⟶ M` be a monomorphism.  Tensoring `φ` by `P` is again a
monomorphism, because tensoring by an invertible module is an equivalence, so the composite

`𝒪 ≅ P ⊗ I ≅ I ⊗ P ⟶ M ⊗ P`

is a monomorphism `𝒪 ⟶ M ⊗ P`, that is, a regular global section of `M ⊗ P`. -/
theorem exists_mono_unit_tensorSheaf
    (P I M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO P]
    (ev : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (P)).obj (I)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (φ : I ⟶ M) (hφ : Mono φ) :
    ∃ g : SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⟶
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (M)).obj (P)), Mono g := by
  have h1 : Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O
      (forget₂ CommRingCat RingCat) hO⟩).flip.obj P).map φ) :=
    mono_tensorRightFunctor_map O hO P φ hφ
  have hev : Mono ev.inv := @IsIso.mono_of_iso _ _ _ _ ev.inv (Iso.isIso_inv ev)
  have hb : Mono (tensorProductBraiding O hO P I).hom := inferInstance
  exact ⟨ev.inv ≫ (tensorProductBraiding O hO P I).hom ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj P).map φ,
    mono_comp' hev (mono_comp' hb h1)⟩

/-- **Cancelling an invertible tensor factor against its inverse**: `(Q ⊗ P) ⊗ P^{⊗ -1} ≅ Q`,
by associativity, the braiding, the evaluation pairing `P^{⊗ -1} ⊗ P ≅ 𝒪` and the right unit
constraint. -/
def tensorInverseCancel
    (P Q : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO P] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (Q)).obj (P))))).obj ((inverseSheaf O hO P))) ≅ Q :=
  tensorProductAssociator O hO Q P (inverseSheaf O hO P) ≪≫
    tensorProductIso O hO (Iso.refl Q) (tensorProductBraiding O hO P (inverseSheaf O hO P)) ≪≫
    tensorProductIso O hO (Iso.refl Q) (inverseSheafEvaluation O hO P) ≪≫
    tensorProductRightUnitor O hO Q

end

end Stacks.SheafOfModules.Invertible

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-! ### Positive multiples of a closed subspace -/

/-- **The multiple `(n + 1) D` of a closed subspace of an algebraic space**, formed by
iterating the sum of closed subspaces of Stacks 083U.  The offset by one is there because that
sum has no neutral element in the development: `succMultipleClosedSubspaces B S hS X D n` is
`(n + 1) D`, so that the multiples it produces are exactly the positive ones. -/
noncomputable def succMultipleClosedSubspaces (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) : ℕ → ClosedSubspaces B S hS X.1
  | 0 => D
  | n + 1 => sumClosedSubspaces B S hS X (succMultipleClosedSubspaces X D n) D

/-- **A positive multiple of an effective Cartier divisor is an effective Cartier divisor.**
Induction on the multiple, the inductive step being Stacks 083V. -/
theorem isEffectiveCartierDivisor_succMultipleClosedSubspaces (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (hD : IsEffectiveCartierDivisor B S hS X D) (n : ℕ) :
    IsEffectiveCartierDivisor B S hS X (succMultipleClosedSubspaces B S hS X D n) := by
  induction n with
  | zero => exact hD
  | succ n ih => exact isEffectiveCartierDivisor_sumClosedSubspaces B S hS X _ D ih hD

/-! ### Twisting a monomorphism out of an ideal sheaf into a divisor difference -/

/-- **A monomorphism from the ideal sheaf of an effective Cartier divisor into an invertible
module exhibits that module as a difference of two effective Cartier divisors.**  Tensoring the
monomorphism `𝓘_E ⟶ L` by the invertible module `𝒪_X(E)` and composing with the evaluation
pairing `𝒪_X(E) ⊗ 𝓘_E ≅ 𝒪_X` of Stacks 0841 gives a monomorphism `𝒪_X ⟶ L ⊗ 𝒪_X(E)`, that is,
a regular global section of the invertible module `L ⊗ 𝒪_X(E)`.  Stacks 0847, part (2) turns
that section into an effective Cartier divisor `D` with `𝒪_X(D) ≅ L ⊗ 𝒪_X(E)`, and cancelling
`𝒪_X(E)` against `𝒪_X(-E)` gives `L ≅ 𝒪_X(D - E)`. -/
theorem exists_isEffectiveCartierDivisor_iso_differenceDivisorSheaf_of_mono
    (X : AlgebraicSpaces B S hS)
    (L : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L)
    (E : ClosedSubspaces B S hS X.1) (hE : IsEffectiveCartierDivisor B S hS X E)
    (φ : idealSheafOfModules B S hS X E ⟶ L) (hφ : Mono φ) :
    ∃ (D : ClosedSubspaces B S hS X.1) (hD : IsEffectiveCartierDivisor B S hS X D),
      Nonempty (L ≅ differenceDivisorSheaf B S hS X D E hD hE) := by
  have hAinv : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property (associatedInvertibleSheaf B S hS X E hE) :=
    associatedInvertibleSheaf_isInvertible B S hS X E hE
  obtain ⟨g, hg⟩ := exists_mono_unit_tensorSheaf (structureCommRings B S hS X)
    (structureRingSheaf B S hS X).property (associatedInvertibleSheaf B S hS X E hE)
    (idealSheafOfModules B S hS X E) L (associatedInvertibleSheafEvaluation B S hS X E hE) φ hφ
  have hMinv : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
          ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
          ((structureRingSheaf B S hS X).property)⟩).obj (L)).obj
            ((associatedInvertibleSheaf B S hS X E hE)))) := by
    have hLB : Stacks.SheafOfModules.IsInvertible (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property L :=
      Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry.{u, u + 1, u} _ _ _ hL
    have hAB : Stacks.SheafOfModules.IsInvertible (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property (associatedInvertibleSheaf B S hS X E hE) :=
      Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry.{u, u + 1, u} _ _ _ hAinv
    exact Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry.{u, u + 1, u} _ _ _
      (Stacks.SheafOfModules.isInvertible_tensorSheaf.{u, u + 1, u} (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property _ _)
  have hs : AlgebraicGeometry.IsRegularSection (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property
      (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
          ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
          ((structureRingSheaf B S hS X).property)⟩).obj (L)).obj
            ((associatedInvertibleSheaf B S hS X E hE)))).unitHomEquiv g) := by
    let twist := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ⟨structureCommRings B S hS X, Presheaf.isSheaf_of_isSheaf_comp _
        (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
        (structureRingSheaf B S hS X).property⟩).obj L).obj
          (associatedInvertibleSheaf B S hS X E hE)
    show Mono (twist.unitHomEquiv.symm (twist.unitHomEquiv g))
    exact (congrArg (fun morphism => Mono morphism)
      (twist.unitHomEquiv.symm_apply_apply g)).mpr hg
  obtain ⟨D, hD, ⟨e⟩⟩ :=
    exists_isEffectiveCartierDivisor_associatedInvertibleSheaf_iso B S hS X _ hMinv _ hs
  refine ⟨D, hD, ⟨?_⟩⟩
  have hcancel : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
        ((structureRingSheaf B S hS X).property)⟩).obj
      (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
          ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
          ((structureRingSheaf B S hS X).property)⟩).obj (L)).obj
            ((associatedInvertibleSheaf B S hS X E hE)))))).obj
      ((negativeDivisorSheaf B S hS X E hE))) ≅ L :=
    tensorInverseCancel (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
      (associatedInvertibleSheaf B S hS X E hE) L
  exact (tensorProductIso (structureCommRings B S hS X) (structureRingSheaf B S hS X).property e
    (Iso.refl (negativeDivisorSheaf B S hS X E hE)) ≪≫ hcancel).symm

/-! ### The ideal sheaf of a positive multiple -/

/-- **The defining ideal sheaf of `(k + 1) D` is `𝓘_D^{k + 1}`**, the `(k + 1)`-st power of the
ideal sheaf of `D` acting on `𝒪_X`, for `𝓘_D` quasi-coherent.  On an affine chart lying over the
chart on which sums are formed the ideal of a sum is the product of the ideals (Stacks 083U), and
on an affine chart the sections of `𝓘_D^{k + 1} 𝒪_X` are `𝓘_D(V)^{k + 1}`. -/
theorem definingIdealSheaf_succMultipleClosedSubspaces (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1)
    (hD : (definingIdealSheaf B S hS X D).toSheafOfModules.IsQuasicoherentOnSite) (k : ℕ) :
    definingIdealSheaf B S hS X (succMultipleClosedSubspaces B S hS X D k) =
      idealPowSubmodule (definingIdealSheaf B S hS X D) (k + 1)
        (SheafOfModules.unit (structureRingSheaf B S hS X)) := by
  have hO : (SheafOfModules.unit (structureRingSheaf B S hS X)).IsQuasicoherentOnSite :=
    SheafOfModules.isQuasicoherentOnSite_unit _
  have hpow : ∀ (n : ℕ) (A : SmallEtale B S hS X.1),
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A) →
      (idealPowSubmodule (definingIdealSheaf B S hS X D) n
        (SheafOfModules.unit (structureRingSheaf B S hS X))).obj (op A) =
        definingIdealAt B S hS X D (op A) ^ n := by
    intro n A hA
    refine (chartSubmodule_idealPowSubmodule_eq_of_isQuasicoherentOnSite B S hS X.1 X.2
      (definingIdealSheaf B S hS X D) n _ hO hD A hA).trans ?_
    exact Ideal.mul_top _
  induction k with
  | zero =>
    refine structureSubmodule_ext_of_forall_isAffine B S hS X _ _ fun A hA => ?_
    exact ((hpow 1 A hA).trans (Submodule.pow_one _)).symm
  | succ k ih =>
    refine structureSubmodule_ext_of_forall_isAffine_hom B S hS X
      ⟨CostructuredArrow.mk (atlasHom B S hS X), atlasHom_etale B S hS X⟩
      ((presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 _ _).1
        (atlasHom_surjective B S hS X)) _ _ fun A hA m => ?_
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj A.obj.left) := hA
    show definingIdealAt B S hS X (sumClosedSubspaces B S hS X
      (succMultipleClosedSubspaces B S hS X D k) D) (op A) = _
    refine (definingIdealAt_sumClosedSubspaces_of_isAffine B S hS X _ D A m).trans ?_
    refine Eq.trans ?_ (hpow (k + 1 + 1) A hA).symm
    have h1 : definingIdealAt B S hS X (succMultipleClosedSubspaces B S hS X D k) (op A) =
        definingIdealAt B S hS X D (op A) ^ (k + 1) :=
      (congrArg (fun N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule =>
        N.obj (op A)) ih).trans (hpow (k + 1) A hA)
    rw [h1]
    exact (Submodule.pow_succ (M := definingIdealAt B S hS X D (op A))).symm

/-! ### Extending a trivialization off a divisor to a monomorphism -/

/-- **A trivialization of a coherent module over `U = X ∖ V(ℐ)` extends to a monomorphism
`ℐ^{N + 1} ⟶ L`.**  Let `X` be Noetherian, `ℐ` quasi-coherent and `θ : 𝒪_U ≅ L|_U`.  By Stacks
07UM `θ` extends to `φ : ℐⁿ ⟶ L` and `θ⁻¹` to `χ : ℐᵐ L ⟶ 𝒪_X`.  The morphism `φ` carries
`ℐ^{n + m}` into `ℐᵐ L`, and the composite `ℐ^{n + m} ⟶ ℐᵐ L ⟶ 𝒪_X` restricts on `U` to
`θ⁻¹ ∘ θ`, which is also the restriction of the inclusion `ℐ^{n + m} ⊆ 𝒪_X`; by injectivity in
Stacks 07UM the two agree on a deeper `ℐ^{n + m + k}`.  There the composite is a monomorphism,
hence so is `φ`. -/
theorem exists_mono_idealPowModule_of_iso (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hN : IsNoetherian B S hS hZ X.1)
    (I : IdealSheaves B S hS X.1 X.2) (hI : I.toSheafOfModules.IsQuasicoherentOnSite)
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : IsCoherent B S hS X.1 X.2 L)
    (θ : (restrictToIdealComplement B S hS X I).obj
        (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) ≅
      (restrictToIdealComplement B S hS X I).obj L) :
    ∃ (N : ℕ) (φ : idealPowModule I (N + 1)
        (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) ⟶ L),
      Mono φ := by
  have : Fact (HasEtaleLocalProperty B S hS X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hN.2.2⟩
  set O := SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
  have hO : IsCoherent B S hS X.1 X.2 O := isCoherent_structureSheaf B S hS X.1 X.2
  have : L.IsQuasicoherentOnSite := hL.toIsQuasicoherentOnSite
  have : O.IsQuasicoherentOnSite := hO.toIsQuasicoherentOnSite
  have hforget : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u + 1}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  have hext : ∀ (G F : Modules.{u, u} B S hS X.1 X.2) (_ : IsCoherent B S hS X.1 X.2 G)
      [F.IsQuasicoherentOnSite]
      (τ : (restrictToIdealComplement B S hS X I).obj G ⟶
        (restrictToIdealComplement B S hS X I).obj F),
      ∃ (n : ℕ) (φ : idealPowModule I n G ⟶ F), homRestrict B S hS X I φ = τ := by
    intro G F hG _ τ
    obtain ⟨z, hz⟩ := (canonicalMapToHomRestrict_bijective B S hS X I hZ hN hI G F hG).2 τ
    obtain ⟨n, φ, rfl⟩ := Limits.Concrete.colimit_exists_rep (homSystem B S hS X I G F) z
    exact ⟨n, φ, (canonicalMapToHomRestrict_ι B S hS X I G F n φ).symm.trans hz⟩
  obtain ⟨n, φ, hφ⟩ := hext O L hO θ.hom
  obtain ⟨m, χ, hχ⟩ := hext L O hL θ.inv
  -- `φ` carries `ℐ^{n + m}` into `ℐᵐ L`.
  have hmem : ∀ (W : (SmallEtale B S hS X.1)ᵒᵖ)
      (z : (idealPowModule I (n + m) O).val.obj W),
      ((idealPowModuleHomOfLE I O (Nat.le_add_right n m) ≫ φ).val.app W).hom z ∈
        (idealPowSubmodule I m L).obj W := fun W z =>
    (Stacks.Sites.idealPowSmul_mono_right I m le_top) W
      (Stacks.Sites.idealPowSmul_top_map_le φ I m W _
        (idealPowModuleHomOfLE_app_mem_idealPowSmul_top B S hS X I O n m W z))
  set φm := (idealPowSubmodule I m L).factorThru
    (idealPowModuleHomOfLE I O (Nat.le_add_right n m) ≫ φ) hmem
  have hφm : φm ≫ idealPowModuleι I m L =
      idealPowModuleHomOfLE I O (Nat.le_add_right n m) ≫ φ :=
    (idealPowSubmodule I m L).factorThru_ι _ hmem
  -- On `U` the composite `ℐ^{n + m} ⟶ ℐᵐ L ⟶ 𝒪_X` is the inclusion.
  have hres : homRestrict B S hS X I (φm ≫ χ) =
      homRestrict B S hS X I (idealPowModuleι I (n + m) O) := by
    have hRφm : (restrictToIdealComplement B S hS X I).map φm =
        ((restrictToIdealComplement B S hS X I).map
            (idealPowModuleHomOfLE I O (Nat.le_add_right n m)) ≫
          (restrictToIdealComplement B S hS X I).map φ) ≫
          (idealPowRestrictIso B S hS X I m L).inv := by
      rw [Iso.eq_comp_inv, idealPowRestrictIso_hom, ← Functor.map_comp, hφm, Functor.map_comp]
    have h1 : homRestrict B S hS X I (φm ≫ χ) = θ.hom ≫ θ.inv := by
      rw [← hφ, ← hχ]
      simp only [homRestrict, Functor.map_comp, hRφm, Category.assoc]
      rw [← Category.assoc (idealPowRestrictIso B S hS X I (n + m) O).inv,
        idealPowRestrictIso_inv_comp_map_idealPowModuleHomOfLE]
    rw [h1, Iso.hom_inv_id]
    simp only [homRestrict, ← idealPowRestrictIso_hom, Iso.inv_hom_id]
  -- By injectivity they agree on a deeper power.
  have hcol : Limits.colimit.ι (homSystem B S hS X I O O) (n + m) (φm ≫ χ) =
      Limits.colimit.ι (homSystem B S hS X I O O) (n + m) (idealPowModuleι I (n + m) O) := by
    refine canonicalMapToHomRestrict_injective B S hS X I hZ hN hI O O hO ?_
    rw [canonicalMapToHomRestrict_ι, canonicalMapToHomRestrict_ι, hres]
  obtain ⟨k, f, g, hfg⟩ := Limits.Concrete.colimit_exists_of_rep_eq _ _ _ hcol
  have hfg' : (homSystem B S hS X I O O).map f (φm ≫ χ) =
      (homSystem B S hS X I O O).map f (idealPowModuleι I (n + m) O) := by
    rw [hfg, Subsingleton.elim f g]
  rw [homSystem_map, homSystem_map, idealPowModuleHomOfLE_comp_ι] at hfg'
  have hmono₁ : Mono (idealPowModuleHomOfLE I O (leOfHom f) ≫ φm) := by
    have : Mono ((idealPowModuleHomOfLE I O (leOfHom f) ≫ φm) ≫ χ) := by
      rw [Category.assoc, hfg']
      infer_instance
    exact mono_of_mono _ χ
  have hk : n ≤ k + 1 := (Nat.le_add_right n m).trans ((leOfHom f).trans (Nat.le_succ k))
  refine ⟨k, idealPowModuleHomOfLE I O hk ≫ φ, ?_⟩
  have hfac : idealPowModuleHomOfLE I O hk ≫ φ =
      idealPowModuleHomOfLE I O (Nat.le_succ k) ≫
        (idealPowModuleHomOfLE I O (leOfHom f) ≫ φm) ≫ idealPowModuleι I m L := by
    rw [Category.assoc, hφm, ← Category.assoc, ← Category.assoc,
      Stacks.SheafOfModules.Submodule.homOfLE_comp_homOfLE,
      Stacks.SheafOfModules.Submodule.homOfLE_comp_homOfLE]
  rw [hfac]
  have : Mono (idealPowModuleHomOfLE I O (Nat.le_succ k)) :=
    mono_of_mono_fac (idealPowModuleHomOfLE_comp_ι I O (Nat.le_succ k))
  infer_instance

/-! ### Stacks 0DMM -/

/-- **Stacks Project, Tag 0DMM.**  Let `S` be a scheme and let `X` be a regular Noetherian
separated algebraic space over `S`.  Then every invertible `𝒪_X`-module `L` is isomorphic to
`𝒪_X(D - D') = 𝒪_X(D) ⊗_{𝒪_X} 𝒪_X(D')^{⊗ -1}` for effective Cartier divisors `D, D' ⊆ X`.

Following the source: choose a dense affine open subspace `U ⊆ X` on which `L` is trivial
(`AlgebraicGeometry.Space.exists_denseAffineOpenChart_bijective_smul`); its complement is an
effective Cartier divisor `D₀` by Stacks 0DML; the trivialization `𝒪_U ≅ L|_U` extends to a
monomorphism `𝓘_{D₀}^{n} ⟶ L` for some `n > 0` by Stacks 07UM
(`AlgebraicGeometry.Space.exists_mono_idealPowModule_of_iso`), and `𝓘_{D₀}^{n}` is the ideal
sheaf of the effective Cartier divisor `n D₀` (Stacks 083U, 083V).  Twisting by `𝒪_X(n D₀)`
gives a regular global section of `L ⊗ 𝒪_X(n D₀)`, which is `𝒪_X(D)` for an effective Cartier
divisor `D` by Stacks 0847, part (2); so `L ≅ 𝒪_X(D - n D₀)`. -/
@[stacks 0DMM]
theorem exists_isEffectiveCartierDivisor_iso_differenceDivisorSheaf
    (X : AlgebraicSpaces B S hS)
    (separated : IsAbsolutelySeparated B S hS hZ X.1)
    (noetherian : IsNoetherian B S hS hZ X.1)
    (regular : HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsRegular T))
    (L : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (invertible : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property L) :
    ∃ (D D' : ClosedSubspaces B S hS X.1) (cD : IsEffectiveCartierDivisor B S hS X D)
      (cD' : IsEffectiveCartierDivisor B S hS X D'),
      Nonempty (L ≅ differenceDivisorSheaf B S hS X D D' cD cD') := by
  have : Fact (HasEtaleLocalProperty B S hS X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨noetherian.2.2⟩
  -- A dense affine open subspace on which `L` is trivial, and its complementary divisor.
  obtain ⟨C, hCaff, hC, hCdense, s, hs⟩ :=
    exists_denseAffineOpenChart_bijective_smul B S hS hZ X noetherian L invertible
  obtain ⟨D₀, hD₀, hpt⟩ := exists_isEffectiveCartierDivisor_compl_denseAffineOpen' B S hS hZ X
    separated noetherian regular C.obj.left hCaff C.1.hom hC hCdense
  set I : IdealSheaves B S hS X.1 X.2 := definingIdealSheaf B S hS X D₀ with hIdef
  have hIq : I.toSheafOfModules.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertible B S hS X _ hD₀
  have hsub : idealUnitLocus B S hS X I ⊆
      Set.range (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom) := by
    have h1 := range_pointsMap_ι_eq_idealZeroLocus B S hS X D₀
    rw [hpt, idealZeroLocus] at h1
    exact (compl_inj_iff.mp h1).symm.le
  -- The trivialization over `U = X ∖ D₀`.
  have hLq := isQuasicoherentOnSite_of_isInvertible B S hS X L invertible
  have hLc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 L hLq
  have hθ := isIso_unitHomEquiv_symm_pcSection X I C hC hsub hCaff L hLc s hs
  have hLcoh : IsCoherent B S hS X.1 X.2 L :=
    isCoherent_of_isInvertible L
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry.{u, u + 1, u} _ _ _ invertible)
  -- It extends to a monomorphism out of a power of the ideal of `D₀`.
  obtain ⟨N, φ, hφ⟩ := exists_mono_idealPowModule_of_iso B S hS hZ X noetherian I hIq L hLcoh
    (@asIso _ _ _ _ ((SheafOfModules.unitHomEquiv _).symm (pcSection X I C hC hsub L s)) hθ)
  have hE : IsEffectiveCartierDivisor B S hS X (succMultipleClosedSubspaces B S hS X D₀ N) :=
    isEffectiveCartierDivisor_succMultipleClosedSubspaces B S hS X D₀ hD₀ N
  have hEq := definingIdealSheaf_succMultipleClosedSubspaces B S hS X D₀ hIq N
  have hmono : Mono (Stacks.SheafOfModules.Submodule.homOfLE hEq.le) :=
    mono_of_mono_fac (Stacks.SheafOfModules.Submodule.homOfLE_comp_ι hEq.le)
  obtain ⟨D, hD, hiso⟩ := exists_isEffectiveCartierDivisor_iso_differenceDivisorSheaf_of_mono
    B S hS X L invertible _ hE (Stacks.SheafOfModules.Submodule.homOfLE hEq.le ≫ φ)
    (mono_comp' hmono hφ)
  exact ⟨D, succMultipleClosedSubspaces B S hS X D₀ N, hD, hE, hiso⟩

end AlgebraicGeometry.Space

end
