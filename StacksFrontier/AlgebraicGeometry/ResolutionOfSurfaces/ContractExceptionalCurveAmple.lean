module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ContractionMorphism
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ContractExceptionalCurveProper
public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.Ample
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologicalCriterion
public import StacksFrontier.AlgebraicGeometry.AmplePositivePower.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurvePicardDecomposition
public import StacksFrontier.AlgebraicGeometry.PicardGroup.TensorPower
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveDivisorTwist

/-!
# Contracting an exceptional curve over an affine Noetherian base

**[Stacks, Tag 0C2M].** Let `S = Spec R` with `R` Noetherian, `X ⟶ S` proper, `ℒ` an ample
invertible `𝒪_X`-module and `E ⊆ X` an exceptional curve of the first kind. Then

1. there exists a contraction `b : X ⟶ X'` of `E`,
2. `X'` is proper over `S`, and
3. the invertible `𝒪_{X'}`-module `ℒ'` of [Stacks, Remark 0C5M] is ample: if `n` is the degree of
   `ℒ` on `E`, then `ℒ'` is the invertible module on `X'` with `b^* ℒ' = ℒ(nE)` in `Pic(X)`.

## The argument

Following the source, `ℒ` is replaced by a power `ℒ^{⊗ d}` for which `H¹(X, ℒ^{⊗ d}) = 0` and
which comes from an immersion into projective space ([Stacks, Tags 0B5U and 01VS]). Then
`AlgebraicGeometry.ExceptionalCurveContraction.exists_contraction_of_immersion` produces a
contraction `b` and an ample `𝓜'` on `X'` with `b^* 𝓜' ≅ ℒ^{⊗ d}(dnE)`.

The source obtains `ℒ'` itself from [Stacks, Tag 0C5L]. Here it is produced by running the
construction for two consecutive powers `d` and `d + 1`: the second contraction factors through
the first ([Stacks, Tag 0C5J]), and the difference of the two ample modules is a class `ℒ'` on
`X'` with `b^* ℒ' = ℒ(nE)`. Any such `ℒ'` is ample: `b^*` is injective on Picard groups because
`𝒪_{X'} ≅ b_* 𝒪_X`, so `ℒ'^{⊗ d} ≅ 𝓜'`, which is ample, and ampleness passes to `ℒ'`
([Stacks, Tag 01PT]). The integers involved are matched on `E ≅ 𝐏¹`, where `m ↦ [𝒪(m)]` is an
injective homomorphism ([Stacks, Tag 0BXJ]).

## Main results

* `AlgebraicGeometry.exists_contraction_isProper_isAmple`: **[Stacks, Tag 0C2M]**, all three
  assertions.
* `AlgebraicGeometry.IsContractionOfExceptionalCurve.nonempty_iso_of_schemePullbackClass_eq`:
  the module `ℒ'` of [Stacks, Remark 0C5M] is determined up to isomorphism by `b^*ℒ' = ℒ(nE)`.

## References

* [Stacks Project, Tag 0C2M](https://stacks.math.columbia.edu/tag/0C2M)
* [Stacks Project, Remark 0C5M](https://stacks.math.columbia.edu/tag/0C5M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction (modulePullback)
open Stacks.RingedSpace (structureIsSheaf)
open Stacks.AmpleProjectiveImmersion (projectiveSpaceTwistingSheaf)

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace AlgebraicGeometry.ExceptionalCurveContraction

/-! ### Picard classes -/

section Classes

variable {X : Scheme.{u}}

/-- The class in `Pic(X)` of an invertible `𝒪_X`-module. -/
abbrev cls (A : X.Modules) [Stacks.Ample.IsInvertibleModule X A] : Stacks.Picard.ofScheme X :=
  Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace) A
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ A ‹_›)

/-- Isomorphic invertible modules have the same class in `Pic(X)`. -/
theorem cls_eq_of_iso {A B : X.Modules} [Stacks.Ample.IsInvertibleModule X A]
    [Stacks.Ample.IsInvertibleModule X B] (e : A ≅ B) : cls A = cls B :=
  (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨e⟩

/-- Invertible modules with the same class in `Pic(X)` are isomorphic. -/
theorem nonempty_iso_of_cls_eq {A B : X.Modules} [Stacks.Ample.IsInvertibleModule X A]
    [Stacks.Ample.IsInvertibleModule X B] (h : cls A = cls B) : Nonempty (A ≅ B) :=
  (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1 h

/-- Pulling back along `b : Y ⟶ X` sends the class of `A` to the class of `b^* A`. -/
theorem schemePullbackClass_cls {Y : Scheme.{u}} (b : Y ⟶ X) (A : X.Modules)
    [Stacks.Ample.IsInvertibleModule X A]
    [Stacks.Ample.IsInvertibleModule Y ((Scheme.Modules.pullback b).obj A)] :
    Stacks.Picard.schemePullbackClass b (cls A) = cls ((Scheme.Modules.pullback b).obj A) :=
  (Stacks.Picard.pullbackClass_classOf b.toLRSHom.toShHom A _).trans
    ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
      ⟨((Stacks.ProjectiveBundleQuotients.pullbackIso b).app A).symm⟩)

/-- The class of the `d`-th tensor power `L^{⊗ d}` is `d • [L]`. -/
theorem cls_tensorPowModule (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (d : ℤ) :
    cls (Stacks.Ample.tensorPowModule X L d) = d • cls L := by
  refine Eq.trans ?_ (Stacks.SheafOfModules.picardClass_schemeTensorPower X L
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L ‹_›) d)
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
    ⟨(Stacks.PowerFamilyBridge.tensorPowerModuleIso X L d).symm⟩

/-- The class of the twist `A(jD)` of `A` by an effective Cartier divisor `D` is
`[A] + j • [𝒪_X(D)]`. -/
theorem cls_divisorTwist (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (A : X.Modules) [Stacks.Ample.IsInvertibleModule X A] :
    ∀ j : ℕ, cls (Stacks.Surfaces.divisorTwist D A j) =
      cls A + (j : ℤ) • Stacks.Divisors.picardClass D
  | 0 => by
    show cls A = cls A + ((0 : ℕ) : ℤ) • Stacks.Divisors.picardClass D
    simp
  | j + 1 => by
    have ih := cls_divisorTwist D A j
    have h := Stacks.SheafOfModules.picardClass_tensorSheaf X.presheaf
      (structureIsSheaf X.toRingedSpace) (Stacks.Surfaces.divisorTwist D A j)
      (Stacks.Divisors.invertibleSheaf' D)
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance)
      (Stacks.Divisors.isInvertible_invertibleSheaf_picard D)
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
        (Stacks.Surfaces.isInvertible_divisorTwist D A (j + 1)))
    refine h.symm.trans ?_
    calc _ = (cls A + (j : ℤ) • Stacks.Divisors.picardClass D) +
          Stacks.Divisors.picardClass D := congrArg₂ (· + ·) ih rfl
      _ = _ := by rw [Nat.cast_succ, add_zsmul, one_zsmul, add_assoc]

end Classes

/-! ### Degrees on the exceptional curve -/

section Degrees

variable {X : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]
  (e : projectiveLineProj k ≅ D.subscheme)

/-- The restriction to `E ≅ 𝐏¹` of the class of a module of degree `n` is `[𝒪(n)]`. -/
theorem exceptionalRestrictionHom_cls [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (A : X.Modules) [Stacks.Ample.IsInvertibleModule X A] {n : ℤ}
    (hdeg : (modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback D.subschemeι.toLRSHom.toShHom).obj A) ≅
      ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) k) n) :
    Scheme.IdealSheafData.exceptionalRestrictionHom D k e (cls A) =
      Stacks.PicardUFD.twistPicardHom k 1 n := by
  have h1 := Stacks.InvertiblePullback.isInvertibleModule_pullback D.subschemeι A
  exact (congrArg (Stacks.Picard.schemePullbackClass e.hom)
      (Stacks.Picard.pullbackClass_classOf D.subschemeι.toLRSHom.toShHom A
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ A ‹_›))).trans
    ((Stacks.Picard.pullbackClass_classOf e.hom.toLRSHom.toShHom _
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ h1)).trans
      ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨hdeg⟩))

/-- `𝒪_X(E)` restricts to `𝒪(-1)` on `E`. -/
theorem exceptionalRestrictionHom_picardClass [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hE : D.IsExceptionalCurveOfFirstKind k e) :
    Scheme.IdealSheafData.exceptionalRestrictionHom D k e (Stacks.Divisors.picardClass D) =
      Stacks.PicardUFD.twistPicardHom k 1 (-1) :=
  Scheme.IdealSheafData.exceptionalRestriction_picardClass D k e hE

/-- **The degree of a class of the form `j • ℒ + a • [𝒪_X(E)]`.** If `ℒ` has degree `n` on `E`,
a module `𝓜` with class `j • [ℒ] + a • [𝒪_X(E)]` has degree `j n - a`. -/
theorem eq_of_cls_eq [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hE : D.IsExceptionalCurveOfFirstKind k e) (A B : X.Modules)
    [Stacks.Ample.IsInvertibleModule X A] [Stacks.Ample.IsInvertibleModule X B] {n m a : ℤ}
    (hA : (modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback D.subschemeι.toLRSHom.toShHom).obj A) ≅
      ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) k) n)
    (hB : (modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback D.subschemeι.toLRSHom.toShHom).obj B) ≅
      ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) k) m)
    (j : ℤ) (h : cls B = j • cls A + a • Stacks.Divisors.picardClass D) :
    m = j * n - a := by
  have h1 := congrArg (Scheme.IdealSheafData.exceptionalRestrictionHom D k e) h
  have e2 : Scheme.IdealSheafData.exceptionalRestrictionHom D k e
      (j • cls A + a • Stacks.Divisors.picardClass D) =
      j • Stacks.PicardUFD.twistPicardHom k 1 n +
        a • Stacks.PicardUFD.twistPicardHom k 1 (-1) := by
    rw [map_add, map_zsmul, map_zsmul, exceptionalRestrictionHom_cls D k e A hA,
      exceptionalRestrictionHom_picardClass D k e hE]
  let T : ℤ →+ Stacks.Picard.ofScheme (projectiveLineProj k) :=
    Stacks.PicardUFD.twistPicardHom k 1
  have e3 : T m = j • T n + a • T (-1) :=
    (exceptionalRestrictionHom_cls D k e B hB).symm.trans (h1.trans e2)
  have e4 : T (j * n - a) = j • T n + a • T (-1) := by
    rw [show j * n - a = j • n + a • (-1 : ℤ) by simp only [smul_eq_mul]; ring,
      map_add, map_zsmul, map_zsmul]
  exact Stacks.PicardUFD.twistPicardHom_injective k 1 Nat.one_pos (e3.trans e4.symm)

end Degrees


/-! ### Vanishing of `H¹` of high powers -/

section Vanishing

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Stacks.Surfaces.schemeModulesMonoidal

/-- **`H¹(X, ℒ^{⊗ d}) = 0` for all large `d`**, for `ℒ` ample on `X` proper over a Noetherian ring:
the case `ℱ = 𝒪_X` of [Stacks, Tag 0B5U]. -/
theorem exists_isZero_rightDerived_one_tensorPowModule {R : Type u} [CommRing R]
    [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Scheme.Modules.IsAmple X L) :
    ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d →
      IsZero (((moduleGlobalSections X).rightDerived 1).obj
        (Stacks.Ample.tensorPowModule X L (d : ℤ))) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨d₁, hd₁⟩ := Scheme.Modules.hasEventualTwistCohomologyVanishing_of_isAmple L f hL
    (SheafOfModules.unit X.ringCatSheaf)
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  refine ⟨d₁, fun d hd => ?_⟩
  refine IsZero.of_iso (hd₁ d 1 hd Nat.one_pos)
    (((moduleGlobalSections X).rightDerived 1).mapIso ?_)
  exact (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso X L d).symm ≪≫
    (MonoidalCategory.leftUnitor
      (C := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
      (Scheme.Modules.tensorPowerModules L (d : ℤ))).symm

end Vanishing


/-! ### One power of `ℒ` -/

section Step

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) [IsProper f]
  {D : X.IdealSheafData} {k : Type u} [Field k] {e : projectiveLineProj k ≅ D.subscheme}

/-- **The contraction attached to one power `ℒ^{⊗ d}`.** If `ℒ^{⊗ d}` comes from an immersion
into projective space and `H¹(X, ℒ^{⊗ d}) = 0`, there are a contraction `b : X ⟶ X'` of `E` with
`𝒪_{X'} ≅ b_* 𝒪_X` and an ample invertible `𝓜'` on `X'` with `b^*[𝓜'] = d • [ℒ(nE)]`, where `n`
is the degree of `ℒ` on `E`. -/
theorem exists_contraction_of_tensorPowModule (hE : D.IsExceptionalCurveOfFirstKind k e)
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {n : ℤ}
    (hn : (modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback D.subschemeι.toLRSHom.toShHom).obj L) ≅
      ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) k) n)
    (d : ℕ) {N : ℕ} (i : X ⟶ projectiveSpaceOver N (Spec (.of R))) [IsImmersion i]
    (hi : i ≫ pullback.fst _ _ = f)
    (α : Stacks.Ample.tensorPowModule X L (d : ℤ) ≅
      (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf N (Spec (.of R))))
    (hH1 : IsZero (((moduleGlobalSections X).rightDerived 1).obj
        (Stacks.Ample.tensorPowModule X L (d : ℤ)))) :
    ∃ (X' : Scheme.{u}) (b : X ⟶ X') (_ : IsIso b.c) (M' : X'.Modules)
      (_ : Stacks.Ample.IsInvertibleModule X' M'),
      IsContractionOfExceptionalCurve D b ∧ Scheme.Modules.IsAmple X' M' ∧
        Stacks.Picard.schemePullbackClass b (cls M') =
          (d : ℤ) • (haveI := hE.isEffectiveCartierDivisor;
            D.exceptionalTwist n (cls L)) := by
  have := hE.isEffectiveCartierDivisor
  set A := Stacks.Ample.tensorPowModule X L (d : ℤ)
  obtain ⟨m, ⟨hdeg⟩⟩ := exists_iso_twistingSheaf_pullback (e := e) A
  have hm := one_le_of_immersion f hE A i hi α hdeg
  obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = (m' : ℤ) + 1 := ⟨(m - 1).toNat, by omega⟩
  have hH1' := Stacks.Surfaces.isZero_rightDerived_one_divisorTwist D k hE A
    (n := (m' : ℤ) + 1) (by omega) hdeg hH1 m' (by omega)
  obtain ⟨X', b, hc, M', hM', hb, hamp, ⟨β⟩⟩ :=
    exists_contraction_of_immersion f hE A m' hdeg hH1' i hi α
  refine ⟨X', b, hc, M', hM', hb, hamp, ?_⟩
  have hdn : (m' : ℤ) + 1 = (d : ℤ) * n - 0 :=
    eq_of_cls_eq D k e hE L A hn hdeg (d : ℤ)
      (by rw [cls_tensorPowModule, zero_smul, add_zero])
  rw [schemePullbackClass_cls b M', cls_eq_of_iso β, cls_divisorTwist,
    cls_tensorPowModule, Scheme.IdealSheafData.exceptionalTwist_def, smul_add, smul_smul]
  congr 1
  rw [show ((m' + 1 : ℕ) : ℤ) = (d : ℤ) * n by push_cast; omega]

end Step

end AlgebraicGeometry.ExceptionalCurveContraction

namespace AlgebraicGeometry

open ExceptionalCurveContraction


/-- **The invertible module `ℒ'` of [Stacks, Remark 0C5M] is unique.** Pullback along a
contraction is injective on Picard groups, since `𝒪_{X'} ≅ b_* 𝒪_X`; so two invertible
`𝒪_{X'}`-modules whose pullbacks have the same class are isomorphic. -/
public theorem IsContractionOfExceptionalCurve.nonempty_iso_of_schemePullbackClass_eq
    {X X' : Scheme.{u}} {D : X.IdealSheafData} {b : X ⟶ X'}
    (hb : IsContractionOfExceptionalCurve D b) {A B : X'.Modules}
    [Stacks.Ample.IsInvertibleModule X' A] [Stacks.Ample.IsInvertibleModule X' B]
    (h : Stacks.Picard.schemePullbackClass b (cls A) =
      Stacks.Picard.schemePullbackClass b (cls B)) :
    Nonempty (A ≅ B) :=
  have := hb.isIso_c
  nonempty_iso_of_cls_eq (Scheme.Modules.injective_schemePullbackClass_of_isIso_c b h)

/-- If `b : X ⟶ X'` satisfies `𝒪_{X'} ≅ b_* 𝒪_X` and `d • b^*[ℒ'] = b^*[𝓜]` for an ample
invertible `𝓜` and some `d ≥ 1`, then `ℒ'` is ample. -/
public theorem isAmple_of_zsmul_schemePullbackClass_eq {X X' : Scheme.{u}} (b : X ⟶ X')
    [IsIso b.c] {L' M : X'.Modules} [Stacks.Ample.IsInvertibleModule X' L']
    [Stacks.Ample.IsInvertibleModule X' M] (hM : Scheme.Modules.IsAmple X' M) {d : ℕ}
    (hd : 1 ≤ d)
    (h : (d : ℤ) • Stacks.Picard.schemePullbackClass b (cls L') =
      Stacks.Picard.schemePullbackClass b (cls M)) :
    Scheme.Modules.IsAmple X' L' := by
  have hpow : Stacks.Picard.schemePullbackClass b (cls (Stacks.Ample.tensorPowModule X' L' d)) =
      Stacks.Picard.schemePullbackClass b (cls M) := by
    rw [cls_tensorPowModule]
    show Stacks.Picard.schemePullbackClassHom b ((d : ℤ) • cls L') = _
    rw [map_zsmul]
    exact h
  obtain ⟨ι⟩ := nonempty_iso_of_cls_eq
    (Scheme.Modules.injective_schemePullbackClass_of_isIso_c b hpow)
  exact Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple X' L'
    ((Stacks.AmplePositivePower.isAmple_iff_isAmple_tensorPowModule L' d hd).mpr
      ((Stacks.RelativeVeryAmple.isAmple_congr _ _ ι).mpr
        (Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple X' M hM)))

/-- **[Stacks, Tag 0C2M].** Let `S = Spec R` be an affine Noetherian scheme, `f : X ⟶ S` a proper
morphism, `ℒ` an ample invertible `𝒪_X`-module, and `E ⊆ X` an exceptional curve of the first
kind, cut out by `D` and presented as `𝐏¹_k` by `e`. Then

1. there exists a contraction `b : X ⟶ X'` of `E`;
2. `X'` is proper over `S`: the structure morphism factors as `b ≫ f'` with `f'` proper;
3. the invertible `𝒪_{X'}`-module `ℒ'` of [Stacks, Remark 0C5M] is ample. Here `ℒ` has a degree
   `n` on `E` (its restriction to `𝐏¹_k` is `𝒪(n)`), and `ℒ'` is an invertible `𝒪_{X'}`-module
   with `b^*ℒ' = ℒ(nE)` in `Pic(X)`, i.e. `b^*[ℒ'] = [ℒ] + n • [𝒪_X(E)]`
   (`AlgebraicGeometry.Scheme.IdealSheafData.exceptionalTwist`). Such an `ℒ'` exists, and every
   such `ℒ'` is ample; it is unique up to isomorphism by
   `AlgebraicGeometry.IsContractionOfExceptionalCurve.nonempty_iso_of_schemePullbackClass_eq`. -/
@[stacks 0C2M]
public theorem exists_contraction_isProper_isAmple {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (hL : Scheme.Modules.IsAmple X L)
    {D : X.IdealSheafData} {k : Type u} [Field k] {e : projectiveLineProj k ≅ D.subscheme}
    (hE : D.IsExceptionalCurveOfFirstKind k e) :
    ∃ (X' : Scheme.{u}) (b : X ⟶ X'),
      IsContractionOfExceptionalCurve D b ∧
      (∃ f' : X' ⟶ Spec (.of R), b ≫ f' = f ∧ IsProper f') ∧
      (∃ n : ℤ, Nonempty ((modulePullback e.hom.toLRSHom.toShHom).obj
          ((modulePullback D.subschemeι.toLRSHom.toShHom).obj L) ≅
        ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) k) n)) ∧
      ∀ n : ℤ, Nonempty ((modulePullback e.hom.toLRSHom.toShHom).obj
          ((modulePullback D.subschemeι.toLRSHom.toShHom).obj L) ≅
        ProjectiveSpectrum.Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin 2) k) n) →
        (∃ (L' : X'.Modules) (_ : Stacks.Ample.IsInvertibleModule X' L'),
          Stacks.Picard.schemePullbackClass b (cls L') =
            (haveI := hE.isEffectiveCartierDivisor; D.exceptionalTwist n (cls L))) ∧
        ∀ (L' : X'.Modules) [Stacks.Ample.IsInvertibleModule X' L'],
          Stacks.Picard.schemePullbackClass b (cls L') =
            (haveI := hE.isEffectiveCartierDivisor; D.exceptionalTwist n (cls L)) →
          Scheme.Modules.IsAmple X' L' := by
  have := hE.isEffectiveCartierDivisor
  have hLs : Stacks.Ample.IsAmple X L := Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple X L hL
  obtain ⟨d₀, -, hd₀⟩ :=
    Stacks.StalkwiseGeneration.exists_immersion_projectiveSpaceOver_of_isAmple f L hLs
  obtain ⟨d₁, hd₁⟩ := exists_isZero_rightDerived_one_tensorPowModule f L hL
  obtain ⟨n₀, ⟨hn₀⟩⟩ := exists_iso_twistingSheaf_pullback (e := e) L
  set E' := D.exceptionalTwist n₀ (cls L)
  have step : ∀ j : ℕ, max d₀ d₁ ≤ j → ∃ (X' : Scheme.{u}) (b : X ⟶ X') (_ : IsIso b.c)
      (M' : X'.Modules) (_ : Stacks.Ample.IsInvertibleModule X' M'),
      IsContractionOfExceptionalCurve D b ∧ Scheme.Modules.IsAmple X' M' ∧
        Stacks.Picard.schemePullbackClass b (cls M') = (j : ℤ) • E' := fun j hj => by
    obtain ⟨N, i, hi_imm, hi, ⟨α⟩⟩ := hd₀ j (le_trans (le_max_left _ _) hj)
    exact exists_contraction_of_tensorPowModule f hE L hn₀ j i hi α
      (hd₁ j (le_trans (le_max_right _ _) hj))
  set d := max d₀ d₁ + 1 with hd
  obtain ⟨X', b, hc, M₁, hM₁, hb, hamp₁, hcl₁⟩ := step d (by omega)
  obtain ⟨X₂, b₂, -, M₂, hM₂, hb₂, -, hcl₂⟩ := step (d + 1) (by omega)
  obtain ⟨h, hh, -⟩ :=
    existsUnique_comp_eq_of_isContractionOfExceptionalCurve D b hb b₂ hb₂.exists_const_on_subscheme
  have hcl'' : Stacks.Picard.schemePullbackClass b (cls ((Scheme.Modules.pullback h).obj M₂)) =
      ((d + 1 : ℕ) : ℤ) • E' := by
    rw [← schemePullbackClass_cls h M₂, Stacks.Picard.schemePullbackClass_comp, hh, hcl₂]
  refine ⟨X', b, hb,
    exists_isProper_comp_eq_of_isContractionOfExceptionalCurve D k e b hb f inferInstance,
    ⟨n₀, ⟨hn₀⟩⟩, fun n hn => ?_⟩
  obtain ⟨hn⟩ := hn
  obtain rfl : n = n₀ := by
    have := eq_of_cls_eq D k e hE L L hn₀ hn 1 (by rw [one_smul, zero_smul, add_zero])
    omega
  set x := cls ((Scheme.Modules.pullback h).obj M₂) - cls M₁
  have hx : Stacks.Picard.schemePullbackClass b x = E' := by
    show Stacks.Picard.schemePullbackClassHom b x = E'
    rw [map_sub]
    show Stacks.Picard.schemePullbackClass b _ - Stacks.Picard.schemePullbackClass b _ = E'
    rw [hcl'', hcl₁]
    push_cast
    rw [add_smul, one_smul, add_sub_cancel_left]
  refine ⟨⟨(Stacks.Picard.picardRepresentative X'.toRingedSpace x).obj,
    (Stacks.Picard.picardRepresentative X'.toRingedSpace x).property.toAlgebraicGeometry, ?_⟩,
    fun L' _ hL' => ?_⟩
  · exact (congrArg _ (Stacks.Picard.classOf_picardRepresentative X'.toRingedSpace x)).trans hx
  · exact isAmple_of_zsmul_schemePullbackClass_eq b hamp₁ (d := d) (by omega) (by rw [hcl₁, hL'])

end AlgebraicGeometry

end
