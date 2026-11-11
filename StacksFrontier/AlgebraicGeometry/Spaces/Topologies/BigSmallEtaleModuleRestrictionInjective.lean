module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.InjectiveOfKInjectiveSingle
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleLocalizationBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.EtaleToposFunctoriality

/-!
# Restriction of injective modules from the big to the small étale site (Stacks 0DG8)

Let `T` be a big étale site of algebraic spaces over a scheme `S`. Tag 0DG8 proves that
restriction of abelian sheaves from the big étale site `(Spaces/X)_étale` to the spaces-étale
site of `Y`, along a morphism `f : Y ⟶ X`, preserves injectives and K-injective complexes, and
records that **the corresponding statements for sheaves of modules do not hold**. The abelian
statements are `AlgebraicGeometry.BigEtaleSpaceSite.injective_spacesEtaleRestriction` and its
companions in `StacksFrontier/AlgebraicGeometry/Spaces/Topologies/BigToSmallEtaleKInjective.lean`.
This file proves the module statement, by the counterexample the source refers to
(Étale Cohomology, Tag 0758): `S = Spec ℤ`, `X = S`, and multiplication by `2`.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.exists_injective_not_injective_restrictModules`: over
  `Spec ℤ`, an injective `𝒪`-module on `(Spaces/S)_étale` whose restriction to `S_{spaces,étale}`
  is not an injective `𝒪_S`-module; the module form of part (1)(b).
* `AlgebraicGeometry.BigEtaleSpaceSite.exists_injective_not_injective_restrictModulesAlong`: the
  module form of part (1)(a).
* `AlgebraicGeometry.BigEtaleSpaceSite.exists_isKInjective_not_isKInjective_restrictModules` and
  `AlgebraicGeometry.BigEtaleSpaceSite.exists_isKInjective_not_isKInjective_restrictModulesAlong`:
  the module forms of parts (2)(b) and (2)(a).
* `AlgebraicGeometry.BigEtaleSpaceSite.not_injective_restrictModules_under`: the argument in the
  abstract: if an integer `n` is a nonzerodivisor on the regular functions of every algebraic
  space étale over `X`, and vanishes on the nonzero regular functions of some algebraic space over
  `X`, then an injective `𝒪`-module containing `𝒪` restricts to a non-injective `𝒪_X`-module.
* `AlgebraicGeometry.BigEtaleSpaceSite.not_injective_restrictModules_baseSpace`: the same at
  `X = S`, for a base scheme `S` such that `n` is regular in every local ring of `S` and vanishes
  in some residue field of `S`.

## Implementation notes

The argument is the source's. Multiplication by `n` is a monomorphism `𝒪_X ⟶ 𝒪_X` on the
spaces-étale site, because every algebraic space étale over `X` has its étale charts étale, hence
flat, over `S`, and `n` is regular in every local ring of `S`
(`AlgebraicGeometry.Scheme.eq_zero_of_intCast_mul_eq_zero_of_flat`). Choose a monomorphism
`α : 𝒪 ⟶ I` into an injective `𝒪`-module. If `I|_{X_étale}` were injective, the restriction of
`α` would factor as `n • ψ`; evaluating on `X` gives `α(1) = n • ψ(1)` in `I(X)`, and pulling back
to the spectrum `V` of a residue field in which `n` vanishes gives `α_V(1) = 0` in the
`𝒪(V)`-module `I(V)`. Since `α_V` is injective and `𝒪(V) ≠ 0`, this is absurd. The source phrases
the last step by adjunction (the injective map `α` would factor through the non-injective map
`π_S^*(2)`); evaluating sections, as here, is the same computation without forming `π_S^*`.

The K-injective statements follow: an injective object placed in degree `0` is K-injective
(`CochainComplex.isKInjective_single_obj_of_injective`), restriction commutes with placing an
object in degree `0`, and an object whose single complex is K-injective is injective
(`CochainComplex.injective_of_isKInjective_single`).

For parts (1)(a) and (2)(a) the morphism `f` is the identity of `X = S`: the inverse image along
`i_{𝟙 X}` is the restriction to the spaces-étale site of `X` on the nose.

`Spec ℤ` is taken in the universe of the base scheme as the spectrum of `ULift ℤ`, and its point
over `2` is any maximal ideal containing `2`.

## References

* [Stacks Project, Tag 0DG8](https://stacks.math.columbia.edu/tag/0DG8)
* [Stacks Project, Tag 0758](https://stacks.math.columbia.edu/tag/0758)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-! ### Torsion-freeness of regular functions on a flat scheme -/

/-- Let `g : Y ⟶ Z` be a flat morphism of schemes and `n` an integer which is a nonzerodivisor
in every local ring of `Z`. Then multiplication by `n` is injective on the global regular
functions of `Y`. -/
theorem Scheme.eq_zero_of_intCast_mul_eq_zero_of_flat {Y Z : Scheme.{u}} (g : Y ⟶ Z) [Flat g]
    (n : ℤ) (hreg : ∀ z : Z, IsRegular (n : Z.presheaf.stalk z))
    (s : Γ(Y, ⊤)) (hs : (n : Γ(Y, ⊤)) * s = 0) : s = 0 := by
  refine TopCat.Presheaf.section_ext Y.sheaf ⊤ s 0 fun y hy => ?_
  change (Y.presheaf.germ ⊤ y hy) s = (Y.presheaf.germ ⊤ y hy) 0
  rw [map_zero]
  let := (g.stalkMap y).hom.toAlgebra
  have : Module.Flat (Z.presheaf.stalk (g y)) (Y.presheaf.stalk y) := Flat.stalkMap g y
  have hr := Module.Flat.isSMulRegular_of_isRegular (M := Y.presheaf.stalk y) (hreg (g y))
  have hmul : (n : Y.presheaf.stalk y) * (Y.presheaf.germ ⊤ y hy) s = 0 := by
    have h0 : (Y.presheaf.germ ⊤ y hy) ((n : Γ(Y, ⊤)) * s) = 0 := by rw [hs, map_zero]
    simpa only [map_mul, map_intCast] using h0
  refine hr ?_
  change (n : Z.presheaf.stalk (g y)) • (Y.presheaf.germ ⊤ y hy) s =
    (n : Z.presheaf.stalk (g y)) • (0 : Y.presheaf.stalk y)
  rw [smul_zero, Algebra.smul_def, map_intCast]
  exact hmul

/-- On the spectrum of a domain, an integer which is nonzero in the ring is a nonzerodivisor in
every local ring. -/
theorem isRegular_intCast_stalk_Spec {R : CommRingCat.{u}} [IsDomain R] (n : ℤ)
    (hn : (n : R) ≠ 0) (z : Spec R) : IsRegular (n : (Spec R).presheaf.stalk z) := by
  have : z.asIdeal.IsPrime := z.isPrime
  let : Algebra R ((Spec R).presheaf.stalk z) := StructureSheaf.stalkAlgebra R z
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk z) z.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R z
  have hle : z.asIdeal.primeCompl ≤ nonZeroDivisors R :=
    Ideal.primeCompl_le_nonZeroDivisors _
  have : IsDomain ((Spec R).presheaf.stalk z) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  have hne : (n : (Spec R).presheaf.stalk z) ≠ 0 := by
    rw [← map_intCast (algebraMap R ((Spec R).presheaf.stalk z))]
    exact IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ hle
      (mem_nonZeroDivisors_of_ne_zero hn)
  exact IsRegular.of_ne_zero hne

namespace BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

/-- Sheaves of `𝒪`-modules on the big étale site of `X` have enough injectives. -/
instance enoughInjectives_bigEtaleModules (X : T.Spaces) :
    EnoughInjectives (BigEtaleModules.{u, u + 1} T X) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

section Abstract

variable {T} {X : T.Spaces} (n : ℤ)

/-- If `n` is a nonzerodivisor on the regular functions of every algebraic space étale over
`X`, then multiplication by `n` is a monomorphism `𝒪_X ⟶ 𝒪_X` of sheaves of modules on the
spaces-étale site of `X`. -/
theorem mono_zsmul_id_unit
    (hreg : ∀ (U : Space.SpacesEtale T.fppfSite S T.fppf_mem X)
      (a : Space.globalFunctions' T.fppfSite S T.fppf_mem U.1.left.obj), (n : _) * a = 0 → a = 0) :
    Mono (n • 𝟙 (SheafOfModules.unit.{u + 1} (spacesEtaleRingSheaf T X))) := by
  refine (SheafOfModules.forget _).mono_of_mono_map ?_
  refine PresheafOfModules.mono_of_injective fun U => ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  simp only [Functor.map_zsmul, PresheafOfModules.zsmul_app,
    ModuleCat.hom_zsmul, LinearMap.smul_apply] at hx
  let w : (spacesEtaleRingSheaf T X).obj.obj U := x
  have hw : (n : (spacesEtaleRingSheaf T X).obj.obj U) * w = 0 := by
    rw [← zsmul_eq_mul]
    exact hx
  exact hreg U.unop w hw

/-- **The module version of Stacks 0DG8 fails, abstractly.** Suppose that the integer `n` is a
nonzerodivisor on the regular functions of every algebraic space étale over `X`, and that some
algebraic space `V` over `X` has nonzero regular functions on which `n` vanishes. Choose an
injective `𝒪`-module `I` on the big étale site of `X` containing `𝒪`. Then the restriction of
`I` to the spaces-étale site of `X` is not an injective `𝒪_X`-module. -/
theorem not_injective_restrictModules_under
    (hreg : ∀ (U : Space.SpacesEtale T.fppfSite S T.fppf_mem X)
      (a : Space.globalFunctions' T.fppfSite S T.fppf_mem U.1.left.obj), (n : _) * a = 0 → a = 0)
    (V : Over X) (hV : (n : Space.globalFunctions' T.fppfSite S T.fppf_mem V.left.obj) = 0)
    (hVnt : (1 : Space.globalFunctions' T.fppfSite S T.fppf_mem V.left.obj) ≠ 0) :
    ¬ Injective ((restrictModules.{u, u + 1} T X).obj
      (Injective.under (SheafOfModules.unit.{u + 1} (bigEtaleRingSheaf T X)))) := by
  intro hJ
  set I := Injective.under (SheafOfModules.unit.{u + 1} (bigEtaleRingSheaf T X))
  set α : SheafOfModules.unit.{u + 1} (bigEtaleRingSheaf T X) ⟶ I := Injective.ι _
  let φ : SheafOfModules.unit.{u + 1} (spacesEtaleRingSheaf T X) ⟶
      (restrictModules.{u, u + 1} T X).obj I :=
    SheafOfModules.unitToPushforwardObjUnit (restrictSharp T X) ≫
      (restrictModules.{u, u + 1} T X).map α
  have hm := mono_zsmul_id_unit n hreg
  have hfac := Injective.comp_factorThru φ
    (n • 𝟙 (SheafOfModules.unit.{u + 1} (spacesEtaleRingSheaf T X)))
  set ψ := Injective.factorThru φ
    (n • 𝟙 (SheafOfModules.unit.{u + 1} (spacesEtaleRingSheaf T X)))
  rw [Preadditive.zsmul_comp, Category.id_comp] at hfac
  have hval : (n • ψ).val = n • ψ.val := Functor.map_zsmul (SheafOfModules.forget _)
  let E := Space.SpacesEtale.final T.fppfSite S T.fppf_mem X
  let oneE : (SheafOfModules.unit.{u + 1} (spacesEtaleRingSheaf T X)).val.obj (op E) :=
    (1 : (spacesEtaleRingSheaf T X).obj.obj (op E))
  let oneX : (SheafOfModules.unit.{u + 1} (bigEtaleRingSheaf T X)).val.obj
      (op (Over.mk (𝟙 X))) :=
    (1 : (bigEtaleRingSheaf T X).obj.obj (op (Over.mk (𝟙 X))))
  let oneV : (SheafOfModules.unit.{u + 1} (bigEtaleRingSheaf T X)).val.obj (op V) :=
    (1 : (bigEtaleRingSheaf T X).obj.obj (op V))
  have h1 : n • ψ.val.app (op E) oneE = α.val.app (op (Over.mk (𝟙 X))) oneX := by
    have h := congrArg (fun k => k.val.app (op E) oneE) hfac
    simp only [hval, PresheafOfModules.zsmul_app, ModuleCat.hom_zsmul, LinearMap.smul_apply] at h
    exact h
  let y : I.val.obj (op (Over.mk (𝟙 X))) := ψ.val.app (op E) oneE
  have h1' : n • y = α.val.app (op (Over.mk (𝟙 X))) oneX := h1
  let v : V ⟶ Over.mk (𝟙 X) := Over.homMk V.hom
  have h2 : α.val.app (op V) oneV = I.val.map v.op (α.val.app (op (Over.mk (𝟙 X))) oneX) := by
    rw [← PresheafOfModules.naturality_apply]
    exact congrArg _ (PresheafOfModules.unit_map_one (bigEtaleRingSheaf T X).obj v.op).symm
  have h3 : α.val.app (op V) oneV = 0 := by
    rw [h2, ← h1', map_zsmul,
      ← Int.cast_smul_eq_zsmul ((bigEtaleRingSheaf T X).obj.obj (op V))]
    rw [show ((n : (bigEtaleRingSheaf T X).obj.obj (op V))) = 0 from hV, zero_smul]
    rfl
  have : Mono α.val := (SheafOfModules.forget _).map_mono α
  have hinj : Function.Injective (α.val.app (op V)) :=
    PresheafOfModules.injective_of_mono α.val (op V)
  exact hVnt (hinj (h3.trans (map_zero _).symm))

end Abstract

section Base

variable {T}

/-- The base scheme `S`, as an object of the big étale site of algebraic spaces over `S`: the
algebraic space represented by the final object of the big fppf site over `S`. -/
noncomputable abbrev baseSpace (T : BigEtaleSpaceSite S) : T.Spaces :=
  schemeSpace (Over.mk (𝟙 (T.fppfSite.obj T.fppf_mem)))

variable (n : ℤ) (hS : ∀ z : S, IsRegular (n : S.presheaf.stalk z))
include hS

/-- If `n` is a nonzerodivisor in every local ring of `S`, it is a nonzerodivisor on the regular
functions of every algebraic space étale over `S`: every étale chart of such a space is a scheme
étale, hence flat, over `S`. -/
theorem eq_zero_of_intCast_mul_eq_zero_of_spacesEtale
    (U : Space.SpacesEtale T.fppfSite S T.fppf_mem (baseSpace T))
    (a : Space.globalFunctions' T.fppfSite S T.fppf_mem U.1.left.obj)
    (ha : (n : Space.globalFunctions' T.fppfSite S T.fppf_mem U.1.left.obj) * a = 0) :
    a = 0 := by
  apply Subtype.ext
  funext j
  let Y := (BigFppfOver.toScheme T.fppfSite S T.fppf_mem).obj j.unop.1.left
  let s : Γ(Y, ⊤) := a.1 j
  have hs : (n : Γ(Y, ⊤)) * s = 0 :=
    congrArg (fun b : Space.globalFunctions' T.fppfSite S T.fppf_mem U.1.left.obj => b.1 j) ha
  let ψ : yoneda.obj j.unop.1.left ⟶ yoneda.obj (Over.mk (𝟙 (T.fppfSite.obj T.fppf_mem))) :=
    j.unop.1.hom ≫ U.1.hom.hom
  have hψ : (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme T.fppfSite S T.fppf_mem)).presheaf ψ :=
    U.2 _ _ j.unop.2
  have hg : (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme T.fppfSite S T.fppf_mem)) (yoneda.preimage ψ) :=
    MorphismProperty.of_relative_map (F := yoneda)
      (P := MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme T.fppfSite S T.fppf_mem))
      (by rw [Functor.map_preimage]; exact hψ)
  have : Etale ((BigFppfOver.toScheme T.fppfSite S T.fppf_mem).map (yoneda.preimage ψ)) := hg
  exact Scheme.eq_zero_of_intCast_mul_eq_zero_of_flat
    ((BigFppfOver.toScheme T.fppfSite S T.fppf_mem).map (yoneda.preimage ψ)) n hS s hs

variable (z : S) (hz : (n : S.residueField z) = 0)
include hz

/-- The spectrum of the residue field at `z`, as a scheme over `S` of the big fppf site. -/
noncomputable abbrev residuePointSite (T : BigEtaleSpaceSite S) (z : S) :
    BigFppfOver T.fppfSite S T.fppf_mem :=
  siteObject T.fppfSite S T.fppf_mem (BigFppfSite.residueField_spec_contains T.fppfSite
    T.fppf_mem z) (S.fromSpecResidueField z)

omit hS hz in
/-- The spectrum of the residue field at `z`, as an algebraic space over the base. -/
noncomputable abbrev residuePoint (T : BigEtaleSpaceSite S) (z : S) : Over (baseSpace T) :=
  Over.mk (schemeSpaceMap (Over.homMk (residuePointSite T z).hom :
    residuePointSite T z ⟶ Over.mk (𝟙 (T.fppfSite.obj T.fppf_mem))))

omit hS in
/-- The integer `n` vanishes on the spectrum of a residue field in which it vanishes. -/
theorem intCast_globalFunctions_residuePoint :
    (n : Space.globalFunctions' T.fppfSite S T.fppf_mem (residuePoint T z).left.obj) = 0 := by
  apply Subtype.ext
  funext j
  let Y := (BigFppfOver.toScheme T.fppfSite S T.fppf_mem).obj j.unop.1.left
  let W := residuePointSite T z
  let g : j.unop.1.left ⟶ W := yoneda.preimage j.unop.1.hom
  have h0 : (n : Γ((BigFppfOver.toScheme T.fppfSite S T.fppf_mem).obj W, ⊤)) = 0 := by
    change (n : Γ(Spec (S.residueField z), ⊤)) = 0
    rw [← map_intCast (Scheme.ΓSpecIso (S.residueField z)).inv.hom, hz, map_zero]
  have h1 : (n : Γ(Y, ⊤)) = 0 := by
    rw [← map_intCast ((BigFppfOver.toScheme T.fppfSite S T.fppf_mem).map g).appTop.hom, h0,
      map_zero]
  exact h1

omit hS hz in
/-- The spectrum of a residue field has nonzero regular functions. -/
theorem one_ne_zero_globalFunctions_residuePoint :
    (1 : Space.globalFunctions' T.fppfSite S T.fppf_mem (residuePoint T z).left.obj) ≠ 0 := by
  intro h
  let W := residuePointSite T z
  have h10 : (1 : Γ((BigFppfOver.toScheme T.fppfSite S T.fppf_mem).obj W, ⊤)) = 0 :=
    congrArg (fun b : Space.globalFunctions' T.fppfSite S T.fppf_mem
      (residuePoint T z).left.obj => b.1 (op (Space.idEtaleChart T.fppfSite S T.fppf_mem W))) h
  have h10' : (1 : Γ(Spec (S.residueField z), ⊤)) = 0 := h10
  have := congrArg (Scheme.ΓSpecIso (S.residueField z)).hom.hom h10'
  rw [map_one, map_zero] at this
  exact one_ne_zero this

/-- **The module version of Stacks 0DG8, part (1)(b), fails over `S`.** Suppose `n` is a
nonzerodivisor in every local ring of `S` and vanishes in the residue field of some point of
`S`. Then an injective `𝒪`-module on the big étale site of `S` containing `𝒪` restricts to a
non-injective `𝒪_S`-module on the spaces-étale site of `S`. -/
theorem not_injective_restrictModules_baseSpace :
    ¬ Injective ((restrictModules.{u, u + 1} T (baseSpace T)).obj
      (Injective.under (SheafOfModules.unit.{u + 1} (bigEtaleRingSheaf T (baseSpace T))))) :=
  not_injective_restrictModules_under n (eq_zero_of_intCast_mul_eq_zero_of_spacesEtale n hS)
    (residuePoint T z) (intCast_globalFunctions_residuePoint n z hz)
    (one_ne_zero_globalFunctions_residuePoint z)

end Base

/-! ### The counterexample over `Spec ℤ` -/

/-- `Spec ℤ`, in the universe `u`. -/
noncomputable abbrev specInt : Scheme.{u} := Spec (CommRingCat.of (ULift.{u} ℤ))

/-- The integer `2` is a nonzerodivisor in every local ring of `Spec ℤ`. -/
theorem isRegular_two_stalk_specInt (z : specInt.{u}) :
    IsRegular ((2 : ℤ) : specInt.{u}.presheaf.stalk z) :=
  isRegular_intCast_stalk_Spec 2 (fun h => by simpa using congrArg ULift.down h) z

/-- The integer `2` vanishes in the residue field of a point of `Spec ℤ` lying over `2`. -/
theorem exists_two_residueField_specInt_eq_zero :
    ∃ z : specInt.{u}, ((2 : ℤ) : specInt.{u}.residueField z) = 0 := by
  let R := CommRingCat.of (ULift.{u} ℤ)
  have hne : Ideal.span {((2 : ℤ) : R)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h2 := hu.map (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ)
    rw [map_intCast, Int.cast_id, Int.isUnit_iff] at h2
    omega
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let z : specInt.{u} := (⟨m, hm.isPrime⟩ : PrimeSpectrum R)
  refine ⟨z, ?_⟩
  have : z.asIdeal.IsPrime := z.isPrime
  let : Algebra R (specInt.{u}.presheaf.stalk z) := StructureSheaf.stalkAlgebra R z
  have : IsLocalization.AtPrime (specInt.{u}.presheaf.stalk z) z.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R z
  have hmem : ((2 : ℤ) : R) ∈ z.asIdeal := hle (Ideal.mem_span_singleton_self _)
  have h1 : algebraMap R (specInt.{u}.presheaf.stalk z) ((2 : ℤ) : R) ∈
      IsLocalRing.maximalIdeal (specInt.{u}.presheaf.stalk z) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ z.asIdeal _).2 hmem
  have h2 : (specInt.{u}.residue z).hom
      (algebraMap R (specInt.{u}.presheaf.stalk z) ((2 : ℤ) : R)) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 h1
  rw [map_intCast, map_intCast] at h2
  exact h2

variable (T : BigEtaleSpaceSite specInt.{u})

/-- **Stacks Project, Tag 0DG8, the statement for modules, part (1)(b).** Over `S = Spec ℤ`
there is an injective `𝒪`-module on the big étale site of `S` whose restriction to the
spaces-étale site of `S` is not an injective `𝒪_S`-module. -/
@[stacks 0DG8 "the corresponding statement (1)(b) for modules does not hold"]
theorem exists_injective_not_injective_restrictModules :
    ∃ I : BigEtaleModules.{u, u + 1} T (baseSpace T), Injective I ∧
      ¬ Injective ((restrictModules.{u, u + 1} T (baseSpace T)).obj I) := by
  obtain ⟨z, hz⟩ := exists_two_residueField_specInt_eq_zero.{u}
  exact ⟨_, inferInstance,
    not_injective_restrictModules_baseSpace 2 isRegular_two_stalk_specInt z hz⟩

/-- **Stacks Project, Tag 0DG8, the statement for modules, part (1)(a).** Over `S = Spec ℤ`
there are a morphism `f : Y ⟶ X` of algebraic spaces over `S` and an injective `𝒪`-module on
the big étale site of `X` whose inverse image `i_f^*` on the spaces-étale site of `Y` is not an
injective `𝒪_Y`-module; one can take `f` the identity of `X = S`. -/
@[stacks 0DG8 "the corresponding statement (1)(a) for modules does not hold"]
theorem exists_injective_not_injective_restrictModulesAlong :
    ∃ (Y : T.Spaces) (f : Y ⟶ baseSpace T) (I : BigEtaleModules.{u, u + 1} T (baseSpace T)),
      Injective I ∧ ¬ Injective ((restrictModulesAlong T f).obj I) := by
  obtain ⟨I, hI, hnot⟩ := exists_injective_not_injective_restrictModules T
  exact ⟨baseSpace T, 𝟙 _, I, hI, hnot⟩

/-- A complex of sheaves of `𝒪_S`-modules on the spaces-étale site concentrated in degree `0`
whose term is not injective is not K-injective. -/
private theorem not_isKInjective_restrict_single {X Y : T.Spaces}
    (F : BigEtaleModules.{u, u + 1} T X ⥤ SpacesEtaleModules.{u, u + 1} T Y) [F.Additive]
    (I : BigEtaleModules.{u, u + 1} T X) (hI : ¬ Injective (F.obj I)) :
    ¬ CochainComplex.IsKInjective ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor _ 0).obj I)) := by
  intro h
  have e : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor _ 0).obj I) ≅
        (CochainComplex.singleFunctor _ 0).obj (F.obj I) :=
    (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app I
  have : ((CochainComplex.singleFunctor _ 0).obj (F.obj I)).IsKInjective :=
    CochainComplex.isKInjective_of_iso e
  exact hI (CochainComplex.injective_of_isKInjective_single _)

/-- **Stacks Project, Tag 0DG8, the statement for modules, part (2)(b).** Over `S = Spec ℤ`
there is a K-injective complex of `𝒪`-modules on the big étale site of `S` whose restriction to
the spaces-étale site of `S` is not a K-injective complex of `𝒪_S`-modules. -/
@[stacks 0DG8 "the corresponding statement (2)(b) for modules does not hold"]
theorem exists_isKInjective_not_isKInjective_restrictModules :
    ∃ I : CochainComplex (BigEtaleModules.{u, u + 1} T (baseSpace T)) ℤ, I.IsKInjective ∧
      ¬ CochainComplex.IsKInjective
        (((restrictModules.{u, u + 1} T (baseSpace T)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) := by
  obtain ⟨I, hI, hnot⟩ := exists_injective_not_injective_restrictModules T
  exact ⟨(CochainComplex.singleFunctor _ 0).obj I,
    CochainComplex.isKInjective_single_obj_of_injective I 0,
    not_isKInjective_restrict_single T _ I hnot⟩

/-- **Stacks Project, Tag 0DG8, the statement for modules, part (2)(a).** Over `S = Spec ℤ`
there are a morphism `f : Y ⟶ X` of algebraic spaces over `S` and a K-injective complex of
`𝒪`-modules on the big étale site of `X` whose inverse image `i_f^*` on the spaces-étale site of
`Y` is not K-injective; one can take `f` the identity of `X = S`. -/
@[stacks 0DG8 "the corresponding statement (2)(a) for modules does not hold"]
theorem exists_isKInjective_not_isKInjective_restrictModulesAlong :
    ∃ (Y : T.Spaces) (f : Y ⟶ baseSpace T)
      (I : CochainComplex (BigEtaleModules.{u, u + 1} T (baseSpace T)) ℤ), I.IsKInjective ∧
      ¬ CochainComplex.IsKInjective
        (((restrictModulesAlong T f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  obtain ⟨I, hI, hnot⟩ := exists_isKInjective_not_isKInjective_restrictModules T
  exact ⟨baseSpace T, 𝟙 _, I, hI, hnot⟩

end BigEtaleSpaceSite

end AlgebraicGeometry
