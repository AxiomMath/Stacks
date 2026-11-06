module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DifferentialMap
public import StacksFrontier.AlgebraicGeometry.AffineDifferentials.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Twist
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedSpaceDifferentials
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.AffineOpenHom
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import StacksCore.Tactic.StacksAttribute

/-!
# Differentials and the relative Frobenius

Let `S` be a scheme in characteristic `p` and let `X` be a scheme over `S`. The relative
Frobenius `F : X ⟶ X^{(p)}` of `X` over `S` is a morphism over `S`, so the differentials of
`X` over `S` and the differentials of `X` over its Frobenius twist are comparable by the
canonical map of a composable pair. This file shows that this canonical map is an
isomorphism: forming differentials over `S` and over the Frobenius twist gives the same
sheaf.

## Main results

* `AlgebraicGeometry.relativeFrobenius_toRelativeDifferentials_isIso`: the canonical map
  `Ω_{X/S} ⟶ Ω_{X/X^{(p)}}` is an isomorphism.
* `AlgebraicGeometry.isIso_toRelativeDifferentials_relativeFrobenius`: the same statement for
  an arbitrary Cartesian square exhibiting the Frobenius twist, together with an arbitrary
  morphism satisfying the two projection equations of the relative Frobenius.
* `AlgebraicGeometry.Scheme.Hom.isIso_toRelativeDifferentials_of_d_inverseImageStructureMap`:
  the criterion used — the canonical map `Ω_{X/S} ⟶ Ω_{X/Y}` of a composable pair
  `X ⟶ Y ⟶ S` is an isomorphism as soon as the universal relative derivation of `X` over `S`
  annihilates the image of the structural map `f⁻¹ 𝒪_Y ⟶ 𝒪_X`.
* `AlgebraicGeometry.d_relativeFrobenius_app_eq_zero`: the universal relative derivation of
  `X` over `S` annihilates every local section of `𝒪_X` pulled back along the relative
  Frobenius.

## Implementation notes

The two sheaves of differentials represent derivations along two different structural ring
maps, `q⁻¹ 𝒪_S ⟶ 𝒪_X` and `F⁻¹ 𝒪_{X^{(p)}} ⟶ 𝒪_X`, the first factoring through the second.
So the comparison map is an isomorphism exactly when the two functors of derivations
coincide, that is, when every derivation relative to `q⁻¹ 𝒪_S` is already a derivation
relative to `F⁻¹ 𝒪_{X^{(p)}}`. That reduction is
`isIso_toRelativeDifferentials_of_d_inverseImageStructureMap`, and it needs no exactness
statement for the transitivity sequence.

What is left is a statement about local sections, and it is where the Cartesian square
enters. Fix a point of `X`, an affine open `U` around it mapping into an affine open `S₀` of
`S`, and let `K ⊆ Γ(X, U)` be the subring of sections annihilated by the universal relative
derivation. Two kinds of sections lie in `K`: the `p`-th powers, because the derivation is
additive and `p = 0`; and the sections pulled back from `Γ(S, S₀)`, because the derivation is
relative to `S`. Those are exactly the two structural ring maps needed to produce, from the
universal property of the fibre product, a morphism `Spec K ⟶ X^{(p)}` through which `F`
restricted to `U` factors. The factorization is useless on its own, because the open of
`Spec K` over which a given section of `𝒪_{X^{(p)}}` is defined need not be everything — and
here the characteristic enters a second time: `Γ(X, U)` is *integral* over `K`, each element
being a root of `T ^ p - a ^ p`, so `Spec Γ(X, U) ⟶ Spec K` is surjective, the image of
`Spec K` in `X^{(p)}` is the image of `U` under `F`, and the open is everything after all.
The section therefore comes from `K` and is annihilated.

This route does not use the base-change isomorphism for differentials, nor the affine
comparison of the sections of `Ω_{X/S}` with Kähler differentials.

## References

* [Stacks Project, Tag 0CCC](https://stacks.math.columbia.edu/tag/0CCC)
* [Stacks Project, Tag 0CC9](https://stacks.math.columbia.edu/tag/0CC9)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Sheaves.RingedSpaceDifferentials (derivationConstantsSubring)
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-! ### Generalities on the canonical map of a composable pair -/

/-- Two morphisms out of the sheaf of relative differentials which agree on the universal
differentials of all local sections of the structure sheaf are equal. -/
theorem Scheme.Hom.relativeDifferentials_hom_ext {X S : Scheme.{u}} {f : X ⟶ S} {T : X.Modules}
    {ψ₁ ψ₂ : relativeDifferentials f ⟶ T}
    (e : ∀ (U : X.Opens) (a : Γ(X, U)),
      (ψ₁.val.app (.op U)).hom ((universalRelativeDerivation f).d a)
        = (ψ₂.val.app (.op U)).hom ((universalRelativeDerivation f).d a)) :
    ψ₁ = ψ₂ := by
  obtain ⟨m, -, hu⟩ := SheafOfModules.universalDerivation_isUniversal
    (inverseImageStructureMap f) T
    ((SheafOfModules.universalDerivation (inverseImageStructureMap f)).postcomp ψ₁.val)
  refine (hu ψ₁ rfl).trans (hu ψ₂ ?_).symm
  apply PresheafOfModulesOfCommRing.Derivation.ext
  ext U a
  exact (e U.unop a).symm

/-- On sections, the identification of the pullback along an identity with the identity
functor is the unit of the pullback-pushforward adjunction. Both are inverse to the
components of that identification, which is how the conjugation relating the two is read on
an open set. -/
theorem Scheme.Modules.pullbackId_inv_val_app {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    ((Scheme.Modules.pullbackId X).inv.app M).val.app (.op U) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app M).val.app (.op U) := by
  have h := unit_conjugateEquiv Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
    (Scheme.Modules.pullbackId X).hom M
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  have h2 := congrArg (fun k : M ⟶ (Scheme.Modules.pushforward (𝟙 X)).obj M =>
    k.val.app (Opposite.op U)) h
  have hu : ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app M).val.app (.op U) ≫
      ((Scheme.Modules.pullbackId X).hom.app M).val.app (.op U) = 𝟙 _ := h2.symm
  have hi : ((Scheme.Modules.pullbackId X).inv.app M).val.app (.op U) ≫
      ((Scheme.Modules.pullbackId X).hom.app M).val.app (.op U) = 𝟙 _ :=
    congrArg (fun k : M ⟶ M => k.val.app (Opposite.op U))
      ((Scheme.Modules.pullbackId X).inv_hom_id_app M)
  have : IsIso (((Scheme.Modules.pullbackId X).hom.app M).val.app (Opposite.op U)) :=
    ⟨((Scheme.Modules.pullbackId X).inv.app M).val.app (.op U),
      congrArg (fun k : (Scheme.Modules.pullback (𝟙 X)).obj M ⟶
        (Scheme.Modules.pullback (𝟙 X)).obj M => k.val.app (Opposite.op U))
        ((Scheme.Modules.pullbackId X).hom_inv_id_app M), hi⟩
  exact (cancel_mono (((Scheme.Modules.pullbackId X).hom.app M).val.app (Opposite.op U))).mp
    (hi.trans hu.symm)

/-- The canonical map `Ω_{X/S} ⟶ Ω_{X/Y}` of a composable pair `X ⟶ Y ⟶ S` sends the
universal relative differential over `S` of a local section to its universal relative
differential over `Y`. -/
theorem Scheme.Hom.toRelativeDifferentials_val_app_d {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) (U : X.Opens) (a : Γ(X, U)) :
    ((toRelativeDifferentials f g).val.app (.op U)).hom
        ((universalRelativeDerivation (f ≫ g)).d a)
      = (universalRelativeDerivation f).d a := by
  have hcomm : (𝟙 X) ≫ (f ≫ g) = f ≫ g := Category.id_comp _
  have key := relativeDifferentialsMap_app_d (f := 𝟙 X) (p := f ≫ g) (p' := f) g hcomm U a
  have hid : (Scheme.Hom.app (𝟙 X) U).hom a = a := by
    rw [Scheme.Hom.id_app]
    rfl
  rw [hid] at key
  exact (congrArg (fun z => (ModuleCat.Hom.hom
      ((relativeDifferentialsMap (𝟙 X) (f ≫ g) f g hcomm).val.app (Opposite.op U))) z)
    (congrArg (fun k => (ModuleCat.Hom.hom k)
        ((universalRelativeDerivation (f ≫ g)).d a))
      (Scheme.Modules.pullbackId_inv_val_app (relativeDifferentials (f ≫ g)) U))).trans key

/-- The canonical map `Ω_{X/S} ⟶ Ω_{X/Y}` of a composable pair `X ⟶ Y ⟶ S` is an isomorphism
as soon as the universal relative derivation of `X` over `S` annihilates the image of the
structural map `f⁻¹ 𝒪_Y ⟶ 𝒪_X`: the hypothesis says that derivations relative to `S` are
already derivations relative to `Y`, so the two sheaves represent the same functor. -/
theorem Scheme.Hom.isIso_toRelativeDifferentials_of_d_inverseImageStructureMap
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (h : ∀ (U : (Opens X)ᵒᵖ)
        (a : ((TopCat.Sheaf.pullback CommRingCat f.base).obj Y.sheaf).obj.obj U),
      (universalRelativeDerivation (f ≫ g)).d
        (((inverseImageStructureMap f).hom.app U).hom a) = 0) :
    IsIso (toRelativeDifferentials f g) := by
  let D' : SheafOfModules.SheafDerivation (inverseImageStructureMap f)
      (relativeDifferentials (f ≫ g)) :=
    { d := (universalRelativeDerivation (f ≫ g)).d
      d_mul := (universalRelativeDerivation (f ≫ g)).d_mul
      d_map := (universalRelativeDerivation (f ≫ g)).d_map
      d_app := fun {U} a => h U a }
  obtain ⟨ρ, hρ, -⟩ := SheafOfModules.universalDerivation_isUniversal
    (inverseImageStructureMap f) (relativeDifferentials (f ≫ g)) D'
  have hρd : ∀ (U : X.Opens) (a : Γ(X, U)),
      (ρ.val.app (.op U)).hom ((universalRelativeDerivation f).d a)
        = (universalRelativeDerivation (f ≫ g)).d a := fun U a =>
    PresheafOfModulesOfCommRing.Derivation.congr_d hρ a
  refine ⟨ρ, relativeDifferentials_hom_ext fun U a => ?_,
    relativeDifferentials_hom_ext fun U a => ?_⟩
  · exact (congrArg (fun z => (ρ.val.app (.op U)).hom z)
      (toRelativeDifferentials_val_app_d f g U a)).trans (hρd U a)
  · exact (congrArg (fun z => ((toRelativeDifferentials f g).val.app (.op U)).hom z)
      (hρd U a)).trans (toRelativeDifferentials_val_app_d f g U a)

/-! ### Derivations in characteristic `p` -/

/-- A relative derivation of the structure sheaf of a scheme in characteristic `p`
annihilates the `p`-th power of every local section. -/
theorem d_pow_eq_zero_of_isInCharacteristic {X S : Scheme.{u}} (f : X ⟶ S) (p : ℕ)
    (hX : IsInCharacteristic X p) (M : X.Modules)
    (D : SheafOfModules.SheafDerivation (inverseImageStructureMap f) M)
    (U : X.Opens) (s : Γ(X, U)) : D.d (s ^ p) = 0 := by
  let _ : Module Γ(X, U) (M.val.obj (.op U)) := (M.val.obj (.op U)).isModule
  let D' : Derivation ℤ (Γ(X, U)) (M.val.obj (.op U)) :=
    { toLinearMap := (D.d (X := .op U)).toIntLinearMap
      map_one_eq_zero' := D.d_one (.op U)
      leibniz' := D.d_mul }
  have hp := D'.leibniz_pow s p
  rw [← Nat.cast_smul_eq_nsmul (Γ(X, U)) p, cast_eq_zero_of_isInCharacteristic hX U] at hp
  exact (by simpa using hp : D' (s ^ p) = 0)

/-! ### The relative Frobenius annihilates the differentials over the base -/

section

variable {S X' W : Scheme.{u}} (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)
  {b : W ⟶ X'} {c : W ⟶ S} (F : X' ⟶ W)
  (hPB : IsPullback b c (F ≫ c) (absoluteFrobenius S p hS))
  (hb : F ≫ b = absoluteFrobenius X' p (isInCharacteristic_of_hom (F ≫ c) p hS))

include hPB hb in
/-- On an affine open `U` of `X` lying over an affine open of the base, the universal
relative derivation of `X` over `S` annihilates every section pulled back along the relative
Frobenius.

The subring `K ⊆ Γ(X, U)` of sections annihilated by the derivation receives the `p`-th
power map and the structural map of the base, hence carries two morphisms out of `Spec K`
forming a commutative square with the absolute Frobenius of the base, hence a morphism
`Spec K ⟶ W` through which the restriction of the relative Frobenius factors. Since
`Γ(X, U)` is integral over `K`, that factorization is through the whole of `Spec K` and the
section is a section of `K`. -/
theorem d_appLE_relativeFrobenius_eq_zero_of_isAffineOpen
    (V : W.Opens) (b₀ : Γ(W, V)) {S₀ : S.Opens} (hS₀ : IsAffineOpen S₀)
    {U : X'.Opens} (hU : IsAffineOpen U) (hUV : U ≤ F ⁻¹ᵁ V)
    (hUS : U ≤ (F ≫ c) ⁻¹ᵁ S₀) :
    (Scheme.Hom.universalRelativeDerivation (F ≫ c)).d ((F.appLE V U hUV).hom b₀) = 0 := by
  have hX : IsInCharacteristic X' p := isInCharacteristic_of_hom (F ≫ c) p hS
  have hchar : (p : Γ(X', U)) = 0 := cast_eq_zero_of_isInCharacteristic hX U
  set D := Scheme.Hom.universalRelativeDerivation (F ≫ c) with hDdef
  set K : Subring Γ(X', U) := derivationConstantsSubring D (.op U) with hKdef
  have hpow : ∀ a : Γ(X', U), a ^ p ∈ K := fun a =>
    d_pow_eq_zero_of_isInCharacteristic (F ≫ c) p hX _ D U a
  have hfrob : ∀ a : Γ(X', U), primePowerEndomorphism Γ(X', U) p hchar a ∈ K := fun a => by
    rw [primePowerEndomorphism_apply]
    exact hpow a
  have hqmem : ∀ γ : Γ(S, S₀), (((F ≫ c).appLE S₀ U hUS).hom) γ ∈ K := fun γ =>
    Stacks.AlgebraicGeometry.AffineDifferentials.d_appLE_eq_zero (F ≫ c) _ D S₀ U hUS γ
  set Kc : CommRingCat.{u} := CommRingCat.of K with hKc
  set frobK : Γ(X', U) ⟶ Kc :=
    CommRingCat.ofHom ((primePowerEndomorphism Γ(X', U) p hchar).codRestrict K hfrob) with hfK
  set qK : Γ(S, S₀) ⟶ Kc :=
    CommRingCat.ofHom ((((F ≫ c).appLE S₀ U hUS).hom).codRestrict K hqmem) with hqK
  set incl : Kc ⟶ Γ(X', U) := CommRingCat.ofHom K.subtype with hincl
  have heS : S₀ ≤ (absoluteFrobenius S p hS) ⁻¹ᵁ S₀ :=
    le_of_eq (absoluteFrobenius_preimage S p hS S₀).symm
  have heU : U ≤ (absoluteFrobenius X' p hX) ⁻¹ᵁ U :=
    le_of_eq (absoluteFrobenius_preimage X' p hX U).symm
  have hmono : Mono incl := ConcreteCategory.mono_of_injective _ Subtype.coe_injective
  have hfrobincl : frobK ≫ incl = (absoluteFrobenius X' p hX).appLE U U heU := by
    apply CommRingCat.hom_ext
    ext a
    change (primePowerEndomorphism Γ(X', U) p hchar) a
      = ((absoluteFrobenius X' p hX).appLE U U heU).hom a
    rw [primePowerEndomorphism_apply, absoluteFrobenius_appLE_apply]
  have hqincl : qK ≫ incl = (F ≫ c).appLE S₀ U hUS := by
    apply CommRingCat.hom_ext
    ext γ
    rfl
  have hcommring : (F ≫ c).appLE S₀ U hUS ≫ frobK
      = (absoluteFrobenius S p hS).appLE S₀ S₀ heS ≫ qK := by
    apply (cancel_mono incl).mp
    rw [Category.assoc, Category.assoc, hfrobincl, hqincl]
    apply CommRingCat.hom_ext
    ext γ
    change ((absoluteFrobenius X' p hX).appLE U U heU).hom (((F ≫ c).appLE S₀ U hUS).hom γ)
      = ((F ≫ c).appLE S₀ U hUS).hom
          (((absoluteFrobenius S p hS).appLE S₀ S₀ heS).hom γ)
    rw [absoluteFrobenius_appLE_apply, absoluteFrobenius_appLE_apply, map_pow]
  set ψ₁ : Spec Kc ⟶ X' := Spec.map frobK ≫ hU.fromSpec with hψ₁
  set ψ₂ : Spec Kc ⟶ S := Spec.map qK ≫ hS₀.fromSpec with hψ₂
  have hcomm : ψ₁ ≫ (F ≫ c) = ψ₂ ≫ absoluteFrobenius S p hS := by
    rw [hψ₁, hψ₂, Category.assoc, Category.assoc,
      ← IsAffineOpen.SpecMap_appLE_fromSpec (F ≫ c) hS₀ hU hUS,
      ← IsAffineOpen.SpecMap_appLE_fromSpec (absoluteFrobenius S p hS) hS₀ hS₀ heS,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hcommring]
  set ψ : Spec Kc ⟶ W := hPB.lift ψ₁ ψ₂ hcomm with hψ
  set j : Spec Γ(X', U) ⟶ Spec Kc := Spec.map incl with hj
  have hjψ : j ≫ ψ = hU.fromSpec ≫ F := by
    apply hPB.hom_ext
    · rw [Category.assoc, hPB.lift_fst, hψ₁, hj, ← Spec.map_comp_assoc, hfrobincl,
        IsAffineOpen.SpecMap_appLE_fromSpec, Category.assoc, hb]
    · rw [Category.assoc, hPB.lift_snd, hψ₂, hj, ← Spec.map_comp_assoc, hqincl,
        IsAffineOpen.SpecMap_appLE_fromSpec, Category.assoc]
  have hint : (K.subtype : K →+* Γ(X', U)).IsIntegral := by
    intro a
    refine ⟨Polynomial.X ^ p - Polynomial.C ⟨a ^ p, hpow a⟩,
      Polynomial.monic_X_pow_sub_C _ (Nat.Prime.ne_zero Fact.out), ?_⟩
    simp
  have hjsurj : Function.Surjective j.base :=
    RingHom.IsIntegral.comap_surjective hint Subtype.coe_injective
  have hψV : (⊤ : (Spec Kc).Opens) ≤ ψ ⁻¹ᵁ V := by
    rintro z -
    obtain ⟨w, rfl⟩ := hjsurj z
    have h1 : ψ.base (j.base w) = F.base (hU.fromSpec.base w) :=
      congrArg (fun k : Spec Γ(X', U) ⟶ W => k.base w) hjψ
    change ψ.base (j.base w) ∈ V
    rw [h1]
    refine hUV ?_
    have hmem : hU.fromSpec.base w ∈ Set.range hU.fromSpec.base := Set.mem_range_self w
    rwa [hU.range_fromSpec] at hmem
  have heTop : (⊤ : (Spec Γ(X', U)).Opens) ≤ j ⁻¹ᵁ (⊤ : (Spec Kc).Opens) := le_top
  have heU' : (⊤ : (Spec Γ(X', U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U :=
    le_of_eq hU.fromSpec_preimage_self.symm
  have hfromSpec : hU.fromSpec.appLE U ⊤ heU' = (Scheme.ΓSpecIso Γ(X', U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp,
      Subsingleton.elim ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE heU').op)
        (𝟙 (Opposite.op (⊤ : (Spec Γ(X', U)).Opens)))]
    simp
  have hjtop : j.appLE ⊤ ⊤ heTop = j.appTop := rfl
  have hfac : F.appLE V U hUV ≫ (Scheme.ΓSpecIso Γ(X', U)).inv
      = ψ.appLE V ⊤ hψV ≫ j.appTop := by
    rw [← hfromSpec, ← hjtop, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact (Stacks.AffineAlgebraEquivalence.appLE_congr_hom hjψ _ _).symm
  have hfinal : F.appLE V U hUV = ψ.appLE V ⊤ hψV ≫ (Scheme.ΓSpecIso Kc).hom ≫ incl := by
    have h := congrArg (fun k : Γ(W, V) ⟶ Γ(Spec Γ(X', U), ⊤) =>
      k ≫ (Scheme.ΓSpecIso Γ(X', U)).hom) hfac
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
    rw [h, hj, Scheme.ΓSpecIso_naturality]
  rw [hfinal]
  exact (((Scheme.ΓSpecIso Kc).hom.hom) ((ψ.appLE V ⊤ hψV).hom b₀)).2

include hPB hb in
/-- The universal relative derivation of `X` over `S` annihilates every local section of the
structure sheaf of `X` pulled back along the relative Frobenius. Annihilation is a local
condition, so this follows from the affine case. -/
theorem d_relativeFrobenius_app_eq_zero (V : W.Opens) (b₀ : Γ(W, V)) :
    (Scheme.Hom.universalRelativeDerivation (F ≫ c)).d ((F.app V).hom b₀) = 0 := by
  refine TopCat.Presheaf.IsSheaf.section_ext
    (Scheme.Modules.isSheaf (Scheme.Hom.relativeDifferentials (F ≫ c))) fun y hy => ?_
  obtain ⟨S₀, hS₀mem, hyS₀, -⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
    (show (F ≫ c).base y ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨U, hUmem, hyU, hUle⟩ := Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens
    (show y ∈ (F ⁻¹ᵁ V) ⊓ ((F ≫ c) ⁻¹ᵁ S₀) from ⟨hy, hyS₀⟩)
  refine ⟨U, hUle.trans inf_le_left, hyU, ?_⟩
  refine Eq.trans ?_ (map_zero _).symm
  refine Eq.trans ((Scheme.Hom.universalRelativeDerivation (F ≫ c)).d_map
    (homOfLE (hUle.trans inf_le_left : U ≤ F ⁻¹ᵁ V)).op ((F.app V).hom b₀)).symm ?_
  exact d_appLE_relativeFrobenius_eq_zero_of_isAffineOpen p hS F hPB hb V b₀ hS₀mem hUmem
    (hUle.trans inf_le_left) (hUle.trans inf_le_right)

include hPB hb in
/-- For a Cartesian square exhibiting the Frobenius twist of `X` over a scheme `S` in
characteristic `p`, and a morphism `F` satisfying the two projection equations of the
relative Frobenius, the canonical map from the differentials of `X` over `S` to the
differentials of `X` over the twist is an isomorphism. -/
@[ega "0 21.3.2" "more general"]
theorem isIso_toRelativeDifferentials_relativeFrobenius :
    IsIso (Scheme.Hom.toRelativeDifferentials F c) :=
  Scheme.Hom.isIso_toRelativeDifferentials_of_d_inverseImageStructureMap F c fun U a =>
    Stacks.Sheaves.RingedSpaceDifferentials.derivation_d_inverseImageStructureMap_eq_zero
      F.toLRSHom.toShHom (Scheme.Modules.isSheaf _)
      (Scheme.Hom.universalRelativeDerivation (F ≫ c))
      (fun V b₀ => d_relativeFrobenius_app_eq_zero p hS F hPB hb V b₀) U a

end

/-- **Stacks Project, Tag 0CCC.** The canonical map from the differentials of
`X` over `S` to the differentials of `X` over its Frobenius twist is an
isomorphism. -/
@[stacks 0CCC, instance, ega "0 21.3.2" "more general"]
theorem relativeFrobenius_toRelativeDifferentials_isIso
    (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p) (X : Over S) :
    IsIso (Scheme.Hom.toRelativeDifferentials
      (relativeFrobenius S p hS X).left ((frobeniusTwist S p hS).obj X).hom) := by
  refine isIso_toRelativeDifferentials_relativeFrobenius
    (b := pullback.fst X.hom (absoluteFrobenius S p hS)) p hS _ ?_ ?_
  · rw [show (relativeFrobenius S p hS X).left ≫ ((frobeniusTwist S p hS).obj X).hom = X.hom from
      relativeFrobenius_snd S p hS X]
    exact IsPullback.of_hasPullback X.hom (absoluteFrobenius S p hS)
  · exact relativeFrobenius_fst S p hS X

end AlgebraicGeometry

end
