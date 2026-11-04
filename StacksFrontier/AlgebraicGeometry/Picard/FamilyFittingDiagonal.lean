/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Picard.FamilyFittingIdeal
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.ShortExactCoker
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.NormalizedSection
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequenceTwistDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeProperties
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeBaseChange.PullbackSections
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertPointAddition
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFamilyPicardClass
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClassPullback
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Scheme
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence

/-!
# The Fitting ideal of `H¹` of a family twisted down by a section

Let `X` be a proper scheme over a field `k` covered by two affine opens, `A` a `k`-algebra and
`X_A = X ×_k Spec A`. Let `N` be an invertible module on `X` whose pullback to `X_A` has
`H¹ = 0` and `H⁰` free on the pullback of a section `s` of `N`, on every fibre. Let `D ⊂ X_A`
be an effective Cartier divisor mapping isomorphically to `Spec A` (the graph of an `A`-point of
`X`), and `M` an invertible module with `M ⊗ 𝒪(D) ≅ N_A`. Then

`Fit₀ H¹(X_A, M) = Z(s)|_D`,

the ideal of the zero scheme of `s` restricted to `D ≅ Spec A`. This is the computation
`R¹π_* (N(-Δ)) = N|_D / (s)` behind the theorem that the theta divisor pulls back to the divisor
of `s` along `c ↦ [D_s - c]`, in the construction of the polarization used for
[Stacks, Tag 03U1].

The proof is the long exact sequence of `0 ⟶ M ⟶ M ⊗ 𝒪(D) ⟶ i_* i^*(M ⊗ 𝒪(D)) ⟶ 0` (the
twisted sequence of [Stacks, Tag 0C6K]) read on two-term Čech complexes
(`Stacks.TwoAffineCech.cokerEquivOfShortExact`): `H¹(X_A, M)` is the cokernel of
`H⁰(X_A, N_A) = A·s ⟶ H⁰(D, N|_D)`, and the zeroth Fitting ideal of an invertible module modulo a
section is the ideal of the zero scheme of the section.

## Main results

* `Stacks.FamilyFitting.fittingIdeal_quotient_span_singleton`: `Fit₀(M / A z₀)` for `M` free of
  rank one through a semilinear bijection.
* `Stacks.FamilyFitting.cechFitting_eq_fittingIdeal_quotient`: `Fit₀ H¹(M) = Fit₀(H⁰(Q)/A t)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry MonoidalCategory

universe u

namespace Stacks.FamilyFitting

/-! ### Fitting ideals of a cyclic quotient of a free module of rank one -/

section Algebra

variable {A R : Type u} [CommRing A] [CommRing R] (ρ : A →+* R) (hρ : Function.Bijective ρ)
  {M : Type u} [AddCommGroup M] [Module A M]

include hρ in
/-- The `A`-linear equivalence `M ≃ₗ[A] A` of a bijection `Ψ : M ⟶ R` that is semilinear over a
ring isomorphism `ρ : A ⟶ R`. -/
private def linearEquivOfSemilinear (Ψ : M →+ R) (hΨ : Function.Bijective Ψ)
    (hsmul : ∀ (a : A) (z : M), Ψ (a • z) = ρ a * Ψ z) : M ≃ₗ[A] A where
  toFun z := (RingEquiv.ofBijective ρ hρ).symm (Ψ z)
  invFun a := (AddEquiv.ofBijective Ψ hΨ).symm (ρ a)
  map_add' z w := by simp
  map_smul' a z := by
    simp only [hsmul, RingHom.id_apply, smul_eq_mul, map_mul]
    congr 1
    exact (RingEquiv.ofBijective ρ hρ).symm_apply_apply a
  left_inv z := by
    simp only
    rw [show ρ ((RingEquiv.ofBijective ρ hρ).symm (Ψ z)) = Ψ z from
      (RingEquiv.ofBijective ρ hρ).apply_symm_apply (Ψ z)]
    exact (AddEquiv.ofBijective Ψ hΨ).symm_apply_apply z
  right_inv a := by
    simp only
    rw [show Ψ ((AddEquiv.ofBijective Ψ hΨ).symm (ρ a)) = ρ a from
      (AddEquiv.ofBijective Ψ hΨ).apply_symm_apply (ρ a)]
    exact (RingEquiv.ofBijective ρ hρ).symm_apply_apply a

include hρ in
/-- **`Fit₀(M / A z₀) = ρ⁻¹(b)`** when `Ψ : M ⟶ R` is a bijection with `Ψ(a z) = ρ(a) Ψ(z)` and
`ρ : A ⟶ R` is a ring isomorphism. -/
theorem fittingIdeal_quotient_span_singleton (Ψ : M →+ R) (hΨ : Function.Bijective Ψ)
    (hsmul : ∀ (a : A) (z : M), Ψ (a • z) = ρ a * Ψ z) (z₀ : M) :
    haveI : Module.Finite A (M ⧸ Submodule.span A {z₀}) := by
      have : Module.Finite A M :=
        Module.Finite.equiv (linearEquivOfSemilinear ρ hρ Ψ hΨ hsmul).symm
      infer_instance
    fittingIdeal (R := A) (M := M ⧸ Submodule.span A {z₀}) ((0 : ℕ) : ℤ) =
      Ideal.comap ρ (Ideal.span {Ψ z₀}) := by
  set ρe := RingEquiv.ofBijective ρ hρ
  let e := linearEquivOfSemilinear ρ hρ Ψ hΨ hsmul
  have : Module.Finite A M := Module.Finite.equiv e.symm
  have hspan : (Submodule.span A {z₀}).map e.toLinearMap = Ideal.span {e z₀} := by
    rw [Submodule.map_span, Set.image_singleton]
    rfl
  refine (fittingIdeal_eq_of_linearEquiv (Submodule.Quotient.equiv _ _ e hspan) 0).trans ?_
  refine ((fittingIdeal_basic_properties.{u, u, u, u} (R := A) (M := A)).2.2.2.2.2.2.2
    (Ideal.span {e z₀})).trans ?_
  ext a
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  show ρe.symm (Ψ z₀) ∣ a ↔ Ψ z₀ ∣ ρ a
  rw [← map_dvd_iff ρe, ρe.apply_symm_apply]
  rfl

end Algebra

/-! ### `Fit₀ H¹` of the kernel of a short exact sequence -/

section ShortExact

open Stacks.TwoAffineCech

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProper fX]
  (U : Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
  {A : Type u} [CommRing A] [Algebra k A] {XA : Scheme.{u}} (gA : XA ⟶ X)
  (fA : XA ⟶ Spec (.of A))
  (hA : IsPullback gA fA fX (Spec.map (CommRingCat.ofHom (algebraMap k A))))

/-- The image of the cocycles of `C.X₂` in those of `C.X₃` is spanned by the cocycle of `β(s)`
when the cocycle of `s` spans the cocycles of `C.X₂`. -/
private theorem range_kerMap_eq_span_sectionCocycle (C : ShortComplex XA.Modules) (s : Γ(C.X₂, ⊤))
    (hs : Submodule.span A {sectionCocycle fA (sqCover U gA) C.X₂ s} = ⊤) :
    LinearMap.range (Stacks.TwoTermComplex.kerMap (cechD_comp_cechMap fA (sqCover U gA) C.g)) =
      Submodule.span A {sectionCocycle fA (sqCover U gA) C.X₃ (C.g.app ⊤ s)} := by
  rw [← Submodule.map_top, ← hs, Submodule.map_span, Set.image_singleton]
  exact congrArg (fun z => Submodule.span A {z}) (kerMap_sectionCocycle fA (sqCover U gA) C.g s)

include hA in
/-- **`Fit₀ H¹(M) = Fit₀(H⁰(Q) / A·β(s))`** for a short exact sequence `0 ⟶ M ⟶ P ⟶ Q ⟶ 0` of
quasi-coherent modules on `X_A` with `M` invertible, `H¹(X_A, P) = 0` and `H⁰(X_A, P)` generated
by a section `s`. -/
theorem cechFitting_eq_fittingIdeal_quotient (C : ShortComplex XA.Modules)
    [Stacks.Ample.IsInvertibleModule XA C.X₁] [C.X₂.IsQuasicoherent] [C.X₃.IsQuasicoherent]
    (hC : C.ShortExact) (hP : Function.Surjective (cechD fA (sqCover U gA) C.X₂))
    (s : Γ(C.X₂, ⊤))
    (hs : Submodule.span A {sectionCocycle fA (sqCover U gA) C.X₂ s} = ⊤) :
    haveI : Module.Finite A (LinearMap.ker (cechD fA (sqCover U gA) C.X₃) ⧸
        Submodule.span A {sectionCocycle fA (sqCover U gA) C.X₃ (C.g.app ⊤ s)}) := by
      have := module_finite_coker_of_model
        (hasFiniteProjectiveModel_of_isPullback fX U hU hUaff gA fA hA C.X₁)
      have : C.X₁.IsQuasicoherent :=
        Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule C.X₁
      have : IsSeparated fA := isSeparated_of_isPullback' fX gA fA hA
      let e := cokerEquivOfShortExact fA (sqCover U gA) (isAffineOpen_sqCover fX U hUaff gA fA hA)
        C hC hP
      exact Module.Finite.equiv (e.trans (Submodule.quotEquivOfEq _ _
        (range_kerMap_eq_span_sectionCocycle U gA fA C s hs)))
    cechFitting fX U hU hUaff gA fA hA C.X₁ =
      fittingIdeal (R := A) (M := LinearMap.ker (cechD fA (sqCover U gA) C.X₃) ⧸
        Submodule.span A {sectionCocycle fA (sqCover U gA) C.X₃ (C.g.app ⊤ s)}) ((0 : ℕ) : ℤ) := by
  have := module_finite_coker_of_model
    (hasFiniteProjectiveModel_of_isPullback fX U hU hUaff gA fA hA C.X₁)
  have : C.X₁.IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule C.X₁
  have : IsSeparated fA := isSeparated_of_isPullback' fX gA fA hA
  let e := (cokerEquivOfShortExact fA (sqCover U gA) (isAffineOpen_sqCover fX U hUaff gA fA hA)
    C hC hP).trans
      (Submodule.quotEquivOfEq _ _ (range_kerMap_eq_span_sectionCocycle U gA fA C s hs))
  have : Module.Finite A (LinearMap.ker (cechD fA (sqCover U gA) C.X₃) ⧸
      Submodule.span A {sectionCocycle fA (sqCover U gA) C.X₃ (C.g.app ⊤ s)}) :=
    Module.Finite.equiv e
  rw [cechFitting, fittingCoker]
  exact fittingIdeal_eq_of_linearEquiv e 0

end ShortExact

/-! ### The chart computation -/

section Chart

open Stacks.TwoAffineCech

variable {A : Type u} [CommRing A] {Z : Scheme.{u}} (fZ : Z ⟶ Spec (.of A))
  (V : Cover.{u} → Z.Opens) (hV : (⊤ : Z.Opens) = ⨆ i, V i)

include hV in
/-- For a cover `V` of `Z`, the map `sectionCocycle` from global sections of `F` to the Čech
cocycles `LinearMap.ker (cechD fZ V F)` is bijective. -/
theorem bijective_sectionCocycle (F : Z.Modules) : Function.Bijective (sectionCocycle fZ V F) :=
  ⟨fun _ _ hxy => sectionCochain_injective V F hV
      (congrArg (fun z : LinearMap.ker (cechD fZ V F) => altCochain fZ V F z.1) hxy),
    fun c => exists_sectionCocycle_eq fZ V F hV c⟩

/-- The map `sectionCocycle` is `A`-linear: it commutes with scalar multiplication by `a : A`. -/
theorem sectionCocycle_smul (F : Z.Modules) (a : A) (q : Γ(F, ⊤)) :
    sectionCocycle fZ V F ((Stacks.Cech.baseRingHom fZ ⊤).hom a • q) =
      a • sectionCocycle fZ V F q :=
  Subtype.ext (Subtype.ext (sectionCochain_smul fZ V F a q))

include hV in
/-- An additive bijection `e : Γ(F, ⊤) ⟶ R`, semilinear over `ρ : A ⟶ R`, transports along
`sectionCocycle` to such a bijection on the Čech cocycles of `F`. -/
private theorem exists_bijective_semilinear_sectionCocycle (F : Z.Modules) {R : Type u} [CommRing R]
    (ρ : A →+* R) (e : Γ(F, ⊤) →+ R) (he : Function.Bijective e)
    (hsmul : ∀ (a : A) (q : Γ(F, ⊤)), e ((Stacks.Cech.baseRingHom fZ ⊤).hom a • q) = ρ a * e q) :
    ∃ Ψ : LinearMap.ker (cechD fZ V F) →+ R, Function.Bijective Ψ ∧
      (∀ (a : A) (z : LinearMap.ker (cechD fZ V F)), Ψ (a • z) = ρ a * Ψ z) ∧
      ∀ q, Ψ (sectionCocycle fZ V F q) = e q := by
  let Φ : Γ(F, ⊤) ≃+ LinearMap.ker (cechD fZ V F) := AddEquiv.ofBijective
    ({ toFun := sectionCocycle fZ V F
       map_zero' := Subtype.ext (Subtype.ext (sectionCochain_zero V F))
       map_add' := fun a b => Subtype.ext (Subtype.ext (sectionCochain_add V F a b)) } :
      Γ(F, ⊤) →+ LinearMap.ker (cechD fZ V F))
    (bijective_sectionCocycle fZ V hV F)
  refine ⟨e.comp Φ.symm.toAddMonoidHom, he.comp Φ.symm.bijective, fun a z => ?_,
    fun q => congrArg e (Φ.symm_apply_apply q)⟩
  obtain ⟨q, rfl⟩ := Φ.surjective z
  have h2 : a • Φ q = Φ ((Stacks.Cech.baseRingHom fZ ⊤).hom a • q) :=
    (sectionCocycle_smul fZ V F a q).symm
  show e (Φ.symm (a • Φ q)) = _ * e (Φ.symm (Φ q))
  rw [h2, Φ.symm_apply_apply, Φ.symm_apply_apply]
  exact hsmul a q

end Chart

section Twist

open Stacks.TwoAffineCech Stacks.Divisors Stacks.FibreCohomology

attribute [local instance] AlgebraicGeometry.schemeModulesMonoidal
  AlgebraicGeometry.schemeModulesSymmetric

/-- On an affine `Y` over `X_A` on which the pullback of `N` is trivialized by `et`, the ideal of
the pulled-back zero scheme of `s` is generated by the value of `et` at the pulled-back section. -/
private theorem zeroScheme_comap_ideal_eq_span {X XA Y : Scheme.{u}} [IsAffine Y] (gA : XA ⟶ X)
    (N : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (s : Γ(N, ⊤)) (i : Y ⟶ XA)
    (et : (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback gA).obj N) ≅
      SheafOfModules.unit Y.ringCatSheaf) :
    ((AlgebraicGeometry.zeroScheme X N s).comap (i ≫ gA)).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      Ideal.span ({et.hom.app ⊤ (((Scheme.Modules.pullback i).obj
        ((Scheme.Modules.pullback gA).obj N)).presheaf.map (homOfLE le_top).op
          (pullbackGlobalSections i _ (pullbackGlobalSections gA N s)))} : Set Γ(Y, ⊤)) := by
  have : Stacks.Ample.IsInvertibleModule X N :=
    ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N›
  have : Stacks.Ample.IsInvertibleModule XA ((Scheme.Modules.pullback gA).obj N) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback _ N
  have : IsIso (et.hom.app ⊤) := Scheme.Modules.Hom.isIso_iff_isIso_app.mp et.isIso_hom ⊤
  let e' : Γ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback gA).obj N), ⊤) ≃ₗ[Γ(Y, ⊤)]
      Γ(Y, ⊤) :=
    LinearEquiv.ofBijective
      ({ toFun := fun t => et.hom.app ⊤ t
         map_add' := fun a b => map_add _ a b
         map_smul' := fun r t => Scheme.Modules.Hom.app_smul et.hom r t } :
        Γ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback gA).obj N), ⊤) →ₗ[Γ(Y, ⊤)]
          Γ(Y, ⊤)) (ConcreteCategory.bijective_of_isIso (et.hom.app ⊤))
  refine (congrArg (fun I : Y.IdealSheafData => I.ideal ⟨⊤, isAffineOpen_top _⟩)
    ((Stacks.Divisors.zeroScheme_pullback i _ (pullbackGlobalSections gA N s)).trans
      ((congrArg (fun I => I.comap i) (Stacks.Divisors.zeroScheme_pullback gA N s)).trans
        (Scheme.IdealSheafData.comap_comp _ _ _).symm))).symm.trans ?_
  exact Stacks.Divisors.zeroScheme_ideal_of_trivialization Y _
    (pullbackGlobalSections i _ (pullbackGlobalSections gA N s)) ⟨⊤, isAffineOpen_top Y⟩ e' _ rfl

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProper fX]
  (U : Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
  {A : Type u} [CommRing A] [Algebra k A] {XA : Scheme.{u}} (gA : XA ⟶ X)
  (fA : XA ⟶ Spec (.of A))
  (hA : IsPullback gA fA fX (Spec.map (CommRingCat.ofHom (algebraMap k A))))
  (N : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  (s : Γ(N, ⊤)) (D : XA.IdealSheafData) [IsEffectiveCartierDivisor D]
  (M : XA.Modules) [Stacks.Ample.IsInvertibleModule XA M]

omit [IsProper fX] in
/-- The restriction to `⊤` of a pulled-back global section is the value of the unit. -/
theorem presheaf_map_pullbackGlobalSections {Y W : Scheme.{u}} (i : Y ⟶ W) (P : W.Modules)
    (t : Γ(P, ⊤)) :
    ((Scheme.Modules.pullback i).obj P).presheaf.map (homOfLE le_top).op
        (pullbackGlobalSections i P t) =
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app P).app ⊤ t := by
  have hid' : ((Scheme.Modules.pullback i).obj P).presheaf.map
      (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [show (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op =
      CategoryTheory.CategoryStruct.id (Opposite.op (⊤ : Y.Opens)) from rfl]
    exact CategoryTheory.Functor.map_id _ _
  exact (ConcreteCategory.congr_hom hid' _).trans
    (ConcreteCategory.congr_hom (pullbackGlobalSections_eq_unit i P) t)

/-- The ring map `A ⟶ Γ(D, 𝒪_D)` of a closed subscheme of `X_A`. -/
abbrev divisorRingHom : A →+* Γ(D.subscheme, ⊤) :=
  D.subschemeι.appTop.hom.comp (Stacks.Cech.baseRingHom fA ⊤).hom

omit [IsEffectiveCartierDivisor D] in
/-- `divisorRingHom fA D` is the map on global sections of the composite `D ⟶ X_A ⟶ Spec A`,
precomposed with `A ≅ Γ(Spec A, ⊤)`. -/
theorem divisorRingHom_eq :
    divisorRingHom fA D =
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (D.subschemeι ≫ fA).appTop).hom := by
  rw [Scheme.Hom.comp_appTop]
  ext a
  show D.subschemeι.appTop ((Stacks.Cech.globalRingHom fA ≫
    XA.presheaf.map (homOfLE le_top).op) a) = _
  rw [show (homOfLE (le_top : (⊤ : XA.Opens) ≤ ⊤)).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rfl

omit [IsEffectiveCartierDivisor D] in
/-- If the composite `D ⟶ X_A ⟶ Spec A` is an isomorphism, then `divisorRingHom fA D` is
bijective. -/
theorem bijective_divisorRingHom (hD : IsIso (D.subschemeι ≫ fA)) :
    Function.Bijective (divisorRingHom fA D) := by
  rw [divisorRingHom_eq]
  have : IsIso (D.subschemeι ≫ fA).appTop :=
    (inferInstance : IsIso ((D.subschemeι ≫ fA).app ⊤))
  exact ConcreteCategory.bijective_of_isIso _

/-- **The chart computation**: `Fit₀ H¹(X_A, M)` is the ideal of the zero scheme of `s` restricted
to `D ≅ Spec A`, when `M ⊗ 𝒪(D) ≅ N_A`, the fibres of `N_A` have `H¹ = 0` and `H⁰` spanned by
`s`, and `N_A|_D` is trivial. -/
theorem cechFitting_eq_comap_zeroScheme (hD : IsIso (D.subschemeι ≫ fA))
    (e₁ : M ⊗ modulesInvertibleSheaf D ≅ (Scheme.Modules.pullback gA).obj N)
    (h1 : ∀ x : Spec (.of A), Module.finrank ((Spec (.of A)).residueField x)
      (fibreCohomology fA ((Scheme.Modules.pullback gA).obj N) x 1) = 0)
    (h0 : ∀ x : Spec (.of A), Module.finrank ((Spec (.of A)).residueField x)
      (fibreCohomology fA ((Scheme.Modules.pullback gA).obj N) x 0) = 1)
    (hnz : ∀ p : PrimeSpectrum A, NonzeroAtFieldPoint fA ((Scheme.Modules.pullback gA).obj N)
      (pullbackGlobalSections gA N s) p)
    (et : (Scheme.Modules.pullback D.subschemeι).obj ((Scheme.Modules.pullback gA).obj N) ≅
      SheafOfModules.unit D.subscheme.ringCatSheaf) :
    haveI : IsAffine D.subscheme := IsAffine.of_isIso (D.subschemeι ≫ fA)
    cechFitting fX U hU hUaff gA fA hA M =
      Ideal.comap (divisorRingHom fA D)
        (((AlgebraicGeometry.zeroScheme X N s).comap (D.subschemeι ≫ gA)).ideal
          ⟨⊤, isAffineOpen_top D.subscheme⟩) := by
  have : IsAffine D.subscheme := IsAffine.of_isIso (D.subschemeι ≫ fA)
  set i := D.subschemeι
  set P := (Scheme.Modules.pullback gA).obj N
  have : SheafOfModules.IsInvertible XA.sheaf.obj XA.ringCatSheaf.property M :=
    isInvertible_of_isInvertibleModule M
  have : Stacks.Ample.IsInvertibleModule X N :=
    ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N›
  have : Stacks.Ample.IsInvertibleModule XA P :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback _ N
  obtain ⟨h, hse⟩ := isShortExactTwistSequence_canonicalSections D M
  set f₀ : M ⟶ M ⊗ modulesInvertibleSheaf D :=
    (ρ_ M).inv ≫ M ◁ (modulesInvertibleSheaf D).unitHomEquiv.symm (canonicalSections D)
  set adj := Scheme.Modules.pullbackPushforwardAdjunction i
  have hnat : adj.unit.app (M ⊗ modulesInvertibleSheaf D) ≫
      (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map e₁.hom) =
        e₁.hom ≫ adj.unit.app P := (adj.unit.naturality e₁.hom).symm
  let C : ShortComplex XA.Modules := ShortComplex.mk (f₀ ≫ e₁.hom) (adj.unit.app P) (by
    rw [Category.assoc, ← hnat, ← Category.assoc, h, zero_comp])
  have hC : C.ShortExact := by
    refine ShortComplex.shortExact_of_iso ?_ hse
    exact ShortComplex.isoMk (Iso.refl _) e₁
      ((Scheme.Modules.pushforward i).mapIso ((Scheme.Modules.pullback i).mapIso e₁))
      (by simp [C, f₀]) (by exact hnat.symm)
  have : C.X₂.IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule P
  have : ((Scheme.Modules.pullback i).obj P).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent D.subscheme.ringCatSheaf).prop_of_iso et.symm
      (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _)
  have : C.X₃.IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom i _ inferInstance
  have : Stacks.Ample.IsInvertibleModule XA C.X₁ := ‹_›
  refine (cechFitting_eq_fittingIdeal_quotient fX U hU hUaff gA fA hA C hC
    (surjective_cechD_of_isPullback fX U hU hUaff gA fA hA P h1) _
    (span_sectionCocycle_eq_top fX U hU hUaff gA fA hA P h1 h0 _ hnz)).trans ?_
  have : IsIso (et.hom.app ⊤) := Scheme.Modules.Hom.isIso_iff_isIso_app.mp et.isIso_hom ⊤
  let eG : Γ((Scheme.Modules.pullback i).obj P, ⊤) →+ Γ(D.subscheme, ⊤) := (et.hom.app ⊤).hom
  obtain ⟨Ψ, hΨ, hsmul, hval⟩ := exists_bijective_semilinear_sectionCocycle fA (sqCover U gA)
    (iSup_sqCover U hU gA) C.X₃ (divisorRingHom fA D) eG
    (ConcreteCategory.bijective_of_isIso (et.hom.app ⊤))
    (fun _ _ => Scheme.Modules.Hom.app_smul et.hom _ _)
  rw [fittingIdeal_quotient_span_singleton (divisorRingHom fA D) (bijective_divisorRingHom fA D hD)
    Ψ hΨ hsmul, hval]
  congr 1
  exact (congrArg (fun t => Ideal.span {eG t})
    (presheaf_map_pullbackGlobalSections i P _).symm).trans
      (zeroScheme_comap_ideal_eq_span gA N s i et).symm

end Twist


/-! ### The family `N(-Δ)` over the curve itself -/

section Global

open Stacks.TwoAffineCech Stacks.Divisors Stacks.FibreCohomology Stacks.PicardCurve

attribute [local instance] AlgebraicGeometry.schemeModulesMonoidal
  AlgebraicGeometry.schemeModulesSymmetric

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProper fX]
  (U : Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))

/-- The diagonal of `X ×_k X`, as the ideal of the graph of the identity. -/
abbrev diagIdeal : (pullback fX fX).IdealSheafData :=
  Stacks.Hilbert.pointIdeal (Over.mk fX) (Over.mk fX) (𝟙 _)

omit [IsProper fX] in
/-- Over a field, `1 ⊗ v ≠ 0` in `K ⊗_k V` for `v ≠ 0`. -/
theorem one_tmul_ne_zero_of_ne_zero (K : Type u) [Field K] [Algebra k K] {V : Type u}
    [AddCommGroup V] [Module k V] {v : V} (hv : v ≠ 0) : (1 : K) ⊗ₜ[k] v ≠ 0 := by
  have hinj : Function.Injective ((Algebra.linearMap k K).rTensor V) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap k K).injective
  intro h0
  apply hv
  have h1 : (Algebra.linearMap k K).rTensor V ((1 : k) ⊗ₜ[k] v) = 0 := by
    rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
    exact h0
  have h2 : (1 : k) ⊗ₜ[k] v = 0 := hinj (h1.trans (map_zero _).symm)
  have h3 := congrArg (TensorProduct.lid k V) h2
  rwa [TensorProduct.lid_tmul, one_smul, map_zero] at h3

omit [IsProper fX] in
include hU hUaff in
/-- **A nonzero section of `N` with `H¹(X, N) = 0` stays nonzero at every field point of a base
change `X_A`.** -/
theorem nonzeroAtFieldPoint_pullback [IsSeparated fX] {A : Type u} [CommRing A] [Algebra k A]
    {XA : Scheme.{u}} (gA : XA ⟶ X) (fA : XA ⟶ Spec (.of A))
    (hA : IsPullback gA fA fX (Spec.map (CommRingCat.ofHom (algebraMap k A))))
    (N : X.Modules) [N.IsQuasicoherent] (s : Γ(N, ⊤)) (hs : s ≠ 0)
    (hd : Function.Surjective (cechD fX U N)) (p : PrimeSpectrum A) :
    NonzeroAtFieldPoint fA ((Scheme.Modules.pullback gA).obj N) (pullbackGlobalSections gA N s)
      p := by
  set K := p.asIdeal.ResidueField
  let φ : A →+* K := algebraMap A K
  have hker : RingHom.ker φ = p.asIdeal := Ideal.ker_algebraMap_residueField p.asIdeal
  let sq := IsPullback.of_hasPullback fA (Spec.map (CommRingCat.ofHom φ))
  refine ⟨K, inferInstance, φ, hker, _, _, _, sq, ?_⟩
  set g' := pullback.fst fA (Spec.map (CommRingCat.ofHom φ))
  set f' := pullback.snd fA (Spec.map (CommRingCat.ofHom φ))
  let φ' : k →+* K := φ.comp (algebraMap k A)
  have hsq' : IsPullback (g' ≫ gA) f' fX (Spec.map (CommRingCat.ofHom φ')) := by
    have h := sq.paste_horiz hA
    rwa [← Spec.map_comp] at h
  let : Algebra k K := φ'.toAlgebra
  have hsc : sectionCocycle fX U N s ≠ 0 := by
    intro h0
    apply hs
    refine sectionCochain_injective U N hU ?_
    rw [sectionCochain_zero]
    exact congrArg (fun z : LinearMap.ker (cechD fX U N) => altCochain fX U N z.1) h0
  have hne := pullbackGlobalSections_ne_zero_of_tmul_ne_zero φ' fX f' (g' ≫ gA) hsq' U N hUaff hd s
    (one_tmul_ne_zero_of_ne_zero K hsc)
  intro h0
  apply hne
  rw [← pullbackGlobalSections_comp_hom g' gA N, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, h0, map_zero]

/-- The closed subscheme cut out by the graph of a relative point lies over the point: its
first projection is its second projection followed by the point. -/
theorem pointIdeal_subschemeι_fst {S : Scheme.{u}} (Y T : Over S) (y : T ⟶ Y)
    [IsClosedImmersion (Stacks.Hilbert.pointGraph Y T y)] :
    (Stacks.Hilbert.pointIdeal Y T y).subschemeι ≫ pullback.fst Y.hom T.hom =
      ((Stacks.Hilbert.pointIdeal Y T y).subschemeι ≫ pullback.snd Y.hom T.hom) ≫ y.left := by
  have hle : (Stacks.Hilbert.pointIdeal Y T y).subschemeι.ker ≤
      (Stacks.Hilbert.pointGraph Y T y).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Stacks.Hilbert.pointIdeal]
  set a := IsClosedImmersion.lift (Stacks.Hilbert.pointIdeal Y T y).subschemeι
    (Stacks.Hilbert.pointGraph Y T y) hle
  have hfac : a ≫ (Stacks.Hilbert.pointIdeal Y T y).subschemeι =
      Stacks.Hilbert.pointGraph Y T y := IsClosedImmersion.lift_fac _ _ hle
  have : IsIso a :=
    IsClosedImmersion.isIso_of_ker_eq (Stacks.Hilbert.pointGraph Y T y)
      (Stacks.Hilbert.pointIdeal Y T y).subschemeι a hfac
      ((Stacks.Hilbert.pointIdeal Y T y).ker_subschemeι).symm
  rw [← cancel_epi a, ← Category.assoc, hfac, ← Category.assoc, ← Category.assoc, hfac,
    Stacks.Hilbert.pointGraph_comp_fst, Stacks.Hilbert.pointGraph_comp_snd, Category.id_comp]

omit [IsProper fX] in
/-- The ring map of `Y ⟶ Spec Γ(X, V) ⟶ X` on `V` is `Γ(X, V) ≅ Γ(Spec Γ(X, V)) ⟶ Γ(Y)`. -/
theorem appLE_comp_fromSpec {Y : Scheme.{u}} [IsAffine Y] {V : X.Opens} (hV : IsAffineOpen V)
    (φ : Y ⟶ Spec Γ(X, V)) (e : (⊤ : Y.Opens) ≤ (φ ≫ hV.fromSpec) ⁻¹ᵁ V) :
    (φ ≫ hV.fromSpec).appLE V ⊤ e = (Scheme.ΓSpecIso Γ(X, V)).inv ≫ φ.appTop := by
  apply Spec.map_injective
  rw [← cancel_mono hV.fromSpec, IsAffineOpen.SpecMap_appLE_fromSpec _ hV (isAffineOpen_top Y),
    IsAffineOpen.fromSpec_top, Spec.map_comp, Category.assoc, ← Scheme.isoSpec_Spec_inv,
    ← Scheme.isoSpec_inv_naturality_assoc]

/-- The Picard class of the pullback of an invertible module is the pullback of its class. -/
theorem picardClass_pullback_module {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf L)
    (hL' : Stacks.SheafOfModules.IsInvertible Y'.presheaf Y'.ringCatIsSheaf
      ((Scheme.Modules.pullback g).obj L)) :
    Y'.picardClass ((Scheme.Modules.pullback g).obj L) hL' =
      Stacks.Picard.schemePullbackClass g (Y.picardClass L hL) := by
  obtain ⟨e⟩ := nonempty_rep_picardClass_iso L hL
  obtain ⟨e'⟩ := nonempty_rep_schemePullbackClass_iso g (Y.picardClass L hL)
  exact ((Y'.picardClass_eq_iff _ _ hL'
    (Stacks.Picard.picardRepresentative Y'.toRingedSpace _).property).2
    ⟨(Scheme.Modules.pullback g).mapIso e.symm ≪≫ e'.symm⟩).trans
      (Stacks.Picard.classOf_picardRepresentative _ _)

/-- An invertible module whose Picard class pulls back to zero along `g` has trivial pullback. -/
theorem nonempty_pullback_iso_unit_of_schemePullbackClass_eq_zero {Y Y' : Scheme.{u}}
    (g : Y' ⟶ Y) (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf L)
    (hcl : Stacks.Picard.schemePullbackClass g (Y.picardClass L hL) = 0) :
    Nonempty ((Scheme.Modules.pullback g).obj L ≅ SheafOfModules.unit Y'.ringCatSheaf) := by
  obtain ⟨e1⟩ := nonempty_rep_picardClass_iso L hL
  obtain ⟨e2⟩ := nonempty_rep_schemePullbackClass_iso g (Y.picardClass L hL)
  have h0 : Stacks.SheafOfModules.IsTrivial Y'.presheaf Y'.ringCatIsSheaf
      (rep (Stacks.Picard.schemePullbackClass g (Y.picardClass L hL))) :=
    (Y'.picardClass_eq_zero_iff _
      (Stacks.Picard.picardRepresentative Y'.toRingedSpace _).property).1
        ((Stacks.Picard.classOf_picardRepresentative _ _).trans hcl)
  obtain ⟨e3⟩ := h0
  exact ⟨(Scheme.Modules.pullback g).mapIso e1.symm ≪≫ e2.symm ≪≫ e3⟩

omit [IsProper fX] in
/-- On a chart `j : Spec A ⟶ X`, if `x + [Δ] = pr₁^* [N]` then the pullback of `x` twisted by the
pulled-back diagonal `D_A` is the pullback of `N`. -/
theorem nonempty_chartMap_pullback_tensor_iso [IsEffectiveCartierDivisor (diagIdeal fX)]
    (N : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (x : Stacks.Picard.ofScheme (pullback fX fX))
    (hx : x + Stacks.Divisors.picardClass (diagIdeal fX) =
      Stacks.Picard.schemePullbackClass (pullback.fst fX fX)
        (X.picardClass N ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N›))
    {A : CommRingCat.{u}} (j : Spec A ⟶ X) (DA : (pullback fX (j ≫ fX)).IdealSheafData)
    [IsEffectiveCartierDivisor DA] (hDA : (diagIdeal fX).comap (chartMap fX fX j) = DA) :
    Nonempty ((Scheme.Modules.pullback (chartMap fX fX j)).obj (rep x) ⊗
      modulesInvertibleSheaf DA ≅ (Scheme.Modules.pullback (pullback.fst fX (j ≫ fX))).obj N) := by
  have : Stacks.Ample.IsInvertibleModule X N :=
    ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N›
  have : IsPullbackDefined (chartMap fX fX j) (diagIdeal fX) := by
    unfold IsPullbackDefined
    rw [hDA]
    infer_instance
  have hMc : Stacks.SheafOfModules.IsInvertible (pullback fX (j ≫ fX)).presheaf
      (pullback fX (j ≫ fX)).ringCatIsSheaf
      ((Scheme.Modules.pullback (chartMap fX fX j)).obj (rep x)) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback _ (rep x)
  have hLD : Stacks.SheafOfModules.IsInvertible (pullback fX (j ≫ fX)).presheaf
      (pullback fX (j ≫ fX)).ringCatIsSheaf (modulesInvertibleSheaf DA) :=
    isInvertible_invertibleSheaf_picard DA
  have hP : Stacks.SheafOfModules.IsInvertible (pullback fX (j ≫ fX)).presheaf
      (pullback fX (j ≫ fX)).ringCatIsSheaf
      ((Scheme.Modules.pullback (pullback.fst fX (j ≫ fX))).obj N) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback _ N
  have hT := Stacks.SheafOfModules.isInvertible_tensorSheaf
    (pullback fX (j ≫ fX)).presheaf (pullback fX (j ≫ fX)).ringCatIsSheaf
    ((Scheme.Modules.pullback (chartMap fX fX j)).obj (rep x)) (modulesInvertibleSheaf DA)
  refine ((pullback fX (j ≫ fX)).picardClass_eq_iff _ _ hT hP).1 ?_
  rw [← AlgebraicGeometry.Scheme.picardClass_tensorSheaf _ _ _ hMc hLD hT,
    picardClass_pullback_module (chartMap fX fX j) (rep x)
      (Stacks.Picard.picardRepresentative _ _).property hMc,
    show (pullback fX fX).picardClass (rep x) (Stacks.Picard.picardRepresentative _ _).property =
        x from Stacks.Picard.classOf_picardRepresentative _ _,
    picardClass_pullback_module (pullback.fst fX (j ≫ fX)) N
      ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N› hP]
  show _ + Stacks.Divisors.picardClass DA = _
  rw [← picardClass_congr hDA, ← Stacks.Divisors.schemePullbackClass_picardClass,
    ← Stacks.Picard.schemePullbackClass_add, hx, Stacks.Picard.schemePullbackClass_comp]
  congr 1
  exact pullback.lift_fst _ _ _

/-- On an affine chart `V`, the ideal of `Z` pulled back to a closed subscheme `D` of `X_A`
mapping isomorphically to `Spec Γ(X, V)`, read back along `Γ(X, V) ≅ Γ(D)`, is the ideal of `Z`
on `V`. -/
theorem comap_divisorRingHom_ideal_comap {V : X.Opens} (hV : IsAffineOpen V) {XA : Scheme.{u}}
    (fA : XA ⟶ Spec Γ(X, V)) (D : XA.IdealSheafData) (hD : IsIso (D.subschemeι ≫ fA))
    (Z : X.IdealSheafData) :
    haveI : IsAffine D.subscheme := IsAffine.of_isIso (D.subschemeι ≫ fA)
    Ideal.comap (divisorRingHom fA D)
        ((Z.comap ((D.subschemeι ≫ fA) ≫ hV.fromSpec)).ideal ⟨⊤, isAffineOpen_top _⟩) =
      Z.ideal ⟨V, hV⟩ := by
  have : IsAffine D.subscheme := IsAffine.of_isIso (D.subschemeι ≫ fA)
  have e : (⊤ : D.subscheme.Opens) ≤ ((D.subschemeι ≫ fA) ≫ hV.fromSpec) ⁻¹ᵁ V := by
    rw [Scheme.Hom.comp_preimage, IsAffineOpen.fromSpec_preimage_self, Scheme.Hom.preimage_top]
  have hb := bijective_divisorRingHom fA D hD
  rw [ideal_comap_of_le Z ((D.subschemeι ≫ fA) ≫ hV.fromSpec) ⟨V, hV⟩ ⟨⊤, isAffineOpen_top _⟩ e,
    appLE_comp_fromSpec hV _ e]
  rw [divisorRingHom_eq] at hb ⊢
  exact Ideal.comap_map_of_bijective _ hb

include hU hUaff in
/-- `H¹(X, N) = 0` on the fibre, read on the two-term Čech complex of `U`. -/
theorem surjective_cechD_of_finrank_fibreCohomology (N : X.Modules)
    [Stacks.Ample.IsInvertibleModule X N]
    (hN1 : ∀ t : Spec (.of k), Module.finrank ((Spec (.of k)).residueField t)
      (fibreCohomology fX N t 1) = 0) :
    Function.Surjective (cechD fX U N) := by
  have hk : IsPullback (𝟙 X) fX fX (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
    rw [show CommRingCat.ofHom (algebraMap k k) = 𝟙 _ from rfl, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact surjective_cechD_of_isPullback fX U hU hUaff (𝟙 X) fX hk N hN1

/-- The chart case of `Stacks.FamilyFitting.familyFitting_diag_eq_zeroScheme`: on an affine open
`V` on which `N` is trivial. Let `N` be an invertible module on `X` with `H¹ = 0`
and `H⁰` spanned by `s`, and let `x` be a class on `X ×_k X` with `x + [Δ] = pr₁^* [N]`. Then the
Fitting ideal sheaf of `H¹` of the family `x` over the second factor is the ideal of the zero
scheme of `s`. -/
theorem chartFitting_diag_eq_zeroScheme [IsSeparated fX] [SmoothOfRelativeDimension 1 fX]
    [IsEffectiveCartierDivisor (diagIdeal fX)]
    (N : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (s : Γ(N, ⊤)) (hs : s ≠ 0)
    (hN1 : ∀ t : Spec (.of k), Module.finrank ((Spec (.of k)).residueField t)
      (fibreCohomology fX N t 1) = 0)
    (hN0 : ∀ t : Spec (.of k), Module.finrank ((Spec (.of k)).residueField t)
      (fibreCohomology fX N t 0) = 1)
    (x : Stacks.Picard.ofScheme (pullback fX fX))
    (hx : x + Stacks.Divisors.picardClass (diagIdeal fX) =
      Stacks.Picard.schemePullbackClass (pullback.fst fX fX)
        (X.picardClass N ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N›))
    (V : X.Opens) (hV : IsAffineOpen V)
    (hVn : Stacks.Picard.schemePullbackClass hV.fromSpec
      (X.picardClass N ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N›) = 0) :
    chartFitting fX U hU hUaff fX (rep x) hV.fromSpec =
      (AlgebraicGeometry.zeroScheme X N s).ideal ⟨V, hV⟩ := by
  rw [chartFitting]
  have hNinv : Stacks.Ample.IsInvertibleModule X N :=
    ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N›
  have : N.IsQuasicoherent := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule N
  set n := X.picardClass N ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N›
  set j := hV.fromSpec
  let := chartAlgebra fX j
  set gA := pullback.fst fX (j ≫ fX)
  set fA := pullback.snd fX (j ≫ fX)
  have hA := isPullback_chart fX fX j
  set T' : Over (Spec (.of k)) := Over.mk (j ≫ fX)
  set jo : T' ⟶ Over.mk fX := Over.homMk j
  have : IsSeparated (Over.mk fX).hom := ‹IsSeparated fX›
  have := Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated (Over.mk fX) T' jo
  have := Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated (Over.mk fX) (Over.mk fX)
    (𝟙 _)
  obtain ⟨DA, hDAdef⟩ : ∃ D : (pullback fX (j ≫ fX)).IdealSheafData,
      D = Stacks.Hilbert.pointIdeal (Over.mk fX) T' jo := ⟨_, rfl⟩
  have hDA : (diagIdeal fX).comap (chartMap fX fX j) = DA := by
    have h := Stacks.Hilbert.pointIdeal_comap_familyBaseChangeMap (Over.mk fX) jo (𝟙 _)
    rwa [Category.comp_id, ← hDAdef] at h
  have : IsEffectiveCartierDivisor DA := by
    rw [hDAdef]
    exact Stacks.Hilbert.HilbertFamily.isEffectiveCartierDivisor_ideal
      ⟨_, Stacks.Hilbert.isFiniteLocallyFreeOfRank_pointIdeal (Over.mk fX) T' jo⟩
  have hiso : IsIso (DA.subschemeι ≫ fA) := by
    rw [hDAdef]
    exact Stacks.Hilbert.isIso_subschemeι_pointIdeal_comp (Over.mk fX) T' jo
  have hgr : DA.subschemeι ≫ gA = (DA.subschemeι ≫ fA) ≫ j := by
    rw [hDAdef]
    exact pointIdeal_subschemeι_fst (Over.mk fX) T' jo
  obtain ⟨e₁⟩ := nonempty_chartMap_pullback_tensor_iso fX N x hx j DA hDA
  have hcl : Stacks.Picard.schemePullbackClass (DA.subschemeι ≫ gA) n = 0 := by
    rw [hgr, ← Stacks.Picard.schemePullbackClass_comp, hVn]
    exact map_zero (Stacks.Picard.schemePullbackClassHom _)
  obtain ⟨et⟩ := nonempty_pullback_iso_unit_of_schemePullbackClass_eq_zero (DA.subschemeι ≫ gA) N
    ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N› hcl
  rw [cechFitting_eq_comap_zeroScheme fX U hU hUaff gA fA hA N s DA _ hiso e₁
    (fun y => (finrank_fibreCohomology_eq_of_isPullback fX N gA fA _ hA _ (Iso.refl _) y 1).trans
      (hN1 _))
    (fun y => (finrank_fibreCohomology_eq_of_isPullback fX N gA fA _ hA _ (Iso.refl _) y 0).trans
      (hN0 _))
    (nonzeroAtFieldPoint_pullback fX U hU hUaff gA fA hA N s hs
      (surjective_cechD_of_finrank_fibreCohomology fX U hU hUaff N hN1))
    ((Scheme.Modules.pullbackComp DA.subschemeι gA).app N ≪≫ et), hgr]
  exact comap_divisorRingHom_ideal_comap hV fA DA hiso _


/-- **`Fit₀ R¹pr₂_*(N(-Δ)) = ℐ_{Z(s)}`.** Let `N` be an invertible module on `X` with `H¹ = 0`
and `H⁰` spanned by `s`, and let `x` be a class on `X ×_k X` with `x + [Δ] = pr₁^* [N]`. Then the
Fitting ideal sheaf of `H¹` of the family `x` over the second factor is the ideal of the zero
scheme of `s`. -/
theorem familyFitting_diag_eq_zeroScheme [IsSeparated fX] [SmoothOfRelativeDimension 1 fX]
    [IsEffectiveCartierDivisor (diagIdeal fX)]
    (N : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (s : Γ(N, ⊤)) (hs : s ≠ 0)
    (hN1 : ∀ t : Spec (.of k), Module.finrank ((Spec (.of k)).residueField t)
      (fibreCohomology fX N t 1) = 0)
    (hN0 : ∀ t : Spec (.of k), Module.finrank ((Spec (.of k)).residueField t)
      (fibreCohomology fX N t 0) = 1)
    (x : Stacks.Picard.ofScheme (pullback fX fX))
    (hx : x + Stacks.Divisors.picardClass (diagIdeal fX) =
      Stacks.Picard.schemePullbackClass (pullback.fst fX fX)
        (X.picardClass N ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N›)) :
    familyFitting fX U hU hUaff fX (rep x) = AlgebraicGeometry.zeroScheme X N s := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := {V : X.affineOpens // Stacks.Picard.schemePullbackClass V.2.fromSpec
      (X.picardClass N ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N›) = 0})
    (fun V => V.1) ?_ ?_
  · refine eq_top_iff.2 fun t _ => ?_
    obtain ⟨V, htV, hV⟩ := exists_affineOpen_schemePullbackClass_fromSpec_eq_zero
      (X.picardClass N ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N›) t
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV⟩, htV⟩
  intro V
  rw [familyFitting_ideal]
  exact chartFitting_diag_eq_zeroScheme fX U hU hUaff N s hs hN1 hN0 x hx V.1.1 V.1.2 V.2

end Global


end Stacks.FamilyFitting

end
