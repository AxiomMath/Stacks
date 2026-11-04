module

public import StacksFrontier.AlgebraicGeometry.AffineOpenSectionsBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FreeSectionsFiniteType
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.StructureSheafProjectiveSections
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedEtaleStalkDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackNecessity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.StalkFinitePresentation
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.KeyObservationFibre
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.LocalFlatTensorBaseCore

/-!
# The base clause of Stacks 05IH

Let `f : X ⟶ S` be locally of finite type, `F` a quasi-coherent `𝒪_X`-module of finite type flat
over `S` at `x`, and `G` a quasi-coherent `𝒪_S`-module. This file proves that if `x` is weakly
associated to `F ⊗_{𝒪_X} f^*G`, then `f x` is weakly associated to `G`: the base clause of the
forward implication of [Stacks, Tag 05IH], under the hypotheses of the tag.

## The argument

This is the base clause of the proof of [Stacks, Tag 05IG], run at the point `x`. Choose affine
opens `V ∋ f x` and `W ∋ x` with `f(W) ⊆ V`, and write `R₀ = Γ(S, V)`, `A = Γ(X, W)`,
`P = Γ(F, W)`, `p` and `q` for the primes of `f x` and `x`. Shrinking `W` to a basic open `D(g)`
around `x` (the key observation, [Stacks, Tag 05IF]), every element of `A` outside `q` acts
injectively on the fibre `P ⊗_{R₀} κ(p)` up to inverting `g` and elements outside `p`. By
[Stacks, Tag 05KZ] there are an elementary étale neighbourhood `(U, u)` of `(S, f x)` and an affine
`X'` étale over `D(g) ×_S Spec 𝒪_{U, u}`, with a point over `x`, on which the sections of the
pullback of `F` are free over `R' = 𝒪_{U, u}`. The coordinate argument
`Stacks.WeaklyAssociatedPrimes.exists_ne_zero_pow_smul_eq_zero_of_isBaseChange_free` turns a
witness of `𝔪_x ∈ WeakAss(F_x ⊗ G_{f x})` into a nonzero element of `R' ⊗ G_{f x}` killed by
powers of the elements of `p`, and the étale descent
`AlgebraicGeometry.isWeaklyAssociatedPoint_of_ne_zero_of_etaleNeighborhood_affineOpen`
([Stacks, Tag 05FP]) concludes.

## Main results

* `Stacks.Divisors.isWeaklyAssociatedPoint_of_isWeaklyAssociatedPoint_tensorPullback_of_finiteType`

## References

* [Stacks Project, Tag 05IH](https://stacks.math.columbia.edu/tag/05IH)
* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
* [Stacks Project, Tag 05KZ](https://stacks.math.columbia.edu/tag/05KZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct Opposite IsLocalRing
open Stacks.WeaklyAssociatedPrimes

universe u

namespace Stacks.Divisors

/-- For `e : U ⟶ S` and `qX : X' ⟶ Spec 𝒪_{U, u'}`, the map from sections of `S` over `V` to the
global functions of `X'` along `qX ≫ U.fromSpecStalk u' ≫ e` is the germ at `e u'`, followed by
the stalk map of `e` and the map on global functions of `qX`. -/
theorem appLE_comp_fromSpecStalk_comp {U S X' : Scheme.{u}} (e : U ⟶ S) (u' : U)
    (qX : X' ⟶ Spec (U.presheaf.stalk u')) (V : S.Opens) (hu : e u' ∈ V)
    (hle : (⊤ : X'.Opens) ≤ (qX ≫ U.fromSpecStalk u' ≫ e) ⁻¹ᵁ V) :
    (qX ≫ U.fromSpecStalk u' ≫ e).appLE V ⊤ hle =
      S.presheaf.germ V (e u') hu ≫ e.stalkMap u' ≫ (Scheme.ΓSpecIso _).inv ≫ qX.appTop := by
  have hu' : u' ∈ e ⁻¹ᵁ V := hu
  have h1 : (qX ≫ U.fromSpecStalk u' ≫ e).appLE V ⊤ hle =
      e.app V ≫ (U.fromSpecStalk u').app (e ⁻¹ᵁ V) ≫ qX.appLE _ ⊤ hle := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE_assoc]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h2 : ∀ (W : (Spec (U.presheaf.stalk u')).Opens) (hW : (⊤ : X'.Opens) ≤ qX ⁻¹ᵁ W),
      (Spec (U.presheaf.stalk u')).presheaf.map (homOfLE le_top).op ≫ qX.appLE W ⊤ hW =
        qX.appTop := by
    intro W hW
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
  have h3 := h2 (U.fromSpecStalk u' ⁻¹ᵁ e ⁻¹ᵁ V) hle
  rw [h1, Scheme.fromSpecStalk_app hu', Scheme.Hom.germ_stalkMap_assoc]
  simp only [Category.assoc, h3]

/-- Let `f : X ⟶ S` be locally of finite type, let `F` be a quasi-coherent `𝒪_X`-module of finite
type which is flat over `S` at `x`, and let `G` be a quasi-coherent `𝒪_S`-module. If `x` is weakly
associated to `F ⊗_{𝒪_X} f^*G`, then `f x` is weakly associated to `G`: the base clause of the
forward implication of Stacks Tag 05IH. -/
theorem isWeaklyAssociatedPoint_of_isWeaklyAssociatedPoint_tensorPullback_of_finiteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) (G : S.Modules) [F.IsQuasicoherent] [F.IsFiniteType] [G.IsQuasicoherent]
    (x : X) (hF : IsFlatOverAt f.toLRSHom.toShHom F x)
    (hx : IsWeaklyAssociatedPoint
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toLocallyRingedSpace.toRingedSpace)).presheaf,
                ((X.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj
        (((Scheme.Modules.pullback f).obj G)))) x) :
    IsWeaklyAssociatedPoint G (f x) := by
  classical
  -- the stalks
  let R := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let φ : R →+* B := (f.stalkMap x).hom
  let : Algebra R B := φ.toAlgebra
  let : IsLocalHom φ := f.toLRSHom.prop x
  let N := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
  let M := TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f x)
  let : Module R N := Module.compHom N φ
  have : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat R N := hF
  have hT : IsWeaklyAssociatedPrime B (N ⊗[R] M) (maximalIdeal B) := by
    let P := (Scheme.Modules.pullback f).obj G
    let tens := (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toLocallyRingedSpace.toRingedSpace)).presheaf,
              ((X.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj (P))
    obtain ⟨eTensor⟩ := exists_tensorStalkLinearEquiv F P x
    let ePull : TopCat.Presheaf.stalk (C := Ab.{u}) P.val.presheaf x ≃ₗ[B]
        TensorProduct R B M := Classical.choose
      (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
        f.toLRSHom.toShHom G x)
    let : Module B (TopCat.Presheaf.stalk (C := Ab.{u}) tens.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) tens.val x
    exact (LinearEquiv.isWeaklyAssociatedPrime_iff (eTensor.trans ((ePull.lTensor N).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R B B N M))) _).mp hx
  -- a witness `z` whose annihilator in `B` has radical `𝔪_B`
  change WeaklyAssociated (maximalIdeal B) (N ⊗[R] M) at hT
  obtain ⟨z, hz⟩ := weaklyAssociated_maximalIdeal_iff_exists_radical_eq.mp hT
  -- affine opens around `f x` and `x`
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨W₁, hW₁, rfl⟩, hxW₁, hW₁V⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ V from hsV) (f ⁻¹ᵁ V).2
  have hW₁V' : W₁ ≤ f ⁻¹ᵁ V := hW₁V
  let R₀ := Γ(S, V)
  let A := Γ(X, W₁)
  let : Algebra R₀ A := (f.appLE V W₁ hW₁V').hom.toAlgebra
  have : Algebra.FiniteType R₀ A :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f inferInstance ⟨V, hV⟩ ⟨W₁, hW₁⟩ hW₁V'
  let P₁ := Γ(F, W₁)
  let : Module R₀ P₁ := Module.compHom P₁ (algebraMap R₀ A)
  have : IsScalarTower R₀ A P₁ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite A P₁ := Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F hW₁
  set p : Ideal R₀ := (hV.primeIdealOf ⟨f x, hsV⟩).asIdeal with hp
  set q : Ideal A := (hW₁.primeIdealOf ⟨x, hxW₁⟩).asIdeal with hq
  have hqp : q.comap (algebraMap R₀ A) = p :=
    congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE V hV W₁ hW₁ hW₁V' hxW₁)
  have : q.LiesOver p := ⟨hqp.symm⟩
  -- the stalks as localizations of sections
  let : Algebra R₀ R := (S.presheaf.germ V (f x) hsV).hom.toAlgebra
  have hlocR : IsLocalization.AtPrime R p := hV.isLocalization_stalk ⟨f x, hsV⟩
  let : Algebra A B := (X.presheaf.germ W₁ x hxW₁).hom.toAlgebra
  have hlocB : IsLocalization.AtPrime B q := hW₁.isLocalization_stalk ⟨x, hxW₁⟩
  have hgerm : ∀ r : R₀, φ (algebraMap R₀ R r) = algebraMap A B (algebraMap R₀ A r) := fun r =>
    Scheme.Hom.germ_stalkMap_apply f V x hsV r |>.trans
      (X.presheaf.germ_res_apply (homOfLE hW₁V') x hxW₁ _).symm
  let : Module A N := affineStalkModule F W₁ x hxW₁
  have : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module R₀ N := Module.compHom N (algebraMap R₀ A)
  have : IsScalarTower R₀ A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R₀ R N := IsScalarTower.of_algebraMap_smul fun r n => by
    change φ (algebraMap R₀ R r) • n = algebraMap A B (algebraMap R₀ A r) • n
    rw [hgerm]
  have : SMulCommClass R A N := ⟨fun r a n => by
    change φ r • algebraMap A B a • n = algebraMap A B a • φ r • n
    rw [smul_smul, smul_smul, mul_comm]⟩
  let : Module R₀ M := Module.compHom M (algebraMap R₀ R)
  have : IsScalarTower R₀ R M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : TensorProduct.CompatibleSMul R₀ R N M :=
    IsLocalization.tensorProduct_compatibleSMul p.primeCompl R N M
  let e₁ : N ⊗[R] M ≃ₗ[A] N ⊗[R₀] M := TensorProduct.equivOfCompatibleSMul R₀ R A N M
  let g₀ : P₁ →ₗ[A] N := affineGerm F W₁ x hxW₁
  have : IsLocalizedModule q.primeCompl g₀ := affineGerm_isLocalized F W₁ hW₁ x hxW₁
  let gT : P₁ ⊗[R₀] M →ₗ[A] N ⊗[R₀] M := TensorProduct.AlgebraTensorModule.rTensor R₀ M g₀
  have : IsLocalizedModule q.primeCompl gT := inferInstance
  obtain ⟨⟨w, t⟩, hwt⟩ := IsLocalizedModule.mk'_surjective q.primeCompl gT (e₁ z)
  simp only [Function.uncurry_apply_pair] at hwt
  -- the action of `A` on `N ⊗_R M` is that of `B` through the germ
  have hAB : ∀ (a : A) (y : N ⊗[R] M), a • y = algebraMap A B a • y := fun a y =>
    (algebraMap_smul B a y).symm
  have hAnn : ∀ b : B, b • z = 0 → b ∈ maximalIdeal B := by
    intro b hb
    rw [← hz]
    exact Ideal.le_radical ((mem_annihilatorOfElem_semiring_iff z b).mpr hb)
  have hwq : ∀ a : A, a • w = 0 → a ∈ q := by
    intro a ha
    have h1 : a • e₁ z = 0 := by
      rw [← hwt, ← IsLocalizedModule.mk'_smul, ha, IsLocalizedModule.mk'_zero]
    have h2 : a • z = 0 := by
      apply e₁.injective
      rw [map_smul, h1, map_zero]
    rw [hAB] at h2
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff B q a).mp (hAnn _ h2)
  have hwf : ∀ r ∈ p, ∃ k : ℕ, ∃ t' : A, t' ∉ q ∧ t' • (r ^ k • w) = 0 := by
    intro r hr
    have hrm : algebraMap A B (algebraMap R₀ A r) ∈ maximalIdeal B := by
      rw [← hgerm]
      exact map_nonunit φ _ ((IsLocalization.AtPrime.to_map_mem_maximal_iff R p r).mpr hr)
    rw [← hz] at hrm
    obtain ⟨k, hk⟩ := hrm
    rw [mem_annihilatorOfElem_semiring_iff, ← map_pow, ← hAB, ← map_pow] at hk
    have h1 : r ^ k • e₁ z = 0 := by
      rw [← algebraMap_smul A (r ^ k), ← map_smul, hk, map_zero]
    rw [← hwt, ← IsLocalizedModule.mk'_smul, IsLocalizedModule.mk'_eq_zero'] at h1
    obtain ⟨t', ht'⟩ := h1
    exact ⟨k, t', t'.2, ht'⟩
  -- the key observation, and the basic open `W = D(g)` around `x`
  obtain ⟨g, hgq, hKO⟩ := exists_mul_pow_smul_mem_smul_top_of_smul_mem_smul_top (P := P₁) p q
  let W : X.Opens := X.basicOpen g
  have hxW : x ∈ W := by
    refine (X.mem_basicOpen g x hxW₁).mpr ?_
    exact (IsLocalization.AtPrime.isUnit_to_map_iff B q g).mpr hgq
  have hWW₁ : W ≤ W₁ := X.basicOpen_le g
  -- Stacks 05KZ on `W ⟶ S`
  let FW := (Scheme.Modules.pullback W.ι).obj F
  have : FW.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion W.ι F
  have : FW.IsFiniteType := AlgebraicGeometry.SheafOfModules.pullback_isFiniteType
    W.ι.toLRSHom.toShHom F
  let xW : W.toScheme := ⟨x, hxW⟩
  have hflatW : IsFlatOverAt (W.ι ≫ f).toLRSHom.toShHom FW xW :=
    (isFlatOverAt_pullback_iff_of_isFlatAt W.ι f F xW (Flat.stalkMap W.ι xW)).mp hF
  obtain ⟨U, hUel, X', x', gX, qX, hgx, hqx, hcomm, het, -, hX'aff, hfree⟩ :=
    exists_etale_neighborhood_with_free_globalSections_of_locallyOfFiniteType (W.ι ≫ f) FW xW
      hflatW
  -- the ring `C = Γ(X', 𝒪)` and its scalars
  let R' := U.scheme.presheaf.stalk U.point
  have hpt : U.toBase U.point = f x := U.map_point
  have hptV : U.toBase U.point ∈ V := by rw [hpt]; exact hsV
  let hX : X' ⟶ X := gX ≫ W.ι
  have hle : (⊤ : X'.Opens) ≤ hX ⁻¹ᵁ W₁ := fun y _ => hWW₁ (gX y).2
  let C := Γ(X', ⊤)
  let : Algebra A C := (hX.appLE W₁ ⊤ hle).hom.toAlgebra
  let : Algebra R' C := ((Scheme.ΓSpecIso (.of R')).inv ≫ qX.appTop).hom.toAlgebra
  let : Algebra R₀ R' :=
    (S.presheaf.germ V (U.toBase U.point) hptV ≫ U.toBase.stalkMap U.point).hom.toAlgebra
  let : Algebra R₀ C := ((algebraMap A C).comp (algebraMap R₀ A)).toAlgebra
  have : IsScalarTower R₀ A C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcompat : ∀ r : R₀, algebraMap R' C (algebraMap R₀ R' r) =
      algebraMap A C (algebraMap R₀ A r) := by
    intro r
    have hmor : hX ≫ f = qX ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase := by
      rw [Category.assoc, hcomm]
    have hleV : (⊤ : X'.Opens) ≤ (hX ≫ f) ⁻¹ᵁ V := fun y _ => hW₁V' (hle trivial)
    have hleV' : (⊤ : X'.Opens) ≤ (qX ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase) ⁻¹ᵁ V := by
      rw [← hmor]; exact hleV
    have hcongr : ∀ (φ ψ : X' ⟶ S) (_ : φ = ψ) (e₁ : (⊤ : X'.Opens) ≤ φ ⁻¹ᵁ V)
        (e₂ : (⊤ : X'.Opens) ≤ ψ ⁻¹ᵁ V), φ.appLE V ⊤ e₁ = ψ.appLE V ⊤ e₂ := by
      rintro φ ψ rfl e₁ e₂; rfl
    have hA : algebraMap A C (algebraMap R₀ A r) = (hX ≫ f).appLE V ⊤ hleV r := by
      change (f.appLE V W₁ hW₁V' ≫ hX.appLE W₁ ⊤ hle).hom r = _
      rw [Scheme.Hom.appLE_comp_appLE]
    have hR' : algebraMap R' C (algebraMap R₀ R' r) =
        (qX ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase).appLE V ⊤ hleV' r := by
      rw [appLE_comp_fromSpecStalk_comp U.toBase U.point qX V hptV hleV']
      rfl
    rw [hA, hR', hcongr _ _ hmor hleV hleV']
  have : IsScalarTower R₀ R' C := IsScalarTower.of_algebraMap_eq fun r => (hcompat r).symm
  -- the sections `P'` of the pullback of `F` to `X'`
  let P' := Γ((Scheme.Modules.pullback hX).obj F, ⊤)
  let : Module A P' := Module.compHom P' (algebraMap A C)
  have : IsScalarTower A C P' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module R' P' := Module.compHom P' (algebraMap R' C)
  have : IsScalarTower R' C P' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module R₀ P' := Module.compHom P' (algebraMap R₀ C)
  have : IsScalarTower R₀ C P' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R₀ A P' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R₀ R' P' := IsScalarTower.of_algebraMap_smul fun r m => by
    change algebraMap R' C (algebraMap R₀ R' r) • m = algebraMap R₀ C r • m
    rw [hcompat]; rfl
  -- `P'` is the base change of `P₁` along `A → C`
  let ι : P₁ →ₗ[A] P' :=
    { toFun := Scheme.Modules.pullbackSection hX F W₁ ⊤ hle
      map_add' := fun a b => map_add
        (Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackSectionsHom hX F W₁ ⊤ hle) a b
      map_smul' := fun r a => by
        change Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackSectionsHom hX F W₁ ⊤ hle
            (r • a) = (hX.appLE W₁ ⊤ hle).hom r •
          Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackSectionsHom hX F W₁ ⊤ hle a
        simp only [Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackSectionsHom,
          AddMonoidHom.coe_comp, Function.comp_apply]
        rw [Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections_smul]
        exact Scheme.Modules.map_smul ((Scheme.Modules.pullback hX).obj F) (homOfLE hle) _ _ }
  have hι : IsBaseChange C ι :=
    AlgebraicGeometry.ModuleCat.isBaseChange_of_extendScalarsIso (hX.appLE W₁ ⊤ hle).hom rfl
      (affinePullbackSectionsBaseChangeIso hX F hW₁ (isAffineOpen_top X') hle) ι
      (fun m => affinePullbackSectionsBaseChangeIso_one_tmul hX F hW₁ (isAffineOpen_top X') hle m)
  -- `P'` is free over `R'`, by Stacks 05KZ
  have : Module.Free R' P' := by
    let P'' := Γ((Scheme.Modules.pullback gX).obj FW, ⊤)
    let : Module R' P'' := Module.compHom P'' (algebraMap R' C)
    have : IsScalarTower R' C P'' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have : Module.Free R' P'' := hfree
    let E : P'' ≃ₗ[C] P' :=
      Scheme.Modules.sectionsTopLinearEquivOfIso ((Scheme.Modules.pullbackComp gX W.ι).app F)
    exact Module.Free.of_equiv (E.restrictScalars R')
  -- `C` is flat over `A`
  have : Module.Flat A C := by
    have : Flat (pullback.fst (W.ι ≫ f) (U.scheme.fromSpecStalk U.point ≫ U.toBase)) := by
      have := Stacks.Flatness.flat_fromSpecStalk_comp_toBase U
      infer_instance
    have : Flat gX := by
      rw [← pullback.lift_fst gX qX hcomm]
      infer_instance
    have hflat : Flat hX := inferInstance
    exact HasRingHomProperty.appLE (P := @Flat) hX hflat ⟨W₁, hW₁⟩ ⟨⊤, isAffineOpen_top X'⟩ hle
  -- the prime of `x'`
  set q' : Ideal C := ((isAffineOpen_top X').primeIdealOf ⟨x', trivial⟩).asIdeal with hq'def
  have hxx' : hX x' = x := by
    change W.ι (gX x') = x
    rw [hgx]; rfl
  have hq'q : q'.comap (algebraMap A C) = q := by
    have h := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE W₁ hW₁ ⊤ (isAffineOpen_top X') hle (x := x') trivial)
    refine h.trans ?_
    congr 3
  have hq' : q.map (algebraMap A C) ≤ q' := Ideal.map_le_iff_le_comap.mpr hq'q.ge
  have hq'top : q' ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  -- the maximal ideal of `R'` is generated by `p`
  have hptp : (hV.primeIdealOf ⟨U.toBase U.point, hptV⟩).asIdeal = p := by
    rw [hp]; congr 3
  let : Algebra R₀ (S.presheaf.stalk (U.toBase U.point)) :=
    (S.presheaf.germ V (U.toBase U.point) hptV).hom.toAlgebra
  have hlocu := hV.isLocalization_stalk ⟨U.toBase U.point, hptV⟩
  have hmax : p.map (algebraMap R₀ R') = maximalIdeal R' := by
    have h1 : (maximalIdeal (S.presheaf.stalk (U.toBase U.point))).map
        (U.toBase.stalkMap U.point).hom = maximalIdeal R' := by
      refine map_maximalIdeal_eq_of_etale_fibers U.toBase (fun s => ?_) U.point
      change Etale (Limits.pullback.snd U.toBase (S.fromSpecResidueField s))
      infer_instance
    rw [← h1, ← hptp, ← IsLocalization.AtPrime.map_eq_maximalIdeal
      (hV.primeIdealOf ⟨U.toBase U.point, hptV⟩).asIdeal (S.presheaf.stalk (U.toBase U.point)),
      Ideal.map_map]
    rfl
  -- the key observation, read in `C`
  have hgunit : IsUnit (algebraMap A C g) := by
    refine X'.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun y _ => ?_
    have hyW : hX y ∈ W := (gX y).2
    have h1 : X'.presheaf.germ ⊤ y trivial (algebraMap A C g) =
        hX.stalkMap y (X.presheaf.germ W₁ (hX y) (hWW₁ hyW) g) := by
      rw [Scheme.Hom.germ_stalkMap_apply]
      change X'.presheaf.germ ⊤ y trivial (X'.presheaf.map (homOfLE hle).op (hX.app W₁ g)) = _
      exact X'.presheaf.germ_res_apply (homOfLE hle) y trivial _
    rw [h1]
    exact ((X.mem_basicOpen g (hX y) (hWW₁ hyW)).mp hyW).map _
  have hrunit : ∀ r : R₀, r ∉ p → IsUnit (algebraMap A C (algebraMap R₀ A r)) := by
    intro r hr
    rw [← hcompat]
    refine IsUnit.map _ ?_
    rw [← hptp] at hr
    exact ((IsLocalization.AtPrime.isUnit_to_map_iff (S.presheaf.stalk (U.toBase U.point)) _
      r).mpr hr).map (U.toBase.stalkMap U.point).hom
  have hKO' : ∀ t : A, t ∉ q → ∀ v : P₁, t • v ∈ p • (⊤ : Submodule R₀ P₁) →
      ∃ s : A, IsUnit (algebraMap A C s) ∧ s • v ∈ p • (⊤ : Submodule R₀ P₁) := by
    intro t ht v hv
    obtain ⟨n, r, hr, hrv⟩ := hKO t ht v hv
    exact ⟨_, by rw [map_mul, map_pow]; exact (hrunit r hr).mul (hgunit.pow n), hrv⟩
  -- the coordinate argument, and étale descent
  obtain ⟨y, hy, hyf⟩ := exists_ne_zero_pow_smul_eq_zero_of_isBaseChange_free p q hmax q' hq'
    hq'top ι hι hKO' w hwq hwf
  exact AlgebraicGeometry.isWeaklyAssociatedPoint_of_ne_zero_of_etaleNeighborhood_affineOpen
    U G hpt hV hsV (fun _ => rfl) (fun _ _ => rfl) y hy hyf

end Stacks.Divisors

end

