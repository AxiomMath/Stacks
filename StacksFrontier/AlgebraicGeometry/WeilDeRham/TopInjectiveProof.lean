module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.StarIdentityProof

/-!
# Top-degree injectivity in cup form from the injectivity of the external cup product

Let `f : X ⟶ Spec A` be proper and smooth of relative dimension `n = e + 1` with a section `σ`,
`W = X ×_A X` with projections `p₁`, `p₂`, and `ξ ∈ Hⁿ(X, Ωⁿ_{X/A})` the Gysin class of the
section. Top-degree injectivity in cup form (`Stacks.WeilDeRham.CupTopInjective`) says that
`x ↦ p₂^*x ∪ p₁^*ξ` is injective on `Hⁿ(X, Ωⁿ_{X/A})`, the cup product being taken along the
wedge product `Ωⁿ_{W/A} ⊗ Ωⁿ_{W/A} ⟶ Ω^{2n}_{W/A}`.

The wedge product `p₂^*Ωⁿ ⊗ p₁^*Ωⁿ ⟶ Ω^{2n}_{W/A}` of the pulled-back forms is split injective:
by graded commutativity it is `(-1)^{n·n}` times the transposition followed by the Künneth
inclusion of the `(n, n)` summand of [Stacks, Tag 0FMA]
(`Stacks.WeilDeRham.sndForms_fstForms_mul_kunnethProj_eq`), so the Künneth projection followed by
the signed transposition retracts it. By naturality of the cup product, `p₂^*x ∪ p₁^*ξ = 0` then
forces the external cup product `p₂^♮x ∪ p₁^♮ξ ∈ H^{2n}(W, p₂^*Ωⁿ ⊗ p₁^*Ωⁿ)` to vanish, and the
injectivity of the latter gives `x = 0`.

## Main results

* `Stacks.WeilDeRham.sndForms_fstForms_mul_kunnethProj_eq`: the `(n, e)`-component of
  `p₂^*ω ∧ p₁^*ϑ` is `(-1)^{en} ϑ ⊗ ω`.
* `Stacks.WeilDeRham.cupTopInjective_of_pullbackCup`: **top-degree injectivity in cup form** from
  the injectivity of the external cup product with `p₁^♮ξ`.

## References

* [Stacks Project, Tag 0G8J](https://stacks.math.columbia.edu/tag/0G8J)
* [Stacks Project, Tag 0FMA](https://stacks.math.columbia.edu/tag/0FMA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction Stacks.Gysin Stacks.DeRham.GysinCohomologyBaseChange
open AlgebraicGeometry.Scheme.Hom Stacks.DeRham.CohomologicalGysin
open Stacks.DeRham.GysinCupHodge
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open AlgebraicGeometry.SheafOfModules (moduleDerived canonicalPairingModule tensorBifunctorNat
  baseRingedSpace multiplicationInt)
open scoped Stacks.StandardDerivedModel

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.WeilDeRham

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

/-- `(-1)^k • (-1)^k • t = t`. -/
theorem neg_one_pow_zsmul_zsmul {M : Type*} [AddCommGroup M] (k : ℕ) (t : M) :
    ((-1 : ℤ) ^ k) • ((-1 : ℤ) ^ k) • t = t := by
  rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/-! ### The cup product with a split injective multiplication -/

section SplitCup

variable {W : Scheme.{u}}

/-- The category of sheaves of modules on a scheme, in the spelling over the ring sheaf of the
tensor product of sheaves, in which the cup product of Section 0FKU is stated. -/
local notation "𝓜" W => _root_.SheafOfModules
  (Stacks.SheafOfModules.Tensor.ringSheaf (Scheme.sheaf W))

/-- **The cup product along a multiplication with a retraction detects the external cup
product**: if `(F ◁ α) ≫ (β ▷ G) ≫ μ` has a retraction, then `β(u) ∪ α(v) = 0` along `μ` forces
`u ∪ v = 0` along the identity. -/
theorem sheafCup_eq_zero_of_retraction {P Q Ωa Ωb Ω T : 𝓜 W} (β : P ⟶ Ωa) (α : Q ⟶ Ωb)
    (μ : ((sheafTensor W.sheaf).obj Ωa).obj Ωb ⟶ Ω) (π : Ω ⟶ T)
    (τ : T ⟶ ((sheafTensor W.sheaf).obj P).obj Q)
    (hρ : (((sheafTensor W.sheaf).obj P).map α ≫ ((sheafTensor W.sheaf).map β).app Ωb ≫ μ ≫ π) ≫
      τ = 𝟙 _) (q r : ℕ) (u : Hgroup (structureSheafRing W.toRingedSpace) ⊤ q P)
    (v : Hgroup (structureSheafRing W.toRingedSpace) ⊤ r Q)
    (h : sheafCup μ q r ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ q).map β u)
      ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ r).map α v) = 0) :
    sheafCup (𝟙 _) q r u v = 0 := by
  rw [sheafCup_map_left, sheafCup_map_right] at h
  have e : (((sheafTensor W.sheaf).obj P).map α ≫ ((sheafTensor W.sheaf).map β).app Ωb ≫ μ ≫ π) ≫
      τ = (((sheafTensor W.sheaf).obj P).map α ≫ ((sheafTensor W.sheaf).map β).app Ωb ≫ μ) ≫
        (π ≫ τ) := by
    simp only [Category.assoc]
  rw [← hρ, e, sheafCup_comp, h, map_zero]

end SplitCup

/-! ### The wedge product of forms pulled back along the two projections -/

section TopWedge

attribute [local instance] hasColimits_sheafOfModules_toRingCat
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The `(n, e)`-component of the product of forms pulled back along the second and the first
projection**: `pr_{(n,e)}(pr₂^*ω ∧ pr₁^*ϑ) = (-1)^{en} ϑ ⊗ ω`, by graded commutativity. -/
theorem sndForms_fstForms_mul_kunnethProj_eq (e n : ℕ) :
    ((sheafTensor (pullback f f).sheaf).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj
        (relativeDifferentialForms f (e : ℤ)))).map (fstForms f (n : ℤ)) ≫
      ((sheafTensor (pullback f f).sheaf).map (sndForms f (e : ℤ))).app
        (relativeDifferentialForms (pullback.fst f f ≫ f) (n : ℤ)) ≫
      _root_.SheafOfModules.GradedAlgebra.mulSheaf
        (relativeDifferentialFormsAlgebra (pullback.fst f f ≫ f)) (e : ℤ) (n : ℤ) ≫
      kunnethProj f (e + n) (deRhamBoxIndexMk n e (e + n) (Nat.add_comm n e)) =
    signedTranspose f e n := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := (pullback f f).sheaf) fun U x y => ?_
  have l1 := sheafTensor_obj_map_val_app_unit (pullback f f).sheaf
    ((Scheme.Modules.pullback (pullback.snd f f)).obj (relativeDifferentialForms f (e : ℤ)))
    (fstForms f (n : ℤ)) U x y
  have l2 := sheafTensor_map_app_val_app_unit (pullback f f).sheaf (sndForms f (e : ℤ))
    (relativeDifferentialForms (pullback.fst f f ≫ f) (n : ℤ)) U x
    ((fstForms f (n : ℤ)).val.app U y)
  have l3 := _root_.SheafOfModules.GradedAlgebra.mulSheaf_unit
    (relativeDifferentialFormsAlgebra (pullback.fst f f ≫ f)) (e : ℤ) (n : ℤ) U
    ((sndForms f (e : ℤ)).val.app U x) ((fstForms f (n : ℤ)).val.app U y)
  have hcomm := AlgebraicGeometry.SheafOfModules.formProduct_comm
    (deRhamAlgebras (pullback.fst f f ≫ f)) e n U ((sndForms f (e : ℤ)).val.app U x)
    ((fstForms f (n : ℤ)).val.app U y)
  have hre : AlgebraicGeometry.SheafOfModules.reindexForm (deRhamAlgebras (pullback.fst f f ≫ f))
      (Nat.add_comm n e) U (AlgebraicGeometry.SheafOfModules.formProduct
        (deRhamAlgebras (pullback.fst f f ≫ f)) n e U ((fstForms f (n : ℤ)).val.app U y)
        ((sndForms f (e : ℤ)).val.app U x)) =
      (kunnethIncl f (e + n) (deRhamBoxIndexMk n e (e + n) (Nat.add_comm n e))).val.app U
        (kunnethTmul f n e U y x) := by
    refine eq_of_heq ((AlgebraicGeometry.SheafOfModules.reindexForm_heq _ _ U _).trans ?_)
    rw [kunnethIncl_apply f (e + n) (deRhamBoxIndexMk n e (e + n) (Nat.add_comm n e)) U y x]
    exact (eqToHom_val_app_heq_nat
      (fun j : ℕ => (deRhamAlgebras (pullback.fst f f ≫ f)).exteriorPower j)
      (Nat.add_comm n e) U _).symm
  have l5 := Stacks.SheafOfModules.Tensor.sheafTensorBraiding_hom_app_sheafifyUnit_tmul
    (pullback f f).sheaf _ _ U x y
  refine (congrArg (fun t => (kunnethProj f (e + n) _).val.app U
    ((_root_.SheafOfModules.GradedAlgebra.mulSheaf
      (relativeDifferentialFormsAlgebra (pullback.fst f f ≫ f)) (e : ℤ) (n : ℤ)).val.app U
      ((((sheafTensor (pullback f f).sheaf).map (sndForms f (e : ℤ))).app
        (relativeDifferentialForms (pullback.fst f f ≫ f) (n : ℤ))).val.app U t))) l1).trans ?_
  refine (congrArg (fun t => (kunnethProj f (e + n) _).val.app U
    ((_root_.SheafOfModules.GradedAlgebra.mulSheaf
      (relativeDifferentialFormsAlgebra (pullback.fst f f ≫ f)) (e : ℤ) (n : ℤ)).val.app U t))
    l2).trans ?_
  refine (congrArg (fun t => (kunnethProj f (e + n) _).val.app U t) (l3.trans hcomm)).trans ?_
  refine (map_zsmul ((kunnethProj f (e + n) _).val.app U).hom _ _).trans ?_
  refine (congrArg (((-1 : ℤ) ^ (e * n)) • ·)
    ((congrArg (fun t => (kunnethProj f (e + n) _).val.app U t) hre).trans
      (kunnethProj_kunnethIncl_apply f (e + n) _ U _))).trans ?_
  refine Eq.trans ?_ (zsmul_val_app f _ _ U _).symm
  exact (congrArg (((-1 : ℤ) ^ (e * n)) • ·) l5).symm

/-- The signed transposition back from `pr₁^*Ωⁿ ⊗ pr₂^*Ωᵉ` to `pr₂^*Ωᵉ ⊗ pr₁^*Ωⁿ`. -/
abbrev signedTransposeInv (e n : ℕ) :
    kunnethSummand f (e + n) (deRhamBoxIndexMk n e (e + n) (Nat.add_comm n e)) ⟶
      ((sheafTensor (pullback f f).sheaf).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj
        (relativeDifferentialForms f (e : ℤ)))).obj
          ((Scheme.Modules.pullback (pullback.fst f f)).obj
            (relativeDifferentialForms f (n : ℤ))) :=
  ((-1 : ℤ) ^ (e * n)) •
    ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding (pullback f f).sheaf).app
      ((Scheme.Modules.pullback (pullback.fst f f)).obj
        (relativeDifferentialForms f (n : ℤ)))).hom.app
      ((Scheme.Modules.pullback (pullback.snd f f)).obj (relativeDifferentialForms f (e : ℤ)))

/-- `Stacks.WeilDeRham.signedTransposeInv` retracts `Stacks.WeilDeRham.signedTranspose`. -/
theorem signedTranspose_comp_signedTransposeInv (e n : ℕ) :
    signedTranspose f e n ≫ signedTransposeInv f e n = 𝟙 _ := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := (pullback f f).sheaf) fun U x y => ?_
  have l₁ := Stacks.SheafOfModules.Tensor.sheafTensorBraiding_hom_app_sheafifyUnit_tmul
    (pullback f f).sheaf _ _ U x y
  have l₂ := Stacks.SheafOfModules.Tensor.sheafTensorBraiding_hom_app_sheafifyUnit_tmul
    (pullback f f).sheaf _ _ U y x
  refine (congrArg (fun t => (signedTransposeInv f e n).val.app U t)
    ((zsmul_val_app f _ _ U _).trans (congrArg (((-1 : ℤ) ^ (e * n)) • ·) l₁))).trans ?_
  refine (map_zsmul ((signedTransposeInv f e n).val.app U).hom _ _).trans ?_
  refine (congrArg (((-1 : ℤ) ^ (e * n)) • ·) ((zsmul_val_app f _ _ U _).trans
    (congrArg (((-1 : ℤ) ^ (e * n)) • ·) l₂))).trans ?_
  exact neg_one_pow_zsmul_zsmul _ _

end TopWedge

/-! ### Top-degree injectivity -/

/-- `Stacks.WeilDeRham.classTransport` on classes of forms is the transport along the equality
of the two cohomology groups. -/
theorem classTransport_eq_eqToHom {X S : Scheme.{u}} (π : X ⟶ S) {k k' : ℤ} (hk : k = k')
    {q q' : ℕ} (hq : q = q')
    (h : Hgroup (structureSheafRing X.toRingedSpace) ⊤ q (relativeDifferentialForms π k) =
      Hgroup (structureSheafRing X.toRingedSpace) ⊤ q' (relativeDifferentialForms π k')) :
    classTransport (relativeDifferentialForms π) hk hq = eqToHom h := by
  subst hk hq
  simp only [classTransport, eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]

section TopInjective

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (e : ℕ) [SmoothOfRelativeDimension (e + 1) f]
  (σ : Spec (.of A) ⟶ X) [IsClosedImmersion σ] [LocallyOfFinitePresentation σ]
  [Smooth (σ ≫ f)] [FormallyUnramified (σ ≫ f)]

/-- **Top-degree injectivity in cup form from the injectivity of the external cup product**: if
`x ↦ p₂^♮x ∪ p₁^♮ξ ∈ H^{2n}(X ×_A X, p₂^*Ωⁿ ⊗ p₁^*Ωⁿ)` is injective on `Hⁿ(X, Ωⁿ_{X/A})`, where
`ξ` is the Gysin class of the section read in degree `n = e + 1`, then so is
`x ↦ p₂^*x ∪ p₁^*ξ`, the cup product along the wedge product of forms. -/
theorem cupTopInjective_of_pullbackCup
    (ξ'' : Hgroup (structureSheafRing X.toRingedSpace) ⊤ (e + 1)
      (relativeDifferentialForms f ((e + 1 : ℕ) : ℤ)))
    (hξ : ξ'' = sectionClassNormalized f e σ)
    (h : ∀ x : Hgroup (structureSheafRing X.toRingedSpace) ⊤ (e + 1)
        (relativeDifferentialForms f ((e + 1 : ℕ) : ℤ)),
      pullbackCup (pullback.snd f f) (pullback.fst f f)
          (relativeDifferentialForms f ((e + 1 : ℕ) : ℤ))
          (relativeDifferentialForms f ((e + 1 : ℕ) : ℤ)) (e + 1) (e + 1)
          ((unitPullback (pullback.snd f f) (relativeDifferentialForms f ((e + 1 : ℕ) : ℤ))
            (e + 1)).hom x)
          ((unitPullback (pullback.fst f f) (relativeDifferentialForms f ((e + 1 : ℕ) : ℤ))
            (e + 1)).hom ξ'') = 0 → x = 0) :
    CupTopInjective f e σ := by
  intro x hx
  refine h x ?_
  subst hξ
  have hsnd : (sndPullback f (e + 1) (e + 1)).hom x =
      (Hfunctor (structureSheafRing (pullback f f).toRingedSpace) ⊤ (e + 1)).map
        (sndForms f ((e + 1 : ℕ) : ℤ))
        ((unitPullback (pullback.snd f f) (relativeDifferentialForms f ((e + 1 : ℕ) : ℤ))
          (e + 1)).hom x) :=
    pullbackHgroup_formsBaseChangeHom_apply _ _ _ _ _ _ _ x
  have hξ₁ := (classTransport_fstSectionClass f e σ).trans
    (pullbackHgroup_formsBaseChangeHom_apply _ _ _ _ _ _ _ (sectionClassNormalized f e σ))
  rw [cupOnProduct_eq_sheafCup, hsnd, hξ₁] at hx
  have key := (congrArg (· ≫ signedTransposeInv f (e + 1) (e + 1))
    (sndForms_fstForms_mul_kunnethProj_eq f (e + 1) (e + 1))).trans
      (signedTranspose_comp_signedTransposeInv f (e + 1) (e + 1))
  exact sheafCup_eq_zero_of_retraction (sndForms f ((e + 1 : ℕ) : ℤ))
    (fstForms f ((e + 1 : ℕ) : ℤ)) _
    (kunnethProj f ((e + 1) + (e + 1)) (deRhamBoxIndexMk (e + 1) (e + 1) ((e + 1) + (e + 1))
      (Nat.add_comm (e + 1) (e + 1)))) (signedTransposeInv f (e + 1) (e + 1)) key (e + 1) (e + 1)
    _ _ hx

end TopInjective

end Stacks.WeilDeRham

end
