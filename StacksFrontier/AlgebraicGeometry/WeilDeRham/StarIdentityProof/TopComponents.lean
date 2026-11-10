module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalCupStatements
public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethWedge
public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethWedgeSection
public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethDifferential
public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamFormsToRelative
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedCommutativity
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.PullbackHgroupRetraction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RelativeEmbeddingDimensionForms
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.StarIdentityProof.SheafCup
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.StarIdentityProof.KunnethRelativeForms

/-!
# The components of products of forms on `X ×_S X`

`Ω^{2n-1}_{X ×_S X/S}` is the sum of two Künneth summands (`Stacks.WeilDeRham.kunneth_top_split`),
and the top components of products with pulled-back forms
(`Stacks.WeilDeRham.fstForms_mul_kunnethProj`, `Stacks.WeilDeRham.sndForms_mul_kunnethProj`),
used in the proof of [Stacks, Tag 0G8J].

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

/-! ### The components of products of forms on `X ×_S X` -/

section TopComponents

attribute [local instance] hasColimits_sheafOfModules_toRingCat
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The projection `Ωⁿ_{X ×_S X/S} ⟶ pr₂^*Ωⁿ_{X/S}` onto the forms pulled back along the second
projection, `Stacks.WeilDeRham.relativeProjection` for `W = X ×_S X` over `X` through `pr₁`. -/
abbrev sndProjection (n : ℤ) :
    relativeDifferentialForms (pullback.fst f f ≫ f) n ⟶
      (Scheme.Modules.pullback (pullback.snd f f)).obj (relativeDifferentialForms f n) :=
  relativeProjection f (pullback.fst f f) (pullback.fst f f ≫ f) rfl (pullback.snd f f)
    (IsPullback.of_hasPullback f f).flip n

/-- The projection `Ωⁿ_{X ×_S X/S} ⟶ pr₁^*Ωⁿ_{X/S}` onto the forms pulled back along the first
projection. -/
abbrev fstProjection (n : ℤ) :
    relativeDifferentialForms (pullback.fst f f ≫ f) n ⟶
      (Scheme.Modules.pullback (pullback.fst f f)).obj (relativeDifferentialForms f n) :=
  relativeProjection f (pullback.snd f f) (pullback.fst f f ≫ f) pullback.condition.symm
    (pullback.fst f f) (IsPullback.of_hasPullback f f) n

/-- `Stacks.WeilDeRham.sndProjection` kills the Künneth summands `(p, q)` with `p > 0`. -/
theorem sndProjection_kunnethIncl_of_pos (n : ℕ) (k : deRhamBoxIndex n) (hk : 0 < k.1.1)
    (U : (pullback f f).Opensᵒᵖ)
    (y : ((Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f (k.1.1 : ℤ))).val.obj U)
    (z : ((Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f (k.1.2 : ℤ))).val.obj U) :
    (sndProjection f (n : ℤ)).val.app U
      ((kunnethIncl f n k).val.app U (kunnethTmul f k.1.1 k.1.2 U y z)) = 0 := by
  have hT : (formsToRelativeOverApp f (pullback.fst f f) (pullback.fst f f ≫ f) rfl
      (n : ℤ)).val.app U ((kunnethIncl f n k).val.app U (kunnethTmul f k.1.1 k.1.2 U y z)) = 0 := by
    have h₁ := kunnethIncl_apply f n k U y z
    have hz : (formsToRelativeOverApp f (pullback.fst f f) (pullback.fst f f ≫ f) rfl
        (k.1.1 : ℤ)).val.app U ((fstForms f (k.1.1 : ℤ)).val.app U y) = 0 :=
      congrArg (fun φ => φ.val.app U y)
        (relativeDifferentialFormsMap_comp_formsToRelativeOver_self f (pullback.fst f f)
          (pullback.fst f f ≫ f) rfl (Category.comp_id _).symm k.1.1 hk)
    refine eq_of_heq ((unitalHom_app_heq _ _ (show (n : ℤ) = (k.1.1 : ℤ) + (k.1.2 : ℤ) by
      have : k.1.1 + k.1.2 = n := k.2; omega)
      (by rw [h₁]; exact eqToHom_val_app_heq_nat _ k.2 _ _)).trans ?_)
    refine (heq_of_eq (((formsToRelativeOver f (pullback.fst f f) (pullback.fst f f ≫ f)
      rfl).map_mul _ _ U _ _).trans ?_)).trans
        (zero_heq_zero _ (by have : k.1.1 + k.1.2 = n := k.2; omega))
    rw [hz, map_zero]
    rfl
  have := isIso_relativeDifferentialFormsMap_of_isPullback f (pullback.fst f f) (pullback.snd f f)
    (IsPullback.of_hasPullback f f).flip (n : ℤ)
  exact (comp₂_val_app _ _ U _).trans ((congrArg _ hT).trans (map_zero _))

/-- **A degree-zero form pulled back along the first projection is a scalar multiple of `1`**, in
the exterior algebra of `pr₁^*Ω_{X/S}` and in `Ω^•_{X ×_S X/S}`, for the same scalar. -/
theorem exists_fstForms_zero_eq_smul_one (U : (pullback f f).Opensᵒᵖ)
    (y : ((Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f ((0 : ℕ) : ℤ))).val.obj U) :
    ∃ r : (Sheaf.toRingCat (Opens.grothendieckTopology (pullback f f : Scheme.{u}))
        (pullback f f).sheaf).obj.obj U,
      (Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f) (relativeDifferentials f)
          ((0 : ℕ) : ℤ)).hom.val.app U y = r • (deRhamBoxAlgebrasLeft f f).exterior.one.eval U ∧
      (fstForms f ((0 : ℕ) : ℤ)).val.app U y =
        r • (relativeDifferentialFormsAlgebra (pullback.fst f f ≫ f)).one.eval U := by
  refine ⟨_, ((deRhamBoxAlgebrasLeft f f).exteriorPieceZeroIsoUnit_smul_one U _ _ rfl).symm, ?_⟩
  refine (congrArg (((leftFormsHom f).app 0).val.app U)
    ((deRhamBoxAlgebrasLeft f f).exteriorPieceZeroIsoUnit_smul_one U _ _ rfl).symm).trans ?_
  exact ((((leftFormsHom f).app 0).val.app U).hom.map_smul _ _).trans
    (congrArg _ ((leftFormsHom f).map_one U))

/-- **A degree-zero form pulled back along the second projection is a scalar multiple of
`1`.** -/
theorem exists_sndForms_zero_eq_smul_one (U : (pullback f f).Opensᵒᵖ)
    (y : ((Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f ((0 : ℕ) : ℤ))).val.obj U) :
    ∃ r : (Sheaf.toRingCat (Opens.grothendieckTopology (pullback f f : Scheme.{u}))
        (pullback f f).sheaf).obj.obj U,
      (Scheme.Modules.exteriorPowerPullbackIso (pullback.snd f f) (relativeDifferentials f)
          ((0 : ℕ) : ℤ)).hom.val.app U y = r • (deRhamBoxAlgebrasRight f f).exterior.one.eval U ∧
      (sndForms f ((0 : ℕ) : ℤ)).val.app U y =
        r • (relativeDifferentialFormsAlgebra (pullback.fst f f ≫ f)).one.eval U := by
  refine ⟨_, ((deRhamBoxAlgebrasRight f f).exteriorPieceZeroIsoUnit_smul_one U _ _ rfl).symm, ?_⟩
  refine (congrArg (((rightFormsHom f).app 0).val.app U)
    ((deRhamBoxAlgebrasRight f f).exteriorPieceZeroIsoUnit_smul_one U _ _ rfl).symm).trans ?_
  exact ((((rightFormsHom f).app 0).val.app U).hom.map_smul _ _).trans
    (congrArg _ ((rightFormsHom f).map_one U))

/-- `Stacks.WeilDeRham.sndProjection` retracts the pullback of forms along the second
projection. -/
theorem sndForms_sndProjection_apply (n : ℕ) (U : (pullback f f).Opensᵒᵖ)
    (z : ((Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f (n : ℤ))).val.obj U) :
    (sndProjection f (n : ℤ)).val.app U ((sndForms f (n : ℤ)).val.app U z) = z :=
  congrArg (fun φ => φ.val.app U z)
    (relativeDifferentialFormsMap_comp_relativeProjection f (pullback.fst f f)
      (pullback.fst f f ≫ f) rfl (pullback.snd f f) (IsPullback.of_hasPullback f f).flip
      (pullback.condition.symm.trans (Category.comp_id _).symm) (n : ℤ))


/-- `Stacks.WeilDeRham.kunnethIncl_proj_self` on a local section. -/
theorem kunnethProj_kunnethIncl_apply (m : ℕ) (k : deRhamBoxIndex m) (U : (pullback f f).Opensᵒᵖ)
    (t : (kunnethSummand f m k).val.obj U) :
    (kunnethProj f m k).val.app U ((kunnethIncl f m k).val.app U t) = t :=
  congrArg (fun φ => φ.val.app U t) (kunnethIncl_proj_self f m k)

/-- `Stacks.WeilDeRham.kunnethIncl_proj_of_ne` on a local section. -/
theorem kunnethProj_kunnethIncl_apply_of_ne (m : ℕ) {k l : deRhamBoxIndex m} (h : k ≠ l)
    (U : (pullback f f).Opensᵒᵖ) (t : (kunnethSummand f m k).val.obj U) :
    (kunnethProj f m l).val.app U ((kunnethIncl f m k).val.app U t) = 0 :=
  congrArg (fun φ => φ.val.app U t) (kunnethIncl_proj_of_ne f m h)

/-- A Künneth component of `φ(x) ∧ ψ(y)`, computed through the tensor product of `φ` and `ψ`,
the multiplication of forms and the Künneth projection. -/
private theorem kunnethProj_mulSheaf_apply (e n : ℕ) (k : deRhamBoxIndex (e + n))
    {F G : (pullback f f).Modules}
    (φ : F ⟶ relativeDifferentialForms (pullback.fst f f ≫ f) (e : ℤ))
    (ψ : G ⟶ relativeDifferentialForms (pullback.fst f f ≫ f) (n : ℤ))
    (U : (pullback f f).Opensᵒᵖ) (x : F.val.obj U) (y : G.val.obj U) :
    (((sheafTensor (pullback f f).sheaf).obj F).map ψ ≫
        ((sheafTensor (pullback f f).sheaf).map φ).app
          (relativeDifferentialForms (pullback.fst f f ≫ f) (n : ℤ)) ≫
        _root_.SheafOfModules.GradedAlgebra.mulSheaf
          (relativeDifferentialFormsAlgebra (pullback.fst f f ≫ f)) (e : ℤ) (n : ℤ) ≫
        kunnethProj f (e + n) k).val.app U
        ((PresheafOfModules.tensorSheafUnit F G).app U (x ⊗ₜ y)) =
      (kunnethProj f (e + n) k).val.app U (wedgeW f (e : ℤ) (n : ℤ) U (φ.val.app U x)
        (ψ.val.app U y)) := by
  have l1 := sheafTensor_obj_map_val_app_unit (pullback f f).sheaf F ψ U x y
  have l2 := sheafTensor_map_app_val_app_unit (pullback f f).sheaf φ
    (relativeDifferentialForms (pullback.fst f f ≫ f) (n : ℤ)) U x (ψ.val.app U y)
  have l3 := _root_.SheafOfModules.GradedAlgebra.mulSheaf_unit
    (relativeDifferentialFormsAlgebra (pullback.fst f f ≫ f)) (e : ℤ) (n : ℤ) U
    (φ.val.app U x) (ψ.val.app U y)
  refine (congrArg (fun t => (kunnethProj f (e + n) k).val.app U t) ?_).trans rfl
  exact (congrArg _ (congrArg _ l1)).trans ((congrArg _ l2).trans l3)

/-- **The `(e, n)`-component of a product with a form pulled back along the first projection, on
the `(0, n)` summand.** -/
theorem kunnethProj_wedge_fstForms_zero (e n : ℕ) (U : (pullback f f).Opensᵒᵖ)
    (x : ((Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f (e : ℤ))).val.obj U)
    (y : ((Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f ((0 : ℕ) : ℤ))).val.obj U)
    (z : ((Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f (n : ℤ))).val.obj U) :
    (kunnethProj f (e + n) (deRhamBoxIndexMk e n (e + n) rfl)).val.app U
        (wedgeW f (e : ℤ) (n : ℤ) U ((fstForms f (e : ℤ)).val.app U x)
          ((kunnethIncl f n (deRhamBoxIndexMk 0 n n (zero_add n))).val.app U
            (kunnethTmul f 0 n U y z))) =
      kunnethTmul f e n U x ((sndProjection f (n : ℤ)).val.app U
        ((kunnethIncl f n (deRhamBoxIndexMk 0 n n (zero_add n))).val.app U
          (kunnethTmul f 0 n U y z))) := by
  obtain ⟨r, hrE, hrΩ⟩ := exists_fstForms_zero_eq_smul_one f U y
  have hI : (kunnethIncl f n (deRhamBoxIndexMk 0 n n (zero_add n))).val.app U
      (kunnethTmul f 0 n U y z) = r • (sndForms f (n : ℤ)).val.app U z := by
    refine eq_of_heq ((heq_of_eq (kunnethIncl_apply f n (deRhamBoxIndexMk 0 n n (zero_add n))
      U y z)).trans ((eqToHom_val_app_heq_nat _ (zero_add n) _ _).trans ?_))
    change HEq (wedgeW f ((0 : ℕ) : ℤ) (n : ℤ) U ((fstForms f ((0 : ℕ) : ℤ)).val.app U y)
      ((sndForms f (n : ℤ)).val.app U z)) _
    rw [hrΩ, Stacks.BilinearMap.map_smul_left]
    exact smul_heq_smul _ (by push_cast; ring) r
      ((relativeDifferentialFormsAlgebra (pullback.fst f f ≫ f)).one_mul _ U _)
  have hR : (sndProjection f (n : ℤ)).val.app U
      ((kunnethIncl f n (deRhamBoxIndexMk 0 n n (zero_add n))).val.app U
        (kunnethTmul f 0 n U y z)) = r • z := by
    rw [hI]
    exact (((sndProjection f (n : ℤ)).val.app U).hom.map_smul _ _).trans
      (congrArg (r • ·) (sndForms_sndProjection_apply f n U z))
  have hL := wedge_fstForms_kunnethIncl f e n (deRhamBoxIndexMk 0 n n (zero_add n)) U x y z
  have hY : (Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f) (relativeDifferentials f)
      ((e + 0 : ℕ) : ℤ)).inv.val.app U
      (((deRhamBoxAlgebrasLeft f f).exterior.mul (e : ℤ) ((0 : ℕ) : ℤ)).app U
        ((Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f)
          (relativeDifferentials f) (e : ℤ)).hom.val.app U x)
        ((Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f)
          (relativeDifferentials f) ((0 : ℕ) : ℤ)).hom.val.app U y)) = r • x := by
    have h1 : ((deRhamBoxAlgebrasLeft f f).exterior.mul (e : ℤ) ((0 : ℕ) : ℤ)).app U
        ((Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f)
          (relativeDifferentials f) (e : ℤ)).hom.val.app U x)
        ((deRhamBoxAlgebrasLeft f f).exterior.one.eval U) =
      (Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f)
          (relativeDifferentials f) (e : ℤ)).hom.val.app U x :=
      eq_of_heq ((deRhamBoxAlgebrasLeft f f).exterior.mul_one _ U _)
    refine (congrArg (fun t => (Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f)
      (relativeDifferentials f) (e : ℤ)).inv.val.app U
      (((deRhamBoxAlgebrasLeft f f).exterior.mul (e : ℤ) ((0 : ℕ) : ℤ)).app U
        ((Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f)
          (relativeDifferentials f) (e : ℤ)).hom.val.app U x) t)) hrE).trans ?_
    refine (congrArg (fun t => (Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f)
      (relativeDifferentials f) (e : ℤ)).inv.val.app U t)
      (((deRhamBoxAlgebrasLeft f f).exterior.mul (e : ℤ) ((0 : ℕ) : ℤ)).map_smul_right
        U r _ _)).trans ?_
    refine (congrArg (fun t => (Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f)
      (relativeDifferentials f) (e : ℤ)).inv.val.app U (r • t)) h1).trans ?_
    refine ((((Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f)
      (relativeDifferentials f) (e : ℤ)).inv.val.app U).hom.map_smul _ _).trans ?_)
    exact congrArg (r • ·) (congrArg (fun φ => φ.val.app U x)
      (Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f)
        (relativeDifferentials f) (e : ℤ)).hom_inv_id)
  refine
    (congrArg ((kunnethProj f (e + n) (deRhamBoxIndexMk e n (e + n) rfl)).val.app U) hL).trans ?_
  refine (kunnethProj_kunnethIncl_apply f (e + n) (deRhamBoxIndexMk e n (e + n) rfl) U _).trans ?_
  refine (congrArg (fun t => kunnethTmul f e n U t z) hY).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => kunnethTmul f e n U x t) hR).symm
  exact congrArg _ (TensorProduct.smul_tmul r x z)

/-- The `(e, n)`-component of a product with a form pulled back along the first projection, on an
arbitrary Künneth summand of the second factor. -/
theorem kunnethProj_wedge_fstForms (e n : ℕ) (k : deRhamBoxIndex n) (U : (pullback f f).Opensᵒᵖ)
    (x : ((Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f (e : ℤ))).val.obj U)
    (y : ((Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f (k.1.1 : ℤ))).val.obj U)
    (z : ((Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f (k.1.2 : ℤ))).val.obj U) :
    (kunnethProj f (e + n) (deRhamBoxIndexMk e n (e + n) rfl)).val.app U
        (wedgeW f (e : ℤ) (n : ℤ) U ((fstForms f (e : ℤ)).val.app U x)
          ((kunnethIncl f n k).val.app U (kunnethTmul f k.1.1 k.1.2 U y z))) =
      kunnethTmul f e n U x ((sndProjection f (n : ℤ)).val.app U
        ((kunnethIncl f n k).val.app U (kunnethTmul f k.1.1 k.1.2 U y z))) := by
  obtain ⟨⟨p, q⟩, hpq⟩ := k
  have hpq' : p + q = n := hpq
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · obtain rfl : q = n := by omega
    exact kunnethProj_wedge_fstForms_zero f e q U x y z
  · refine (congrArg _ (wedge_fstForms_kunnethIncl f e n ⟨(p, q), hpq⟩ U x y z)).trans ?_
    have hne :
        deRhamBoxIndexMk (e + p) q (e + n) (by omega) ≠ deRhamBoxIndexMk e n (e + n) rfl := by
      intro h
      have := congrArg (fun k : deRhamBoxIndex (e + n) => k.1.1) h
      simp at this
      omega
    refine (kunnethProj_kunnethIncl_apply_of_ne f (e + n) hne U _).trans ?_
    refine Eq.trans ?_ (congrArg (kunnethTmul f e n U x)
      (sndProjection_kunnethIncl_of_pos f n ⟨(p, q), hpq⟩ hp U y z)).symm
    exact (congrArg _ (TensorProduct.tmul_zero _ x)).trans (map_zero _) |>.symm

/-- **The `(e, n)`-component of the product with forms pulled back along the first projection**:
`pr_{(e,n)}(pr₁^*ω ∧ θ) = ω ⊗ π(θ)` for `θ` an `n`-form on `X ×_S X`, where `π` is the projection
onto the forms pulled back along the second projection. -/
theorem fstForms_mul_kunnethProj (e n : ℕ) :
    ((sheafTensor (pullback f f).sheaf).map (fstForms f (e : ℤ))).app
        (relativeDifferentialForms (pullback.fst f f ≫ f) (n : ℤ)) ≫
      _root_.SheafOfModules.GradedAlgebra.mulSheaf
        (relativeDifferentialFormsAlgebra (pullback.fst f f ≫ f)) (e : ℤ) (n : ℤ) ≫
      kunnethProj f (e + n) (deRhamBoxIndexMk e n (e + n) rfl) =
    ((sheafTensor (pullback f f).sheaf).obj ((Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f (e : ℤ)))).map (sndProjection f (n : ℤ)) := by
  refine kunneth_hom_ext_right f n fun k => ?_
  refine Stacks.SheafOfModules.TopWedge.tensorSheaf_hom_ext_right (Osharp := (pullback f f).sheaf)
    (F := (Scheme.Modules.pullback (pullback.fst f f)).obj (relativeDifferentialForms f (e : ℤ)))
    (G := (Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f (k.1.1 : ℤ)))
    (H := (Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f (k.1.2 : ℤ))) fun U x y z => ?_
  have l1 := sheafTensor_obj_map_val_app_unit (pullback f f).sheaf
    ((Scheme.Modules.pullback (pullback.fst f f)).obj (relativeDifferentialForms f (e : ℤ)))
    (kunnethIncl f n k) U x (kunnethTmul f k.1.1 k.1.2 U y z)
  have l4 := sheafTensor_obj_map_val_app_unit (pullback f f).sheaf
    ((Scheme.Modules.pullback (pullback.fst f f)).obj (relativeDifferentialForms f (e : ℤ)))
    (sndProjection f (n : ℤ)) U x
    ((kunnethIncl f n k).val.app U (kunnethTmul f k.1.1 k.1.2 U y z))
  refine (kunnethProj_mulSheaf_apply f e n _ (fstForms f (e : ℤ)) (kunnethIncl f n k) U x
    (kunnethTmul f k.1.1 k.1.2 U y z)).trans ?_
  refine (kunnethProj_wedge_fstForms f e n k U x y z).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => (((sheafTensor (pullback f f).sheaf).obj
    ((Scheme.Modules.pullback (pullback.fst f f)).obj (relativeDifferentialForms f (e : ℤ)))).map
      (sndProjection f (n : ℤ))).val.app U t) l1).symm
  exact l4.symm

/-- `Stacks.WeilDeRham.fstProjection` kills the Künneth summands `(p, q)` with `q > 0`. -/
theorem fstProjection_kunnethIncl_of_pos (n : ℕ) (k : deRhamBoxIndex n) (hk : 0 < k.1.2)
    (U : (pullback f f).Opensᵒᵖ)
    (y : ((Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f (k.1.1 : ℤ))).val.obj U)
    (z : ((Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f (k.1.2 : ℤ))).val.obj U) :
    (fstProjection f (n : ℤ)).val.app U
      ((kunnethIncl f n k).val.app U (kunnethTmul f k.1.1 k.1.2 U y z)) = 0 := by
  have hT : (formsToRelativeOverApp f (pullback.snd f f) (pullback.fst f f ≫ f)
      pullback.condition.symm (n : ℤ)).val.app U
      ((kunnethIncl f n k).val.app U (kunnethTmul f k.1.1 k.1.2 U y z)) = 0 := by
    have h₁ := kunnethIncl_apply f n k U y z
    have hz : (formsToRelativeOverApp f (pullback.snd f f) (pullback.fst f f ≫ f)
        pullback.condition.symm (k.1.2 : ℤ)).val.app U ((sndForms f (k.1.2 : ℤ)).val.app U z) = 0 :=
      congrArg (fun φ => φ.val.app U z)
        (relativeDifferentialFormsMap_comp_formsToRelativeOver_self f (pullback.snd f f)
          (pullback.fst f f ≫ f) pullback.condition.symm
          (pullback.condition.symm.trans (Category.comp_id _).symm) k.1.2 hk)
    refine eq_of_heq ((unitalHom_app_heq _ _ (show (n : ℤ) = (k.1.1 : ℤ) + (k.1.2 : ℤ) by
      have : k.1.1 + k.1.2 = n := k.2; omega)
      (by rw [h₁]; exact eqToHom_val_app_heq_nat _ k.2 _ _)).trans ?_)
    refine (heq_of_eq (((formsToRelativeOver f (pullback.snd f f) (pullback.fst f f ≫ f)
      pullback.condition.symm).map_mul _ _ U _ _).trans ?_)).trans
        (zero_heq_zero _ (by have : k.1.1 + k.1.2 = n := k.2; omega))
    rw [hz, map_zero]
  have := isIso_relativeDifferentialFormsMap_of_isPullback f (pullback.snd f f) (pullback.fst f f)
    (IsPullback.of_hasPullback f f) (n : ℤ)
  exact (comp₂_val_app _ _ U _).trans ((congrArg _ hT).trans (map_zero _))

/-- `Stacks.WeilDeRham.fstProjection` retracts the pullback of forms along the first
projection. -/
theorem fstForms_fstProjection_apply (n : ℕ) (U : (pullback f f).Opensᵒᵖ)
    (z : ((Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f (n : ℤ))).val.obj U) :
    (fstProjection f (n : ℤ)).val.app U ((fstForms f (n : ℤ)).val.app U z) = z :=
  congrArg (fun φ => φ.val.app U z)
    (relativeDifferentialFormsMap_comp_relativeProjection f (pullback.snd f f)
      (pullback.fst f f ≫ f) pullback.condition.symm (pullback.fst f f)
      (IsPullback.of_hasPullback f f) (Category.comp_id _).symm (n : ℤ))

/-- The Künneth inclusion of the `(n, 0)` summand, on `y ⊗ z` with `z` of degree `0`. -/
theorem kunnethIncl_right_zero (n : ℕ) (U : (pullback f f).Opensᵒᵖ)
    (y : ((Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f (n : ℤ))).val.obj U)
    (z : ((Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f ((0 : ℕ) : ℤ))).val.obj U)
    (r : (Sheaf.toRingCat (Opens.grothendieckTopology (pullback f f : Scheme.{u}))
        (pullback f f).sheaf).obj.obj U)
    (hr : (sndForms f ((0 : ℕ) : ℤ)).val.app U z =
        r • (relativeDifferentialFormsAlgebra (pullback.fst f f ≫ f)).one.eval U) :
    (kunnethIncl f n (deRhamBoxIndexMk n 0 n rfl)).val.app U (kunnethTmul f n 0 U y z) =
      r • (fstForms f (n : ℤ)).val.app U y := by
  refine (kunnethIncl_apply f n (deRhamBoxIndexMk n 0 n rfl) U y z).trans ?_
  change wedgeW f (n : ℤ) ((0 : ℕ) : ℤ) U ((fstForms f (n : ℤ)).val.app U y)
    ((sndForms f ((0 : ℕ) : ℤ)).val.app U z) = _
  rw [hr, Stacks.BilinearMap.map_smul_right]
  exact congrArg (r • ·) (eq_of_heq
    ((relativeDifferentialFormsAlgebra (pullback.fst f f ≫ f)).mul_one _ U _))


/-- **The `(n, e)`-component of a product with a form pulled back along the second projection**,
on an arbitrary Künneth summand of the second factor: by graded commutativity it is
`(-1)^{en}` times the transposed tensor. -/
theorem kunnethProj_wedge_sndForms (e n : ℕ) (k : deRhamBoxIndex n) (U : (pullback f f).Opensᵒᵖ)
    (x : ((Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f (e : ℤ))).val.obj U)
    (y : ((Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f (k.1.1 : ℤ))).val.obj U)
    (z : ((Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f (k.1.2 : ℤ))).val.obj U) :
    (kunnethProj f (e + n) (deRhamBoxIndexMk n e (e + n) (Nat.add_comm n e))).val.app U
        (wedgeW f (e : ℤ) (n : ℤ) U ((sndForms f (e : ℤ)).val.app U x)
          ((kunnethIncl f n k).val.app U (kunnethTmul f k.1.1 k.1.2 U y z))) =
      ((-1 : ℤ) ^ (e * n)) • kunnethTmul f n e U ((fstProjection f (n : ℤ)).val.app U
        ((kunnethIncl f n k).val.app U (kunnethTmul f k.1.1 k.1.2 U y z))) x := by
  have hcomm := AlgebraicGeometry.SheafOfModules.formProduct_comm
    (deRhamAlgebras (pullback.fst f f ≫ f)) e n U ((sndForms f (e : ℤ)).val.app U x)
    ((kunnethIncl f n k).val.app U (kunnethTmul f k.1.1 k.1.2 U y z))
  refine (congrArg (fun t => (kunnethProj f (e + n)
    (deRhamBoxIndexMk n e (e + n) (Nat.add_comm n e))).val.app U t) hcomm).trans ?_
  refine (map_zsmul ((kunnethProj f (e + n) (deRhamBoxIndexMk n e (e + n)
    (Nat.add_comm n e))).val.app U).hom _ _).trans ?_
  refine congrArg (((-1 : ℤ) ^ (e * n)) • ·) ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := k
  have hpq' : p + q = n := hpq
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · obtain rfl : p = n := by omega
    obtain ⟨r, -, hr⟩ := exists_sndForms_zero_eq_smul_one f U z
    have hI := kunnethIncl_right_zero f p U y z r hr
    dsimp only at hI ⊢
    rw [hI]
    have e₁ : AlgebraicGeometry.SheafOfModules.reindexForm (deRhamAlgebras (pullback.fst f f ≫ f))
        (Nat.add_comm p e) U (AlgebraicGeometry.SheafOfModules.formProduct
          (deRhamAlgebras (pullback.fst f f ≫ f)) p e U (r • (fstForms f (p : ℤ)).val.app U y)
          ((sndForms f (e : ℤ)).val.app U x)) =
        r • (kunnethIncl f (e + p) (deRhamBoxIndexMk p e (e + p) (Nat.add_comm p e))).val.app U
          (kunnethTmul f p e U y x) := by
      refine eq_of_heq ((AlgebraicGeometry.SheafOfModules.reindexForm_heq _ _ U _).trans ?_)
      change HEq (wedgeW f (p : ℤ) (e : ℤ) U (r • (fstForms f (p : ℤ)).val.app U y)
        ((sndForms f (e : ℤ)).val.app U x)) _
      rw [Stacks.BilinearMap.map_smul_left]
      refine smul_heq_smul _ (by push_cast; ring) r ?_
      rw [kunnethIncl_apply f (e + p) (deRhamBoxIndexMk p e (e + p) (Nat.add_comm p e)) U y x]
      exact (eqToHom_val_app_heq_nat
        (fun j : ℕ => (deRhamAlgebras (pullback.fst f f ≫ f)).exteriorPower j)
        (Nat.add_comm p e) U _).symm
    rw [e₁]
    refine ((((kunnethProj f (e + p) (deRhamBoxIndexMk p e (e + p) (Nat.add_comm p e))).val.app
      U).hom.map_smul _ _).trans ?_)
    refine (congrArg (r • ·) (kunnethProj_kunnethIncl_apply f (e + p)
      (deRhamBoxIndexMk p e (e + p) (Nat.add_comm p e)) U _)).trans ?_
    refine Eq.trans ?_ (congrArg (fun t => kunnethTmul f p e U t x)
      ((((fstProjection f (p : ℤ)).val.app U).hom.map_smul _ _).trans
        (congrArg (r • ·) (fstForms_fstProjection_apply f p U y)))).symm
    exact ((((PresheafOfModules.tensorSheafUnit
      ((Scheme.Modules.pullback (pullback.fst f f)).obj (relativeDifferentialForms f (p : ℤ)))
      ((Scheme.Modules.pullback (pullback.snd f f)).obj
        (relativeDifferentialForms f (e : ℤ)))).app U).hom.map_smul r (y ⊗ₜ x)).symm).trans
      (congrArg (fun t => ((PresheafOfModules.tensorSheafUnit
        ((Scheme.Modules.pullback (pullback.fst f f)).obj (relativeDifferentialForms f (p : ℤ)))
        ((Scheme.Modules.pullback (pullback.snd f f)).obj
          (relativeDifferentialForms f (e : ℤ)))).app U) t) (TensorProduct.smul_tmul' r y x))
  · have h₃ := wedge_kunnethIncl_sndForms_heq f e n ⟨(p, q), hpq⟩ (e + n)
      (show p + (q + e) = e + n by omega) U x y z
    have hne : deRhamBoxIndexMk p (q + e) (e + n) (by omega) ≠
        deRhamBoxIndexMk n e (e + n) (Nat.add_comm n e) := by
      intro h
      have := congrArg (fun k : deRhamBoxIndex (e + n) => k.1.2) h
      simp at this
      omega
    refine (congrArg (fun t => (kunnethProj f (e + n)
      (deRhamBoxIndexMk n e (e + n) (Nat.add_comm n e))).val.app U t)
      (eq_of_heq ((AlgebraicGeometry.SheafOfModules.reindexForm_heq _ _ U _).trans h₃))).trans ?_
    refine (kunnethProj_kunnethIncl_apply_of_ne f (e + n) hne U _).trans ?_
    refine Eq.trans ?_ (congrArg (fun t => kunnethTmul f n e U t x)
      (fstProjection_kunnethIncl_of_pos f n ⟨(p, q), hpq⟩ hq U y z)).symm
    exact (congrArg _ (TensorProduct.zero_tmul _ x)).trans (map_zero _) |>.symm

/-- The zero morphism of sheaves of modules on a local section. -/
theorem zero_val_app {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (Osharp : Sheaf J CommRingCat.{u})
    (M N : _root_.SheafOfModules.{u} (Sheaf.toRingCat J Osharp)) (U : Cᵒᵖ) (t : M.val.obj U) :
    (0 : M ⟶ N).val.app U t = 0 :=
  rfl

/-- An integer multiple of a morphism of sheaves of modules, on a local section. -/
theorem zsmul_val_app {M N : (pullback f f).Modules} (c : ℤ) (φ : M ⟶ N)
    (U : (pullback f f).Opensᵒᵖ) (t : M.val.obj U) :
    (c • φ).val.app U t = c • φ.val.app U t := by
  let ev : (M ⟶ N) →+ N.val.obj U :=
    { toFun := fun χ => χ.val.app U t
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact map_zsmul ev c φ

/-- The transposition `pr₂^*Ωᵉ ⊗ pr₁^*Ωⁿ ⟶ pr₁^*Ωⁿ ⊗ pr₂^*Ωᵉ` with the Koszul sign `(-1)^{en}`. -/
abbrev signedTranspose (e n : ℕ) :
    ((sheafTensor (pullback f f).sheaf).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f (e : ℤ)))).obj ((Scheme.Modules.pullback (pullback.fst f f)).obj
        (relativeDifferentialForms f (n : ℤ))) ⟶
      kunnethSummand f (e + n) (deRhamBoxIndexMk n e (e + n) (Nat.add_comm n e)) :=
  ((-1 : ℤ) ^ (e * n)) •
    ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding (pullback f f).sheaf).app
      ((Scheme.Modules.pullback (pullback.snd f f)).obj
        (relativeDifferentialForms f (e : ℤ)))).hom.app
      ((Scheme.Modules.pullback (pullback.fst f f)).obj (relativeDifferentialForms f (n : ℤ)))

/-- **The `(n, e)`-component of the product with forms pulled back along the second projection**:
`pr_{(n,e)}(pr₂^*ω ∧ θ) = (-1)^{en} π(θ) ⊗ ω` for `θ` an `n`-form on `X ×_S X`, where `π` is the
projection onto the forms pulled back along the first projection. -/
theorem sndForms_mul_kunnethProj (e n : ℕ) :
    ((sheafTensor (pullback f f).sheaf).map (sndForms f (e : ℤ))).app
        (relativeDifferentialForms (pullback.fst f f ≫ f) (n : ℤ)) ≫
      _root_.SheafOfModules.GradedAlgebra.mulSheaf
        (relativeDifferentialFormsAlgebra (pullback.fst f f ≫ f)) (e : ℤ) (n : ℤ) ≫
      kunnethProj f (e + n) (deRhamBoxIndexMk n e (e + n) (Nat.add_comm n e)) =
    ((sheafTensor (pullback f f).sheaf).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f (e : ℤ)))).map (fstProjection f (n : ℤ)) ≫
      signedTranspose f e n := by
  refine kunneth_hom_ext_right f n fun k => ?_
  refine Stacks.SheafOfModules.TopWedge.tensorSheaf_hom_ext_right (Osharp := (pullback f f).sheaf)
    (F := (Scheme.Modules.pullback (pullback.snd f f)).obj (relativeDifferentialForms f (e : ℤ)))
    (G := (Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f (k.1.1 : ℤ)))
    (H := (Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f (k.1.2 : ℤ))) fun U x y z => ?_
  have l1 := sheafTensor_obj_map_val_app_unit (pullback f f).sheaf
    ((Scheme.Modules.pullback (pullback.snd f f)).obj (relativeDifferentialForms f (e : ℤ)))
    (kunnethIncl f n k) U x (kunnethTmul f k.1.1 k.1.2 U y z)
  have l4 := sheafTensor_obj_map_val_app_unit (pullback f f).sheaf
    ((Scheme.Modules.pullback (pullback.snd f f)).obj (relativeDifferentialForms f (e : ℤ)))
    (fstProjection f (n : ℤ)) U x
    ((kunnethIncl f n k).val.app U (kunnethTmul f k.1.1 k.1.2 U y z))
  have l5 := Stacks.SheafOfModules.Tensor.sheafTensorBraiding_hom_app_sheafifyUnit_tmul
    (pullback f f).sheaf
    ((Scheme.Modules.pullback (pullback.snd f f)).obj (relativeDifferentialForms f (e : ℤ)))
    ((Scheme.Modules.pullback (pullback.fst f f)).obj (relativeDifferentialForms f (n : ℤ))) U x
    ((fstProjection f (n : ℤ)).val.app U
      ((kunnethIncl f n k).val.app U (kunnethTmul f k.1.1 k.1.2 U y z)))
  refine (kunnethProj_mulSheaf_apply f e n _ (sndForms f (e : ℤ)) (kunnethIncl f n k) U x
    (kunnethTmul f k.1.1 k.1.2 U y z)).trans ?_
  refine (kunnethProj_wedge_sndForms f e n k U x y z).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => (signedTranspose f e n).val.app U
    ((((sheafTensor (pullback f f).sheaf).obj
    ((Scheme.Modules.pullback (pullback.snd f f)).obj (relativeDifferentialForms f (e : ℤ)))).map
      (fstProjection f (n : ℤ))).val.app U t)) l1).symm
  refine Eq.trans ?_ (congrArg (fun t => (signedTranspose f e n).val.app U t) l4).symm
  refine Eq.trans ?_ (zsmul_val_app f _ _ U _).symm
  exact (congrArg (((-1 : ℤ) ^ (e * n)) • ·) l5).symm

/-- **The product of forms pulled back along the second and the first projection has no
`(e, n)`-component** when `n ≠ e`: by graded commutativity it lies in the `(n, e)` summand. -/
theorem sndForms_fstForms_mul_kunnethProj (e n : ℕ) (h : n ≠ e) :
    (((sheafTensor (pullback f f).sheaf).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj
        (relativeDifferentialForms f (e : ℤ)))).map (fstForms f (n : ℤ)) ≫
      ((sheafTensor (pullback f f).sheaf).map (sndForms f (e : ℤ))).app
        (relativeDifferentialForms (pullback.fst f f ≫ f) (n : ℤ)) ≫
      _root_.SheafOfModules.GradedAlgebra.mulSheaf
        (relativeDifferentialFormsAlgebra (pullback.fst f f ≫ f)) (e : ℤ) (n : ℤ) ≫
      kunnethProj f (e + n) (deRhamBoxIndexMk e n (e + n) rfl)) =
      (0 : ((sheafTensor (pullback f f).sheaf).obj ((Scheme.Modules.pullback (pullback.snd f f)).obj
        (relativeDifferentialForms f (e : ℤ)))).obj
          ((Scheme.Modules.pullback (pullback.fst f f)).obj
            (relativeDifferentialForms f (n : ℤ))) ⟶
        ((sheafTensor (pullback f f).sheaf).obj ((Scheme.Modules.pullback (pullback.fst f f)).obj
          (relativeDifferentialForms f (e : ℤ)))).obj
            ((Scheme.Modules.pullback (pullback.snd f f)).obj
              (relativeDifferentialForms f (n : ℤ)))) := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := (pullback f f).sheaf)
    (F := (Scheme.Modules.pullback (pullback.snd f f)).obj (relativeDifferentialForms f (e : ℤ)))
    (G := (Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f (n : ℤ))) fun U x y => ?_
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
  have hne :
      deRhamBoxIndexMk n e (e + n) (Nat.add_comm n e) ≠ deRhamBoxIndexMk e n (e + n) rfl := by
    intro h'
    exact h (congrArg (fun k : deRhamBoxIndex (e + n) => k.1.1) h')
  refine ((kunnethProj_mulSheaf_apply f e n _ (sndForms f (e : ℤ)) (fstForms f (n : ℤ)) U x
    y).trans (congrArg (fun t => (kunnethProj f (e + n)
      (deRhamBoxIndexMk e n (e + n) rfl)).val.app U t) hcomm)).trans ?_
  refine (map_zsmul ((kunnethProj f (e + n) (deRhamBoxIndexMk e n (e + n) rfl)).val.app U).hom
    _ _).trans ?_
  refine (congrArg (((-1 : ℤ) ^ (e * n)) • ·) ((congrArg (fun t => (kunnethProj f (e + n)
    (deRhamBoxIndexMk e n (e + n) rfl)).val.app U t) hre).trans
      (kunnethProj_kunnethIncl_apply_of_ne f (e + n) hne U _))).trans ?_
  exact (smul_zero _).trans (zero_val_app _ _ _ U _).symm

/-- **The product of forms pulled back along the first and the second projection has no
`(n, e)`-component** when `n ≠ e`: it is the Künneth inclusion of the `(e, n)` summand. -/
theorem fstForms_sndForms_mul_kunnethProj (e n : ℕ) (h : n ≠ e) :
    (((sheafTensor (pullback f f).sheaf).obj ((Scheme.Modules.pullback (pullback.fst f f)).obj
        (relativeDifferentialForms f (e : ℤ)))).map (sndForms f (n : ℤ)) ≫
      ((sheafTensor (pullback f f).sheaf).map (fstForms f (e : ℤ))).app
        (relativeDifferentialForms (pullback.fst f f ≫ f) (n : ℤ)) ≫
      _root_.SheafOfModules.GradedAlgebra.mulSheaf
        (relativeDifferentialFormsAlgebra (pullback.fst f f ≫ f)) (e : ℤ) (n : ℤ) ≫
      kunnethProj f (e + n) (deRhamBoxIndexMk n e (e + n) (Nat.add_comm n e))) =
      (0 : ((sheafTensor (pullback f f).sheaf).obj ((Scheme.Modules.pullback (pullback.fst f f)).obj
        (relativeDifferentialForms f (e : ℤ)))).obj
          ((Scheme.Modules.pullback (pullback.snd f f)).obj
            (relativeDifferentialForms f (n : ℤ))) ⟶
        ((sheafTensor (pullback f f).sheaf).obj ((Scheme.Modules.pullback (pullback.fst f f)).obj
          (relativeDifferentialForms f (n : ℤ)))).obj
            ((Scheme.Modules.pullback (pullback.snd f f)).obj
              (relativeDifferentialForms f (e : ℤ)))) := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := (pullback f f).sheaf)
    (F := (Scheme.Modules.pullback (pullback.fst f f)).obj (relativeDifferentialForms f (e : ℤ)))
    (G := (Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f (n : ℤ))) fun U x y => ?_
  have hne :
      deRhamBoxIndexMk e n (e + n) rfl ≠ deRhamBoxIndexMk n e (e + n) (Nat.add_comm n e) := by
    intro h'
    exact h (congrArg (fun k : deRhamBoxIndex (e + n) => k.1.1) h').symm
  refine ((kunnethProj_mulSheaf_apply f e n _ (fstForms f (e : ℤ)) (sndForms f (n : ℤ)) U x
    y).trans (congrArg (fun t => (kunnethProj f (e + n)
      (deRhamBoxIndexMk n e (e + n) (Nat.add_comm n e))).val.app U t)
      (wedge_fstForms_sndForms f e n U x y))).trans ?_
  exact (kunnethProj_kunnethIncl_apply_of_ne f (e + n) hne U _).trans (zero_val_app _ _ _ U _).symm

end TopComponents

end Stacks.WeilDeRham

end
