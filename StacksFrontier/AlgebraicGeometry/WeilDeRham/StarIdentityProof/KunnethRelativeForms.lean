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

/-!
# The Künneth decomposition of forms on `X ×_S X` and forms relative to `W ⟶ X`

The inclusions and projections of the Künneth decomposition of `Ωᵐ_{X ×_S X/S}`
(`Stacks.WeilDeRham.kunnethIncl`, `Stacks.WeilDeRham.kunnethProj`), the homomorphism
`Ω^•_{W/S} ⟶ Ω^•_{W/X}` (`Stacks.WeilDeRham.formsToRelativeOver`) and the projection
`Ωⁿ_{W/S} ⟶ G^*Ωⁿ_{X/S}` for a cartesian square `W = X ×_S X`
(`Stacks.WeilDeRham.relativeProjection`), used in the proof of [Stacks, Tag 0G8J].

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

/-! ### The Künneth decomposition of differential forms on `X ×_S X` -/

section Kunneth

attribute [local instance] hasColimits_sheafOfModules_toRingCat
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The `(p, q)` summand `pr₁^*Ωᵖ_{X/S} ⊗ pr₂^*Ω^q_{X/S}` of `Ωᵐ_{X ×_S X/S}`. -/
abbrev kunnethSummand (m : ℕ) (k : deRhamBoxIndex m) : (pullback f f).Modules :=
  (deRhamBoxSummand f f m k).module

/-- **The inclusion of the `(p, q)` summand** of the Künneth decomposition of `Ωᵐ_{X ×_S X/S}`
of [Stacks, Tag 0FMA]. -/
def kunnethIncl (m : ℕ) (k : deRhamBoxIndex m) :
    kunnethSummand f m k ⟶ relativeDifferentialForms (pullback.fst f f ≫ f) (m : ℤ) :=
  biproduct.ι (fun k => (deRhamBoxSummand f f m k).module) k ≫ (deRhamBoxModuleIso f f m).hom

/-- **The projection onto the `(p, q)` summand** of the Künneth decomposition. -/
def kunnethProj (m : ℕ) (k : deRhamBoxIndex m) :
    relativeDifferentialForms (pullback.fst f f ≫ f) (m : ℤ) ⟶ kunnethSummand f m k :=
  (deRhamBoxModuleIso f f m).inv ≫ biproduct.π (fun k => (deRhamBoxSummand f f m k).module) k

/-- The projection onto a Künneth summand retracts its inclusion. -/
theorem kunnethIncl_proj_self (m : ℕ) (k : deRhamBoxIndex m) :
    kunnethIncl f m k ≫ kunnethProj f m k = 𝟙 _ := by
  simp only [kunnethIncl, kunnethProj, Category.assoc, Iso.hom_inv_id_assoc, biproduct.ι_π_self]

/-- The projection onto a Künneth summand kills the other summands. -/
theorem kunnethIncl_proj_of_ne (m : ℕ) {k l : deRhamBoxIndex m} (h : k ≠ l) :
    kunnethIncl f m k ≫ kunnethProj f m l = 0 := by
  simp only [kunnethIncl, kunnethProj, Category.assoc, Iso.hom_inv_id_assoc,
    biproduct.ι_π_ne _ h]

/-- The Künneth projections and inclusions decompose the identity of `Ωᵐ_{X ×_S X/S}`. -/
theorem sum_kunnethProj_incl (m : ℕ) :
    ∑ k, kunnethProj f m k ≫ kunnethIncl f m k = 𝟙 _ := by
  have e : ∑ k, kunnethProj f m k ≫ kunnethIncl f m k = (deRhamBoxModuleIso f f m).inv ≫
      (∑ k, biproduct.π (fun k => (deRhamBoxSummand f f m k).module) k ≫
        biproduct.ι (fun k => (deRhamBoxSummand f f m k).module) k) ≫
        (deRhamBoxModuleIso f f m).hom := by
    simp only [kunnethIncl, kunnethProj, Preadditive.comp_sum, Preadditive.sum_comp,
      Category.assoc]
  rw [e, biproduct.total, Category.id_comp, Iso.inv_hom_id]

/-- The canonical map `pr₁^*Ωᵖ_{X/S} ⟶ Ωᵖ_{X ×_S X/S}` on forms of the first projection. -/
abbrev fstForms (p : ℤ) :
    (Scheme.Modules.pullback (pullback.fst f f)).obj (relativeDifferentialForms f p) ⟶
      relativeDifferentialForms (pullback.fst f f ≫ f) p :=
  relativeDifferentialFormsMap (pullback.fst f f) f (pullback.fst f f ≫ f) (𝟙 S)
    (Category.comp_id _).symm p

/-- The canonical map `pr₂^*Ωᵖ_{X/S} ⟶ Ωᵖ_{X ×_S X/S}` on forms of the second projection. -/
abbrev sndForms (p : ℤ) :
    (Scheme.Modules.pullback (pullback.snd f f)).obj (relativeDifferentialForms f p) ⟶
      relativeDifferentialForms (pullback.fst f f ≫ f) p :=
  relativeDifferentialFormsMap (pullback.snd f f) f (pullback.fst f f ≫ f) (𝟙 S)
    (pullback.condition.symm.trans (Category.comp_id _).symm) p

/-- **The Künneth inclusion on a local pure tensor** is the wedge product of the two pulled-back
forms, `y ⊗ z ↦ pr₁^*y ∧ pr₂^*z`, with its degree transported along `p + q = m`. -/
theorem kunnethIncl_apply (m : ℕ) (k : deRhamBoxIndex m) (U : (pullback f f).Opensᵒᵖ)
    (y : ((Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f (k.1.1 : ℤ))).val.obj U)
    (z : ((Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f (k.1.2 : ℤ))).val.obj U) :
    (kunnethIncl f m k).val.app U ((PresheafOfModules.tensorSheafUnit
        ((Scheme.Modules.pullback (pullback.fst f f)).obj (relativeDifferentialForms f (k.1.1 : ℤ)))
        ((Scheme.Modules.pullback (pullback.snd f f)).obj
          (relativeDifferentialForms f (k.1.2 : ℤ)))).app U (y ⊗ₜ z)) =
      (eqToHom (congrArg (fun j : ℕ => (deRhamAlgebras (pullback.fst f f ≫ f)).exteriorPower j)
        k.2)).val.app U
        (((relativeDifferentialFormsAlgebra (pullback.fst f f ≫ f)).mul (k.1.1 : ℤ)
          (k.1.2 : ℤ)).app U
          ((fstForms f (k.1.1 : ℤ)).val.app U y) ((sndForms f (k.1.2 : ℤ)).val.app U z)) := by
  have h1 := Stacks.Tag01VSPullbackTensor.tensorSheafMapIso_inv_val_app_tensorSheafUnit
    (Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f)
      (relativeDifferentials f) (k.1.1 : ℤ)).symm
    (Scheme.Modules.exteriorPowerPullbackIso (pullback.snd f f)
      (relativeDifferentials f) (k.1.2 : ℤ)).symm U y z
  have h2 := SheafOfModules.prodWedgeHom_unit (deRhamBoxAlgebrasLeft f f)
    (deRhamBoxAlgebrasRight f f) (deRhamAlgebras (pullback.fst f f ≫ f)) (deRhamBoxLeftMap f f)
    (deRhamBoxRightMap f f) k.1.1 k.1.2 U
    ((Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f)
      (relativeDifferentials f) (k.1.1 : ℤ)).hom.val.app U y)
    ((Scheme.Modules.exteriorPowerPullbackIso (pullback.snd f f)
      (relativeDifferentials f) (k.1.2 : ℤ)).hom.val.app U z)
  have e : kunnethIncl f m k = (deRhamBoxSummandIso f f m k).inv ≫
      SheafOfModules.prodWedgeHom (deRhamBoxAlgebrasLeft f f) (deRhamBoxAlgebrasRight f f)
        (deRhamAlgebras (pullback.fst f f ≫ f)) (deRhamBoxLeftMap f f) (deRhamBoxRightMap f f)
        k.1.1 k.1.2 ≫
      eqToHom (congrArg (fun j : ℕ => (deRhamAlgebras (pullback.fst f f ≫ f)).exteriorPower j)
        k.2) :=
    biproduct_ι_comp_deRhamBoxModuleIso_hom f f m k
  refine (congrArg (fun φ : kunnethSummand f m k ⟶ _ => φ.val.app U
    ((PresheafOfModules.tensorSheafUnit
        ((Scheme.Modules.pullback (pullback.fst f f)).obj (relativeDifferentialForms f (k.1.1 : ℤ)))
        ((Scheme.Modules.pullback (pullback.snd f f)).obj
          (relativeDifferentialForms f (k.1.2 : ℤ)))).app U (y ⊗ₜ z))) e).trans
    ((comp₃_val_app _ _ _ U _).trans ?_)
  refine congrArg ((eqToHom (congrArg (fun j : ℕ =>
    (deRhamAlgebras (pullback.fst f f ≫ f)).exteriorPower j) k.2)).val.app U) ?_
  exact (congrArg ((SheafOfModules.prodWedgeHom (deRhamBoxAlgebrasLeft f f)
    (deRhamBoxAlgebrasRight f f) (deRhamAlgebras (pullback.fst f f ≫ f)) (deRhamBoxLeftMap f f)
    (deRhamBoxRightMap f f) k.1.1 k.1.2).val.app U) h1).trans h2

/-- **A Künneth summand vanishes outside the bidegrees `(p, q)` with `p, q ≤ N`** when `X/S` is
smooth of relative dimension `N`: forms of degree `> N` vanish. -/
theorem isZero_kunnethSummand (N : ℕ) [SmoothOfRelativeDimension N f] (m : ℕ)
    (k : deRhamBoxIndex m) (hk : N < k.1.1 ∨ N < k.1.2) : IsZero (kunnethSummand f m k) := by
  rcases hk with h | h
  · have h0 := Scheme.Hom.isZero_relativeDifferentialForms_of_smoothOfRelativeDimension f N k.1.1 h
    exact AlgebraicGeometry.SheafOfModules.isZero_tensorFunctor_obj_obj_of_left
      (A := (pullback f f).sheaf) ((Scheme.Modules.pullback (pullback.fst f f)).map_isZero h0) _
  · have h0 := Scheme.Hom.isZero_relativeDifferentialForms_of_smoothOfRelativeDimension f N k.1.2 h
    exact AlgebraicGeometry.SheafOfModules.isZero_tensorFunctor_obj_obj_of_right
      (A := (pullback f f).sheaf) _ ((Scheme.Modules.pullback (pullback.snd f f)).map_isZero h0)

/-- The bidegree `(e, e + 1)` of `Ω^{2e+1}_{X ×_S X/S}`. -/
abbrev leftTopIndex (e : ℕ) : deRhamBoxIndex (e + (e + 1)) :=
  deRhamBoxIndexMk e (e + 1) (e + (e + 1)) rfl

/-- The bidegree `(e + 1, e)` of `Ω^{2e+1}_{X ×_S X/S}`. -/
abbrev rightTopIndex (e : ℕ) : deRhamBoxIndex (e + (e + 1)) :=
  deRhamBoxIndexMk (e + 1) e (e + (e + 1)) (by omega)

/-- **For `X/S` smooth of relative dimension `n = e + 1`, `Ω^{2n-1}_{X ×_S X/S}` is the direct sum
of its `(e, n)` and `(n, e)` Künneth summands.** -/
theorem kunneth_top_split (e : ℕ) [SmoothOfRelativeDimension (e + 1) f] :
    kunnethProj f _ (leftTopIndex e) ≫ kunnethIncl f _ (leftTopIndex e) +
      kunnethProj f _ (rightTopIndex e) ≫ kunnethIncl f _ (rightTopIndex e) = 𝟙 _ := by
  have hne : leftTopIndex e ≠ rightTopIndex e := by
    intro h
    have := congrArg (fun k : deRhamBoxIndex (e + (e + 1)) => k.1.1) h
    simp at this
  refine ((Fintype.sum_eq_add (f := fun k => kunnethProj f _ k ≫ kunnethIncl f _ k)
    (leftTopIndex e) (rightTopIndex e) hne ?_).symm).trans (sum_kunnethProj_incl f _)
  · intro k hk
    have hz : IsZero (kunnethSummand f _ k) := by
      refine isZero_kunnethSummand f (e + 1) _ k ?_
      by_contra hc
      push Not at hc
      have hs : k.1.1 + k.1.2 = e + (e + 1) := k.2
      rcases Nat.lt_or_ge k.1.1 (e + 1) with h1 | h1
      · refine hk.1 (Subtype.ext (Prod.ext ?_ ?_)) <;> simp <;> omega
      · refine hk.2 (Subtype.ext (Prod.ext ?_ ?_)) <;> simp <;> omega
    rw [hz.eq_of_tgt (kunnethProj f _ k) 0, zero_comp]

/-- The wedge product of `Ω^•_{X ×_S X/S}` on local sections. -/
abbrev wedgeW (i j : ℤ) (U : (pullback f f).Opensᵒᵖ) :=
  ((relativeDifferentialFormsAlgebra (pullback.fst f f ≫ f)).mul i j).app U

/-- The pulled-back forms of `pr₁^*Ω^•_{X/S}`, as a unital homomorphism from the exterior algebra
of `pr₁^*Ω_{X/S}` to `Ω^•_{X ×_S X/S}`. -/
abbrev leftFormsHom :=
  (deRhamBoxAlgebrasLeft f f).exterior_isExteriorAlgebra.map
    (deRhamAlgebras (pullback.fst f f ≫ f)).exterior_isExteriorAlgebra (deRhamBoxLeftMap f f)

/-- The pulled-back forms of `pr₂^*Ω^•_{X/S}`, as a unital homomorphism from the exterior algebra
of `pr₂^*Ω_{X/S}` to `Ω^•_{X ×_S X/S}`. -/
abbrev rightFormsHom :=
  (deRhamBoxAlgebrasRight f f).exterior_isExteriorAlgebra.map
    (deRhamAlgebras (pullback.fst f f ≫ f)).exterior_isExteriorAlgebra (deRhamBoxRightMap f f)

/-- The local section `y ⊗ z` of `pr₁^*Ωᵖ_{X/S} ⊗ pr₂^*Ω^q_{X/S}`. -/
abbrev kunnethTmul (p q : ℕ) (U : (pullback f f).Opensᵒᵖ)
    (y : ((Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f (p : ℤ))).val.obj U)
    (z : ((Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f (q : ℤ))).val.obj U) :=
  (PresheafOfModules.tensorSheafUnit
    ((Scheme.Modules.pullback (pullback.fst f f)).obj (relativeDifferentialForms f (p : ℤ)))
    ((Scheme.Modules.pullback (pullback.snd f f)).obj (relativeDifferentialForms f (q : ℤ)))).app U
      (y ⊗ₜ z)

/-- **`pr₁^*ω ∧ pr₂^*η` is the Künneth inclusion of `ω ⊗ η`.** -/
theorem wedge_fstForms_sndForms (a q : ℕ) (U : (pullback f f).Opensᵒᵖ)
    (x : ((Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f (a : ℤ))).val.obj U)
    (y : ((Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f (q : ℤ))).val.obj U) :
    wedgeW f (a : ℤ) (q : ℤ) U ((fstForms f (a : ℤ)).val.app U x)
        ((sndForms f (q : ℤ)).val.app U y) =
      (kunnethIncl f (a + q) (deRhamBoxIndexMk a q (a + q) rfl)).val.app U
        (kunnethTmul f a q U x y) :=
  (kunnethIncl_apply f (a + q) (deRhamBoxIndexMk a q (a + q) rfl) U x y).symm

/-- A unital homomorphism turns the product of the images of `eᵢ x` and `eⱼ y` into the image of
`eₙ (eₙ⁻¹ (eᵢ x * eⱼ y))`. -/
private theorem mul_app_heq_unitalHom_app_iso {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {A B : _root_.SheafOfModules.GradedAlgebra R}
    (Φ : _root_.SheafOfModules.GradedAlgebra.UnitalHom A B) {i j : ℤ}
    {Pi Pj Pn : _root_.SheafOfModules R} (ei : Pi ≅ A.piece i) (ej : Pj ≅ A.piece j)
    (en : Pn ≅ A.piece (i + j)) {U : Cᵒᵖ} (x : Pi.val.obj U) (y : Pj.val.obj U) :
    HEq ((B.mul i j).app U ((Φ.app i).val.app U (ei.hom.val.app U x))
        ((Φ.app j).val.app U (ej.hom.val.app U y)))
      ((Φ.app (i + j)).val.app U (en.hom.val.app U (en.inv.val.app U
        ((A.mul i j).app U (ei.hom.val.app U x) (ej.hom.val.app U y))))) := by
  rw [← comp₂_val_app en.inv en.hom, en.inv_hom_id]
  exact heq_of_eq (Φ.map_mul i j U _ _).symm

/-- **The product of forms pulled back along the first projection.** -/
theorem wedge_fstForms_kunnethIncl (a m : ℕ) (k : deRhamBoxIndex m) (U : (pullback f f).Opensᵒᵖ)
    (x : ((Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f (a : ℤ))).val.obj U)
    (y : ((Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f (k.1.1 : ℤ))).val.obj U)
    (z : ((Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f (k.1.2 : ℤ))).val.obj U) :
    wedgeW f (a : ℤ) (m : ℤ) U ((fstForms f (a : ℤ)).val.app U x)
        ((kunnethIncl f m k).val.app U (kunnethTmul f k.1.1 k.1.2 U y z)) =
      (kunnethIncl f (a + m) (deRhamBoxIndexMk (a + k.1.1) k.1.2 (a + m)
          (by have : k.1.1 + k.1.2 = m := k.2; omega))).val.app U
        (kunnethTmul f (a + k.1.1) k.1.2 U
          ((Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f) (relativeDifferentials f)
            ((a + k.1.1 : ℕ) : ℤ)).inv.val.app U
            (((deRhamBoxAlgebrasLeft f f).exterior.mul (a : ℤ) (k.1.1 : ℤ)).app U
              ((Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f)
                (relativeDifferentials f) (a : ℤ)).hom.val.app U x)
              ((Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f)
                (relativeDifferentials f) (k.1.1 : ℤ)).hom.val.app U y))) z) := by
  have hk : k.1.1 + k.1.2 = m := k.2
  have h₁ := kunnethIncl_apply f m k U y z
  have h₂ := kunnethIncl_apply f (a + m) (deRhamBoxIndexMk (a + k.1.1) k.1.2 (a + m)
    (by omega)) U
    ((Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f) (relativeDifferentials f)
      ((a + k.1.1 : ℕ) : ℤ)).inv.val.app U
      (((deRhamBoxAlgebrasLeft f f).exterior.mul (a : ℤ) (k.1.1 : ℤ)).app U
        ((Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f)
          (relativeDifferentials f) (a : ℤ)).hom.val.app U x)
        ((Scheme.Modules.exteriorPowerPullbackIso (pullback.fst f f)
          (relativeDifferentials f) (k.1.1 : ℤ)).hom.val.app U y))) z
  refine eq_of_heq ((mul_heq_mul _ rfl (show (m : ℤ) = (k.1.1 : ℤ) + (k.1.2 : ℤ) by omega)
    HEq.rfl (by rw [h₁]; exact eqToHom_val_app_heq_nat _ k.2 _ _)).trans ?_)
  refine ((relativeDifferentialFormsAlgebra _).mul_assoc _ _ _ U _ _ _).symm.trans ?_
  rw [h₂]
  refine HEq.trans ?_ (eqToHom_val_app_heq_nat _
    (deRhamBoxIndexMk (a + k.1.1) k.1.2 (a + m) (by omega)).2 _ _).symm
  refine mul_heq_mul _ (show (a : ℤ) + (k.1.1 : ℤ) = ((a + k.1.1 : ℕ) : ℤ) by push_cast; rfl)
    rfl ?_ HEq.rfl
  exact mul_app_heq_unitalHom_app_iso (leftFormsHom f) _ _ _ _ _

/-- **The product with a form pulled back along the second projection, on the right**, as a
heterogeneous equality with the Künneth inclusion in any degree `M = p + q + b`. -/
theorem wedge_kunnethIncl_sndForms_heq (b m : ℕ) (k : deRhamBoxIndex m) (M : ℕ)
    (hM : k.1.1 + (k.1.2 + b) = M) (U : (pullback f f).Opensᵒᵖ)
    (x : ((Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f (b : ℤ))).val.obj U)
    (y : ((Scheme.Modules.pullback (pullback.fst f f)).obj
      (relativeDifferentialForms f (k.1.1 : ℤ))).val.obj U)
    (z : ((Scheme.Modules.pullback (pullback.snd f f)).obj
      (relativeDifferentialForms f (k.1.2 : ℤ))).val.obj U) :
    HEq (wedgeW f (m : ℤ) (b : ℤ) U
        ((kunnethIncl f m k).val.app U (kunnethTmul f k.1.1 k.1.2 U y z))
        ((sndForms f (b : ℤ)).val.app U x))
      ((kunnethIncl f M (deRhamBoxIndexMk k.1.1 (k.1.2 + b) M hM)).val.app U
        (kunnethTmul f k.1.1 (k.1.2 + b) U y
          ((Scheme.Modules.exteriorPowerPullbackIso (pullback.snd f f) (relativeDifferentials f)
            ((k.1.2 + b : ℕ) : ℤ)).inv.val.app U
            (((deRhamBoxAlgebrasRight f f).exterior.mul (k.1.2 : ℤ) (b : ℤ)).app U
              ((Scheme.Modules.exteriorPowerPullbackIso (pullback.snd f f)
                (relativeDifferentials f) (k.1.2 : ℤ)).hom.val.app U z)
              ((Scheme.Modules.exteriorPowerPullbackIso (pullback.snd f f)
                (relativeDifferentials f) (b : ℤ)).hom.val.app U x))))) := by
  have hk : k.1.1 + k.1.2 = m := k.2
  have h₁ := kunnethIncl_apply f m k U y z
  have h₂ := kunnethIncl_apply f M (deRhamBoxIndexMk k.1.1 (k.1.2 + b) M hM) U y
    ((Scheme.Modules.exteriorPowerPullbackIso (pullback.snd f f) (relativeDifferentials f)
      ((k.1.2 + b : ℕ) : ℤ)).inv.val.app U
      (((deRhamBoxAlgebrasRight f f).exterior.mul (k.1.2 : ℤ) (b : ℤ)).app U
        ((Scheme.Modules.exteriorPowerPullbackIso (pullback.snd f f)
          (relativeDifferentials f) (k.1.2 : ℤ)).hom.val.app U z)
        ((Scheme.Modules.exteriorPowerPullbackIso (pullback.snd f f)
          (relativeDifferentials f) (b : ℤ)).hom.val.app U x)))
  refine (mul_heq_mul _ (show (m : ℤ) = (k.1.1 : ℤ) + (k.1.2 : ℤ) by omega) rfl
    (by rw [h₁]; exact eqToHom_val_app_heq_nat _ k.2 _ _) HEq.rfl).trans ?_
  refine ((relativeDifferentialFormsAlgebra _).mul_assoc _ _ _ U _ _ _).trans ?_
  rw [h₂]
  refine HEq.trans ?_ (eqToHom_val_app_heq_nat _
    (deRhamBoxIndexMk k.1.1 (k.1.2 + b) M hM).2 _ _).symm
  refine mul_heq_mul _ rfl (show (k.1.2 : ℤ) + (b : ℤ) = ((k.1.2 + b : ℕ) : ℤ) by push_cast; rfl)
    HEq.rfl ?_
  exact mul_app_heq_unitalHom_app_iso (rightFormsHom f) _ _ _ _ _

/-- **Morphisms out of `F ⊗ Ωᵐ_{X ×_S X/S}` are determined on the Künneth summands of the second
factor.** -/
theorem kunneth_hom_ext_right
    {F Q : _root_.SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology
      (pullback f f : Scheme.{u})) (pullback f f).sheaf)} (m : ℕ)
    {φ ψ : ((sheafTensor (pullback f f).sheaf).obj F).obj
      (relativeDifferentialForms (pullback.fst f f ≫ f) (m : ℤ)) ⟶ Q}
    (h : ∀ k, ((sheafTensor (pullback f f).sheaf).obj F).map (kunnethIncl f m k) ≫ φ =
      ((sheafTensor (pullback f f).sheaf).obj F).map (kunnethIncl f m k) ≫ ψ) : φ = ψ :=
  tensor_hom_ext_of_sum_eq_id (pullback f f).sheaf (kunnethIncl f m) (kunnethProj f m)
    (sum_kunnethProj_incl f m) h


end Kunneth

/-! ### Forms relative to a morphism `W ⟶ X` -/

section RelativeForms

variable {X W S : Scheme.{u}} (f : X ⟶ S) (H : W ⟶ X) (πW : W ⟶ S) (hH : H ≫ f = πW)

/-- The canonical map `Ω_{W/S} ⟶ Ω_{W/X}` of [Stacks, Tag 01UX], for `W` over `S` through
`H ≫ f = π_W`. -/
def toRelativeOver : relativeDifferentials πW ⟶ relativeDifferentials H :=
  eqToHom (congrArg relativeDifferentials hH.symm) ≫ toRelativeDifferentials H f

/-- **The homomorphism of algebras of forms `Ω^•_{W/S} ⟶ Ω^•_{W/X}`** extending
`Stacks.WeilDeRham.toRelativeOver`. -/
def formsToRelativeOver :
    SheafOfModules.GradedAlgebra.UnitalHom (relativeDifferentialFormsAlgebra πW)
      (relativeDifferentialFormsAlgebra H) :=
  (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials πW)).map
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials H))
    (toRelativeOver f H πW hH)

/-- The degree-`n` component `Ωⁿ_{W/S} ⟶ Ωⁿ_{W/X}` of `Stacks.WeilDeRham.formsToRelativeOver`. -/
abbrev formsToRelativeOverApp (n : ℤ) :
    relativeDifferentialForms πW n ⟶ relativeDifferentialForms H n :=
  (formsToRelativeOver f H πW hH).app n

/-- The canonical map on forms of a square over `S`, followed by the passage to forms relative to
`H`, is the canonical map on forms of the square over `X`. -/
theorem relativeDifferentialFormsMap_comp_formsToRelativeOver (r : W ⟶ X)
    (hr : r ≫ f = πW ≫ 𝟙 S) (hr' : r ≫ f = H ≫ f) (n : ℤ) :
    relativeDifferentialFormsMap r f πW (𝟙 S) hr n ≫ formsToRelativeOverApp f H πW hH n =
      relativeDifferentialFormsMap r f H f hr' n := by
  subst hH
  have h₁ := SheafOfModules.GradedAlgebra.IsExteriorAlgebra.map_app_one
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials (H ≫ f)))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials H))
    (toRelativeOver f H (H ≫ f) rfl)
  have h₂ := relativeDifferentialsMap_comp_toRelativeDifferentials r f H f hr'
  refine (congrArg (· ≫ formsToRelativeOverApp f H (H ≫ f) rfl n)
    (relativeDifferentialFormsMap_eq_pullbackComparison r f (H ≫ f) (𝟙 S) hr n)).trans ?_
  refine (SheafOfModules.GradedAlgebra.pullbackComparison_comp_unitalHom _ _ _
    (formsToRelativeOver f H (H ≫ f) rfl) n).trans ?_
  refine (SheafOfModules.GradedAlgebra.pullbackComparison_congr _ _ ?_ _ _ n).trans
    (relativeDifferentialFormsMap_eq_pullbackComparison r f H f hr' n).symm
  have h₃ : toRelativeOver f H (H ≫ f) rfl = toRelativeDifferentials H f := Category.id_comp _
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (relativeDifferentialsMap r f (H ≫ f) (𝟙 S) hr ≫ ·) h₁).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ (relativeDifferentials H).exteriorGenerator)
    ((congrArg (relativeDifferentialsMap r f (H ≫ f) (𝟙 S) hr ≫ ·) h₃).trans h₂)

/-- **The canonical map on forms of the square of a morphism with itself vanishes in positive
degree**: it factors through `Ωⁿ_{X/X} = 0`. -/
theorem relativeDifferentialFormsMap_self_eq_zero (k : W ⟶ X) (n : ℕ) (hn : 0 < n) :
    relativeDifferentialFormsMap k f k f rfl (n : ℤ) = 0 := by
  have key := relativeDifferentialFormsMap_comp (𝟙 X) k f (𝟙 X) k f (𝟙 X) f rfl rfl
    (by rw [Category.comp_id]) (n : ℤ)
  have hz : relativeDifferentialFormsMap (𝟙 X) f (𝟙 X) f rfl (n : ℤ) = 0 :=
    (Scheme.Hom.isZero_relativeDifferentialForms_of_smoothOfRelativeDimension (𝟙 X) 0 n
      hn).eq_of_tgt _ _
  rw [hz, Functor.map_zero, zero_comp, comp_zero] at key
  have h : ∀ (k' : W ⟶ X) (hk : k' = k) (h : k' ≫ f = k ≫ f),
      relativeDifferentialFormsMap k' f k f h (n : ℤ) = 0 →
        relativeDifferentialFormsMap k f k f rfl (n : ℤ) = 0 := by
    rintro k' rfl h hz
    exact hz
  exact h _ (Category.comp_id k) _ key

/-- The passage to forms relative to `H` kills the forms pulled back along `H` in positive
degree. -/
theorem relativeDifferentialFormsMap_comp_formsToRelativeOver_self (hr : H ≫ f = πW ≫ 𝟙 S)
    (n : ℕ) (hn : 0 < n) :
    relativeDifferentialFormsMap H f πW (𝟙 S) hr (n : ℤ) ≫
      formsToRelativeOverApp f H πW hH (n : ℤ) = 0 :=
  (relativeDifferentialFormsMap_comp_formsToRelativeOver f H πW hH H hr rfl (n : ℤ)).trans
    (relativeDifferentialFormsMap_self_eq_zero f H n hn)

variable (G : W ⟶ X) (hpb : IsPullback G H f f)

include hpb in
/-- The canonical map `G^*Ωⁿ_{X/S} ⟶ Ωⁿ_{W/X}` of a cartesian square is an isomorphism. -/
theorem isIso_relativeDifferentialFormsMap_of_isPullback (n : ℤ) :
    IsIso (relativeDifferentialFormsMap G f H f hpb.w n) :=
  isIso_relativeDifferentialFormsMap G f H f hpb.w
    (isIso_relativeDifferentialsMap_of_isPullback G H f f hpb) n

/-- **The projection `Ωⁿ_{W/S} ⟶ G^*Ωⁿ_{X/S}`** for a cartesian square `W = X ×_S X` with
projections `G` and `H`: the passage to forms relative to `H`, followed by the inverse of the
base change isomorphism `G^*Ωⁿ_{X/S} ≅ Ωⁿ_{W/X}`. It retracts the pullback of forms along `G`
(`relativeDifferentialFormsMap_comp_relativeProjection`) and kills the forms pulled back along
`H` in positive degree. -/
def relativeProjection (n : ℤ) :
    relativeDifferentialForms πW n ⟶
      (Scheme.Modules.pullback G).obj (relativeDifferentialForms f n) :=
  haveI := isIso_relativeDifferentialFormsMap_of_isPullback f H G hpb n
  formsToRelativeOverApp f H πW hH n ≫ inv (relativeDifferentialFormsMap G f H f hpb.w n)

/-- `Stacks.WeilDeRham.relativeProjection` retracts the pullback of forms along `G`. -/
theorem relativeDifferentialFormsMap_comp_relativeProjection (hr : G ≫ f = πW ≫ 𝟙 S) (n : ℤ) :
    relativeDifferentialFormsMap G f πW (𝟙 S) hr n ≫ relativeProjection f H πW hH G hpb n =
      𝟙 _ := by
  have := isIso_relativeDifferentialFormsMap_of_isPullback f H G hpb n
  unfold relativeProjection
  rw [← Category.assoc, relativeDifferentialFormsMap_comp_formsToRelativeOver f H πW hH G hr hpb.w,
    IsIso.hom_inv_id]

/-- The canonical map of a square `X ⟶ W ⟶ X` through a morphism `i` with `i ≫ H = f ≫ σ` is
`i^*` of the passage to relative differentials followed by the canonical map of the square over
`X`. -/
theorem pullback_map_toRelativeOver_comp (i : X ⟶ W) (σ : S ⟶ X) (hiH : i ≫ H = f ≫ σ)
    (hi : i ≫ πW = f ≫ 𝟙 S) :
    (Scheme.Modules.pullback i).map (toRelativeOver f H πW hH) ≫
        relativeDifferentialsMap i H f σ hiH = relativeDifferentialsMap i πW f (𝟙 S) hi := by
  subst hH
  refine (isRelativeDifferentialsMap_iff_eq i (H ≫ f) f (𝟙 S) hi _).mp fun U h => ?_
  have h₁ := (isRelativeDifferentialsMap_iff_eq i H f σ hiH _).mpr rfl U h
  rw [Adjunction.homEquiv_naturality_left]
  refine Eq.trans (comp₂_val_app _ _ _ _) (Eq.trans ?_ h₁)
  exact congrArg _ ((congrArg (fun φ => (Scheme.Modules.Hom.app φ U)
    ((universalRelativeDerivation (H ≫ f)).d h)) (Category.id_comp
      (toRelativeDifferentials H f))).trans (toRelativeDifferentials_app_d H f U h))

include hpb in
/-- The canonical map `i^*Ω_{W/X} ⟶ Ω_{X/S}` along a section `i` of `G` is an isomorphism. -/
theorem isIso_relativeDifferentialsMap_section (i : X ⟶ W) (σ : S ⟶ X) (hiG : i ≫ G = 𝟙 X)
    (hiH : i ≫ H = f ≫ σ) : IsIso (relativeDifferentialsMap i H f σ hiH) := by
  have key := relativeDifferentialsMap_pullbackComp G i f H f f σ (𝟙 S) hpb.w hiH
    (by rw [hiG, Category.id_comp, Category.comp_id])
  have : IsIso (i ≫ G) := by rw [hiG]; infer_instance
  have hI : IsIso (relativeDifferentialsMap (i ≫ G) f f (𝟙 S)
      (by rw [hiG, Category.id_comp, Category.comp_id])) :=
    isIso_relativeDifferentialsMap_of_isIso _ _ _ _ _
  have : IsIso (relativeDifferentialsMap G f H f hpb.w) :=
    isIso_relativeDifferentialsMap_of_isPullback G H f f hpb
  rw [key] at hI
  have : IsIso ((Scheme.Modules.pullback i).map (relativeDifferentialsMap G f H f hpb.w) ≫
      relativeDifferentialsMap i H f σ hiH) :=
    IsIso.of_isIso_comp_left ((Scheme.Modules.pullbackComp i G).inv.app (relativeDifferentials f)) _
  exact IsIso.of_isIso_comp_left ((Scheme.Modules.pullback i).map
    (relativeDifferentialsMap G f H f hpb.w)) _

/-- The comparison `Ωⁿ_{X/S} ⟶ i^*G^*Ωⁿ_{X/S}` correcting the pullback of forms along a section
`i` of `G` into the pullback of `Stacks.WeilDeRham.relativeProjection`. -/
def sectionComparison (i : X ⟶ W) (σ : S ⟶ X) (hiG : i ≫ G = 𝟙 X) (hiH : i ≫ H = f ≫ σ)
    (n : ℤ) :
    relativeDifferentialForms f n ⟶ (Scheme.Modules.pullback i).obj
      ((Scheme.Modules.pullback G).obj (relativeDifferentialForms f n)) :=
  haveI := isIso_relativeDifferentialFormsMap i H f σ hiH
    (isIso_relativeDifferentialsMap_section f H G hpb i σ hiG hiH) n
  haveI := isIso_relativeDifferentialFormsMap_of_isPullback f H G hpb n
  inv (relativeDifferentialFormsMap i H f σ hiH n) ≫
    (Scheme.Modules.pullback i).map (inv (relativeDifferentialFormsMap G f H f hpb.w n))

/-- **The pullback of `Stacks.WeilDeRham.relativeProjection` along a section `i` of `G` factors
through the pullback of forms along `i`**: `i^*π = (i^*Ωⁿ_{W/S} ⟶ Ωⁿ_{X/S}) ≫ κ`. -/
theorem pullback_map_relativeProjection (i : X ⟶ W) (σ : S ⟶ X) (hiG : i ≫ G = 𝟙 X)
    (hiH : i ≫ H = f ≫ σ) (hi : i ≫ πW = f ≫ 𝟙 S) (n : ℤ) :
    (Scheme.Modules.pullback i).map (relativeProjection f H πW hH G hpb n) =
      relativeDifferentialFormsMap i πW f (𝟙 S) hi n ≫
        sectionComparison f H G hpb i σ hiG hiH n := by
  have := isIso_relativeDifferentialFormsMap i H f σ hiH
    (isIso_relativeDifferentialsMap_section f H G hpb i σ hiG hiH) n
  have := isIso_relativeDifferentialFormsMap_of_isPullback f H G hpb n
  have hT : (Scheme.Modules.pullback i).map (formsToRelativeOverApp f H πW hH n) ≫
      relativeDifferentialFormsMap i H f σ hiH n =
        relativeDifferentialFormsMap i πW f (𝟙 S) hi n := by
    refine (congrArg (_ ≫ ·)
      (relativeDifferentialFormsMap_eq_pullbackComparison i H f σ hiH n)).trans ?_
    refine (modulePullback_map_comp_pullbackComparison i.toLRSHom.toShHom _ _ _ _
      (toRelativeOver f H πW hH) ?_ n).trans
        (relativeDifferentialFormsMap_eq_pullbackComparison i πW f (𝟙 S) hi n).symm
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
      (pullback_map_toRelativeOver_comp f H πW hH i σ hiH hi))
  unfold relativeProjection sectionComparison
  rw [Functor.map_comp, ← Category.assoc, ← IsIso.eq_comp_inv _ |>.mpr hT]

/-- **Pulling back along a section after `Stacks.WeilDeRham.relativeProjection` factors through
the pullback of forms**: for a class `y ∈ Hᵠ(W, Ωⁿ_{W/S})`, `i^*(π(y)) = κ(i^*y)`, where on the
right `i^*` is the pullback map on classes of forms. -/
theorem unitPullback_map_relativeProjection (i : X ⟶ W) (σ : S ⟶ X) (hiG : i ≫ G = 𝟙 X)
    (hiH : i ≫ H = f ≫ σ) (hi : i ≫ πW = f ≫ 𝟙 S) (n : ℤ) (q : ℕ)
    (y : Hgroup (structureSheafRing W.toRingedSpace) ⊤ q (relativeDifferentialForms πW n)) :
    (unitPullback i ((Scheme.Modules.pullback G).obj (relativeDifferentialForms f n)) q).hom
        ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ q).map
          (relativeProjection f H πW hH G hpb n) y) =
      (Hfunctor (structureSheafRing X.toRingedSpace) ⊤ q).map
        (sectionComparison f H G hpb i σ hiG hiH n)
        ((pullbackHgroup (CohomologyPullbackComparison.canonical i.toLRSHom.toShHom) 0 (q : ℤ) q
          (by simp) (formsBaseChangeHom i πW f (𝟙 S) hi n)).hom y) := by
  have adj := modulePullbackPushforwardAdjunction i.toLRSHom.toShHom
  have h3 : relativeProjection f H πW hH G hpb n ≫
        (modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
          ((Scheme.Modules.pullback G).obj (relativeDifferentialForms f n)) =
      formsBaseChangeHom i πW f (𝟙 S) hi n ≫
        (modulePushforward i.toLRSHom.toShHom).map (sectionComparison f H G hpb i σ hiG hiH n) := by
    refine
      ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit_naturality _).symm.trans ?_
    refine (congrArg (fun φ => (modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app _ ≫
      (modulePushforward i.toLRSHom.toShHom).map φ)
      (pullback_map_relativeProjection f H πW hH G hpb i σ hiG hiH hi n)).trans ?_
    refine (congrArg ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
      (relativeDifferentialForms πW n) ≫ ·) (Functor.map_comp (modulePushforward i.toLRSHom.toShHom)
        (relativeDifferentialFormsMap i πW f (𝟙 S) hi n)
        (sectionComparison f H G hpb i σ hiG hiH n))).trans ?_
    exact (Category.assoc _ _ _).symm
  have h1 := pullbackHgroup_eq_map_comp_of_eq
    (CohomologyPullbackComparison.canonical i.toLRSHom.toShHom) 0 (q : ℤ) q (by simp)
    (relativeProjection f H πW hH G hpb n)
    (relativeProjection f H πW hH G hpb n ≫
      (modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app _)
    ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app _) rfl
  have h2 := pullbackHgroup_naturality (CohomologyPullbackComparison.canonical i.toLRSHom.toShHom)
    0 (q : ℤ) q (by simp) (𝟙 _) (sectionComparison f H G hpb i σ hiG hiH n)
    (formsBaseChangeHom i πW f (𝟙 S) hi n)
    (formsBaseChangeHom i πW f (𝟙 S) hi n ≫
      (modulePushforward i.toLRSHom.toShHom).map (sectionComparison f H G hpb i σ hiG hiH n))
    (Category.id_comp _).symm
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h2
  refine (ConcreteCategory.congr_hom h1 y).symm.trans ?_
  refine Eq.trans ?_ (ConcreteCategory.congr_hom h2 y)
  exact congrArg (fun φ => (pullbackHgroup
    (CohomologyPullbackComparison.canonical i.toLRSHom.toShHom) 0 (q : ℤ) q (by simp) φ).hom y) h3

end RelativeForms

end Stacks.WeilDeRham

end
