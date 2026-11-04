module

public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.DeRhamHodgeCechTransfer
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.CupContractionCech
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeCohomology.HodgeDuality
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyGradedPairingTop
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# The pairings of the graded pieces of the de Rham complex and Hodge duality

Let `X` be a smooth proper scheme over a field `k` of dimension `d`. The graded pieces of the
brutal filtration of the de Rham complex `Ω^•_{X/k}` are the sheaves `Ωᵖ[-p]`, and the pairing of
the graded pieces of bidegrees `(p, d - p)` induced by the wedge product
`Ωᵖ ⊗ Ω^{d-p} ⟶ Ωᵈ = σ^{≥d}Ω^•` is, on hypercohomology, the cup product of Hodge cohomology of
Tag 0FM4, `H^q(X, Ωᵖ) × H^{d-q}(X, Ω^{d-p}) ⟶ Hᵈ(X, Ωᵈ)`, up to the sign `(-1)^{p(d-q)}`: both
are computed by the Alexander–Whitney product of Čech cocycles. Hence a linear form on
`H^{2d}_{dR}(X/k)` which is the trace of Hodge duality (Tag 0FW4) through
`Hᵈ(X, Ωᵈ) = H^{2d}(X, Ωᵈ[-d]) ⟶ H^{2d}_{dR}(X/k)` makes all these pairings perfect. This is the
input of the five-lemma induction proving Poincaré duality, [Stacks, Tag 0FW7].

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.deRhamCoeff`: the scalars `k ⟶ Γ(X, f⁻¹𝒪_{Spec k})`.
* `AlgebraicGeometry.Scheme.Hom.formsTransfer`: `H^{q+p}(X, Ωᵖ[-p]) ≃ H^q(X, Ωᵖ)`, `k`-linearly.

## Main results

* `AlgebraicGeometry.Scheme.Hom.gradedPerfect_deRham`: **the pairings of the graded pieces are
  perfect.**

## References

* [Stacks Project, Tag 0FW7](https://stacks.math.columbia.edu/tag/0FW7)
* [Stacks Project, Tag 0FW4](https://stacks.math.columbia.edu/tag/0FW4)
* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf (abSections SectionRing)
open Stacks.Cech.Hypercohomology
open Stacks.Cohomology.GlobalKunneth (baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open Stacks.Duality (sheafCohomology singleModule)

universe u

namespace AlgebraicGeometry.Scheme.Hom

open scoped Stacks.StandardDerivedModel
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules Stacks.SheafOfModules.Tensor.ringSheaf
  AlgebraicGeometry.SheafOfModules.deRhamComplexPlus

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The scalars of de Rham cohomology over `k`**: `k ⟶ Γ(Spec k, 𝒪) ⟶ Γ(X, f⁻¹𝒪_{Spec k})`. -/
def deRhamCoeff :
    k →+* SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingSheaf f)) ⊤ :=
  (inverseImageGlobalSections f).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-- The scalars of de Rham cohomology act on `𝒪_X` through the structure morphism. -/
theorem inverseImageRingTop_deRhamCoeff (c : k) :
    inverseImageRingTop f (deRhamCoeff f c) = Stacks.Duality.globalRingHom f c :=
  congrArg (fun φ => φ ((Scheme.ΓSpecIso (.of k)).inv c))
    (congrArg CommRingCat.Hom.hom (inverseImageGlobalSections_comp_inverseImageStructureMap_app f))

/-- **The identification of the two models of the cohomology of a sheaf of modules**, as an
additive equivalence. -/
def hodgeTheta (F : X.Modules) (n : ℤ) :
    hypercohomology X.sheaf (singlePlus X.sheaf F 0) n ≃+ cohomologyModule (singleModule F) n :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) n).mapIso
    ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIsoBaseSections
      X.toRingedSpace).app (singlePlus X.sheaf F 0))).toLinearEquiv.toAddEquiv

/-- `hodgeTheta F n` is the comparison map from hypercohomology of `F` placed in degree `0` to
the cohomology module of `F`. -/
theorem hodgeTheta_apply (F : X.Modules) (n : ℤ)
    (x : hypercohomology X.sheaf (singlePlus X.sheaf F 0) n) :
    hodgeTheta F n x =
      Stacks.Cech.CupProductSquare.hypercohomologyToCohomologyModule X.toRingedSpace
        (singlePlus X.sheaf F 0) n x :=
  rfl

variable [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- **`H^{q+p}(X, Ωᵖ[-p]) ≃ H^q(X, Ωᵖ)`, `k`-linearly**: the hypercohomology of a term of the de
Rham complex placed in its degree, computed in sheaves of `f⁻¹𝒪_{Spec k}`-modules, is the Hodge
cohomology group of Tag 0FM4. -/
def formsTransfer (p q : ℕ) :
    hypercohomologyK (inverseImageRingSheaf f) (deRhamCoeff f)
        (singlePlus (inverseImageRingSheaf f) ((deRhamPlus f).obj.X (p : ℤ)) p) ((q : ℤ) + p) ≃ₗ[k]
      sheafCohomology f (relativeDifferentialForms f (p : ℤ)) q :=
  AddEquiv.toLinearEquiv
    (show hypercohomologyK (inverseImageRingSheaf f) (deRhamCoeff f)
        (singlePlus (inverseImageRingSheaf f) ((deRhamPlus f).obj.X (p : ℤ)) p) ((q : ℤ) + p) ≃+
      sheafCohomology f (relativeDifferentialForms f (p : ℤ)) q from
      (deRhamTermTransfer f p q).trans (hodgeTheta (relativeDifferentialForms f (p : ℤ)) q))
    (fun c x => by
      change hodgeTheta _ q (deRhamTermTransfer f p q (deRhamCoeff f c • x)) =
        (Stacks.Duality.globalRingHom f c) • hodgeTheta _ q (deRhamTermTransfer f p q x)
      exact (congrArg (hodgeTheta (relativeDifferentialForms f (p : ℤ)) q)
        (deRhamTermTransfer_smul f p q (deRhamCoeff f c) x)).trans
        ((congrArg (fun r : SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⊤ =>
          hodgeTheta (relativeDifferentialForms f (p : ℤ)) q (r • deRhamTermTransfer f p q x))
          (inverseImageRingTop_deRhamCoeff f c)).trans
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) q).map
          ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIsoBaseSections
            X.toRingedSpace).hom.app _)).hom.map_smul _ _)))

/-- `formsTransfer f p q` is `deRhamTermTransfer f p q` followed by the comparison map from
hypercohomology of `Ωᵖ` placed in degree `0` to the cohomology module of `Ωᵖ`. -/
theorem formsTransfer_apply (p q : ℕ)
    (x : hypercohomologyK (inverseImageRingSheaf f) (deRhamCoeff f)
        (singlePlus (inverseImageRingSheaf f) ((deRhamPlus f).obj.X (p : ℤ)) p) ((q : ℤ) + p)) :
    formsTransfer f p q x =
      Stacks.Cech.CupProductSquare.hypercohomologyToCohomologyModule X.toRingedSpace
        (singlePlus X.sheaf (relativeDifferentialForms f (p : ℤ)) 0) q
        (deRhamTermTransfer f p q x) :=
  rfl

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- **The wedge product of forms is, on sections, the sheaf-tensor pairing followed by the wedge
product `Ωᵃ ⊗ Ωᵇ ⟶ Ωⁿ`.** -/
theorem bilinearPairing_formsWedge (a b n : ℤ) (h : a + b = n) :
    bilinearPairing (formsWedge f a b n h) =
      Stacks.Cech.SheafTensorPairing.sheafTensorPairing X.sheaf ⊤ (relativeDifferentialForms f a)
          (relativeDifferentialForms f b) ≫
        (Stacks.Cech.ModuleCupProduct.sectionsFunctor X.sheaf ⊤).map (formsMul f a b n h) := by
  refine NatTrans.ext (funext fun Z => ModuleCat.hom_ext (TensorProduct.ext' fun x y => ?_))
  have hu := SheafOfModules.GradedAlgebra.mulSheaf_unit (relativeDifferentialFormsAlgebra f) a b
    (op Z.unop.left) x y
  show (eqToHom (congrArg (relativeDifferentialForms f) h)).val.app (op Z.unop.left)
      (((relativeDifferentialFormsAlgebra f).mul a b).app (op Z.unop.left) x y) =
    (eqToHom (congrArg (relativeDifferentialForms f) h)).val.app (op Z.unop.left)
      (((relativeDifferentialFormsAlgebra f).mulSheaf a b).val.app (op Z.unop.left)
        ((PresheafOfModules.tensorSheafUnit ((relativeDifferentialFormsAlgebra f).piece a)
          ((relativeDifferentialFormsAlgebra f).piece b)).app (op Z.unop.left) (x ⊗ₜ y)))
  rw [hu]

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- **The pairings of Hodge duality in arbitrary complementary bidegrees** `(a, b)`, `a + b = d`,
and degrees `(q, j)`, `q + j = d`, are perfect when those of [Stacks, Tag 0FW4] are. -/
theorem isPerfPair_hodgeCup_of_hodgePairing (d : ℕ)
    (tH : sheafCohomology f (relativeDifferentialForms f d) d →ₗ[k] k)
    (hH : ∀ p q : ℤ, (hodgePairing f d tH p q).IsPerfPair) (a b q j : ℤ) (h : a + b = d)
    (hm : q + j = d) : ((hodgeCup f a b d h q j d hm).compr₂ tH).IsPerfPair := by
  obtain rfl : b = d - a := by omega
  obtain rfl : j = d - q := by omega
  exact hH a q

/-- **The top-degree identification carries the cup product of the graded pieces to the cup
product of Hodge cohomology**, up to the sign `(-1)^{aq'}`. -/
theorem formsTransfer_cup (a b d q q' : ℕ) (hab : (a : ℤ) + b = d) (hqq : q + q' = d)
    (hm : (q : ℤ) + q' = d)
    (x : hypercohomology (inverseImageRingSheaf f)
      (singlePlus (inverseImageRingSheaf f) ((deRhamPlus f).obj.X (a : ℤ)) a) ((q : ℤ) + a))
    (y : hypercohomology (inverseImageRingSheaf f)
      (singlePlus (inverseImageRingSheaf f) ((deRhamPlus f).obj.X (b : ℤ)) b) ((q' : ℤ) + b)) :
    formsTransfer f d d
        (cup (inverseImageRingSheaf f) (cechComputes_deRhamPlus_X f a)
          (cechComputes_deRhamPlus_X f b)
          (singlePairingAtTo (inverseImageRingSheaf f) a b d hab
            (bilinearPairing (deRhamWedge f a b d hab)))
          ((q : ℤ) + a) ((q' : ℤ) + b) ((d : ℤ) + d) (by subst hqq; push_cast; omega) x y) =
      (((a : ℤ) * q').negOnePow : ℤ) •
        hodgeCup f a b d hab q q' d hm (formsTransfer f a q x) (formsTransfer f b q' y) :=
  (congrArg (hodgeTheta (relativeDifferentialForms f (d : ℤ)) d)
    (deRhamTermTransfer_cup' f a b d hab q q' d hqq x y)).trans
    ((map_zsmul (hodgeTheta (relativeDifferentialForms f (d : ℤ)) d) _ _).trans
      (congrArg ((((a : ℤ) * q').negOnePow : ℤ) • ·)
        (Stacks.Duality.cupContraction_hypercohomologyToCohomologyModule' (formsMul f a b d hab)
          (formsWedge f a b d hab) (bilinearPairing_formsWedge f a b d hab)
          (cechComputes_relativeDifferentialForms f a) (cechComputes_relativeDifferentialForms f b)
          q q' d hm (deRhamTermTransfer f a q x) (deRhamTermTransfer f b q' y)).symm))

/-- **The pairings of the graded pieces of the de Rham complex are perfect.** Let `X` be smooth
of relative dimension `d` over `k`, with `X` Noetherian of dimension at most `d`, and let `tH` be
a linear form on `Hᵈ(X, Ωᵈ)` making the pairings of Hodge duality ([Stacks, Tag 0FW4]) perfect.
A linear form `t` on `H^{2d}_{dR}(X/k)` which is `tH` on the image of
`H^{2d}(X, Ωᵈ[-d]) = Hᵈ(X, Ωᵈ)` makes the pairings
`H^i(X, Ωᵃ[-a]) × H^j(X, Ωᵇ[-b]) ⟶ H^{2d}_{dR}(X/k) ⟶ k`, `a + b = d`, `i + j = 2d`, perfect.
The form `t` is read through `σ^{≤d}Ω^• = Ω^•` (`t'`). -/
theorem gradedPerfect_deRham (d : ℕ) [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (hd : ∀ n, (d : ℤ) < n → IsZero ((deRhamPlus f).obj.X n))
    (tH : sheafCohomology f (relativeDifferentialForms f d) d →ₗ[k] k)
    (hH : ∀ p q : ℤ, (hodgePairing f d tH p q).IsPerfPair)
    (t : hypercohomologyK (inverseImageRingSheaf f) (deRhamCoeff f) (deRhamPlus f) ((d : ℤ) + d)
      →ₗ[k] k)
    (t' : hypercohomologyK (inverseImageRingSheaf f) (deRhamCoeff f)
      (truncLEPlus (inverseImageRingSheaf f) (deRhamPlus f) d) ((d : ℤ) + d) →ₗ[k] k)
    (ht : ∀ z, t z = t' (hypercohomologyMapK (inverseImageRingSheaf f) (deRhamCoeff f)
      (truncLEπ (inverseImageRingSheaf f) (deRhamPlus f) d) _ z))
    (htop : ∀ z, t' (hypercohomologyMapK (inverseImageRingSheaf f) (deRhamCoeff f)
      (truncLEι (inverseImageRingSheaf f) (deRhamPlus f) d) _ z) = tH (formsTransfer f d d z))
    (a b : ℤ) (hab : a + b = d) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    GradedPerfect (deRhamCoeff f) (deRhamPlus f) (cechComputesSheaf_deRhamComplexInt_X f)
      (SheafOfModules.deRhamCechPairing (deRhamAlgebras f)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras f)))
      d hd ((d : ℤ) + d) t a b hab := by
  intro i j hij
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  have hsub : ∀ (e : ℕ) (n : ℤ), n < e ∨ (d : ℤ) < n - e →
      Subsingleton (hypercohomologyK (inverseImageRingSheaf f) (deRhamCoeff f)
        (singlePlus (inverseImageRingSheaf f) ((deRhamPlus f).obj.X e) e) n) :=
    fun e n hn => show Subsingleton (hypercohomology (inverseImageRingSheaf f)
      (singlePlus (inverseImageRingSheaf f) ((deRhamPlus f).obj.X e) e) n) from
      ModuleCat.subsingleton_of_isZero (hn.elim
        (isZero_hypercohomology_singlePlus_of_lt _ _)
        (isZero_hypercohomology_singlePlus_of_lt_sub _ _ hdim
          (e : ℤ) (cechComputes_deRhamPlus_X f e)
          ((cechComputesSheaf_deRhamComplexInt_X f e).singlePlus _ 0)))
  by_cases hi : i < a
  · have := hsub a i (.inl hi)
    have := hsub b j (.inr (by omega))
    exact LinearMap.IsPerfPair.of_subsingleton _
  by_cases hj : j < b
  · have := hsub b j (.inl hj)
    have := hsub a i (.inr (by omega))
    exact LinearMap.IsPerfPair.of_subsingleton _
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, i = q + a := ⟨(i - a).toNat, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q' : ℕ, j = q' + b := ⟨(j - b).toNat, by omega⟩
  have hqq : q + q' = d := by omega
  have hm : (q : ℤ) + q' = d := by exact_mod_cast hqq
  refine LinearMap.isPerfPair_of_addEquiv _ ((hodgeCup f a b d hab q q' d hm).compr₂ tH)
    (formsTransfer f a q).toAddEquiv (formsTransfer f b q').toAddEquiv
    (negOnePowK ((a : ℤ) * q')) (fun x y => ?_)
    (isPerfPair_hodgeCup_of_hodgePairing f d tH hH a b q q' hab hm)
  have hπ : hypercohomologyMap (inverseImageRingSheaf f)
      (truncLEπ (inverseImageRingSheaf f) (deRhamPlus f) d)
      ((d : ℤ) + d) (cup (inverseImageRingSheaf f)
        (cechComputes_singlePlus_X (deRhamPlus f) (cechComputesSheaf_deRhamComplexInt_X f) a)
        (cechComputes_singlePlus_X (deRhamPlus f) (cechComputesSheaf_deRhamComplexInt_X f) b)
        (gradedPairing (deRhamPlus f) (SheafOfModules.deRhamCechPairing (deRhamAlgebras f)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras f))) d hd a b hab)
        ((q : ℤ) + a) ((q' : ℤ) + b) ((d : ℤ) + d) hij x y) =
      hypercohomologyMap (inverseImageRingSheaf f)
        (truncLEι (inverseImageRingSheaf f) (deRhamPlus f) d)
        ((d : ℤ) + d) (cup (inverseImageRingSheaf f) (cechComputes_deRhamPlus_X f a)
          (cechComputes_deRhamPlus_X f b)
          (singlePairingAtTo (inverseImageRingSheaf f) a b d hab
            (bilinearPairing (deRhamWedge f a b d hab)))
          ((q : ℤ) + a) ((q' : ℤ) + b) ((d : ℤ) + d) hij x y) :=
    ((cup_comp (inverseImageRingSheaf f)
        (cechComputes_singlePlus_X (deRhamPlus f) (cechComputesSheaf_deRhamComplexInt_X f) a)
        (cechComputes_singlePlus_X (deRhamPlus f) (cechComputesSheaf_deRhamComplexInt_X f) b)
        _ (truncLEπ (inverseImageRingSheaf f) (deRhamPlus f) d) _ _ _ hij x y).symm.trans
      (congrArg (fun D => cup (inverseImageRingSheaf f)
        (cechComputes_singlePlus_X (deRhamPlus f) (cechComputesSheaf_deRhamComplexInt_X f) a)
        (cechComputes_singlePlus_X (deRhamPlus f) (cechComputesSheaf_deRhamComplexInt_X f) b)
        D ((q : ℤ) + a) ((q' : ℤ) + b) ((d : ℤ) + d) hij x y)
        (gradedPairing_comp_truncLEπ (deRhamPlus f) _ (d : ℤ) hd a b hab _
          (deRhamCechPairing_μ f a b d hab)))).trans
      (cup_comp (inverseImageRingSheaf f) (cechComputes_deRhamPlus_X f a)
        (cechComputes_deRhamPlus_X f b) _ (truncLEι (inverseImageRingSheaf f) (deRhamPlus f) d)
        _ _ _ hij x y)
  have hT := (ht _).trans ((congrArg t' hπ).trans ((htop _).trans
    ((congrArg tH (formsTransfer_cup f a b d q q' hab hqq hm x y)).trans (map_zsmul tH _ _))))
  show tH (hodgeCup f a b d hab q q' d hm (formsTransfer f a q x) (formsTransfer f b q' y)) =
    (negOnePowK (k := k) ((a : ℤ) * q') : k) * t (cup (inverseImageRingSheaf f)
      (cechComputes_singlePlus_X (deRhamPlus f) (cechComputesSheaf_deRhamComplexInt_X f) a)
      (cechComputes_singlePlus_X (deRhamPlus f) (cechComputesSheaf_deRhamComplexInt_X f) b)
      (gradedPairing (deRhamPlus f) (SheafOfModules.deRhamCechPairing (deRhamAlgebras f)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras f))) d hd a b hab)
      ((q : ℤ) + a) ((q' : ℤ) + b) ((d : ℤ) + d) hij x y)
  rw [hT, zsmul_eq_mul, ← mul_assoc]
  have hu :
      (negOnePowK (k := k) ((a : ℤ) * q') : k) * ((((a : ℤ) * q').negOnePow : ℤ) : k) = 1 := by
    show ((((a : ℤ) * q').negOnePow : ℤ) : k) * ((((a : ℤ) * q').negOnePow : ℤ) : k) = 1
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  rw [hu, one_mul]

end AlgebraicGeometry.Scheme.Hom

end
