module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.PairingBijective
public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceElementUnique
public import StacksFrontier.RingTheory.TraceElement.BaseChange
public import StacksFrontier.RingTheory.TraceElement.Construction
public import StacksFrontier.RingTheory.TraceElement.Existence
public import StacksFrontier.RingTheory.TraceElement.FiniteFlat
public import StacksFrontier.RingTheory.TraceElement.Independence
public import StacksFrontier.RingTheory.TraceElement.TargetLocalization

/-!
# The Noether different is the image of evaluation at the trace element

For a flat quasi-finite homomorphism of Noetherian rings, the isomorphism of the diagonal
annihilator with the dual of the relative dualizing module carries multiplication of an element
of the annihilator to evaluation at the trace element. Consequently the Noether different is the
image of evaluation at the trace element.

## Main definitions

* `Stacks.Discriminant.dualizingModule.traceElement` is the trace element of the relative
  dualizing module.

## Main results

* `Stacks.Discriminant.eq_traceElement_of_isTraceElement` and
  `Stacks.Discriminant.dualizingModuleEquiv_traceElement`: the trace element is the unique
  element satisfying the trace condition, and it is carried along the canonical comparison of
  dualizing modules.
* `Stacks.Discriminant.noetherPairingEquiv_apply_traceElement`: **Stacks Project, Tag 0BVT**,
  the commutative diagram.
* `Stacks.Discriminant.noetherDifferent_eq_range_traceElement`: **Stacks Project, Tag 0BVT**,
  the Noether different is the image of evaluation at the trace element.

## Implementation notes

The trace element is `Stacks.Discriminant.dualizingModule.traceCandidate`, which exists for a
flat algebra with finitely presented intermediate algebra; over a Noetherian base that
hypothesis is automatic, so the trace element is defined without it and characterized by
uniqueness.

Both results are checked after localizing at a maximal ideal of the target, where an étale
neighbourhood of the base separates a finite direct factor. There the trace element is the
ordinary trace of a finite flat algebra and the pairing is plain contraction, and contracting
the trace against the diagonal annihilator returns the multiplication map; the general case
follows because the comparisons of localizations are faithfully flat.

## References

* [Stacks Project, Tag 0BVT](https://stacks.math.columbia.edu/tag/0BVT)
-/

@[expose] public section

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory

namespace Stacks.Discriminant

universe u v w x y z

attribute [local instance] algebraDualModule

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

section TraceElement

variable [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B] [Algebra.QuasiFinite A B]

/-- The trace element of the relative dualizing module of a flat quasi-finite homomorphism of
Noetherian rings. -/
noncomputable def dualizingModule.traceElement
    (F : FiniteOpenFactorization.{u, v, w} A B) : dualizingModule F :=
  letI := Module.finitePresentation_of_finite A F.middle
  dualizingModule.traceCandidate F

/-- The trace element satisfies the trace condition. -/
theorem isTraceElement_traceElement (F : FiniteOpenFactorization.{u, v, w} A B) :
    IsTraceElement.{u, v, w, x, y, z} F (dualizingModule.traceElement F) := by
  let _ := Module.finitePresentation_of_finite A F.middle
  exact isTraceElement_traceCandidate F

/-- The trace element is the unique element satisfying the trace condition. -/
theorem eq_traceElement_of_isTraceElement (F : FiniteOpenFactorization.{u, v, w} A B)
    {τ : dualizingModule F}
    (h : IsTraceElement.{u, v, w, u, max u v, max u v} F τ) :
    τ = dualizingModule.traceElement F :=
  isTraceElement_unique F h (isTraceElement_traceElement F)

/-- The canonical comparison of dualizing modules carries the trace element to the trace
element. -/
theorem dualizingModuleEquiv_traceElement (F : FiniteOpenFactorization.{u, v, w} A B)
    (G : FiniteOpenFactorization.{u, v, x} A B) :
    dualizingModuleEquiv F G (dualizingModule.traceElement F) =
      dualizingModule.traceElement G :=
  eq_traceElement_of_isTraceElement G
    ((isTraceElement_congr.{u, v, w, x, u, max u v, max u v} F G _).mp
      (isTraceElement_traceElement F))

end TraceElement

/-- Contracting the trace of a finite projective algebra against an element of the diagonal
annihilator returns its image under the multiplication map. -/
private theorem tensorContract_finiteTrace_eq_lmul
    [Module.Finite A B] [Module.Projective A B] (j : ↑(diagonalAnnihilator A B)) :
    tensorContract A B ((finiteProjectiveTrace A B).comp (Algebra.lmul A B).toLinearMap) j.1 =
      Algebra.TensorProduct.lmul' A j.1 := by
  classical
  let h := Module.Finite.exists_comp_eq_id_of_projective A B
  let n := h.choose
  let p : (Fin n → A) →ₗ[A] B := h.choose_spec.choose
  let i : B →ₗ[A] (Fin n → A) := h.choose_spec.choose_spec.choose
  have hi : p.comp i = LinearMap.id := h.choose_spec.choose_spec.choose_spec.2.2
  let b := Module.Free.chooseBasis A (Fin n → A)
  let u (k : Module.Free.ChooseBasisIndex A (Fin n → A)) : B := p (b k)
  let f (k : Module.Free.ChooseBasisIndex A (Fin n → A)) : Module.Dual A B :=
    (b.coord k).comp i
  have htrace (x : B) :
      finiteProjectiveTrace A B ((Algebra.lmul A B).toLinearMap x) = ∑ k, f k (x * u k) := by
    rw [finiteProjectiveTrace_eq_trace_of_split A B (Fin n → A) p i hi,
      LinearMap.trace_eq_matrix_trace A b]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    show b.coord k (i ((Algebra.lmul A B).toLinearMap x (p (b k)))) = _
    rfl
  have hcontract (z : B ⊗[A] B) :
      (∑ k, u k * tensorContract A B (f k) z) = (Algebra.TensorProduct.lmul' A) z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z t hz ht =>
        calc
          (∑ k, u k * tensorContract A B (f k) (z + t)) =
              ∑ k, u k * (tensorContract A B (f k) z + tensorContract A B (f k) t) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [map_add]
          _ = (∑ k, u k * tensorContract A B (f k) z) +
              ∑ k, u k * tensorContract A B (f k) t := by
                rw [← Finset.sum_add_distrib]
                exact Finset.sum_congr rfl fun k _ => mul_add _ _ _
          _ = (Algebra.TensorProduct.lmul' A) z + (Algebra.TensorProduct.lmul' A) t := by
                rw [hz, ht]
          _ = (Algebra.TensorProduct.lmul' A) (z + t) := by rw [map_add]
    | tmul x y =>
        simp only [Algebra.TensorProduct.lmul'_apply_tmul, tensorContract,
          TensorProduct.lift.tmul]
        show (∑ k, u k * ((f k x) • y)) = x * y
        have hframe : (∑ k, (f k x) • u k) = x := by
          have hp := congrArg p (b.sum_repr (i x))
          simp only [map_sum, map_smul] at hp
          have hrepr : (∑ k, (f k x) • u k) = p (i x) := by
            simpa [f, u, LinearMap.comp_apply] using hp
          exact hrepr.trans (by simpa [LinearMap.comp_apply] using LinearMap.congr_fun hi x)
        calc
          (∑ k, u k * ((f k x) • y)) = (∑ k, (f k x) • u k) * y := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun k _ => ?_
            simp only [Algebra.smul_def]
            ring
          _ = x * y := by rw [hframe]
  have htraceMap :
      (finiteProjectiveTrace A B).comp (Algebra.lmul A B).toLinearMap = ∑ k, u k • f k := by
    ext x
    show finiteProjectiveTrace A B ((Algebra.lmul A B).toLinearMap x) = _
    rw [htrace]
    simp only [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    show f k (x * u k) = (u k • f k) x
    simp [algebraDualModule_smul_apply, mul_comm]
  calc
    tensorContract A B ((finiteProjectiveTrace A B).comp (Algebra.lmul A B).toLinearMap) j.1 =
        ∑ k, tensorContract A B (u k • f k) j.1 := by
          rw [htraceMap]
          induction j.1 using TensorProduct.induction_on with
          | zero => simp [tensorContract]
          | tmul x y => simp [tensorContract, TensorProduct.lift.tmul, LinearMap.sum_apply]
          | add x y hx hy => simp [hx, hy, map_add, Finset.sum_add_distrib]
    _ = ∑ k, u k * tensorContract A B (f k) j.1 :=
          Finset.sum_congr rfl fun k _ =>
            tensorContract_smul_functional A B (f k) (u k) j
    _ = Algebra.TensorProduct.lmul' A j.1 := hcontract j.1

section FiniteTarget

variable [IsNoetherianRing A] [IsNoetherianRing B] [Module.Finite A B] [Module.Flat A B]
  [Algebra.QuasiFinite A B]

/-- For the self factorization of a finite flat algebra the pairing with the trace element is
the multiplication map. -/
private theorem noetherPairing_apply_traceElement_selfFactorization
    (j : ↑(diagonalAnnihilator A B)) :
    noetherPairing (selfFactorization A B)
        (dualizingModule.traceElement (selfFactorization A B)) j =
      Algebra.TensorProduct.lmul' A j.1 := by
  have : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  have : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  have hchosen : finiteFlatTraceElement A B =
      dualizingModule.traceElement (selfFactorization A B) :=
    eq_traceElement_of_isTraceElement (selfFactorization A B)
      (isTraceElement_finiteFlatTraceElement A B)
  rw [← hchosen]
  have h := noetherPairing_selfFactorization_tmul
    ((finiteProjectiveTrace A B).comp (Algebra.lmul A B).toLinearMap) 1 j
  refine h.trans ?_
  rw [one_mul]
  exact tensorContract_finiteTrace_eq_lmul j

/-- For a finite flat algebra the pairing with the trace element is the multiplication map, for
any finite-open factorization. -/
private theorem noetherPairing_apply_traceElement_of_finiteTarget
    (F : FiniteOpenFactorization.{u, v, w} A B) (j : ↑(diagonalAnnihilator A B)) :
    noetherPairing F (dualizingModule.traceElement F) j =
      Algebra.TensorProduct.lmul' A j.1 := by
  have h := noetherPairing_naturality F (selfFactorization A B)
    (dualizingModule.traceElement F) j
  rw [dualizingModuleEquiv_traceElement F (selfFactorization A B)] at h
  exact h.symm.trans (noetherPairing_apply_traceElement_selfFactorization j)

end FiniteTarget

section Localization

variable {Bg : Type v} [CommRing Bg] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
  [Algebra.FiniteType A B]

/-- The image of an element of the diagonal annihilator in the diagonal annihilator of an away
localization of the target. -/
noncomputable def diagonalAnnihilatorLocalize (g : B) [IsLocalization.Away g Bg]
    (j : ↑(diagonalAnnihilator A B)) : ↑(diagonalAnnihilator A Bg) :=
  diagonalAnnihilatorTargetEquiv A B Bg
    (specMap_ulift_isOpenImmersion_localizationAway g) (1 ⊗ₜ[B] j)

/-- As an element of `Bg ⊗[A] Bg`, `diagonalAnnihilatorLocalize g j` is the base change of
`1 ⊗ₜ j` along `B → Bg`. -/
@[simp]
theorem diagonalAnnihilatorLocalize_coe (g : B) [IsLocalization.Away g Bg]
    (j : ↑(diagonalAnnihilator A B)) :
    (diagonalAnnihilatorLocalize (Bg := Bg) g j : Bg ⊗[A] Bg) =
      diagonalAnnihilatorBaseChange A B Bg (1 ⊗ₜ[B] j) := rfl

/-- `diagonalAnnihilatorLocalize g` sends `0` to `0`. -/
theorem diagonalAnnihilatorLocalize_zero (g : B) [IsLocalization.Away g Bg] :
    diagonalAnnihilatorLocalize (A := A) (Bg := Bg) g 0 = 0 := by
  apply Subtype.ext
  simp [diagonalAnnihilatorLocalize_coe]

/-- `diagonalAnnihilatorLocalize g` is additive. -/
theorem diagonalAnnihilatorLocalize_add (g : B) [IsLocalization.Away g Bg]
    (j k : ↑(diagonalAnnihilator A B)) :
    diagonalAnnihilatorLocalize (Bg := Bg) g (j + k) =
      diagonalAnnihilatorLocalize (Bg := Bg) g j +
        diagonalAnnihilatorLocalize (Bg := Bg) g k := by
  apply Subtype.ext
  simp [diagonalAnnihilatorLocalize_coe, TensorProduct.tmul_add]

/-- The base change of `y ⊗ j` to `Bg ⊗[A] Bg` is `y` times the image of `j`. -/
private theorem diagonalAnnihilatorBaseChange_tmul_coe {B' : Type*} [CommRing B'] [Algebra A B']
    [Algebra B' Bg] [IsScalarTower A B' Bg] (y : Bg) (j : ↑(diagonalAnnihilator A B')) :
    (diagonalAnnihilatorBaseChange A B' Bg (y ⊗ₜ[B'] j) : Bg ⊗[A] Bg) =
      y • Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B' Bg)
        (IsScalarTower.toAlgHom A B' Bg) j.1 := by
  simp only [diagonalAnnihilatorBaseChange, TensorProduct.AlgebraTensorModule.lift_tmul,
    LinearMap.toSpanSingleton_apply]
  rfl

/-- The multiplication map commutes with localizing the diagonal annihilator. -/
theorem lmul_diagonalAnnihilatorLocalize (g : B) [IsLocalization.Away g Bg]
    (j : ↑(diagonalAnnihilator A B)) :
    Algebra.TensorProduct.lmul' A (diagonalAnnihilatorLocalize (Bg := Bg) g j).1 =
      algebraMap B Bg (Algebra.TensorProduct.lmul' A j.1) := by
  rw [diagonalAnnihilatorLocalize_coe, diagonalAnnihilatorBaseChange_tmul_coe, one_smul]
  exact AlgHom.congr_fun (Algebra.TensorProduct.ext
    (AlgHom.ext fun _ => by simp) (AlgHom.ext fun _ => by simp) :
      (Algebra.TensorProduct.lmul' A).comp (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom A B Bg) (IsScalarTower.toAlgHom A B Bg)) =
      (IsScalarTower.toAlgHom A B Bg).comp (Algebra.TensorProduct.lmul' A)) j.1

/-- The canonical pairing commutes with an away localization of the target. -/
theorem noetherPairing_localize [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra.QuasiFinite A B] (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (ω : dualizingModule F) (j : ↑(diagonalAnnihilator A B)) :
    algebraMap B Bg (noetherPairing F ω j) =
      noetherPairing (locFact (Bg := Bg) g F)
        (localizedModule_dualizingModule_equiv g F (locFact (Bg := Bg) g F)
          (TensorProduct.mk B Bg (dualizingModule F) (1 : Bg))
          (inferInstance : IsLocalizedModule (Submonoid.powers g)
            (TensorProduct.mk B Bg (dualizingModule F) (1 : Bg)))
          (TensorProduct.mk B Bg (dualizingModule F) (1 : Bg) ω))
        (diagonalAnnihilatorLocalize (A := A) (B := B) (Bg := Bg) g j) := by
  let localizationMap : dualizingModule F →ₗ[B] Bg ⊗[B] dualizingModule F :=
    TensorProduct.mk B Bg _ 1
  let hM : IsLocalizedModule (Submonoid.powers g) localizationMap := inferInstance
  let G := locFact (Bg := Bg) g F
  let eω := localizedModule_dualizingModule_equiv g F G localizationMap hM
  let _ : Algebra F.middle Bg := Algebra.compHom Bg (algebraMap F.middle B)
  let _ : IsScalarTower F.middle B Bg :=
    IsScalarTower.of_algebraMap_eq' (by rw [Algebra.compHom_algebraMap_eq])
  let _ : IsScalarTower A F.middle Bg := IsScalarTower.of_algebraMap_eq' (by
    ext a
    calc
      algebraMap A Bg a = algebraMap B Bg (algebraMap A B a) :=
        IsScalarTower.algebraMap_apply A B Bg a
      _ = algebraMap B Bg (algebraMap F.middle B (algebraMap A F.middle a)) := by
        rw [IsScalarTower.algebraMap_apply A F.middle B])
  let eJ := diagonalAnnihilatorBaseChangeEquiv F
  have he0 : eJ 0 = 0 := map_zero eJ
  have headd : ∀ z t, eJ (z + t) = eJ z + eJ t := fun z t => map_add eJ z t
  induction ω using dualizingModule.induction_on generalizing j with
  | zero => simp only [map_zero, LinearMap.zero_apply, map_zero]
  | add ω η hω hη =>
      simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) (hω j) (hη j)
  | tmul φ y₀ =>
      obtain ⟨z, rfl⟩ := eJ.surjective j
      induction z using TensorProduct.induction_on with
      | zero =>
          rw [he0, map_zero, map_zero, diagonalAnnihilatorLocalize_zero, map_zero]
      | add z t hz ht =>
          rw [headd, map_add, map_add, diagonalAnnihilatorLocalize_add, map_add, hz, ht]
      | tmul y j' =>
          have hr : ∀ c : G.middle,
              algebraMap B Bg (algebraMap F.middle B
                ((AlgEquiv.refl : G.middle ≃ₐ[A] F.middle) c)) = algebraMap G.middle Bg c :=
            fun c => IsScalarTower.algebraMap_apply F.middle B Bg c
          have hω' := localizedModule_dualizingModule_equiv_tmul g F G localizationMap hM
            (AlgEquiv.refl : G.middle ≃ₐ[A] F.middle) hr φ y₀
          have hF : (eJ (y ⊗ₜ[F.middle] j') : B ⊗[A] B) =
              diagonalAnnihilatorBaseChange A F.middle B (y ⊗ₜ[F.middle] j') := rfl
          have hJ : (diagonalAnnihilatorLocalize (A := A) (B := B) (Bg := Bg) g
                (eJ (y ⊗ₜ[F.middle] j')) : Bg ⊗[A] Bg) =
              diagonalAnnihilatorBaseChange A F.middle Bg
                ((algebraMap B Bg y) ⊗ₜ[F.middle] j') := by
            rw [diagonalAnnihilatorLocalize_coe, diagonalAnnihilatorBaseChange_tmul_coe,
              one_smul, hF, diagonalAnnihilatorBaseChange_tmul_coe,
              diagonalAnnihilatorBaseChange_tmul_coe]
            have hcomp : ∀ z : F.middle ⊗[A] F.middle,
                Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B Bg)
                    (IsScalarTower.toAlgHom A B Bg)
                  (y • Algebra.TensorProduct.map (IsScalarTower.toAlgHom A F.middle B)
                    (IsScalarTower.toAlgHom A F.middle B) z) =
                  algebraMap B Bg y • Algebra.TensorProduct.map
                    (IsScalarTower.toAlgHom A F.middle Bg)
                    (IsScalarTower.toAlgHom A F.middle Bg) z := by
              intro z
              induction z using TensorProduct.induction_on with
              | zero => simp
              | add z t hz ht => simpa only [map_add, smul_add] using congrArg₂ (· + ·) hz ht
              | tmul a c =>
                  simp [Algebra.TensorProduct.map_tmul, Algebra.smul_def]
                  rfl
            exact hcomp j'.1
          have h₁ : noetherPairing G
                (eω (localizationMap (dualizingModule.tmul F φ y₀)))
                (diagonalAnnihilatorLocalize (A := A) (B := B) (Bg := Bg) g
                  (eJ (y ⊗ₜ[F.middle] j'))) =
              algebraMap B Bg y₀ * algebraMap B Bg y *
                algebraMap G.middle Bg
                  (tensorContract A G.middle (φ.comp AlgEquiv.refl.toLinearMap) j'.1) := by
            rw [hω']
            exact noetherPairing_apply_of_eq_baseChange G (φ.comp AlgEquiv.refl.toLinearMap)
              (algebraMap B Bg y₀) (algebraMap B Bg y) j' _ hJ
          have h₂ : noetherPairing F (dualizingModule.tmul F φ y₀)
                (eJ (y ⊗ₜ[F.middle] j')) =
              y₀ * y * algebraMap F.middle B (tensorContract A F.middle φ j'.1) :=
            noetherPairing_apply_of_eq_baseChange F φ y₀ y j' _ hF
          rw [h₁, h₂]
          simp only [map_mul]
          rfl

end Localization

/-- The multiplication map commutes with a flat base change of the source. -/
theorem lmul_diagonalAnnihilatorBaseChange (A₁ : Type x) [CommRing A₁] [Algebra A A₁]
    [Algebra.FiniteType A B] [Module.Flat A A₁] (j : ↑(diagonalAnnihilator A B)) :
    Algebra.TensorProduct.lmul' A₁
        (diagonalAnnihilatorFlatBaseChange A B A₁ j).1 =
      Algebra.TensorProduct.includeRight (Algebra.TensorProduct.lmul' A j.1) := by
  show Algebra.TensorProduct.lmul' A₁ (envelopingBaseChange A B A₁ j.1) = _
  induction j.1 using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul x y => simp [envelopingBaseChange_tmul]

/-- An equality of images in a localization at a prime descends along a flat ring map to an
equality in the localization at the prime underneath. -/
private theorem localization_eq_of_flat {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat)
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap f) (a b : R)
    (h : algebraMap S (Localization.AtPrime q) (f a) =
      algebraMap S (Localization.AtPrime q) (f b)) :
    algebraMap R (Localization.AtPrime p) a =
      algebraMap R (Localization.AtPrime p) b := by
  let l := Localization.localRingHom p q f hpq
  let _ := l.toAlgebra
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    hf.localRingHom q p hpq
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
    inferInstanceAs (IsLocalHom l)
  have : Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply FaithfulSMul.algebraMap_injective (Localization.AtPrime p) (Localization.AtPrime q)
  show l (algebraMap R _ a) = l (algebraMap R _ b)
  simpa [l, Localization.localRingHom_to_map] using h

/-- **Stacks Project, Tag 0BVT.** Under the isomorphism induced by the canonical pairing,
multiplication of an element of the diagonal annihilator is evaluation at the trace
element. -/
@[stacks 0BVT "commutative diagram"]
theorem noetherPairingEquiv_apply_traceElement
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) (j : ↑(diagonalAnnihilator A B)) :
    noetherPairingEquiv F j (dualizingModule.traceElement F) =
      Algebra.TensorProduct.lmul' A j.1 := by
  show noetherPairing F (dualizingModule.traceElement F) j = _
  have : Algebra.FiniteType A B := finiteType_of_finiteOpenFactorization F
  apply sub_eq_zero.mp
  apply eq_zero_of_localization
  intro q hq
  let _ := hq
  let p := q.under A
  obtain ⟨A₁, hA₁, hAA₁, het, P, hP, hPp, g, hg, Q, hQ, hQP,
      hQq, hgQ, hres, hfin, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q
  let _ := hA₁
  let _ := hAA₁
  let _ := het
  let _ := hP
  let _ := hPp
  let _ := hQ
  let _ := hQP
  let _ := hfin
  let B₁ := A₁ ⊗[A] B
  let _ : Algebra B B₁ := Algebra.TensorProduct.rightAlgebra
  have : IsNoetherianRing A₁ := Algebra.FiniteType.isNoetherianRing A A₁
  have : IsNoetherianRing B₁ := Algebra.FiniteType.isNoetherianRing A₁ B₁
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let j₁ := diagonalAnnihilatorFlatBaseChange A B A₁ j
  have ht := isTraceElement_baseChange F A₁ (dualizingModule.traceElement F)
    (isTraceElement_traceElement F)
  have he := eq_traceElement_of_isTraceElement F₁ ht
  have hloc : algebraMap B₁ (Localization.Away g)
        (noetherPairing F₁ (dualizingModule.traceElement F₁) j₁) =
      algebraMap B₁ (Localization.Away g)
        (Algebra.TensorProduct.lmul' A₁ j₁.1) := by
    have hG := locFact (Bg := Localization.Away g) g F₁
    have hNoeth : IsNoetherianRing (Localization.Away g) :=
      IsLocalization.isNoetherianRing (.powers g) (Localization.Away g) inferInstance
    have hflat : Module.Flat A₁ (Localization.Away g) := Module.Flat.trans A₁ B₁ _
    have hqf : Algebra.QuasiFinite A₁ (Localization.Away g) :=
      Algebra.QuasiFinite.of_isLocalization (.powers g)
    have hfinAway : Module.Finite A₁ (Localization.Away g) := hfin
    have htl := isTraceElement_localization g F₁ (locFact (Bg := Localization.Away g) g F₁)
      (TensorProduct.mk B₁ (Localization.Away g) (dualizingModule F₁) 1) inferInstance
      (isTraceElement_traceElement F₁)
    have hel := eq_traceElement_of_isTraceElement
      (locFact (Bg := Localization.Away g) g F₁) htl
    rw [noetherPairing_localize g F₁, hel]
    exact (noetherPairing_apply_traceElement_of_finiteTarget
      (locFact (Bg := Localization.Away g) g F₁)
      (diagonalAnnihilatorLocalize g j₁)).trans
      (lmul_diagonalAnnihilatorLocalize g j₁)
  rw [← he, noetherPairing_baseChange, lmul_diagonalAnnihilatorBaseChange] at hloc
  have hunit : IsUnit (algebraMap B₁ (Localization.AtPrime Q) g) :=
    IsLocalization.map_units (Localization.AtPrime Q) (⟨g, hgQ⟩ : Q.primeCompl)
  have heq : algebraMap B₁ (Localization.AtPrime Q)
        (algebraMap B B₁ (noetherPairing F (dualizingModule.traceElement F) j)) =
      algebraMap B₁ (Localization.AtPrime Q)
        (algebraMap B B₁ (Algebra.TensorProduct.lmul' A j.1)) := by
    have h := congrArg (IsLocalization.Away.lift g hunit) hloc
    rwa [IsLocalization.Away.lift_eq g hunit, IsLocalization.Away.lift_eq g hunit] at h
  have : Module.Flat B B₁ := Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.commRight A B A₁).symm.toLinearEquiv
  have hf : (algebraMap B B₁).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have H := localization_eq_of_flat (algebraMap B B₁) hf q Q hQq.symm _ _ heq
  simpa only [map_sub, sub_eq_zero] using H

/-- **Stacks Project, Tag 0BVT.** The Noether different is the image of evaluation at the trace
element. -/
@[stacks 0BVT "image of evaluation"]
theorem noetherDifferent_eq_range_traceElement
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    (noetherDifferent A B : Set B) =
      Set.range fun φ : dualizingModule F →ₗ[B] B ↦
        φ (dualizingModule.traceElement F) := by
  have hsurj : Function.Surjective
      ((Algebra.TensorProduct.lmul' A).toRingHom : B ⊗[A] B →+* B) := fun b =>
    ⟨b ⊗ₜ[A] (1 : B), by simp [Algebra.TensorProduct.lmul'_apply_tmul]⟩
  ext b
  show b ∈ Ideal.map (Algebra.TensorProduct.lmul' A).toRingHom (diagonalAnnihilator A B) ↔ _
  rw [Ideal.mem_map_iff_of_surjective _ hsurj]
  constructor
  · rintro ⟨ξ, hξ, rfl⟩
    exact ⟨noetherPairingEquiv F ⟨ξ, hξ⟩,
      noetherPairingEquiv_apply_traceElement F ⟨ξ, hξ⟩⟩
  · rintro ⟨φ, rfl⟩
    refine ⟨((noetherPairingEquiv F).symm φ).1, ((noetherPairingEquiv F).symm φ).2, ?_⟩
    have hj := noetherPairingEquiv_apply_traceElement F ((noetherPairingEquiv F).symm φ)
    rw [LinearEquiv.apply_symm_apply] at hj
    exact hj.symm

end Stacks.Discriminant

end
