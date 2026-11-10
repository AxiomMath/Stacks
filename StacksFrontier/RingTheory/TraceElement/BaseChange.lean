module

public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingBaseChange.Tower
public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceCondition
public import StacksFrontier.RingTheory.TraceElement.ProjectiveTrace

/-!
# Trace elements and base change

A trace element of the relative dualizing module of a flat quasi-finite map `A → B` of
Noetherian rings remains a trace element after a Noetherian base change `A → A₁`, under the
base-change map of Tag 0BVB.

The trace-element condition over `A₁` tests decompositions of `A₂ ⊗_{A₁} (A₁ ⊗_A B)` for
Noetherian `A₁`-algebras `A₂`. Such a test is transported to a test of the original condition
over `A` along the cancellation isomorphism `A₂ ⊗_{A₁} (A₁ ⊗_A B) ≅ A₂ ⊗_A B`. Under that
isomorphism the two base-change maps of the dualizing module agree, by Tag 0BVC, and the two
restriction maps to the finite factor agree because the two intermediate algebras act on it by
the same scalars, so the two traces correspond.

## Main results

* `Stacks.Discriminant.isTraceElement_baseChange`: Tag 0BT9, the base-changed image of a trace
  element is a trace element.

## References

* [Stacks Project, Tag 0BT9](https://stacks.math.columbia.edu/tag/0BT9)
* [Stacks Project, Tag 0BVC](https://stacks.math.columbia.edu/tag/0BVC)
-/

@[expose] public section

open scoped TensorProduct

universe u v w x s t r

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

/-- **Stacks Project, Tag 0BT9.** The image of a trace element under the base-change map of
the relative dualizing module is a trace element over the new base. -/
@[stacks 0BT9 "trace_base_change"]
theorem isTraceElement_baseChange
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B] [Algebra.QuasiFinite A B]
    [Algebra.FiniteType A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] [IsNoetherianRing A₁]
    (τ : dualizingModule F) (hτ : IsTraceElement.{u, v, w, s, t, r} F τ) :
    letI : IsNoetherianRing (A₁ ⊗[A] B) := Algebra.FiniteType.isNoetherianRing A₁ _
    IsTraceElement.{x, max x v, max x w, s, t, r}
      (FiniteOpenFactorization.baseChange F A₁) (dualizingModule.baseChange F A₁ τ) := by
  dsimp [IsTraceElement]
  intro A₂ _ _ _ C D _ _ _ _ e hfinite
  let : Algebra A A₂ := ((algebraMap A₁ A₂).comp (algebraMap A A₁)).toAlgebra
  have : IsScalarTower A A₁ A₂ := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => rfl)
  let cB := Algebra.TensorProduct.cancelBaseChange A A₁ A₂ A₂ B
  let e₂ : (A₂ ⊗[A] B) ≃ₐ[A₂] C × D := cB.symm.trans e
  obtain ⟨hp, hm, hmp, hres⟩ := hτ A₂ C D e₂ hfinite
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let Fiter := FiniteOpenFactorization.baseChange F₁ A₂
  let Fdirect := FiniteOpenFactorization.baseChange F A₂
  let cM : Fiter.middle ≃ₐ[A₂] Fdirect.middle :=
    Algebra.TensorProduct.cancelBaseChange A A₁ A₂ A₂ F.middle
  let : Algebra Fdirect.middle C :=
    ((RingHom.fst C D).comp
      (e₂.toRingEquiv.toRingHom.comp Fdirect.algebraTarget.algebraMap)).toAlgebra
  let : Algebra Fiter.middle C :=
    ((RingHom.fst C D).comp
      (e.toRingEquiv.toRingHom.comp Fiter.algebraTarget.algebraMap)).toAlgebra
  let : Algebra (A₂ ⊗[A] F.middle) (A₂ ⊗[A] B) := Fdirect.algebraTarget
  have : IsScalarTower A₂ (A₂ ⊗[A] F.middle) (A₂ ⊗[A] B) := Fdirect.scalarTower
  let cMlin := TensorProduct.AlgebraTensorModule.cancelBaseChange A A₁ A₂ A₂ F.middle
  have hcMap (m : Fiter.middle) :
      cB (algebraMap Fiter.middle (A₂ ⊗[A₁] (A₁ ⊗[A] B)) m) =
        algebraMap Fdirect.middle (A₂ ⊗[A] B) (cM m) := by
    let : Algebra (A₂ ⊗[A₁] (A₁ ⊗[A] F.middle)) (A₂ ⊗[A₁] (A₁ ⊗[A] B)) := Fiter.algebraTarget
    have : IsScalarTower A₂ (A₂ ⊗[A₁] (A₁ ⊗[A] F.middle)) (A₂ ⊗[A₁] (A₁ ⊗[A] B)) :=
      Fiter.scalarTower
    have hscalarRaw (r : A₂ ⊗[A₁] (A₁ ⊗[A] F.middle)) :
        cB (algebraMap _ _ r) = algebraMap _ _ (cMlin r) := by
      induction r using TensorProduct.inductionOn with
      | tmul a₂ z =>
        induction z using TensorProduct.inductionOn with
        | tmul a₁ m =>
          have hinner : IsScalarTower.toAlgHom A₁ F₁.middle (A₁ ⊗[A] B) (a₁ ⊗ₜ[A] m) =
              a₁ ⊗ₜ[A] algebraMap F.middle B m := by
            change (Algebra.TensorProduct.map (AlgHom.id A A₁)
              (IsScalarTower.toAlgHom A F.middle B)) (a₁ ⊗ₜ[A] m) = _
            simp [Algebra.TensorProduct.map_tmul]
          change cB ((Algebra.TensorProduct.map (AlgHom.id A₁ A₂)
              (IsScalarTower.toAlgHom A₁ F₁.middle (A₁ ⊗[A] B)))
              (a₂ ⊗ₜ[A₁] (a₁ ⊗ₜ[A] m))) =
            (Algebra.TensorProduct.map (AlgHom.id A A₂)
              (IsScalarTower.toAlgHom A F.middle B))
              (cMlin (a₂ ⊗ₜ[A₁] (a₁ ⊗ₜ[A] m)))
          rw [Algebra.TensorProduct.map_tmul (AlgHom.id A₁ A₂)
            (IsScalarTower.toAlgHom A₁ F₁.middle (A₁ ⊗[A] B)) a₂ (a₁ ⊗ₜ[A] m),
            AlgHom.id_apply, hinner]
          simp [Algebra.smul_def, cB, cMlin, Algebra.TensorProduct.map_tmul,
            Algebra.TensorProduct.cancelBaseChange_tmul]
        | add z₁ z₂ hz₁ hz₂ =>
          simp only [TensorProduct.tmul_add, map_add, hz₁, hz₂, cMlin.map_add]
      | add r₁ r₂ hr₁ hr₂ => simp only [map_add, hr₁, hr₂, cMlin.map_add]
    exact hscalarRaw m
  have hcAlg (m : Fiter.middle) :
      algebraMap Fiter.middle C m = algebraMap Fdirect.middle C (cM m) :=
    congrArg (fun z => (e z).1) <| cB.injective <| (hcMap m).trans (cB.apply_symm_apply _).symm
  have hcAlgSymm (m : Fdirect.middle) :
      algebraMap Fdirect.middle C m = algebraMap Fiter.middle C (cM.symm m) := by
    rw [hcAlg, cM.apply_symm_apply]
  let : RingHomInvPair cM.toRingHom cM.symm.toRingHom := .of_ringEquiv cM.toRingEquiv
  let : RingHomInvPair cM.symm.toRingHom cM.toRingHom := .of_ringEquiv_symm cM.toRingEquiv
  let eC : C ≃ₛₗ[cM.symm.toRingHom] C :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun m c => by
        change algebraMap Fdirect.middle C m * c = algebraMap Fiter.middle C (cM.symm m) * c
        rw [hcAlgSymm] }
  have hmfiniteIter : Module.Finite Fiter.middle C :=
    Module.Finite.of_equiv_equiv cM.symm.toRingEquiv (RingEquiv.refl C)
      (RingHom.ext fun m => (hcAlgSymm m).symm)
  have hmprojIter : Module.Projective Fiter.middle C := Module.Projective.of_equiv eC
  have htrace (f : Module.Dual A₂ Fiter.middle) (b : A₂ ⊗[A₁] (A₁ ⊗[A] B)) (c : C) :
      f (finiteProjectiveTrace Fiter.middle C (Algebra.lmul Fiter.middle C ((e b).1 * c))) =
        (f.comp cM.symm.toLinearMap) (finiteProjectiveTrace Fdirect.middle C
          (Algebra.lmul Fdirect.middle C ((e₂ (cB b)).1 * c))) := by
    have hcoeff : (e b).1 = (e₂ (cB b)).1 :=
      congrArg (fun z => (e z).1) (cB.symm_apply_apply b).symm
    have htr := finiteProjectiveTrace_congr_ringEquiv cM.toRingEquiv (fun m => (hcAlg m).symm)
      (Algebra.lmul Fiter.middle C ((e b).1 * c))
      (Algebra.lmul Fdirect.middle C ((e₂ (cB b)).1 * c)) (fun d => by simp [hcoeff])
    exact congrArg f (show finiteProjectiveTrace Fiter.middle C
        (Algebra.lmul Fiter.middle C ((e b).1 * c)) =
        cM.symm (finiteProjectiveTrace Fdirect.middle C
          (Algebra.lmul Fdirect.middle C ((e₂ (cB b)).1 * c))) from
      cM.injective (by simpa using htr))
  have hcompatIter (a : Fiter.middle) :
      algebraMap Fiter.middle C a =
        (e (algebraMap Fiter.middle (A₂ ⊗[A₁] (A₁ ⊗[A] B)) a)).1 := rfl
  have hcompatDirect (a : Fdirect.middle) :
      algebraMap Fdirect.middle C a = (e₂ (algebraMap Fdirect.middle (A₂ ⊗[A] B) a)).1 := rfl
  let RI := finiteFactorRestriction F₁ A₂ C D e hcompatIter hfinite hp hmfiniteIter hmprojIter
  let RD := finiteFactorRestriction F A₂ C D e₂ hcompatDirect hfinite hp hm hmp
  let tower := dualizingModule.baseChangeTowerEquiv F A₁ A₂
  let : Module A₂ (dualizingModule (FiniteOpenFactorization.baseChange F₁ A₂)) :=
    Module.compHom _ (algebraMap A₂ (A₂ ⊗[A₁] (A₁ ⊗[A] B)))
  let : Module A₂ (dualizingModule (FiniteOpenFactorization.baseChange F A₂)) :=
    Module.compHom _ (algebraMap A₂ (A₂ ⊗[A] B))
  have hrestr (z : dualizingModule (FiniteOpenFactorization.baseChange F₁ A₂)) :
      RI.1 z = RD.1 (tower.1 z) := by
    refine LinearMap.ext fun c => ?_
    induction z using TensorProduct.inductionOn with
    | tmul f b =>
      change RI.1 (dualizingModule.tmul Fiter f b) c =
        RD.1 (tower.1 (dualizingModule.tmul Fiter f b)) c
      rw [RI.2 f b c, tower.2 f b]
      exact (htrace f b c).trans (RD.2 (f.comp cM.symm.toLinearMap) (cB b) c).symm
    | add z₁ z₂ hz₁ hz₂ =>
      let w₁ : dualizingModule (FiniteOpenFactorization.baseChange F₁ A₂) := z₁
      let w₂ : dualizingModule (FiniteOpenFactorization.baseChange F₁ A₂) := z₂
      have hw₁ : RI.1 w₁ c = RD.1 (tower.1 w₁) c := by simpa [w₁] using hz₁
      have hw₂ : RI.1 w₂ c = RD.1 (tower.1 w₂) c := by simpa [w₂] using hz₂
      change RI.1 (w₁ + w₂) c = RD.1 (tower.1 (w₁ + w₂)) c
      rw [RI.1.map_add, tower.1.map_add, RD.1.map_add]
      exact congrArg₂ (· + ·) hw₁ hw₂
  refine ⟨hp, hmfiniteIter, hmprojIter, ?_⟩
  rw [hrestr (dualizingModule.baseChange F₁ A₂ (dualizingModule.baseChange F A₁ τ)),
    dualizingModule.baseChange_comp F A₁ A₂ τ, hres]

end Stacks.Discriminant

end
