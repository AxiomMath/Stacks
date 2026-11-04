module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.ChainTowerDeRham07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PthRootCompletedTheorem
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionComparisonDegreewise

/-!
# One completed `p`-th root extension, and the completed forms of a completion

Two results on completed divided power forms:

* **one step**: along a single completed `p`-th root extension `D → D'` of
  [Stacks, Lemma 60.25.3, Tag 07N1], the cones of the base change maps of completed de Rham
  complexes of integrable modules are killed by `p` — this is the conclusion `e ∘ c = p`,
  `c ∘ e = p - d h - h d`, `h ∘ c = 0` of
  `Crystalline.PthRootExtension.exists_homotopyInverse_completedPthRootExtension`;
* **the completed forms of a completion**: the comparison of the completed forms of a divided
  power ring with those of its completion is bijective, [Stacks, Lemma 60.20.1, Tag 07KK] in every
  exterior degree, read off `Crystalline.bijective_mapAddHom_of_tmul_ιMulti`.

## Main results

* `Crystalline.genuineBaseChangeConeKilled07Q9_completedPrimeStep` — one step.
* `Crystalline.CompletedDeRham.bijective_completionFormsMap07Q9` — the comparison of forms is
  bijective.

## References

* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
-/

@[expose] public noncomputable section

open DividedPowers CategoryTheory
open scoped TensorProduct

universe u

namespace Crystalline

open CompletedDeRham

section Step

variable (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime] [Algebra (IntegersAtPrime p) A]
  (B : DividedPowerRing.{u}) [Algebra A (B : Type u)] (hp : p ≠ 0)
  (hB : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u)))) (lam : (B : Type u))

omit [Fact (Nat.Prime p)] [Algebra (IntegersAtPrime p) A] in
/-- The comparison `Crystalline.PthRootExtension.completedPrimeFormsMap` of forms along `B → D'`
is the comparison of completed forms along the structure map. -/
theorem completedPrimeFormsMap_eq_genuineFormsMap07Q9 (i : ℕ)
    (ω : completedDividedPowerForms p A B.dividedPowers i) :
    genuineFormsMap07Q9 p A (B : Type u) B.dividedPowers
        (completedPrimeStep07Q9 B p hp hB lam : Type u)
        (completedPrimeStep07Q9 B p hp hB lam).dividedPowers
        (IsScalarTower.toAlgHom A (B : Type u) (completedPrimeStep07Q9 B p hp hB lam : Type u))
        (isDPMorphism_completedPrimeStep07Q9 A B p hp hB lam) (fun _ ↦ rfl) i ω =
      PthRootExtension.completedPrimeFormsMap A B p lam hp hB i ω := by
  have hcomp : IsScalarTower.toAlgHom A (B : Type u)
      (completedPrimeStep07Q9 B p hp hB lam : Type u) =
      (PthRootExtension.genuineAlgHom A B p lam).comp (PthRootExtension.primeAlgHom A B p lam) :=
    AlgHom.ext fun b ↦ (AdicCompletion.algebraMap_apply (S := (B : Type u)) _ b).trans (by simp)
  have hgf := IsDPMorphism.comp _ (PthRootExtension.isDPMorphism_genuineAlgHom A B p lam hp hB)
    (PthRootExtension.isDPMorphism_primeAlgHom A B p lam hp)
  refine (completedMapDifferentialForms_congr p A _ _ hcomp
    (isDPMorphism_completedPrimeStep07Q9 A B p hp hB lam) hgf i ω).trans ?_
  refine (completedMapDifferentialForms_comp p A B.dividedPowers _
    (PthRootExtension.primeAlgHom A B p lam)
    (PthRootExtension.isDPMorphism_primeAlgHom A B p lam hp)
    _ (PthRootExtension.genuineAlgHom A B p lam)
    (PthRootExtension.isDPMorphism_genuineAlgHom A B p lam hp hB) hgf i ω).trans ?_
  refine Eq.trans ?_ (PthRootExtension.completedPrimeFormsMap_apply A B p lam hp hB i ω).symm
  refine Eq.trans ?_ (PthRootExtension.genuineCompletedFormsMap_eq A B p lam hp hB i _).symm
  exact congrArg _ (PthRootExtension.primeCompletedFormsMap_eq A B p lam hp i ω).symm

/-- **One completed `p`-th root extension**: along `D → D' = (D[z]⟨ξ⟩/(ξ - (z^p - λ)))^∧`, with
the genuine completed forms of `D` and of `D'`, the cones of the base change maps of completed
de Rham complexes of integrable modules are killed by `p`, by
[Stacks, Lemma 60.25.3, Tag 07N1]. -/
theorem genuineBaseChangeConeKilled07Q9_completedPrimeStep :
    GenuineBaseChangeConeKilled07Q9 p A (B : Type u) B.dividedPowers
      (completedPrimeStep07Q9 B p hp hB lam : Type u)
      (completedPrimeStep07Q9 B p hp hB lam).dividedPowers
      (IsScalarTower.toAlgHom A (B : Type u) (completedPrimeStep07Q9 B p hp hB lam : Type u))
      (isDPMorphism_completedPrimeStep07Q9 A B p hp hB lam) (fun _ ↦ rfl) (p : ℤ) := by
  intro M _ _ nabla hint hsq hsq'
  obtain ⟨-, hsqT, -, e, h, he, hec, h0, hs, hhc⟩ :=
    PthRootExtension.exists_homotopyInverse_completedPthRootExtension A p B hB lam M nabla hint
  refine coneKilledNat07Q9_baseChange_congr p _ _ M _ _ _ _ _ _ _ nabla _ _ _ _ hsq _
    (PthRootExtension.completedPrimeFormsMap A B p lam hp hB)
    (completedPrimeFormsMap_eq_genuineFormsMap07Q9 A p B hp hB lam) _
    (PthRootExtension.completedPrimeFormsMap_differential A B p lam hp hB) _ _
    (PthRootExtension.completedPrimeFormsMap_wedge A B p lam hp hB)
    (PthRootExtension.completedPrimeFormsMap_deRham A B p lam hp hB) hsq' hsqT ?_
  exact coneKilledNat07Q9_baseChange_of_data p _ _ M _ _ _ _ _ _ _ _ nabla _ _ _ _ _ _ _ hsq hsqT
    p e h he hec h0 hs hhc

end Step

namespace CompletedDeRham

section FormsBijective

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type u} [CommRing B] [Algebra A B] {J : Ideal B}
  (hJ : DividedPowers J) (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))

/-- The `B̂`-linear identification `(B̂ ⊗_B B) ⊗_{B̂} X ≅ X`. -/
def unitTensorEquiv07Q9 (X : Type u) [AddCommGroup X]
    [Module (AdicCompletion (pAdicIdeal (A := B) p) B) X] :
    ((AdicCompletion (pAdicIdeal (A := B) p) B ⊗[B] B) ⊗[AdicCompletion (pAdicIdeal (A := B) p) B]
        X) ≃ₗ[AdicCompletion (pAdicIdeal (A := B) p) B] X :=
  (TensorProduct.congr (TensorProduct.AlgebraTensorModule.rid B
      (AdicCompletion (pAdicIdeal (A := B) p) B) (AdicCompletion (pAdicIdeal (A := B) p) B))
    (LinearEquiv.refl _ X)).trans (TensorProduct.lid _ X)

/-- The identification `(B̂ ⊗_B B) ⊗_{B̂} X ≅ X` on a pure tensor. -/
theorem unitTensorEquiv07Q9_tmul (X : Type u) [AddCommGroup X]
    [Module (AdicCompletion (pAdicIdeal (A := B) p) B) X]
    (c : AdicCompletion (pAdicIdeal (A := B) p) B) (b : B) (x : X) :
    unitTensorEquiv07Q9 p X ((c ⊗ₜ[B] b) ⊗ₜ x) = (b • c) • x := by
  simp [unitTensorEquiv07Q9]

/-- The comparison of the degree-one differentials only depends on the algebra map. -/
theorem mapDifferentialsOfDPMorphism_congr07Q9 {C : Type u} [CommRing C] [Algebra A C]
    {K : Ideal C} (ε : DividedPowers K) {f g : B →ₐ[A] C} (h : f = g)
    (hf : IsDPMorphism hJ ε f.toRingHom) (hg : IsDPMorphism hJ ε g.toRingHom)
    (x : dividedPowerDifferentials (A := A) hJ) :
    mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := hJ) ε f hf x =
      mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := hJ) ε g hg x := by
  subst h; rfl

/-- The completion of an additive map underlying a linear equivalence is bijective. -/
theorem bijective_mapAddHom_linearEquiv07Q9 (R : Type u) [CommRing R] {X Y : Type u}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] (e : X ≃ₗ[R] Y) :
    Function.Bijective (PAdicCompletion.mapAddHom p R R e.toLinearMap.toAddMonoidHom) := by
  rw [PAdicCompletion.mapAddHom_eq_adicCompletionMap]
  exact (AdicCompletion.congr (pAdicIdeal (A := R) p) e).bijective

/-- The uncompleted comparison `Ω^i_{B/A,δ} → Ω^i_{B̂/A,γ̂}` along the completion map. -/
abbrev completionFormsRaw07Q9 (i : ℕ) :
    dividedPowerDifferentialForms (A := A) hJ i
      →ₛₗ[(completionDPAlgHom (A := A) (B := B) p).toRingHom]
      dividedPowerDifferentialForms (A := A) (completedDividedPowers J hJ p hp).1 i :=
  mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := hJ)
    (completedDividedPowers J hJ p hp).1 (completionDPAlgHom (A := A) (B := B) p)
    (completionDPAlgHom_isDPMorphism (A := A) _ hJ p hp) i

/-- The degreewise comparison of `Crystalline.bijective_mapAddHom_of_tmul_ιMulti` for the module
`B`: `b ⊗ ω ↦ (1 ⊗ 1) ⊗ b ν(ω)`. -/
def completionFormsPhi07Q9 (i : ℕ) :
    (B ⊗[B] dividedPowerDifferentialForms (A := A) hJ i) →+
      ((AdicCompletion (pAdicIdeal (A := B) p) B ⊗[B] B) ⊗[AdicCompletion (pAdicIdeal (A := B) p) B]
        dividedPowerDifferentialForms (A := A) (completedDividedPowers J hJ p hp).1 i) :=
  (unitTensorEquiv07Q9 p (B := B) _).symm.toLinearMap.toAddMonoidHom.comp
    ((completionFormsRaw07Q9 p A hJ hp i).toAddMonoidHom.comp
      (TensorProduct.lid B _).toLinearMap.toAddMonoidHom)

/-- The degreewise comparison on a tensor of a wedge. -/
theorem completionFormsPhi07Q9_wedge (i : ℕ) (n : B)
    (v : Fin i → dividedPowerDifferentials (A := A) hJ) :
    completionFormsPhi07Q9 p A hJ hp i (n ⊗ₜ[B] exteriorPower.ιMulti B i v) =
      ((1 : AdicCompletion (pAdicIdeal (A := B) p) B) ⊗ₜ[B] n) ⊗ₜ[AdicCompletion
        (pAdicIdeal (A := B) p) B] exteriorPower.ιMulti _ i
          (completionDifferentialsMap (A := A) J hJ p hp ∘ v) := by
  have hv : (completionDifferentialsMap (A := A) J hJ p hp ∘ v) = fun j ↦
      mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := hJ)
        (completedDividedPowers J hJ p hp).1 (completionDPAlgHom (A := A) (B := B) p)
        (completionDPAlgHom_isDPMorphism (A := A) _ hJ p hp) (v j) :=
    funext fun j ↦ mapDifferentialsOfDPMorphism_congr07Q9 A hJ _ rfl _ _ (v j)
  refine (LinearEquiv.symm_apply_eq (unitTensorEquiv07Q9 p (B := B) _)).2 ?_
  refine Eq.trans ?_ (unitTensorEquiv07Q9_tmul p (B := B) _ 1 n _).symm
  have h1 : completionFormsRaw07Q9 p A hJ hp i (TensorProduct.lid B _
      (n ⊗ₜ[B] exteriorPower.ιMulti B i v)) =
      completionFormsRaw07Q9 p A hJ hp i (n • exteriorPower.ιMulti B i v) :=
    congrArg _ (TensorProduct.lid_tmul _ _)
  refine h1.trans ?_
  refine ((completionFormsRaw07Q9 p A hJ hp i).map_smulₛₗ n _).trans ?_
  refine congrArg₂ (· • ·) ((Algebra.algebraMap_eq_smul_one n).trans rfl) ?_
  rw [hv]
  exact mapDifferentialFormsOfDPMorphism_ιMulti (A := A) (J := J) (delta := hJ)
    (completedDividedPowers J hJ p hp).1 (completionDPAlgHom (A := A) (B := B) p)
    (completionDPAlgHom_isDPMorphism (A := A) _ hJ p hp) i v

/-- The completed comparison of forms is the completion of the uncompleted comparison, as an
additive map. -/
theorem completionFormsMap07Q9_eq_mapAddHom (i : ℕ) :
    (completionFormsMap07Q9 p A hJ hp i).toAddMonoidHom =
      PAdicCompletion.mapAddHom p B _ (completionFormsRaw07Q9 p A hJ hp i).toAddMonoidHom := by
  refine PAdicCompletion.mapAddHom_eq_of_val p B _ _ _ fun n z y hz ↦ ?_
  show adicQuotientMap (completionFormsRaw07Q9 p A hJ hp i) _ n (z.val n) = _
  rw [hz]
  rfl

/-- The uncompleted comparison factors through the degreewise comparison of
`Crystalline.bijective_mapAddHom_of_tmul_ιMulti`. -/
theorem completionFormsRaw07Q9_eq (i : ℕ) :
    (completionFormsRaw07Q9 p A hJ hp i).toAddMonoidHom =
      (unitTensorEquiv07Q9 p (B := B) _).toLinearMap.toAddMonoidHom.comp
        ((completionFormsPhi07Q9 p A hJ hp i).comp
          (TensorProduct.lid B _).symm.toLinearMap.toAddMonoidHom) :=
  AddMonoidHom.ext fun y ↦ by
    show _ = unitTensorEquiv07Q9 p (B := B) _ ((unitTensorEquiv07Q9 p (B := B) _).symm
      (completionFormsRaw07Q9 p A hJ hp i (TensorProduct.lid B _
        ((TensorProduct.lid B _).symm y))))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rfl

/-- **[Stacks, Lemma 60.20.1, Tag 07KK] for the completed forms**: the comparison
`Ω̂^i_{B/A,δ} → Ω̂^i_{B̂/A,γ̂}` of the completed forms of a divided power ring with those of its
completion is bijective.  It is, up to the identifications `X ≅ B ⊗_B X` and
`(B̂ ⊗_B B) ⊗_{B̂} Y ≅ Y`, the completion of the degreewise comparison of
`Crystalline.bijective_mapAddHom_of_tmul_ιMulti` for the module `B`. -/
theorem bijective_completionFormsMap07Q9 [Fact p.Prime] [Algebra (IntegersAtPrime p) A]
    (i : ℕ) : Function.Bijective (completionFormsMap07Q9 p A hJ hp i) := by
  have hbij := bijective_mapAddHom_of_tmul_ιMulti (A := A) J hJ p hp B i
    (completionFormsPhi07Q9 p A hJ hp i) (completionFormsPhi07Q9_wedge p A hJ hp i)
  let Bc := AdicCompletion (pAdicIdeal (A := B) p) B
  let β := (unitTensorEquiv07Q9 p (B := B)
    (dividedPowerDifferentialForms (A := A) (completedDividedPowers J hJ p hp).1 i))
  let ℓ := (TensorProduct.lid B (dividedPowerDifferentialForms (A := A) hJ i)).symm
  have h2 := (PAdicCompletion.mapAddHom_comp p B Bc Bc
      ((completionFormsPhi07Q9 p A hJ hp i).comp ℓ.toLinearMap.toAddMonoidHom)
      β.toLinearMap.toAddMonoidHom).trans
    (congrArg (fun F ↦ (PAdicCompletion.mapAddHom p Bc Bc β.toLinearMap.toAddMonoidHom).comp F)
      (PAdicCompletion.mapAddHom_comp p B B Bc ℓ.toLinearMap.toAddMonoidHom
        (completionFormsPhi07Q9 p A hJ hp i)))
  have h := ((completionFormsMap07Q9_eq_mapAddHom p A hJ hp i).trans
    (congrArg (PAdicCompletion.mapAddHom p B Bc) (completionFormsRaw07Q9_eq p A hJ hp i))).trans h2
  have key : (completionFormsMap07Q9 p A hJ hp i : _ → _) =
      PAdicCompletion.mapAddHom p Bc Bc β.toLinearMap.toAddMonoidHom ∘
        (PAdicCompletion.mapAddHom p B Bc (completionFormsPhi07Q9 p A hJ hp i) ∘
          PAdicCompletion.mapAddHom p B B ℓ.toLinearMap.toAddMonoidHom) :=
    funext fun x ↦ DFunLike.congr_fun h x
  rw [key]
  exact (bijective_mapAddHom_linearEquiv07Q9 p Bc β).comp
    (hbij.comp (bijective_mapAddHom_linearEquiv07Q9 p B ℓ))

end FormsBijective

end CompletedDeRham

end Crystalline

end
