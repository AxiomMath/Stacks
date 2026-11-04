module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilPoint
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilThreeAxioms
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData

/-!
# Axiom (A5) for de Rham cohomology

Let `k` be a field. Axiom (A5) of Weil cohomology theories ([Stacks, Section 0FID]) asks that
`H^*(Spec k) = F` and that for smooth projective `X`, `Y` over `k` the Künneth map
`H^*(X) ⊗_F H^*(Y) ⟶ H^*(X × Y)`, `a ⊗ b ↦ p^*a ∪ q^*b`, be an isomorphism. For de Rham
cohomology with its data (D0), (D1), (D2') `Stacks.DeRhamWeil.deRhamFirstChernClassData k`
(Section 0FWC), the first half is `Stacks.DeRhamWeil.bijective_algebraMap_of_isIso` and the second
is the Künneth formula of [Stacks, Tag 0FMB] in cup-product form,
`Stacks.WeilDeRham.bijective_kunnethCupMap`, degree by degree. This file assembles them into
the statement of (A5) in the shape `Stacks.WeilCohomology.FirstChernClassData.KunnethAxiom`.

The Künneth map of the base is graded by total degree: on `H^i(X) ⊗ H^j(Y)` it is the degree-`n`
Künneth map of `bijective_kunnethCupMap` for `n = i + j`, the product `X × Y` being the fibre
product `X ×_k Y` with its first and second projections and the pullbacks of the data being the
pullbacks `deRhamPullLinear` along them (both by `rfl`). Regrouping
`H^*(X) ⊗ H^*(Y) = ⨁_{(i, j)} H^i(X) ⊗ H^j(Y) = ⨁_n ⨁_{i + j = n} H^i(X) ⊗ H^j(Y)`
(`Stacks.WeilDeRham.deRhamKunnethRegroup`) turns the Künneth map into the direct sum of the
degreewise ones.

## Main results

* `Stacks.WeilDeRham.kunnethMap_comp_deRhamKunnethRegroup`: the Künneth map of the base, after
  regrouping, is the direct sum over `n` of the degree-`n` Künneth maps.
* `Stacks.WeilDeRham.deRham_kunnethAxiom`: **axiom (A5) for de Rham cohomology over any field.**

## References

* [Stacks Project, Section 0FWC](https://stacks.math.columbia.edu/tag/0FWC)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FMB](https://stacks.math.columbia.edu/tag/0FMB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open scoped TensorProduct DirectSum

universe u

namespace Stacks.WeilDeRham

variable {k : Type u} [Field k] (X Y : (SmoothProjectiveScheme k).FullSubcategory)

/-- **Regrouping by total degree**:
`⨁_n ⨁_{i + j = n} H^i_{dR}(X/k) ⊗_k H^j_{dR}(Y/k) ≅ H^*_{dR}(X/k) ⊗_k H^*_{dR}(Y/k)`. -/
def deRhamKunnethRegroup :
    (⨁ n : ℤ, ⨁ ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n},
        DeRhamWeil.piece X ij.1.1 ⊗[k] DeRhamWeil.piece Y ij.1.2) ≃ₗ[k]
      DeRhamWeil.cohomology X ⊗[k] DeRhamWeil.cohomology Y :=
  (DirectSum.sigmaLcurryEquiv k).symm ≪≫ₗ
    DirectSum.lequivCongrLeft k (Equiv.sigmaFiberEquiv fun p : ℤ × ℤ => p.1 + p.2) ≪≫ₗ
    (TensorProduct.directSum k k (DeRhamWeil.piece X) (DeRhamWeil.piece Y)).symm

/-- `Stacks.WeilDeRham.deRhamKunnethRegroup` sends `x ⊗ y` in the `(i, j)`-summand of degree `n`
to `[x] ⊗ [y]`. -/
theorem deRhamKunnethRegroup_lof_lof_tmul (n : ℤ) (ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n})
    (x : DeRhamWeil.piece X ij.1.1) (y : DeRhamWeil.piece Y ij.1.2) :
    deRhamKunnethRegroup X Y (DirectSum.lof k _ _ n (DirectSum.lof k _ _ ij (x ⊗ₜ y))) =
      DirectSum.of (DeRhamWeil.piece X) ij.1.1 x ⊗ₜ DirectSum.of (DeRhamWeil.piece Y) ij.1.2 y := by
  obtain ⟨⟨i, j⟩, rfl⟩ := ij
  have h₁ : (DirectSum.sigmaLcurryEquiv k (δ := fun n (ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n}) =>
        DeRhamWeil.piece X ij.1.1 ⊗[k] DeRhamWeil.piece Y ij.1.2)).symm
      (DirectSum.lof k ℤ (fun n => ⨁ ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n},
        DeRhamWeil.piece X ij.1.1 ⊗[k] DeRhamWeil.piece Y ij.1.2) (i + j)
        (DirectSum.lof k {ij : ℤ × ℤ // ij.1 + ij.2 = i + j}
          (fun ij => DeRhamWeil.piece X ij.1.1 ⊗[k] DeRhamWeil.piece Y ij.1.2)
          ⟨(i, j), rfl⟩ (x ⊗ₜ y))) =
      DirectSum.lof k (Σ n : ℤ, {ij : ℤ × ℤ // ij.1 + ij.2 = n})
        (fun p => DeRhamWeil.piece X p.2.1.1 ⊗[k] DeRhamWeil.piece Y p.2.1.2)
        (Sigma.mk (i + j) (⟨(i, j), rfl⟩ : {ij : ℤ × ℤ // ij.1 + ij.2 = i + j})) (x ⊗ₜ y) := by
    rw [LinearEquiv.symm_apply_eq]
    exact (DFinsupp.sigmaCurry_single (δ := fun n (ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n}) =>
      DeRhamWeil.piece X ij.1.1 ⊗[k] DeRhamWeil.piece Y ij.1.2)
      (Sigma.mk (i + j) (⟨(i, j), rfl⟩ : {ij : ℤ × ℤ // ij.1 + ij.2 = i + j})) (x ⊗ₜ y)).symm
  refine (LinearEquiv.trans_apply _).trans ?_
  refine (congrArg _ (LinearEquiv.trans_apply _)).trans ?_
  rw [h₁]
  exact (congrArg (TensorProduct.directSum k k (DeRhamWeil.piece X) (DeRhamWeil.piece Y)).symm
    (DirectSum.lequivCongrLeft_lof k (e := Equiv.sigmaFiberEquiv fun p : ℤ × ℤ => p.1 + p.2)
      (M := fun p : Σ n : ℤ, {ij : ℤ × ℤ // ij.1 + ij.2 = n} =>
        DeRhamWeil.piece X p.2.1.1 ⊗[k] DeRhamWeil.piece Y p.2.1.2)
      (i := Sigma.mk (i + j) (⟨(i, j), rfl⟩ : {ij : ℤ × ℤ // ij.1 + ij.2 = i + j}))
      (k := (i, j)) rfl (x ⊗ₜ y) (x ⊗ₜ y) rfl)).trans
    (TensorProduct.directSum_symm_lof_tmul k k i x j y)

/-- The direct sum over `n` of the degree-`n` de Rham Künneth maps of
`Stacks.WeilDeRham.kunnethCupMap`. -/
def deRhamKunnethSum :
    (⨁ n : ℤ, ⨁ ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n},
        DeRhamWeil.piece X ij.1.1 ⊗[k] DeRhamWeil.piece Y ij.1.2) →ₗ[k]
      DeRhamWeil.cohomology (prod X Y) :=
  DirectSum.toModule k ℤ _ fun n =>
    DirectSum.lof k ℤ (DeRhamWeil.piece (prod X Y)) n ∘ₗ kunnethCupMap X.obj.hom Y.obj.hom n

/-- **The Künneth map of the base is, after regrouping, the sum of the degreewise de Rham Künneth
maps**: the pullbacks of the data along the projections of `X × Y = X ×_k Y` are the pullbacks
`deRhamPullLinear` of `kunnethCupMap`, and the product of `H^i` and `H^j` lands in `H^{i + j}`. -/
theorem kunnethMap_comp_deRhamKunnethRegroup :
    (DeRhamWeil.deRhamFirstChernClassData k).kunnethMap X Y ∘ₗ
        (deRhamKunnethRegroup X Y).toLinearMap = deRhamKunnethSum X Y := by
  refine DirectSum.linearMap_ext k fun n => DirectSum.linearMap_ext k fun ij =>
    TensorProduct.ext' fun x y => ?_
  change (DeRhamWeil.deRhamFirstChernClassData k).kunnethMap X Y (deRhamKunnethRegroup X Y
      (DirectSum.lof k ℤ _ n (DirectSum.lof k _ _ ij (x ⊗ₜ y)))) =
    deRhamKunnethSum X Y (DirectSum.lof k ℤ _ n (DirectSum.lof k _ _ ij (x ⊗ₜ y)))
  rw [deRhamKunnethSum, DirectSum.toModule_lof]
  refine (congrArg ((DeRhamWeil.deRhamFirstChernClassData k).kunnethMap X Y)
    (deRhamKunnethRegroup_lof_lof_tmul X Y n ij x y)).trans ?_
  refine Eq.trans ?_ (congrArg (DirectSum.lof k ℤ (DeRhamWeil.piece (prod X Y)) n)
    (kunnethCupMap_lof_tmul X.obj.hom Y.obj.hom n ij x y)).symm
  change DeRhamWeil.pullback (fst X Y) (DirectSum.of _ ij.1.1 x) *
      DeRhamWeil.pullback (snd X Y) (DirectSum.of _ ij.1.2 y) = _
  rw [DeRhamWeil.pullback_of, DeRhamWeil.pullback_of, DirectSum.of_mul_of]
  obtain ⟨⟨i, j⟩, rfl⟩ := ij
  rfl

/-- **The de Rham Künneth map is bijective** in the shape of the base:
`H^*_{dR}(X/k) ⊗_k H^*_{dR}(Y/k) ⟶ H^*_{dR}(X × Y/k)`, `a ⊗ b ↦ p^*a ∪ q^*b`. -/
theorem bijective_deRham_kunnethMap :
    Function.Bijective ((DeRhamWeil.deRhamFirstChernClassData k).kunnethMap X Y) := by
  have := (isProjective X).isProper
  have := (isProjective Y).isProper
  let e : (⨁ n : ℤ, ⨁ ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n},
        DeRhamWeil.piece X ij.1.1 ⊗[k] DeRhamWeil.piece Y ij.1.2) ≃ₗ[k]
      DeRhamWeil.cohomology (prod X Y) :=
    DFinsupp.mapRange.linearEquiv fun n =>
      LinearEquiv.ofBijective (kunnethCupMap X.obj.hom Y.obj.hom n)
        (bijective_kunnethCupMap X.obj.hom Y.obj.hom n)
  have he : deRhamKunnethSum X Y = e.toLinearMap := by
    refine DirectSum.linearMap_ext k fun n => LinearMap.ext fun t => ?_
    change deRhamKunnethSum X Y (DirectSum.lof k ℤ _ n t) = e (DirectSum.lof k ℤ _ n t)
    rw [deRhamKunnethSum, DirectSum.toModule_lof]
    exact (DFinsupp.mapRange_single (f := fun n => ⇑(LinearEquiv.ofBijective
      (kunnethCupMap X.obj.hom Y.obj.hom n) (bijective_kunnethCupMap X.obj.hom Y.obj.hom n)))
      (hf := fun n => map_zero _)).symm
  exact (Function.Bijective.of_comp_iff _ (deRhamKunnethRegroup X Y).bijective).1
    (show Function.Bijective ⇑((DeRhamWeil.deRhamFirstChernClassData k).kunnethMap X Y ∘ₗ
      (deRhamKunnethRegroup X Y).toLinearMap) from
      ((kunnethMap_comp_deRhamKunnethRegroup X Y).trans he) ▸ e.bijective)

variable (k) in
/-- **Axiom (A5) for de Rham cohomology** ([Stacks, Section 0FWC], axiom (A5) of
[Stacks, Section 0FID]): over any field `k`, `H^*_{dR}(Spec(k)/k) = k` and for smooth projective
`X`, `Y` over `k` the Künneth map `H^*_{dR}(X/k) ⊗_k H^*_{dR}(Y/k) ⟶ H^*_{dR}(X × Y/k)`,
`a ⊗ b ↦ p^*a ∪ q^*b`, is bijective. -/
theorem deRham_kunnethAxiom : (DeRhamWeil.deRhamFirstChernClassData k).KunnethAxiom := by
  refine ⟨?_, bijective_deRham_kunnethMap⟩
  have : IsIso (point k).obj.hom := by
    change IsIso (𝟙 (Spec (.of k)))
    infer_instance
  exact DeRhamWeil.bijective_algebraMap_of_isIso (point k)

end Stacks.WeilDeRham

end
