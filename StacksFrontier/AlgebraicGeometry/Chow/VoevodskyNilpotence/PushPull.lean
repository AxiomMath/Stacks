module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.FlatPullbackFirstChernShift
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.IteratedChernCapBridge
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Pullback

/-!
# The push-pull step of Voevodsky nilpotence

In the proof of Stacks 0FH9 the zero cycle `αₙ = c₁(ℒ₁) ∩ ⋯ ∩ c₁(ℒₙ) ∩ [Xⁿ]` is compared with
`βₙ = c₁(𝒩)ⁿ ∩ [Sⁿ(X)]` along the finite flat `π : Xⁿ ⟶ Sⁿ(X)` of degree `n!`, where
`π^*𝒩 = (ℒ₁ ⊗ ⋯ ⊗ ℒₙ)^{⊗(n-1)!}` in `Pic(Xⁿ)`:

  `π^*βₙ = c₁(π^*𝒩)ⁿ ∩ [Xⁿ] = ((n-1)!)ⁿ (∑ᵢ c₁(ℒᵢ))ⁿ ∩ [Xⁿ] = ((n-1)!)ⁿ · n! · αₙ`,

so that `αₙ` is torsion as soon as `βₙ` is. This file proves that implication, for an arbitrary
flat `f : T ⟶ H` of relative dimension `r`, an arbitrary class `β` on `H`, an invertible `𝒩` on
`H` and a family `ℒᵢ` on `T` with `[f^*𝒩] = m • ∑ᵢ [ℒᵢ]` in `Pic(T)`, `m ≠ 0`, whose first Chern
classes square to zero: if `c₁(𝒩)ⁿ ∩ β` is torsion then so is `c₁(ℒ₀) ⋯ c₁(ℒ_{n-1}) ∩ f^*β`.
For `β = [H]` with `dim_δ H ≤ n` and the family `ℒᵢ = uᵢ^*ℒ` of pullbacks of one invertible
module from a curve, both classes are iterated cap products `Stacks.Chow.iteratedChernCapOnChow`
of fundamental classes.

## Main results

* `Stacks.Chow.isOfFinAddOrder_evalChowGraded_listProd_of_isOfFinAddOrder_pow` — the core
  statement, in the shift-operator encoding of the hinge.
* `Stacks.Chow.isOfFinAddOrder_iteratedChernCapOnChow_fundamental_of_isOfFinAddOrder` — the
  statement of Stacks 0FH9's push-pull step, for iterated cap products of fundamental classes.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 0FDX](https://stacks.math.columbia.edu/tag/0FDX)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Nat
open scoped Stacks.AlgebraicGeometry.AmpleLimit

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {T H : Scheme.{u}} (sT : T ⟶ C.S) [LocallyOfFiniteType sT]
  (sH : H ⟶ C.S) [LocallyOfFiniteType sH]

/-- **The push-pull step of Stacks 0FH9, in the shift-operator encoding.** Let `f : T ⟶ H` be
flat of relative dimension `r`, `β ∈ A_e(H)`, `𝒩` invertible on `H` and `ℒ₀, …, ℒ_{n-1}`
invertible on `T` with `[f^*𝒩] = m • ∑ᵢ [ℒᵢ]` in `Pic(T)`, `m ≠ 0`, and `c₁(ℒᵢ)² = 0`. If
`c₁(𝒩)ⁿ ∩ β` is torsion, then so is `c₁(ℒ₀) ⋯ c₁(ℒ_{n-1}) ∩ f^*β`. -/
theorem isOfFinAddOrder_evalChowGraded_listProd_of_isOfFinAddOrder_pow (f : T ⟶ H)
    [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sH = sT) (r : ℕ)
    (hrel : AlgebraicGeometry.RelativeDimension f r) (e : ℤ) (β : chowGroup C sH e) {n : ℕ}
    (N : H.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible H.sheaf.obj H.ringCatSheaf.property N]
    (L : Fin n → T.Modules)
    [hL : ∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property
      (L i)] (m : ℕ) (hm : m ≠ 0)
    (hpic : T.picardClass ((Scheme.Modules.pullback f).obj N)
      (inferInstance : AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj
        T.ringCatSheaf.property _) =
      m • ∑ i, T.picardClass (L i) (hL i))
    (hsq : ∀ i, firstChernShift C sT (e + r) (L i) (invertibleChernCapDescends C sT (L i)) *
      firstChernShift C sT (e + r) (L i) (invertibleChernCapDescends C sT (L i)) = 0)
    (htors : IsOfFinAddOrder
      (evalChowGraded C sH e β n
        (firstChernShift C sH e N (invertibleChernCapDescends C sH N) ^ n))) :
    IsOfFinAddOrder (evalChowGraded C sT (e + r)
      (flatPullbackChowOfRelativeDimension C sT sH f hf r hrel e β) n
      (List.ofFn fun i => firstChernShift C sT (e + r) (L i)
        (invertibleChernCapDescends C sT (L i))).prod) := by
  have h1 := (flatPullbackChowOfRelativeDimension C sT sH f hf r hrel (e - n)).isOfFinAddOrder
    htors
  have h2 := isOfFinAddOrder_of_heq C sT (by ring)
    (flatPullbackChowOfRelativeDimension_evalChowGraded_firstChernShift_pow C sT sH f hf r hrel N
      _ (invertibleChernCapDescends C sT _) e β n) h1
  rw [evalChowGraded_firstChernShift_pow C sT (e + r) L (fun i => invertibleChernCapDescends C sT
      (L i)) ((Scheme.Modules.pullback f).obj N) (invertibleChernCapDescends C sT _) _ m
      (firstChernShift_eq_nsmul_sum_of_picardClass C sT (e + r) _ L m hpic) hsq
      (fun i j => firstChernCapStepsCommute C sT (e + r) (L i) (L j) _ _)] at h2
  exact isOfFinAddOrder_of_nsmul_of_ne_zero
    (Nat.mul_ne_zero (pow_ne_zero n hm) n.factorial_ne_zero) h2

/-- **The push-pull step of Stacks 0FH9.** Let `π : T ⟶ H` be flat of relative dimension `r`
with `dim_δ H ≤ n`, let `𝒩` be invertible on `H`, and let `ℒᵢ = uᵢ^*ℒ`, `i < n`, be pullbacks of
one invertible module `ℒ` on a Noetherian curve `X` carrying an ample invertible module, along
morphisms `uᵢ : T ⟶ X` over the base. If `[π^*𝒩] = m • ∑ᵢ [ℒᵢ]` in `Pic(T)` with `m ≠ 0`, and

  `c₁(𝒩)ⁿ ∩ [H]_n` is torsion in `A_0(H)`,

then `c₁(ℒ₀) ∩ ⋯ ∩ c₁(ℒ_{n-1}) ∩ [T]_{n+r}` is torsion in `A_r(T)`. The fundamental classes are
taken in the degrees the iterated cap products start from, `0 + n` and `r + n`. -/
theorem isOfFinAddOrder_iteratedChernCapOnChow_fundamental_of_isOfFinAddOrder (π : T ⟶ H)
    [LocallyOfFiniteType π] [Flat π] (hπ : π ≫ sH = sT) (r : ℕ)
    (hrel : AlgebraicGeometry.RelativeDimension π r) (n : ℕ)
    (hdimH : schemeDeltaDimension C sH ≤ ((n : ℤ) : EInt))
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsNoetherian X] (A : X.Modules)
    [Stacks.Ample.IsInvertibleModule X A] (hA : Stacks.Ample.IsAmple X A)
    (hdim : topologicalKrullDim X ≤ 1) (Lx : X.Modules)
    [hLx : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property Lx]
    (u : Fin n → (T ⟶ X)) [∀ i, LocallyOfFiniteType (u i)] (hu : ∀ i, u i ≫ sX = sT)
    (N : H.Modules)
    [hN : AlgebraicGeometry.SheafOfModules.IsInvertible H.sheaf.obj H.ringCatSheaf.property N]
    (m : ℕ) (hm : m ≠ 0)
    (hpic : Stacks.SheafOfModules.pullbackPicardClass π N hN =
      m • ∑ i, Stacks.SheafOfModules.pullbackPicardClass (u i) Lx hLx)
    (htors : IsOfFinAddOrder (iteratedChernCapOnChow C sH
      (List.ofFn fun _ : Fin n => invCap C sH N) 0
      (fundamentalChowClass C sH (0 + ((List.ofFn fun _ : Fin n => invCap C sH N).length : ℤ))))) :
    IsOfFinAddOrder (iteratedChernCapOnChow C sT
      (List.ofFn fun i => invCap C sT ((Scheme.Modules.pullback (u i)).obj Lx)) r
      (fundamentalChowClass C sT
        (r + ((List.ofFn fun i => invCap C sT ((Scheme.Modules.pullback (u i)).obj Lx)).length :
          ℤ)))) := by
  have hlenH : (n : ℤ) = (n : ℤ) - n + ((List.ofFn fun _ : Fin n => invCap C sH N).length : ℤ) := by
    simp
  have hfundH : fundamentalChowClass C sH (n : ℤ) ≍
      fundamentalChowClass C sH (0 + ((List.ofFn fun _ : Fin n => invCap C sH N).length : ℤ)) := by
    rw [List.length_ofFn, zero_add]
  have hβ : IsOfFinAddOrder (evalChowGraded C sH n (fundamentalChowClass C sH n) n
      (firstChernShift C sH n N (invertibleChernCapDescends C sH N) ^ n)) := by
    rw [evalChowGraded_firstChernShift_pow_eq_iteratedChernCapOnChow C sH n
      (fundamentalChowClass C sH n) N _ n (chowGroupCast C sH hlenH _)
      (chowGroupCast_heq C sH hlenH _).symm]
    refine isOfFinAddOrder_of_heq C sH (by simp) ?_ htors
    exact iteratedChernCapOnChow_heq C sH _ (by simp)
      (hfundH.symm.trans (chowGroupCast_heq C sH hlenH _).symm)
  have hpic' : T.picardClass ((Scheme.Modules.pullback π).obj N)
      (inferInstance : AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj
        T.ringCatSheaf.property _) =
      m • ∑ i, T.picardClass ((Scheme.Modules.pullback (u i)).obj Lx)
        (inferInstance : AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj
          T.ringCatSheaf.property _) := hpic
  have hmain := isOfFinAddOrder_evalChowGraded_listProd_of_isOfFinAddOrder_pow C sT sH π hπ r
    hrel n (fundamentalChowClass C sH n) N (fun i => (Scheme.Modules.pullback (u i)).obj Lx) m hm
    hpic' (fun i => firstChernShift_mul_self_eq_zero_of_topologicalKrullDim_le_one C sX A hA hdim
      Lx (u i) sT (hu i) _ _) hβ
  rw [flatPullbackChowOfRelativeDimension_fundamentalChowClass C sT sH π hπ r hrel n hdimH] at hmain
  have hlenT : (n : ℤ) + r = (n : ℤ) + r - n + ((List.ofFn fun i =>
      invCap C sT ((Scheme.Modules.pullback (u i)).obj Lx)).length : ℤ) := by
    simp only [List.length_ofFn]; ring
  rw [evalChowGraded_prod_ofFn_firstChernShift_eq_iteratedChernCapOnChow C sT _ _
    (fun i => (Scheme.Modules.pullback (u i)).obj Lx) _ (chowGroupCast C sT hlenT _)
    (chowGroupCast_heq C sT hlenT _).symm] at hmain
  refine isOfFinAddOrder_of_heq C sT (by simp) ?_ hmain
  refine iteratedChernCapOnChow_heq C sT _ (by simp) ((chowGroupCast_heq C sT hlenT _).trans ?_)
  rw [List.length_ofFn, add_comm (r : ℤ)]

end Stacks.Chow

end
