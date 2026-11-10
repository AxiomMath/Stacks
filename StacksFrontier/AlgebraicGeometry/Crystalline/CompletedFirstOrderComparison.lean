module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsToPairs

/-!
# The first-order comparison datum over the **completed** base change

`Crystalline.FirstOrderComparison` is the comparison map of a crystal written over the
*uncompleted* base change,

`ε : M → (D ⊕ Ω) ⊗_D M`,

and that is where the finiteness hypothesis of the chapter comes from.  The module `M` of
[Stacks, Lemma 60.17.3, Tag 07JG] is the limit `lim_e Γ(T_e, ℱ)` of the sections over the finite
levels, the comparison data available are the ones at the single levels, and assembling them into
a map on `M` asks for the interchange

`(D ⊕ Ω) ⊗_D M ≅ lim_e ((D ⊕ Ω) ⊗_D M_e)`,

which is **false** as soon as `Ω` is free of infinite rank: the support of a compatible family may
grow with the level, so the comparison map is not surjective, and surjectivity is exactly what
assembling the datum consumes.  The source's own presentation is `P = A[x_i]` with an arbitrary
family of variables, so the finite case is not the source's case.

**This module restates the datum over the completed base change**

`ε : M → (D ⊕ Ω) ⊗̂_D M`,

where `(D ⊕ Ω) ⊗̂_D M` is the `p`-adic completion of `(D ⊕ Ω) ⊗_D M`.  The interchange then holds
for every `Ω` whatsoever, by
`Crystalline.tensorCompletionLevelEquiv` of
`StacksFrontier/RingTheory/AdicCompletion/InverseLimitTensorShift.lean`, and item (07JC) of the tag
— the connection with its Leibniz rule — is read off the completed datum with no basis, no
finiteness and no further hypothesis.

## Main definitions

* `Crystalline.CompletedFirstOrderTensor` — the completed base change `(D ⊕ Ω) ⊗̂_D M`.
* `Crystalline.firstOrderMul` — multiplication by an element of `D ⊕ Ω` on the base change, as a
  `D`-linear map; this is what the semilinearity clause is stated through, the completion of a
  `D`-module carrying no `D ⊕ Ω`-action of its own.
* `Crystalline.firstOrderDifferentialComm` — the differential component of the base change
  followed by the exchange of the two factors, `(D ⊕ Ω) ⊗_D M ⟶ M ⊗_D Ω`.
* `Crystalline.CompletedFirstOrderComparison` — **the comparison datum over the completed base
  change**: an additive map `M → (D ⊕ Ω) ⊗̂_D M` reducing to the canonical map `M → M̂` modulo `Ω`
  and semilinear for `p₁`.
* `Crystalline.CompletedFirstOrderComparison.completedConnection` — **item (07JC) of
  [Stacks, Lemma 60.17.3, Tag 07JG] from the completed datum**: the connection
  `∇ : M → M ⊗̂_D Ω` it determines, with the Leibniz rule.
* `Crystalline.FirstOrderComparison.toCompleted` — an uncompleted datum, completed.

## Main results

* `Crystalline.firstOrderDifferentialComm_comp_firstOrderMul_P₁` — the identity behind the
  Leibniz rule, as an equality of `D`-linear maps on the uncompleted base change.
* `Crystalline.firstOrderDifferentialComm_comp_lTensor` — the differential component of the base
  change is natural in the module, which is what makes the connection functorial.
* `Crystalline.firstOrderMul_comp_lTensor` — multiplication by an element of `D ⊕ Ω` on a base
  change is natural in the module, which is what makes the semilinearity clause checkable level by
  level.
* `Crystalline.CompletedFirstOrderComparison.completedConnection_apply` — the connection is the
  completion of the differential component of the datum.
* `Crystalline.FirstOrderComparison.completedConnection_toCompleted` — **the restatement is a
  generalisation and not a change of subject**: the connection of a completed uncompleted datum is
  the connection the uncompleted datum already had.

## Implementation notes

The clause `reduction'` is stated as an identity in `M̂` rather than in `M` on purpose: the
completed base change has no reduction map to `M` itself, and on the modules the tag is about —
which are `p`-adically complete by item (07JB) — the two readings agree.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
-/

@[expose] public section

open scoped TensorProduct

universe u v w uA

noncomputable section

namespace Crystalline

section CompletedComparison

variable (A : Type uA) [CommRing A] (D : DividedPowerRing.{u}) (g : A →+* D)
  (Omega : Type v) [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega]
  [IsCentralScalar D Omega] (d : DividedPowerDerivation A D g Omega) (p : ℕ)
  (M : Type w) [AddCommGroup M] [Module D M]

/-- **The completed base change `(D ⊕ Ω) ⊗̂_D M`**, the `p`-adic completion of the base change of
`M` along the first-order thickening of [Stacks, Tag 07J2]. -/
abbrev CompletedFirstOrderTensor : Type (max u v w) :=
  AdicCompletion (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
    (firstOrderExtension D Omega ⊗[D] M)

/-- **Multiplication by an element of `D ⊕ Ω` on the base change, as a `D`-linear map.**  The
completion of a `D`-module carries no action of `D ⊕ Ω`, so the semilinearity clause of a
completed comparison datum is stated through the functoriality of the completion applied to this
map rather than through an action. -/
def firstOrderMul (a : firstOrderExtension D Omega) :
    (firstOrderExtension D Omega ⊗[D] M) →ₗ[(D : Type u)]
      (firstOrderExtension D Omega ⊗[D] M) where
  toFun z := a • z
  map_add' z w := smul_add a z w
  map_smul' c z := by
    change a • (c • z) = c • (a • z)
    induction z using TensorProduct.inductionOn with
    | tmul b m =>
        calc a • (c • (b ⊗ₜ[D] m))
            = (a • (c • b)) ⊗ₜ[D] m := by
              rw [TensorProduct.smul_tmul' c b m, TensorProduct.smul_tmul' a (c • b) m]
          _ = (c • (a • b)) ⊗ₜ[D] m := by rw [smul_comm c a b]
          _ = c • (a • (b ⊗ₜ[D] m)) := by
              rw [TensorProduct.smul_tmul' a b m, TensorProduct.smul_tmul' c (a • b) m]
    | add x y hx hy => rw [smul_add, smul_add, smul_add, smul_add, hx, hy]

/-- `firstOrderMul D Omega M a` is multiplication by `a`. -/
@[simp] theorem firstOrderMul_apply (a : firstOrderExtension D Omega)
    (z : firstOrderExtension D Omega ⊗[D] M) :
    firstOrderMul D Omega M a z = a • z :=
  rfl

/-- **The differential component of the base change, with the two factors exchanged**:
`(D ⊕ Ω) ⊗_D M ⟶ M ⊗_D Ω`. -/
def firstOrderDifferentialComm :
    (firstOrderExtension D Omega ⊗[D] M) →ₗ[(D : Type u)] (M ⊗[D] Omega) :=
  (TensorProduct.comm (D : Type u) Omega M).toLinearMap ∘ₗ
    firstOrderDifferentialPart D Omega M

/-- `firstOrderDifferentialComm` sends `a ⊗ m` to `m ⊗ a.snd`. -/
@[simp] theorem firstOrderDifferentialComm_tmul (a : firstOrderExtension D Omega) (m : M) :
    firstOrderDifferentialComm D Omega M (a ⊗ₜ[D] m) = m ⊗ₜ[D] a.snd := by
  simp [firstOrderDifferentialComm, TensorProduct.comm_tmul]

/-- The `D`-linear map `m ↦ m ⊗ ω` for a fixed differential `ω`. -/
def tmulRight (omega : Omega) : M →ₗ[(D : Type u)] (M ⊗[D] Omega) :=
  (TensorProduct.mk (D : Type u) M Omega).flip omega

omit [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega] in
/-- `tmulRight D Omega M ω` sends `m` to `m ⊗ ω`. -/
@[simp] theorem tmulRight_apply (omega : Omega) (m : M) :
    tmulRight D Omega M omega m = m ⊗ₜ[D] omega :=
  rfl

/-- **The identity behind the Leibniz rule**, as an equality of `D`-linear maps on the uncompleted
base change: multiplying by `p₁ f` multiplies the differential component by `f` and adds the
reduction tensored with `d f`. -/
theorem firstOrderDifferentialComm_comp_firstOrderMul_P₁ (f : (D : Type u)) :
    firstOrderDifferentialComm D Omega M ∘ₗ
        firstOrderMul D Omega M (firstOrderP₁ A D g Omega d f) =
      f • firstOrderDifferentialComm D Omega M +
        tmulRight D Omega M (d f) ∘ₗ firstOrderReduction D Omega M := by
  refine LinearMap.ext fun z ↦ ?_
  change (TensorProduct.comm (D : Type u) Omega M)
      (firstOrderDifferentialPart D Omega M (firstOrderP₁ A D g Omega d f • z)) = _
  rw [firstOrderDifferentialPart_smul_P₁ A D g Omega d M f z, map_add, map_smul,
    TensorProduct.comm_tmul]
  rfl

/-- **The differential component of the base change is natural in the module.**  A `D`-linear map
`φ : M ⟶ M'` carries the differential component of the base change of `M` to the differential
component of the base change of `M'`, the two being joined by `φ ⊗ id`. -/
theorem firstOrderDifferentialComm_comp_lTensor {M' : Type w} [AddCommGroup M']
    [Module D M'] (phi : M →ₗ[(D : Type u)] M') :
    firstOrderDifferentialComm D Omega M' ∘ₗ
        LinearMap.lTensor (firstOrderExtension D Omega) phi =
      TensorProduct.map phi (LinearMap.id (R := (D : Type u)) (M := Omega)) ∘ₗ
        firstOrderDifferentialComm D Omega M := by
  refine LinearMap.ext fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
      rw [LinearMap.comp_apply, LinearMap.lTensor_tmul, firstOrderDifferentialComm_tmul,
        LinearMap.comp_apply, firstOrderDifferentialComm_tmul, TensorProduct.map_tmul]
      rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **Multiplication by an element of `D ⊕ Ω` on a base change is natural in the module.** -/
theorem firstOrderMul_comp_lTensor {M' : Type w} [AddCommGroup M'] [Module D M']
    (a : firstOrderExtension D Omega) (phi : M →ₗ[(D : Type u)] M') :
    firstOrderMul D Omega M' a ∘ₗ LinearMap.lTensor (firstOrderExtension D Omega) phi =
      LinearMap.lTensor (firstOrderExtension D Omega) phi ∘ₗ firstOrderMul D Omega M a := by
  refine LinearMap.ext fun z ↦ ?_
  change a • LinearMap.lTensor (firstOrderExtension D Omega) phi z =
    LinearMap.lTensor (firstOrderExtension D Omega) phi (a • z)
  induction z using TensorProduct.inductionOn with
  | tmul b m =>
      rw [LinearMap.lTensor_tmul, TensorProduct.smul_tmul' a b (phi m),
        TensorProduct.smul_tmul' a b m, LinearMap.lTensor_tmul]
  | add x y hx hy => rw [map_add, smul_add, smul_add, map_add, hx, hy]

/-! ### The datum -/

/-- **The first-order comparison datum of a crystal, over the completed base change.**

For a `D`-module `M` this is a map

`ε : M → (D ⊕ Ω) ⊗̂_{D, p₀} M`

which is additive, reduces to the canonical map `M → M̂` modulo `Ω`, and is semilinear for `p₁` in
the sense that `ε (f m)` is `p₁ f · ε m`, the multiplication being read through the functoriality
of the completion.

This is `Crystalline.FirstOrderComparison` with its target completed.  The completion is what
makes the datum assemblable from the finite levels for an arbitrary module of differentials: see
the module documentation. -/
structure CompletedFirstOrderComparison where
  /-- The underlying comparison map. -/
  toFun : M → CompletedFirstOrderTensor D Omega p M
  /-- The comparison map is additive. -/
  map_add' : ∀ m n : M, toFun (m + n) = toFun m + toFun n
  /-- The comparison map reduces to the canonical map `M → M̂` modulo the square-zero summand. -/
  reduction' : ∀ m : M,
    AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
        (firstOrderReduction D Omega M) (toFun m) =
      AdicCompletion.of (DividedPowers.pAdicIdeal (A := (D : Type u)) p) M m
  /-- The comparison map is semilinear for the second divided power section `p₁`. -/
  semilinear' : ∀ (f : (D : Type u)) (m : M),
    toFun (f • m) =
      AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
        (firstOrderMul D Omega M (firstOrderP₁ A D g Omega d f)) (toFun m)

namespace CompletedFirstOrderComparison

variable {A D g Omega d p M}

/-- A completed comparison datum coerces to its underlying map. -/
instance : CoeFun (CompletedFirstOrderComparison A D g Omega d p M)
    (fun _ ↦ M → CompletedFirstOrderTensor D Omega p M) where
  coe c := c.toFun

/-- A completed comparison datum is additive. -/
theorem map_add (c : CompletedFirstOrderComparison A D g Omega d p M) (m n : M) :
    c (m + n) = c m + c n :=
  c.map_add' m n

/-- A completed comparison datum reduces to the canonical map `M → M̂` modulo `Ω`. -/
theorem reduction (c : CompletedFirstOrderComparison A D g Omega d p M) (m : M) :
    AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
        (firstOrderReduction D Omega M) (c m) =
      AdicCompletion.of (DividedPowers.pAdicIdeal (A := (D : Type u)) p) M m :=
  c.reduction' m

/-- A completed comparison datum `c` satisfies `c (f • m) = p₁ f · c m`, the multiplication read
through the functoriality of the completion. -/
theorem semilinear (c : CompletedFirstOrderComparison A D g Omega d p M) (f : (D : Type u))
    (m : M) :
    c (f • m) =
      AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
        (firstOrderMul D Omega M (firstOrderP₁ A D g Omega d f)) (c m) :=
  c.semilinear' f m

/-- **Item (07JC) of [Stacks, Lemma 60.17.3, Tag 07JG] from the completed comparison datum.**

The connection `∇ : M → M ⊗̂_D Ω` is the differential component of the comparison map, read on the
completion through `Crystalline.firstOrderDifferentialComm`.  The Leibniz rule is
`Crystalline.firstOrderDifferentialComm_comp_firstOrderMul_P₁` pushed through the functoriality of
the completion, which is linear in the map it is applied to; no basis of `Ω`, no finiteness of the
coordinates and no completeness of `M` is used. -/
def completedConnection (c : CompletedFirstOrderComparison A D g Omega d p M) :
    CompletedConnection p (D : Type u) Omega (derivationFun A D g Omega d) M where
  toFun m := AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
    (firstOrderDifferentialComm D Omega M) (c m)
  map_add' m n := by rw [c.map_add m n, _root_.map_add]
  leibniz' f m := by
    rw [c.semilinear f m, AdicCompletion.map_comp_apply,
      firstOrderDifferentialComm_comp_firstOrderMul_P₁ A D g Omega d M f,
      _root_.map_add (AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)),
      LinearMap.add_apply,
      _root_.map_smul (AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)),
      LinearMap.smul_apply, ← AdicCompletion.map_comp_apply, c.reduction m,
      AdicCompletion.map_of]
    rfl

/-- The connection of a completed comparison datum `c` sends `m` to the image of `c m` under the
completion of `Crystalline.firstOrderDifferentialComm`. -/
@[simp] theorem completedConnection_apply (c : CompletedFirstOrderComparison A D g Omega d p M)
    (m : M) :
    c.completedConnection m =
      AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
        (firstOrderDifferentialComm D Omega M) (c m) :=
  rfl

end CompletedFirstOrderComparison

/-! ### An uncompleted datum, completed -/

namespace FirstOrderComparison

variable {A D g Omega d M}

/-- **An uncompleted first-order comparison datum, read over the completed base change.**  The
comparison map is followed by the canonical map to the completion; the three clauses are the
original three pushed through it. -/
def toCompleted (c : FirstOrderComparison A D g Omega d M) (p : ℕ) :
    CompletedFirstOrderComparison A D g Omega d p M where
  toFun m := AdicCompletion.of (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
    (firstOrderExtension D Omega ⊗[D] M) (c m)
  map_add' m n := by rw [c.map_add m n, _root_.map_add]
  reduction' m := by rw [AdicCompletion.map_of, c.reduction m]
  semilinear' f m := by rw [c.semilinear f m, AdicCompletion.map_of]; rfl

/-- `c.toCompleted p` sends `m` to the image of `c m` in the completion. -/
@[simp] theorem toCompleted_apply (c : FirstOrderComparison A D g Omega d M) (p : ℕ) (m : M) :
    c.toCompleted p m =
      AdicCompletion.of (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
        (firstOrderExtension D Omega ⊗[D] M) (c m) :=
  rfl

/-- **The restatement is a generalisation and not a change of subject.**  The connection of the
completion of an uncompleted datum is the connection that datum already determined, namely
`Crystalline.FirstOrderComparison.completedConnection`. -/
theorem completedConnection_toCompleted (c : FirstOrderComparison A D g Omega d M) (p : ℕ)
    (m : M) :
    (c.toCompleted p).completedConnection m = c.completedConnection p m := by
  rw [CompletedFirstOrderComparison.completedConnection_apply, toCompleted_apply,
    AdicCompletion.map_of, completedConnection_apply]
  rfl

end FirstOrderComparison

end CompletedComparison

end Crystalline

end

end
