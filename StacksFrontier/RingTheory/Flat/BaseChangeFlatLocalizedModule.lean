module

public import StacksFrontier.RingTheory.Flat.FlatAtPointCriteria

/-!
# Flatness of a base change survives localizing the module

For two algebras `B` and `L` over a ring `A` and `M'` a localization of the `B`-module `M` at a
submonoid of `B`, flatness of `L ⊗[A] M` over `L` gives flatness of `L ⊗[A] M'` over `L`.

## Main results

* `Module.Flat.tensor_of_isLocalizedModule_of_tower`: for two algebras `B` and `L` over a ring
  `A` and `M'` a localization of the `B`-module `M` at a submonoid of `B`, flatness of
  `L ⊗[A] M` over `L` gives flatness of `L ⊗[A] M'` over `L`. Here the ring carrying the
  submonoid and the base ring of the flatness are unrelated, so the results of
  `StacksFrontier.RingTheory.Flat.FlatAtPointCriteria` do not apply; see the docstring.
-/

@[expose] public section

open TensorProduct

namespace Module.Flat

variable {A B L : Type*} [CommRing A] [CommRing B] [CommRing L] [Algebra A B] [Algebra A L]

/-- **The flatness criterion for a base change, read one level down.** For an `A`-module `X`,
the map `Q ⊗[L] (L ⊗[A] X) → P ⊗[L] (L ⊗[A] X)` attached to an `L`-submodule `Q` of an
`L`-module `P` is, after cancelling the base change, the map `Q ⊗[A] X → P ⊗[A] X`; so one is
injective exactly when the other is. -/
private theorem injective_rTensor_baseChange_iff (X : Type*) [AddCommGroup X] [Module A X]
    {P : Type*} [AddCommMonoid P] [Module L P] [Module A P] [IsScalarTower A L P]
    (Q : Submodule L P) :
    Function.Injective (Q.subtype.rTensor (L ⊗[A] X)) ↔
      Function.Injective (TensorProduct.AlgebraTensorModule.rTensor A X Q.subtype) := by
  set eQ := TensorProduct.AlgebraTensorModule.cancelBaseChange A L L (↥Q) X with heQ
  set eP := TensorProduct.AlgebraTensorModule.cancelBaseChange A L L P X with heP
  have key : (TensorProduct.AlgebraTensorModule.rTensor A X Q.subtype) ∘ₗ
      (eQ : ↥Q ⊗[L] (L ⊗[A] X) →ₗ[L] ↥Q ⊗[A] X) =
      (eP : P ⊗[L] (L ⊗[A] X) →ₗ[L] P ⊗[A] X) ∘ₗ Q.subtype.rTensor (L ⊗[A] X) := by
    ext q l
    simp [heQ, heP]
  refine (EquivLike.comp_injective _ eP).symm.trans
    (Iff.trans ?_ (EquivLike.injective_comp eQ _))
  exact Iff.of_eq (congrArg Function.Injective
    (funext fun z => (DFunLike.congr_fun key z).symm))

/-- **Flatness of a base change survives localizing the module.** Let `B` and `L` be two
algebras over `A` and let `g : M → M'` exhibit the `B`-module `M'` as the localization of `M` at
a multiplicative subset `S` of `B`. If `L ⊗[A] M` is flat over `L`, then so is `L ⊗[A] M'`.

Neither `Module.Flat.of_isLocalizedModule_of_tower` nor `Module.flat_of_isLocalizedModule`
applies: both ask the base ring of the flatness to map to the ring the localizing submonoid
lives in, and here `L` and `B` are two algebras over `A` with no map between them, so `L ⊗[A] M`
and `L ⊗[A] M'` carry no common algebra over which one is a localization of the other. The proof
is theirs, run one level down: over `L` the flatness criterion for `L ⊗[A] X` is the injectivity
of `Q ⊗[A] X → P ⊗[A] X` for every `L`-submodule `Q` of every `L`-module `P`
(`injective_rTensor_baseChange_iff`), and that is a statement about `X` as a `B`-module, to
which `IsLocalizedModule.rTensor` and `IsLocalizedModule.map_lTensor` apply. -/
theorem tensor_of_isLocalizedModule_of_tower {M M' : Type*} [AddCommGroup M] [Module A M]
    [Module B M] [IsScalarTower A B M] [AddCommGroup M'] [Module A M'] [Module B M']
    [IsScalarTower A B M'] (S : Submonoid B) (g : M →ₗ[B] M') [IsLocalizedModule S g]
    (h : Module.Flat L (L ⊗[A] M)) : Module.Flat L (L ⊗[A] M') := by
  rw [Module.Flat.iff_rTensor_injectiveₛ] at h ⊢
  intro P _ _ Q
  let : Module A P := Module.compHom P (algebraMap A L)
  have : IsScalarTower A L P := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hM : Function.Injective
      (TensorProduct.AlgebraTensorModule.lTensor B M (Q.subtype.restrictScalars A)) := by
    rw [TensorProduct.AlgebraTensorModule.coe_lTensor,
      LinearMap.lTensor_inj_iff_rTensor_inj,
      ← TensorProduct.AlgebraTensorModule.coe_rTensor (R := A) (A := L),
      ← injective_rTensor_baseChange_iff]
    exact h Q
  have hloc := IsLocalizedModule.map_injective
    (f := TensorProduct.AlgebraTensorModule.rTensor A (↥Q) g)
    (g := TensorProduct.AlgebraTensorModule.rTensor A P g) S _ hM
  rw [IsLocalizedModule.map_lTensor B S (Q.subtype.restrictScalars A) g] at hloc
  rwa [injective_rTensor_baseChange_iff,
    TensorProduct.AlgebraTensorModule.coe_rTensor (R := A) (A := L),
    ← LinearMap.lTensor_inj_iff_rTensor_inj,
    ← TensorProduct.AlgebraTensorModule.coe_lTensor (A := B)]

end Module.Flat

end
