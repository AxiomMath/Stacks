module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChange

/-!
# Functoriality of the base change map of completed de Rham complexes

`Crystalline.CompletedDeRham.baseChangeComplexHom` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedConnectionBaseChange.lean` is the map
`α : M ⊗^∧_D Ω^*_D ⟶ M' ⊗^∧_{D'} Ω^*_{D'}` of completed de Rham complexes induced by a map of
rings `D → D'` together with a graded comparison `ψ` of forms.  That construction says nothing
about how the map behaves under *composition* of two such base changes, nor what it is when the
base change is along the identity.  This module supplies the identity case.

## Why the identity case is the content, and not a triviality

`Crystalline.CompletedConnection.baseChangeCarrier p D D M` is not `M`: it is
`AdicCompletion (p) (D ⊗[D] M)`, the `p`-adic completion of `M`.  So base change along the
identity is not literally the identity map, and `baseChangeComplexHom` along the identity is the
comparison of `M ⊗^∧_D Ω^*_D` with `M̂ ⊗^∧_D Ω^*_D`.  What is proved here is that this comparison
is an **isomorphism of complexes** as soon as `M` is `p`-adically complete — which is
[Stacks, Tag 07JB] and is one of the four conditions a `Crystalline.Pair` carries, so it costs
nothing at the application site.

Completeness of `M` is not a convenience: `Crystalline.CompletedConnection.baseChangeInclusion`
is the canonical map `M → M̂` of a module into its `p`-adic completion, and no amount of work
makes that bijective for an incomplete `M`.  The hypothesis is therefore unremovable, and it is
stated as `Crystalline.IsPAdicallyComplete` rather than as a `Prop` standing in for a missing
proof.

## Where this is needed

`...SmallSite.computes07LH_of_computes07LG` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmoothPresentationDeRham.lean` carries `hab`, that
`β ≫ α = 𝟙`, as a hypothesis, and its documentation records exactly what is missing: "the
functoriality of `Crystalline.CompletedDeRham.baseChangeComplexHom` under composition and under
the identity: no declaration in this library states either".  This module states and proves
both, **in every degree separately**.

What it does *not* do is assemble the composition law into a statement about the complexes.  The
composite of two base changes carries the module `(M ⊗̂_D D') ⊗̂_{D'} D''` while the single base
change along `D → D''` carries `M ⊗̂_D D''`, so a composition law has to be stated along a
comparison of those two; the comparison is built here as
`Crystalline.CompletedConnection.baseChangeComposite`, and the degreewise law
`Crystalline.CompletedDeRham.baseChangeTerm_comp` holds along it.  Reading that law on
`CochainComplex AddCommGrpCat ℕ` needs one further thing, that the comparison is horizontal for
the two base-changed connections, hence a morphism of complexes; that is **proved**, in
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedConnectionBaseChangeComposite.lean`, as
`Crystalline.CompletedConnection.baseChange_baseChangeComposite`, and the composition law on the
complexes is `Crystalline.CompletedDeRham.baseChangeComplexHom_comp` there.

`hab` is still not discharged, and not by that module either: what it also needs is the
identification of the `Algebra` instances carried by
`...SmallSite.computes07LH_of_computes07LG` with the maps `a`, `b` that
`Crystalline.exists_completedEnvelopeRetract` produces existentially, and the compatibility of
that theorem's hypothesis `gamma` — the direction `G ∘ F ≅ id` of the second assertion of
[Stacks, Lemma 60.17.5, Tag 07L5] — with the two base changes.  Neither is available.

## How the identity case is proved

Everything reduces to one uncompleted identity, by the two functoriality lemmas
`Crystalline.adicCompletionMapₛₗ_comp_apply` and `Crystalline.adicCompletionMapₛₗ_id_apply`:
every map in sight is `Crystalline.adicCompletionMapₛₗ` of a map of uncompleted modules, and a
composite of two of them is the one induced by the uncompleted composite.  So both round trips
are checked on an uncompleted pure tensor `m ⊗ ω`, where they are the two round trips of
`TensorProduct.lid D M`.  No level-by-level argument and no density argument appears.

A chain map of complexes of abelian groups whose components are bijective is an isomorphism, by
`HomologicalComplex.Hom.isIso_of_components`; the inverse is then automatically a chain map, so
nothing has to be proved about the inverse commuting with the de Rham differentials — in
particular the collapse is never shown to be horizontal for the two connections, and does not
need to be.

## Main definitions

* `Crystalline.CompletedConnection.baseChangeCollapse` — the inverse `M̂ → M` of the inclusion
  `m ↦ 1 ⊗ m`, for a `p`-adically complete `M`.
* `Crystalline.CompletedConnection.baseChangeValuesCollapse` — that inverse on the completed
  tensor products, `M̂ ⊗̂_D Ω → M ⊗̂_D Ω`.
* `Crystalline.CompletedConnection.carrierTensorMap` and `..._carrierMap` — the comparison
  `M ⊗̂_D D' → M ⊗̂_D D''` of base-changed modules along `D' → D''`.
* `Crystalline.CompletedConnection.baseChangeComposite` — **the comparison
  `(M ⊗̂_D D') ⊗̂_{D'} D'' → M ⊗̂_D D''`** of the twice base-changed module with the once base
  changed one, along which functoriality under composition is stated.
* `Crystalline.CompletedConnection.compositeTensorMap` — two base changes of the uncompleted
  tensor product in succession, bundled as one map semilinear over `algebraMap D D''`.

## Main results

* `Crystalline.CompletedConnection.baseChangeCollapse_inclusion` and
  `..._inclusion_baseChangeCollapse` — the two round trips: the inclusion `m ↦ 1 ⊗ m` is a
  bijection onto the base change along the identity.
* `Crystalline.CompletedConnection.baseChangeValues_id_bijective` — the map induced on the
  values of a connection by the base change along the identity is bijective.
* `Crystalline.CompletedDeRham.baseChangeTerm_id_bijective` — the same for the degree-`i`
  component of the base change map of de Rham complexes.
* `Crystalline.CompletedDeRham.isIso_baseChangeComplexHom_id` — **the base change map of
  completed de Rham complexes along the identity is an isomorphism of complexes**, which is the
  identity half of the functoriality `hab` needs.
* `Crystalline.CompletedConnection.baseChangeComposite_inclusion` — the comparison of the twice
  base-changed module with the once base-changed one carries `1 ⊗ (1 ⊗ m)` to `1 ⊗ m`.
* `Crystalline.CompletedConnection.baseChangeValues_comp` and
  `Crystalline.CompletedDeRham.baseChangeTerm_comp` — **functoriality under composition, in
  each degree**: base changing along `D → D'` and then along `D' → D''` is base changing along
  `D → D''`, up to that comparison.

## References

* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
-/

@[expose] public noncomputable section

open CategoryTheory DividedPowers
open scoped TensorProduct

universe u v v' v'' w

namespace Crystalline

namespace CompletedConnection

/-! ### The base change along the identity, on the module -/

/-- Completing a semilinear map and then a semilinear left inverse of it is the identity. -/
private theorem adicCompletionMapₛₗ_leftInverse_apply {R S X Y : Type*} [CommRing R] [CommRing S]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module S Y] {σ : R →+* S} {τ : S →+* R}
    {I : Ideal R} {J : Ideal S} (f : X →ₛₗ[σ] Y) (g : Y →ₛₗ[τ] X) (hf : I.map σ ≤ J)
    (hg : J.map τ ≤ I) (h : ∀ x, g (f x) = x) (z : AdicCompletion I X) :
    adicCompletionMapₛₗ g hg (adicCompletionMapₛₗ f hf z) = z :=
  (adicCompletionMapₛₗ_comp_apply f g (LinearMap.id (R := R) (M := X)) hf hg
    (le_of_eq (Ideal.map_id I)) (fun x ↦ (h x).symm) z).symm.trans
    (adicCompletionMapₛₗ_id_apply _ (le_of_eq (Ideal.map_id I)) (fun _ ↦ rfl) z)

section IdentityCarrier

variable (p : ℕ) (D : Type u) [CommRing D] (M : Type w) [AddCommGroup M] [Module D M]

/-- **The collapse of the base change of `M` along the identity of `D`.**

`Crystalline.CompletedConnection.baseChangeCarrier p D D M` is `AdicCompletion (p) (D ⊗[D] M)`,
so for a `p`-adically complete `M` it is `M` itself, through `TensorProduct.lid` and
`AdicCompletion.ofLinearEquiv`.  This is that identification, written as the map back to `M`;
`Crystalline.CompletedConnection.baseChangeInclusion` is the map forwards. -/
public def baseChangeCollapse (hM : IsPAdicallyComplete p D M) :
    baseChangeCarrier p D D M →ₗ[D] M :=
  letI : IsAdicComplete (pAdicIdeal (A := D) p) M := hM
  (AdicCompletion.ofLinearEquiv (pAdicIdeal (A := D) p) M).symm.toLinearMap ∘ₗ
    adicCompletionMapLinear (TensorProduct.lid D M).toLinearMap (pAdicIdeal (A := D) p)

/-- The collapse, read on the canonical image of an uncompleted element of `D ⊗[D] M`. -/
public theorem baseChangeCollapse_of (hM : IsPAdicallyComplete p D M) (a : D ⊗[D] M) :
    baseChangeCollapse p D M hM
        (AdicCompletion.of (pAdicIdeal (A := D) p) (D ⊗[D] M) a) =
      TensorProduct.lid D M a := by
  let : IsAdicComplete (pAdicIdeal (A := D) p) M := hM
  change (AdicCompletion.ofLinearEquiv (pAdicIdeal (A := D) p) M).symm
      (adicCompletionMapLinear (TensorProduct.lid D M).toLinearMap
        (pAdicIdeal (A := D) p) (AdicCompletion.of _ _ a)) = _
  rw [adicCompletionMapLinear_of, AdicCompletion.ofLinearEquiv_symm_of]
  rfl

/-- **The collapse retracts the inclusion**: `1 ⊗ m` collapses to `m`. -/
public theorem baseChangeCollapse_inclusion (hM : IsPAdicallyComplete p D M) (m : M) :
    baseChangeCollapse p D M hM (baseChangeInclusion p D D M m) = m := by
  rw [baseChangeInclusion_apply, baseChangeCollapse_of]
  exact TensorProduct.lid_tmul (R := D) m 1 |>.trans (one_smul D m)

/-- **The inclusion retracts the collapse**, so the two are mutually inverse and the base change
of `M` along the identity is `M`.

This is where completeness of `M` is used twice over: once for the collapse to exist at all, and
once in `AdicCompletion.of_ofLinearEquiv_symm`, which says that the collapse composed with the
canonical map back into the completion is the identity.  No density argument is needed — both
sides are `Crystalline.adicCompletionMapₛₗ` of an uncompleted map and the identity is the
functoriality of that construction. -/
public theorem inclusion_baseChangeCollapse (hM : IsPAdicallyComplete p D M)
    (x : baseChangeCarrier p D D M) :
    baseChangeInclusion p D D M (baseChangeCollapse p D M hM x) = x := by
  let : IsAdicComplete (pAdicIdeal (A := D) p) M := hM
  have hof : AdicCompletion.of (pAdicIdeal (A := D) p) M (baseChangeCollapse p D M hM x) =
      adicCompletionMapLinear (TensorProduct.lid D M).toLinearMap
        (pAdicIdeal (A := D) p) x :=
    AdicCompletion.of_ofLinearEquiv_symm _ _
  have hinc : baseChangeInclusion p D D M (baseChangeCollapse p D M hM x) =
      adicCompletionMapLinear (TensorProduct.lid D M).symm.toLinearMap
        (pAdicIdeal (A := D) p)
        (AdicCompletion.of (pAdicIdeal (A := D) p) M (baseChangeCollapse p D M hM x)) := by
    rw [adicCompletionMapLinear_of]
    rfl
  rw [hinc, hof]
  exact adicCompletionMapₛₗ_leftInverse_apply _ _ _ _
    (fun y ↦ (TensorProduct.lid D M).symm_apply_apply y) x

end IdentityCarrier

/-! ### The base change along the identity, on the values of a connection -/

section IdentityValues

variable (p : ℕ) (D : Type u) [CommRing D] (M : Type w) [AddCommGroup M] [Module D M]
  (Omega : Type v) [AddCommGroup Omega] [Module D Omega]

/-- **The collapse on the completed tensor products**: `M̂ ⊗̂_D Ω → M ⊗̂_D Ω`, the completion of
`Crystalline.CompletedConnection.baseChangeCollapse` tensored with the identity of `Ω`. -/
public def baseChangeValuesCollapse (hM : IsPAdicallyComplete p D M) :
    CompletedTensor p D Omega (baseChangeCarrier p D D M) →ₗ[D] CompletedTensor p D Omega M :=
  adicCompletionMapLinear (LinearMap.rTensor Omega (baseChangeCollapse p D M hM))
    (pAdicIdeal (A := D) p)

/-- The collapse retracts the base change of the values along the identity. -/
public theorem baseChangeValuesCollapse_baseChangeValues (hM : IsPAdicallyComplete p D M)
    (z : CompletedTensor p D Omega M) :
    baseChangeValuesCollapse p D M Omega hM
        (baseChangeValues p D D M Omega Omega LinearMap.id z) = z := by
  have hcomp : ∀ y : M ⊗[D] Omega,
      LinearMap.rTensor Omega (baseChangeCollapse p D M hM)
          (baseChangeTensor p D D M Omega Omega LinearMap.id y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rw [_root_.map_zero, _root_.map_zero]
    | tmul m omega =>
      rw [baseChangeTensor, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
        baseChangeCollapse_inclusion]
      rfl
    | add a b ha hb => rw [_root_.map_add, _root_.map_add, ha, hb]
  exact adicCompletionMapₛₗ_leftInverse_apply _ _ _ _ hcomp z

/-- The base change of the values along the identity retracts the collapse. -/
public theorem baseChangeValues_baseChangeValuesCollapse (hM : IsPAdicallyComplete p D M)
    (w : CompletedTensor p D Omega (baseChangeCarrier p D D M)) :
    baseChangeValues p D D M Omega Omega LinearMap.id
        (baseChangeValuesCollapse p D M Omega hM w) = w := by
  have hcomp : ∀ y : baseChangeCarrier p D D M ⊗[D] Omega,
      baseChangeTensor p D D M Omega Omega LinearMap.id
          (LinearMap.rTensor Omega (baseChangeCollapse p D M hM) y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rw [_root_.map_zero, _root_.map_zero]
    | tmul x omega =>
      rw [LinearMap.rTensor_tmul, baseChangeTensor, TensorProduct.map_tmul,
        inclusion_baseChangeCollapse]
      rfl
    | add a b ha hb => rw [_root_.map_add, _root_.map_add, ha, hb]
  exact adicCompletionMapₛₗ_leftInverse_apply _ _ _ _ hcomp w

/-- **The map induced on the values of a connection by the base change along the identity is
bijective**, with inverse `Crystalline.CompletedConnection.baseChangeValuesCollapse`. -/
public theorem baseChangeValues_id_bijective (hM : IsPAdicallyComplete p D M) :
    Function.Bijective (baseChangeValues p D D M Omega Omega LinearMap.id) :=
  ⟨Function.LeftInverse.injective
      (baseChangeValuesCollapse_baseChangeValues p D M Omega hM),
    Function.RightInverse.surjective
      (baseChangeValues_baseChangeValuesCollapse p D M Omega hM)⟩

end IdentityValues

/-! ### Two base changes in succession, on the module -/

section Composition

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (D'' : Type u) [CommRing D''] [Algebra D' D''] [Algebra D D'']
  [IsScalarTower D D' D''] (M : Type w) [AddCommGroup M] [Module D M]

/-- The map `D' ⊗_D M → D'' ⊗_D M` along `D' → D''`, semilinear over that ring map: this is
the uncompleted map whose completion compares the two base-changed modules. -/
public def carrierTensorMap : (D' ⊗[D] M) →ₛₗ[algebraMap D' D''] (D'' ⊗[D] M) where
  toFun := TensorProduct.map ((Algebra.linearMap D' D'').restrictScalars D)
    (LinearMap.id (R := D) (M := M))
  map_add' x y := _root_.map_add _ x y
  map_smul' c x := by
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero, _root_.map_zero, smul_zero]
    | tmul b' m =>
      rw [TensorProduct.smul_tmul']
      change TensorProduct.map ((Algebra.linearMap D' D'').restrictScalars D)
          (LinearMap.id (R := D) (M := M)) ((c • b') ⊗ₜ[D] m) = _
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.smul_tmul']
      congr 1
      change algebraMap D' D'' (c • b') = algebraMap D' D'' c • algebraMap D' D'' b'
      rw [smul_eq_mul, map_mul, smul_eq_mul]
    | add a b ha hb =>
      rw [smul_add, _root_.map_add, _root_.map_add, ha, hb, smul_add]

/-- The map `D' ⊗_D M → D'' ⊗_D M` on a pure tensor. -/
@[simp] public theorem carrierTensorMap_tmul (b' : D') (m : M) :
    carrierTensorMap D D' D'' M (b' ⊗ₜ[D] m) = algebraMap D' D'' b' ⊗ₜ[D] m :=
  rfl

/-- The comparison map of base-changed modules `M ⊗̂_D D' → M ⊗̂_D D''`, the completion of
`Crystalline.CompletedConnection.carrierTensorMap`. -/
public def carrierMap :
    baseChangeCarrier p D D' M →ₛₗ[algebraMap D' D''] baseChangeCarrier p D D'' M :=
  adicCompletionMapₛₗ (carrierTensorMap D D' D'' M) (pAdicIdeal_map_le p D' D'')

/-- The comparison map of base-changed modules, on the canonical image of an uncompleted
element. -/
public theorem carrierMap_of (a : D' ⊗[D] M) :
    carrierMap p D D' D'' M (AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] M) a) =
      AdicCompletion.of (pAdicIdeal (A := D'') p) (D'' ⊗[D] M)
        (carrierTensorMap D D' D'' M a) :=
  adicCompletionMapₛₗ_of _ _ a

/-- The comparison map of base-changed modules, read as a `D'`-linear map into the `D''`-module:
semilinearity over `algebraMap D' D''` is `D'`-linearity for the restricted action. -/
public def carrierMapLinear :
    baseChangeCarrier p D D' M →ₗ[D'] baseChangeCarrier p D D'' M where
  toFun := carrierMap p D D' D'' M
  map_add' x y := _root_.map_add _ x y
  map_smul' c z := by
    rw [LinearMap.map_smulₛₗ]
    exact algebraMap_smul D'' c (carrierMap p D D' D'' M z)

/-- The `D'`-linear reading of the comparison map is that map. -/
@[simp] public theorem carrierMapLinear_apply (z : baseChangeCarrier p D D' M) :
    carrierMapLinear p D D' D'' M z = carrierMap p D D' D'' M z :=
  rfl

/-- **The comparison of the twice base-changed module with the once base-changed one**:
`(M ⊗̂_D D') ⊗̂_{D'} D'' → M ⊗̂_D D''`.

This is the map that functoriality under composition has to be stated along, the two modules
being different: the composite of two base changes carries the module
`(M ⊗̂_D D') ⊗̂_{D'} D''` while the single base change along `D → D''` carries `M ⊗̂_D D''`.
It is built from `Crystalline.CompletedConnection.carrierMapLinear` by
`LinearMap.liftBaseChange`, and the double completion collapses because
`Crystalline.CompletedConnection.isPAdicallyComplete_baseChangeCarrier` makes the target
`p`-adically complete — no hypothesis is needed for that. -/
public def baseChangeComposite :
    baseChangeCarrier p D' D'' (baseChangeCarrier p D D' M) →ₗ[D'']
      baseChangeCarrier p D D'' M :=
  letI : IsAdicComplete (pAdicIdeal (A := D'') p) (baseChangeCarrier p D D'' M) :=
    isPAdicallyComplete_baseChangeCarrier p D D'' M
  (AdicCompletion.ofLinearEquiv (pAdicIdeal (A := D'') p)
      (baseChangeCarrier p D D'' M)).symm.toLinearMap ∘ₗ
    adicCompletionMapLinear ((carrierMapLinear p D D' D'' M).liftBaseChange D'')
      (pAdicIdeal (A := D'') p)

/-- **The comparison carries the twice-included element to the once-included one**:
`1 ⊗ (1 ⊗ m) ↦ 1 ⊗ m`.  This is the one value of the comparison the functoriality needs. -/
public theorem baseChangeComposite_inclusion (m : M) :
    baseChangeComposite p D D' D'' M
        (baseChangeInclusion p D' D'' (baseChangeCarrier p D D' M)
          (baseChangeInclusion p D D' M m)) =
      baseChangeInclusion p D D'' M m := by
  let : IsAdicComplete (pAdicIdeal (A := D'') p) (baseChangeCarrier p D D'' M) :=
    isPAdicallyComplete_baseChangeCarrier p D D'' M
  change (AdicCompletion.ofLinearEquiv (pAdicIdeal (A := D'') p)
      (baseChangeCarrier p D D'' M)).symm
      (adicCompletionMapLinear ((carrierMapLinear p D D' D'' M).liftBaseChange D'')
        (pAdicIdeal (A := D'') p)
        (AdicCompletion.of _ _ ((1 : D'') ⊗ₜ[D'] baseChangeInclusion p D D' M m))) = _
  rw [adicCompletionMapLinear_of, AdicCompletion.ofLinearEquiv_symm_of,
    LinearMap.liftBaseChange_one_tmul, carrierMapLinear_apply, baseChangeInclusion_apply,
    carrierMap_of, carrierTensorMap_tmul, map_one, baseChangeInclusion_apply]

end Composition

/-! ### Two base changes in succession, on the values of a connection -/

section CompositionValues

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (D'' : Type u) [CommRing D''] [Algebra D' D''] [Algebra D D'']
  [IsScalarTower D D' D''] (M : Type w) [AddCommGroup M] [Module D M]
  (Omega : Type v) [AddCommGroup Omega] [Module D Omega]
  (Omega' : Type v') [AddCommGroup Omega'] [Module D' Omega']
  (Omega'' : Type v'') [AddCommGroup Omega''] [Module D'' Omega'']
  (psi : Omega →ₛₗ[algebraMap D D'] Omega') (psi' : Omega' →ₛₗ[algebraMap D' D''] Omega'')

/-- The two base changes of the uncompleted tensor product in succession,
`M ⊗_D Ω → (M' ⊗̂_{D'} D'') ⊗_{D''} Ω''`, as a single map semilinear over `algebraMap D D''`.

The composite of the two semilinear maps is semilinear over the composite of the two ring maps,
and that composite is `algebraMap D D''` by `IsScalarTower.algebraMap_apply`; bundling the
composite as one semilinear map is what lets `Crystalline.adicCompletionMapₛₗ_comp_apply` be
applied twice, once to split it into its two factors and once to compare it with the single base
change along `D → D''`. -/
public def compositeTensorMap : (M ⊗[D] Omega) →ₛₗ[algebraMap D D'']
    (baseChangeCarrier p D' D'' (baseChangeCarrier p D D' M) ⊗[D''] Omega'') where
  toFun y := baseChangeTensor p D' D'' (baseChangeCarrier p D D' M) Omega' Omega'' psi'
    (baseChangeTensor p D D' M Omega Omega' psi y)
  map_add' x y := by
    change baseChangeTensor p D' D'' (baseChangeCarrier p D D' M) Omega' Omega'' psi'
        (baseChangeTensor p D D' M Omega Omega' psi (x + y)) = _
    rw [_root_.map_add, _root_.map_add]
  map_smul' c x := by
    change baseChangeTensor p D' D'' (baseChangeCarrier p D D' M) Omega' Omega'' psi'
        (baseChangeTensor p D D' M Omega Omega' psi (c • x)) = _
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ,
      IsScalarTower.algebraMap_apply D D' D'']

/-- The comparison `Crystalline.CompletedConnection.baseChangeComposite` of the two base-changed
modules, read on the completed tensor products with `Ω''`. -/
public def baseChangeValuesComposite :
    CompletedTensor p D'' Omega''
        (baseChangeCarrier p D' D'' (baseChangeCarrier p D D' M)) →ₗ[D'']
      CompletedTensor p D'' Omega'' (baseChangeCarrier p D D'' M) :=
  adicCompletionMapLinear (LinearMap.rTensor Omega'' (baseChangeComposite p D D' D'' M))
    (pAdicIdeal (A := D'') p)

/-- **Functoriality under composition of the map induced on the values of a connection**: base
changing along `D → D'` and then along `D' → D''` is base changing along `D → D''`, up to the
comparison `Crystalline.CompletedConnection.baseChangeComposite` of the two base-changed
modules.

The comparison of forms along `D → D''` is given as a variable `psiComp` together with the
equation `hpsiComp` identifying it with `ψ' ∘ ψ`, rather than being spelled as that composite:
the composite of two semilinear maps carries the composite of the two ring maps, which is
`algebraMap D D''` only up to `IsScalarTower.algebraMap_apply` and not syntactically, so a
statement spelled with the composite could not be applied where a comparison along `D → D''` is
what one has.

Both sides are `Crystalline.adicCompletionMapₛₗ` of maps of uncompleted modules, so the whole
proof is two applications of `Crystalline.adicCompletionMapₛₗ_comp_apply` and one computation on
an uncompleted pure tensor `m ⊗ ω`, where it is
`Crystalline.CompletedConnection.baseChangeComposite_inclusion`. -/
public theorem baseChangeValues_comp (psiComp : Omega →ₛₗ[algebraMap D D''] Omega'')
    (hpsiComp : ∀ omega : Omega, psiComp omega = psi' (psi omega))
    (z : CompletedTensor p D Omega M) :
    baseChangeValuesComposite p D D' D'' M Omega''
        (baseChangeValues p D' D'' (baseChangeCarrier p D D' M) Omega' Omega'' psi'
          (baseChangeValues p D D' M Omega Omega' psi z)) =
      baseChangeValues p D D'' M Omega Omega'' psiComp z := by
  have hid : (pAdicIdeal (A := D'') p).map (RingHom.id D'') ≤ pAdicIdeal (A := D'') p :=
    le_of_eq (Ideal.map_id _)
  have hsplit := adicCompletionMapₛₗ_comp_apply
    (baseChangeTensor p D D' M Omega Omega' psi)
    (baseChangeTensor p D' D'' (baseChangeCarrier p D D' M) Omega' Omega'' psi')
    (compositeTensorMap p D D' D'' M Omega Omega' Omega'' psi psi')
    (pAdicIdeal_map_le p D D') (pAdicIdeal_map_le p D' D'') (pAdicIdeal_map_le p D D'')
    (fun _ ↦ rfl) z
  have hcomp : ∀ y : M ⊗[D] Omega,
      baseChangeTensor p D D'' M Omega Omega'' psiComp y =
        LinearMap.rTensor Omega'' (baseChangeComposite p D D' D'' M)
          (compositeTensorMap p D D' D'' M Omega Omega' Omega'' psi psi' y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero]
    | tmul m omega =>
      change baseChangeTensor p D D'' M Omega Omega'' psiComp (m ⊗ₜ[D] omega) =
        LinearMap.rTensor Omega'' (baseChangeComposite p D D' D'' M)
          (baseChangeTensor p D' D'' (baseChangeCarrier p D D' M) Omega' Omega'' psi'
            (baseChangeTensor p D D' M Omega Omega' psi (m ⊗ₜ[D] omega)))
      simp only [baseChangeTensor, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
        baseChangeComposite_inclusion, hpsiComp]
    | add a b ha hb =>
      rw [_root_.map_add, _root_.map_add, _root_.map_add, ha, hb]
  have hjoin := adicCompletionMapₛₗ_comp_apply
    (compositeTensorMap p D D' D'' M Omega Omega' Omega'' psi psi')
    (LinearMap.rTensor Omega'' (baseChangeComposite p D D' D'' M))
    (baseChangeTensor p D D'' M Omega Omega'' psiComp)
    (pAdicIdeal_map_le p D D'') hid (pAdicIdeal_map_le p D D'') hcomp z
  exact Eq.trans
    (congrArg (fun w ↦ baseChangeValuesComposite p D D' D'' M Omega'' w) hsplit.symm)
    hjoin.symm

end CompositionValues

end CompletedConnection

/-! ### The base change map of de Rham complexes along the identity -/

namespace CompletedDeRham

section IdentityComplex

variable (p : ℕ) (D : Type u) [CommRing D] (M : Type u) [AddCommGroup M] [Module D M]
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1)) (deRham : ∀ i, Om i →+ Om (i + 1))
  {d : D → Om 1} (nabla : CompletedConnection p D (Om 1) d M)
  (hdadd : ∀ x y : D, d (x + y) = d x + d y)
  (hdleib : ∀ x y : D, d (x * y) = x • d y + y • d x)
  (hleib : IsGradedLeibniz D Om wedge deRham d)

/-- **The degree-`i` component of the base change map of de Rham complexes along the identity is
bijective.**  It is `Crystalline.CompletedConnection.baseChangeValues` for the degree-`i`
comparison, which is the identity of `Ω^i_D`. -/
public theorem baseChangeTerm_id_bijective (hM : IsPAdicallyComplete p D M) (i : ℕ) :
    Function.Bijective (baseChangeTerm p D D M Om Om (fun _ ↦ LinearMap.id) i) :=
  CompletedConnection.baseChangeValues_id_bijective p D M (Om i) hM

include hdadd hdleib hleib in
/-- **The base change map of completed de Rham complexes along the identity of `D` is an
isomorphism of complexes**, for a `p`-adically complete `M`.

This is the identity half of the functoriality that `hab` of
`...SmallSite.computes07LH_of_computes07LG` needs: `β ≫ α` is the base change along
`a ∘ b = id_{D'}`, and this says what the base change along an identity is.  The other half,
functoriality under composition, is
`Crystalline.CompletedDeRham.baseChangeComplexHom_comp` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedConnectionBaseChangeComposite.lean`.

Every component is bijective by
`Crystalline.CompletedDeRham.baseChangeTerm_id_bijective`, and a chain map of complexes of
abelian groups with bijective components is an isomorphism, so the inverse is a chain map for
free.  The hypotheses are exactly those of
`Crystalline.CompletedDeRham.baseChangeComplexHom` with every primed datum instantiated to its
unprimed counterpart: the three compatibilities of the comparison hold by `rfl` for the identity
comparison, while `hdadd` and `hdleib` — additivity and the product rule for `d` — are what the
base-changed connection is built from and remain genuine hypotheses on `d`. -/
public theorem isIso_baseChangeComplexHom_id (hM : IsPAdicallyComplete p D M)
    (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
    (hsq' : IsSquareZero p D Om wedge deRham
      (CompletedConnection.baseChangeCarrier p D D M)
      (CompletedConnection.baseChange p D D M (Om 1) (Om 1) d LinearMap.id nabla hdadd hdleib
        (fun _ ↦ rfl)) hleib) :
    IsIso (baseChangeComplexHom p D D M Om Om (fun _ ↦ LinearMap.id) wedge wedge deRham deRham
      d nabla hdadd hdleib (fun _ ↦ rfl) hleib hleib (fun _ _ _ ↦ rfl) (fun _ _ ↦ rfl)
      hsq hsq') := by
  have : ∀ i : ℕ, IsIso ((baseChangeComplexHom p D D M Om Om (fun _ ↦ LinearMap.id) wedge wedge
      deRham deRham d nabla hdadd hdleib (fun _ ↦ rfl) hleib hleib (fun _ _ _ ↦ rfl)
      (fun _ _ ↦ rfl) hsq hsq').f i) := fun i ↦
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (baseChangeTerm_id_bijective p D M Om hM i)
  exact HomologicalComplex.Hom.isIso_of_components _

end IdentityComplex

/-! ### The components of the base change map under composition -/

section CompositionComplex

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (D'' : Type u) [CommRing D''] [Algebra D' D''] [Algebra D D'']
  [IsScalarTower D D' D''] (M : Type u) [AddCommGroup M] [Module D M]
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  (Om'' : ℕ → Type u) [∀ i, AddCommGroup (Om'' i)] [∀ i, Module D'' (Om'' i)]
  (psi : ∀ i, Om i →ₛₗ[algebraMap D D'] Om' i)
  (psi' : ∀ i, Om' i →ₛₗ[algebraMap D' D''] Om'' i)
  (psiComp : ∀ i, Om i →ₛₗ[algebraMap D D''] Om'' i)

/-- **Functoriality of the components of the base change map of completed de Rham complexes
under composition**: the degree-`i` component of the base change along `D → D'` followed by that
of the base change along `D' → D''` is the degree-`i` component of the base change along
`D → D''`, up to the comparison
`Crystalline.CompletedConnection.baseChangeComposite` of the twice base-changed module with the
once base-changed one.

This is `Crystalline.CompletedConnection.baseChangeValues_comp` for the degree-`i` comparison of
forms, `Crystalline.CompletedDeRham.baseChangeTerm` being that map read as a map of abelian
groups.  Reading it on the complexes themselves needs the comparison to be a morphism of
complexes, which is
`Crystalline.CompletedConnection.baseChange_baseChangeComposite` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedConnectionBaseChangeComposite.lean`; the law
on the complexes is `Crystalline.CompletedDeRham.baseChangeComplexHom_comp` there. -/
public theorem baseChangeTerm_comp
    (hpsiComp : ∀ (i : ℕ) (omega : Om i), psiComp i omega = psi' i (psi i omega))
    (i : ℕ) (x : CompletedTensor p D (Om i) M) :
    CompletedConnection.baseChangeValuesComposite p D D' D'' M (Om'' i)
        (baseChangeTerm p D' D'' (CompletedConnection.baseChangeCarrier p D D' M) Om' Om''
          psi' i (baseChangeTerm p D D' M Om Om' psi i x)) =
      baseChangeTerm p D D'' M Om Om'' psiComp i x :=
  CompletedConnection.baseChangeValues_comp p D D' D'' M (Om i) (Om' i) (Om'' i)
    (psi i) (psi' i) (psiComp i) (hpsiComp i) x

end CompositionComplex

end CompletedDeRham

end Crystalline

end
